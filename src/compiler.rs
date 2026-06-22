use std::collections::HashMap;
use std::fs;

use bumpalo::Bump;

use crate::backend::ir::FunSig;
use crate::checker::TypeChecker;
use crate::checker::context::empty_ctx;
use crate::checker::erase::Eraser;
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::syntax::{FuncDef, Name, Term};
use crate::front::parser::{TopLevel, parse_expr_top, parse_program};
use crate::pretty::PrettyPrinter;

/// The compiler orchestrator — owns the bump allocator, term arena, and
/// coordinates parsing, type checking, and evaluation.
///
/// This struct bundles all compilation state together instead of threading
/// it through free functions.
pub struct Compiler<'bump> {
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
    evaluator: Evaluator<'bump>,
    checker: TypeChecker<'bump>,
    /// Environment: maps top-level names to their defining terms (O(1) lookup).
    env: HashMap<&'bump str, &'bump Term<'bump>>,
    /// Accumulated top-level items (for code generation).
    pub tops: Vec<TopLevel<'bump>>,
    /// Function signatures extracted before erasure (for C codegen).
    fun_sigs: Vec<(&'bump str, FunSig)>,
}

impl<'bump> Compiler<'bump> {
    pub fn new(bump: &'bump Bump, arena: &'bump TermArena<'bump>) -> Self {
        Self {
            bump,
            arena,
            evaluator: Evaluator::new(arena),
            checker: TypeChecker::new(arena),
            env: HashMap::new(),
            tops: vec![],
            fun_sigs: vec![],
        }
    }

    /// Process a source file: parse it and handle each top-level item.
    pub fn process_file(&mut self, file: &str) -> Result<(), String> {
        let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
        self.process_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn process_file_str(&mut self, source: &str) -> Result<(), String> {
        self.process_str(source, "<str>")
    }

    fn process_str(&mut self, content: &str, file: &str) -> Result<(), String> {
        let tops = parse_program(&content, self.bump, self.arena)
            .map_err(|e| format!("{}: parse error: {}", file, e))?;
        for top in tops {
            self.process_top_level(top, file)?;
        }
        Ok(())
    }

    /// Process a source file, collect top-level items, and type-check.
    pub fn collect_file(&mut self, file: &str) -> Result<(), String> {
        let content = fs::read_to_string(file).map_err(|e| format!("{}: {}", file, e))?;
        let tops = parse_program(&content, self.bump, self.arena)
            .map_err(|e| format!("{}: parse error: {}", file, e))?;
        for top in &tops {
            self.process_top_level(*top, file)?;
        }
        // Extract function signatures from the original (un-erased) FuncDef
        // so the C backend can emit correct parameter and return types.
        for top in &tops {
            match top {
                TopLevel::TLDef(name, func_def) => {
                    self.fun_sigs.push((
                        name,
                        FunSig::from_func(func_def.params, func_def.ret, func_def.body),
                    ));
                }
                _ => {}
            }
        }
        let eraser = Eraser::new(self.arena);
        let evald_tops: Vec<TopLevel<'bump>> = tops
            .into_iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, func_def) => {
                    let term = self.arena.desugar_func_def(func_def);
                    let resolved = self.subst_top_level(term);
                    let erased = eraser.erase(resolved);
                    let erased_func_def = FuncDef {
                        name,
                        params: func_def.params,
                        ret: func_def.ret,
                        body: erased,
                    };
                    Some(TopLevel::TLDef(
                        name,
                        self.arena.bump().alloc(erased_func_def),
                    ))
                }
                TopLevel::TLShow(term) | TopLevel::TLExpr(term) => {
                    let resolved = self.subst_top_level(term);
                    match self.evaluator.eval(resolved) {
                        Ok(val) => Some(TopLevel::TLShow(eraser.erase(val))),
                        Err(_) => Some(TopLevel::TLShow(eraser.erase(resolved))),
                    }
                }
                TopLevel::TLTheorem(name, _, body) => {
                    let resolved_body = self.subst_top_level(body);
                    let erased = eraser.erase(resolved_body);
                    let func_def = FuncDef {
                        name,
                        params: &[],
                        ret: None,
                        body: erased,
                    };
                    Some(TopLevel::TLDef(name, self.arena.bump().alloc(func_def)))
                }
                TopLevel::TLCheck(_, _) => None,
            })
            // Drop zero-param definitions whose body is a bare builtin
            // (type aliases like `def nat := int where ...`).
            .filter(|top| {
                !matches!(
                    top,
                    TopLevel::TLDef(_, FuncDef { params, body, .. })
                        if params.is_empty()
                            && matches!(body, Term::Builtin(_) | Term::UnionDef(..))
                )
            })
            .collect();
        self.tops.extend(evald_tops);
        Ok(())
    }

    /// Evaluate an expression string (for `--eval`).
    pub fn eval_expr(&self, expr: &str) -> Result<(), String> {
        let term = parse_expr_top(expr, self.bump, self.arena)
            .map_err(|err| format!("--eval parse error: {}", err))?;
        let resolved = self.subst_top_level(term);
        match self.evaluator.eval(resolved) {
            Err(err) => Err(format!("--eval error: {}", err)),
            Ok(val) => {
                println!("{}", PrettyPrinter::pretty(val));
                Ok(())
            }
        }
    }

    /// Get the collected top-level items (for code generation).
    pub fn tops(&self) -> &[TopLevel<'bump>] {
        &self.tops
    }

    /// Get the function signatures extracted before erasure (for C codegen).
    pub fn fun_sigs(&self) -> &[(&'bump str, FunSig)] {
        &self.fun_sigs
    }

    // ── private helpers ──

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>, file: &str) -> Result<(), String> {
        match top {
            TopLevel::TLDef(name, func_def) => {
                // parse_def always wraps the body in a FuncDef.
                // For zero-parameter definitions whose body is a
                // refinement, extract the Refine so it is properly
                // registered in the constraint table.
                if func_def.params.is_empty() && matches!(func_def.body, Term::UnionDef(..)) {
                    println!("[union] {}", name);
                    self.checker.add_union(name, func_def.body);
                } else if func_def.params.is_empty()
                    && matches!(func_def.body, Term::Refine(_, _, _))
                {
                    let Term::Refine(_, parent, predicate) = func_def.body else {
                        unreachable!()
                    };
                    println!("[refinement] {}", name);
                    self.checker.add_refinement(name, parent, predicate);
                } else {
                    let term = self.arena.desugar_func_def(func_def);
                    println!("[defined] {}", name);
                    self.env.insert(name, term);
                }
            }
            TopLevel::TLCheck(term, constraint) => {
                let resolved = self.subst_top_level(term);
                let resolved_constraint = self.subst_top_level(constraint);
                match self
                    .checker
                    .check(&empty_ctx(), resolved, resolved_constraint)
                {
                    Err(err) => return Err(format!("{}: check failed: {}", file, err)),
                    Ok(_) => println!("[OK]"),
                }
            }
            TopLevel::TLTheorem(name, prop, body) => {
                let resolved_body = self.subst_top_level(body);
                let resolved_prop = self.subst_top_level(prop);
                match self
                    .checker
                    .check(&empty_ctx(), resolved_body, resolved_prop)
                {
                    Err(err) => return Err(format!("{}: theorem check failed: {}", file, err)),
                    Ok(_) => {
                        println!("[theorem] {}", name);
                        self.env.insert(name, body);
                    }
                }
            }
            TopLevel::TLShow(term) => {
                let resolved = self.subst_top_level(term);
                match self.evaluator.eval(resolved) {
                    Err(err) => eprintln!("{}: show error: {}", file, err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
            TopLevel::TLExpr(term) => {
                let resolved = self.subst_top_level(term);
                match self.evaluator.eval(resolved) {
                    Err(err) => eprintln!("{}: eval error: {}", file, err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
        }
        Ok(())
    }

    /// Substitute known top-level definitions into a term (O(1) lookup).
    /// Also resolves variant constructors to Variant terms.
    fn subst_top_level(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // First pass: resolve env lookups only (not variants)
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) = t {
                if let Some(def) = self.env.get(name) {
                    return Some(def);
                }
            }
            None
        });
        // Second pass: resolve variant apps
        let t = self.resolve_variant_apps(t);
        // Third pass: resolve remaining zero-arg variant constructors
        self.arena.map(t, &|t| {
            if let Term::Builtin(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name) {
                    if field_specs.is_empty() {
                        return Some(self.arena.variant(uname, idx, &[]));
                    }
                }
            }
            None
        })
    }

    /// Convert `App*(Builtin(name), args...)` to `Variant(union, idx, args)`.
    fn resolve_variant_apps(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // Try top-level first (handles the common case)
        if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(t) {
            if args.len() == field_specs.len() {
                return self
                    .arena
                    .variant(uname, idx, self.arena.alloc_slice(&args));
            }
        }
        self.arena.map(t, &|node| {
            if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(node) {
                if args.len() == field_specs.len() {
                    return Some(
                        self.arena
                            .variant(uname, idx, self.arena.alloc_slice(&args)),
                    );
                }
            }
            None
        })
    }

    /// Unwrap an App chain to find a variant constructor and collect its args.
    fn collect_variant_args(
        &self,
        t: &'bump Term<'bump>,
    ) -> Option<(
        Name<'bump>,
        usize,
        &'bump [(Name<'bump>, &'bump Term<'bump>)],
        Vec<&'bump Term<'bump>>,
    )> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        loop {
            if let Term::App(f, a) = current {
                args.push(*a);
                current = f;
            } else {
                break;
            }
        }
        args.reverse();
        if let Term::Builtin(name) = current {
            if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name) {
                return Some((uname, idx, field_specs, args));
            }
        }
        None
    }
}
