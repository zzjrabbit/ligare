//! Compiler orchestrator — coordinates parsing, type checking, and code generation.
//!
//! Resolution logic lives in `resolve.rs`; this module holds the `Compiler`
//! struct and its lifecycle methods.

mod resolve;

use std::collections::{HashMap, HashSet};
use std::fs;

use bumpalo::Bump;

use crate::backend::ir::FunSig;
use crate::checker::TypeChecker;
use crate::checker::context::empty_ctx;
use crate::checker::erase::Eraser;
use crate::core::classify::classify;
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Term, Universe};
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, parse_expr_top, parse_program};
use crate::pretty::PrettyPrinter;

/// The compiler orchestrator — owns the bump allocator, term arena, and
/// coordinates parsing, type checking, and evaluation.
///
/// Resolution methods are implemented in `resolve.rs` via `impl Compiler`.
pub struct Compiler<'bump> {
    pub(crate) bump: &'bump Bump,
    pub(crate) arena: &'bump TermArena<'bump>,
    pub(crate) checker: TypeChecker<'bump>,
    /// Environment: maps top-level names to their desugared defining terms.
    pub(crate) env: HashMap<&'bump str, &'bump Term<'bump>>,
    /// Accumulated top-level items (for code generation).
    pub tops: Vec<TopLevel<'bump>>,
    /// Raw (un-erased) function definitions for on-demand codegen.
    /// Bodies are resolved & desugared, but type params are NOT erased yet.
    raw_defs: Vec<TopLevel<'bump>>,
    /// Function signatures extracted before erasure (for C codegen).
    fun_sigs: Vec<(&'bump str, FunSig)>,
    /// Union type definitions collected before erasure (for C codegen).
    pub union_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Struct type definitions collected before erasure (for C codegen).
    pub struct_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    /// Suppress diagnostic output (set during codegen).
    quiet: bool,
}

impl<'bump> Compiler<'bump> {
    pub fn new(bump: &'bump Bump, arena: &'bump TermArena<'bump>) -> Self {
        Self {
            bump,
            arena,
            checker: TypeChecker::new(arena),
            env: HashMap::new(),
            tops: vec![],
            raw_defs: vec![],
            fun_sigs: vec![],
            union_types: vec![],
            struct_types: vec![],
            quiet: false,
        }
    }

    /// Process a source file: parse it and handle each top-level item.
    pub fn process_file(&mut self, file: &str) -> Result<(), Diagnostic> {
        let content =
            fs::read_to_string(file).map_err(|e| Diagnostic::new(format!("{}: {}", file, e)))?;
        self.process_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn process_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.process_str(source, "<str>")
    }

    fn process_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("{}: parse error: {}", file, e.message), e.span)
        })?;
        for top in tops {
            self.process_top_level(top, file)?;
        }
        Ok(())
    }

    /// Process a source file, collect top-level items, and type-check.
    pub fn collect_file(&mut self, file: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        let content =
            fs::read_to_string(file).map_err(|e| Diagnostic::new(format!("{}: {}", file, e)))?;
        self.collect_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn collect_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        self.collect_str(source, "<str>")
    }

    fn collect_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("{}: parse error: {}", file, e.message), e.span)
        })?;
        for top in &tops {
            self.process_top_level(top.clone(), file)?;
        }
        let (union_names, struct_names) = self.build_name_sets(&tops);
        self.collect_signatures(&tops, &union_names, &struct_names)?;

        // Build raw (un-erased) definitions for on-demand codegen.
        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
        for top in &tops {
            if let TopLevel::TLDef(name, params, m_ret, body_term, span) = top {
                if matches!(body_term, Term::UnionDef(..) | Term::StructDef(..)) {
                    continue;
                }
                let term = self.env.get(name).copied().unwrap_or(*body_term);
                let resolved = self.subst_top_level(term);
                let desugared = desugarer.desugar(resolved);
                self.raw_defs.push(TopLevel::TLDef(
                    name,
                    params,
                    *m_ret,
                    desugared,
                    span.clone(),
                ));
            }
        }

        let eraser = Eraser::new(self.arena, self.checker.builtins.clone());
        let evald_tops = self.erase_and_collect_tops(tops, &eraser);
        self.tops.extend(evald_tops);
        Ok(())
    }

    /// Build sets of union and struct type names from the top-level definitions.
    fn build_name_sets(&self, tops: &[TopLevel<'bump>]) -> (HashSet<String>, HashSet<String>) {
        let union_names: HashSet<String> = tops
            .iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, _, _, Term::UnionDef(..), _) => Some(name.to_string()),
                _ => None,
            })
            .collect();
        let struct_names: HashSet<String> = tops
            .iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(name, _, _, Term::StructDef(..), _) => Some(name.to_string()),
                _ => None,
            })
            .collect();
        (union_names, struct_names)
    }

    /// Collect function signatures, union types, and struct types from the
    /// original (un-erased) top-level definitions before erasure.
    fn collect_signatures(
        &mut self,
        tops: &[TopLevel<'bump>],
        union_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<(), Diagnostic> {
        for top in tops {
            if let TopLevel::TLDef(name, params, m_ret, body, _) = top {
                if matches!(body, Term::UnionDef(..)) {
                    self.union_types.push((name, body));
                } else if matches!(body, Term::StructDef(..)) {
                    self.struct_types.push((name, body));
                }
                if !matches!(body, Term::UnionDef(..) | Term::StructDef(..)) {
                    let sig = FunSig::from_func(params, *m_ret, body, union_names, struct_names)?;
                    self.fun_sigs.push((name, sig));
                }
            }
        }
        Ok(())
    }

    /// Erase, resolve, and filter top-level definitions. Skips union/struct
    /// typedefs (including generic ones) and drops zero-param type aliases after erasure.
    fn erase_and_collect_tops(
        &self,
        tops: Vec<TopLevel<'bump>>,
        eraser: &Eraser<'bump>,
    ) -> Vec<TopLevel<'bump>> {
        tops.into_iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(_name, _params, _m_ret, Term::UnionDef(..) | Term::StructDef(..), _) =>
                {
                    None
                }
                TopLevel::TLDef(name, params, m_ret, body_term, span) => {
                    let term = self.env.get(name).copied().unwrap_or(body_term);
                    let resolved = self.subst_top_level(term);
                    let desugared = self.checker.desugarer.desugar(resolved);
                    let erased = eraser.erase(desugared);
                    Some(TopLevel::TLDef(name, params, m_ret, erased, span))
                }
                TopLevel::TLShow(term, span) | TopLevel::TLExpr(term, span) => {
                    let resolved = self.subst_top_level(term);
                    let desugared = self.checker.desugarer.desugar(resolved);
                    Some(TopLevel::TLShow(eraser.erase(desugared), span))
                }
                TopLevel::TLTheorem(name, _, body, span) => {
                    let resolved_body = self.subst_top_level(body);
                    let desugared = self.checker.desugarer.desugar(resolved_body);
                    let erased = eraser.erase(desugared);
                    Some(TopLevel::TLDef(name, &[], None, erased, span))
                }
                TopLevel::TLCheck(_, _, _) => None,
            })
            .filter(|top| {
                !matches!(
                    top,
                    TopLevel::TLDef(_, params, _, body, _)
                        if params.is_empty()
                            && matches!(body, Term::Builtin(_) | Term::Named(_) | Term::UnionDef(..) | Term::StructDef(..))
                )
            })
            .collect()
    }

    /// Evaluate an expression string (for `--eval`).
    pub fn eval_expr(&self, expr: &str) -> Result<(), Diagnostic> {
        let term = parse_expr_top(expr, self.bump, self.arena).map_err(|err| {
            Diagnostic::with_span(format!("--eval parse error: {}", err.message), err.span)
        })?;
        let resolved = self.resolve_all(term);
        let self_name = self.extract_func_name(term);
        let mut ev = Evaluator::new(self.arena);
        if let Some(n) = self_name {
            ev.set_self_name(n);
        }
        match ev.eval(resolved) {
            Err(err) => Err(Diagnostic::new(format!("--eval error: {}", err))),
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

    /// Get un-erased function definitions (for on-demand codegen).
    pub fn raw_defs(&self) -> &[TopLevel<'bump>] {
        &self.raw_defs
    }

    /// Get the function signatures extracted before erasure (for C codegen).
    pub fn fun_sigs(&self) -> &[(&'bump str, FunSig)] {
        &self.fun_sigs
    }

    // ── private helpers ──

    /// Desugar a generic union/struct definition (one with type parameters)
    /// into `Annot(Lam(...), Pi(...))` for env storage.
    fn desugar_top_def(
        &self,
        _name: Name<'bump>,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let func_body = params.iter().rfold(body, |b, &(_pn, _)| self.arena.lam(b));
        let default = self.arena.builtin(self.arena.alloc_str("data"));
        let func_type = params
            .iter()
            .rfold(m_ret.unwrap_or(default), |b, &(pn, mc)| {
                self.arena.pi(pn, mc.unwrap_or(default), b)
            });
        self.arena.annot(func_body, func_type)
    }

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>, file: &str) -> Result<(), Diagnostic> {
        match top {
            TopLevel::TLDef(name, params, _m_ret, body, _span) => {
                let universe = classify(self.checker.builtins(), &empty_ctx(), body);
                if universe == Some(Universe::UProp) {
                    if self.register_prop_definition(name, params, _m_ret, body) {
                        return Ok(());
                    }
                }

                if !self.quiet {
                    println!("[defined] {}", name);
                }
                self.env.insert(name, body);
            }
            TopLevel::TLCheck(term, constraint, span) => {
                let resolved = self.resolve_all(term);
                let resolved_constraint = self.resolve_all(constraint);
                match self
                    .checker
                    .check(&empty_ctx(), resolved, resolved_constraint)
                {
                    Err(err) => {
                        return Err(Diagnostic::with_span(
                            format!("{}: check failed: {}", file, err),
                            span,
                        ));
                    }
                    Ok(_) => {
                        if !self.quiet {
                            println!("[OK]");
                        }
                    }
                }
            }
            TopLevel::TLTheorem(name, prop, body, span) => {
                let resolved_body = self.resolve_all(body);
                let resolved_prop = self.resolve_all(prop);
                match self
                    .checker
                    .check(&empty_ctx(), resolved_body, resolved_prop)
                {
                    Err(err) => {
                        return Err(Diagnostic::with_span(
                            format!("{}: theorem check failed: {}", file, err),
                            span,
                        ));
                    }
                    Ok(_) => {
                        if !self.quiet {
                            println!("[theorem] {}", name);
                        }
                        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
                        self.env.insert(name, desugarer.desugar(body));
                    }
                }
            }
            TopLevel::TLShow(_term, _span) => {
                if self.quiet {
                    return Ok(());
                }
                let resolved = self.resolve_all(_term);
                let self_name = self.extract_func_name(_term);
                let mut ev = Evaluator::new(self.arena);
                if let Some(n) = self_name {
                    ev.set_self_name(n);
                }
                match ev.eval(resolved) {
                    Err(err) => eprintln!("{}: show error: {}", file, err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
            TopLevel::TLExpr(_term, _span) => {
                if self.quiet {
                    return Ok(());
                }
                let resolved = self.resolve_all(_term);
                let self_name = self.extract_func_name(_term);
                let mut ev = Evaluator::new(self.arena);
                if let Some(n) = self_name {
                    ev.set_self_name(n);
                }
                match ev.eval(resolved) {
                    Err(err) => eprintln!("{}: eval error: {}", file, err),
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
        }
        Ok(())
    }

    fn register_prop_definition(
        &mut self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> bool {
        match body {
            Term::UnionDef(..) => {
                if !self.quiet {
                    println!("[union] {}", name);
                }
                let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                let type_params = self.arena.alloc_slice(&type_param_names);
                self.checker.add_union(name, body, type_params);
                if !params.is_empty() {
                    let term = self.desugar_top_def(name, params, m_ret, body);
                    self.env.insert(name, term);
                }
                true
            }
            Term::StructDef(..) => {
                if !self.quiet {
                    println!("[struct] {}", name);
                }
                let type_param_names: Vec<_> = params.iter().map(|(n, _)| *n).collect();
                let type_params = self.arena.alloc_slice(&type_param_names);
                self.checker.add_struct(name, body, type_params);
                if !params.is_empty() {
                    let term = self.desugar_top_def(name, params, m_ret, body);
                    self.env.insert(name, term);
                }
                true
            }
            _ if params.is_empty() && Self::refinement_parts(body).is_some() => {
                let desugared = self.checker.desugarer.desugar(body);
                let (parent, predicate) = Self::refinement_parts(desugared).unwrap();
                if !self.quiet {
                    println!("[refinement] {}", name);
                }
                self.checker.add_refinement(name, parent, predicate);
                true
            }
            _ => false,
        }
    }

    fn refinement_parts(
        body: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        match body {
            Term::Refine(_, parent, predicate) => Some((*parent, *predicate)),
            Term::Annot(inner, _) => Self::refinement_parts(inner),
            _ => None,
        }
    }
}
