//! Compiler orchestrator — coordinates parsing, constraint checking, and code generation.
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
use crate::config::BUILTIN_DATA;
use crate::core::classify::classify;
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::semantics::SemanticQueries;
use crate::core::syntax::{Name, Term, Universe};
use crate::diagnostic::Diagnostic;
use crate::front::parser::{TopLevel, parse_expr_top, parse_program};
use crate::pretty::PrettyPrinter;

mod monomorph;

fn read_source_file(file: &str) -> Result<String, Diagnostic> {
    fs::read_to_string(file)
        .map_err(|e| Diagnostic::new(format!("cannot read source file `{}`: {}", file, e)))
}

/// Borrowed view of the data C codegen needs.
///
/// This is intentionally a light wrapper over the existing compiler-owned
/// storage. It makes the handoff explicit without introducing a full pipeline
/// of separate IR types.
pub struct CodegenInput<'a, 'bump> {
    pub tops: &'a [TopLevel<'bump>],
    pub raw_defs: &'a [TopLevel<'bump>],
    pub fun_sigs: &'a [(&'bump str, FunSig)],
    pub union_types: &'a [(&'bump str, &'bump Term<'bump>)],
    pub struct_types: &'a [(&'bump str, &'bump Term<'bump>)],
}

struct ParsedProgram<'bump> {
    tops: Vec<TopLevel<'bump>>,
}

pub(crate) struct CodegenState<'bump> {
    raw_defs: Vec<TopLevel<'bump>>,
    fun_sigs: Vec<(&'bump str, FunSig)>,
    union_types: Vec<(&'bump str, &'bump Term<'bump>)>,
    struct_types: Vec<(&'bump str, &'bump Term<'bump>)>,
}

impl<'bump> CodegenState<'bump> {
    fn empty() -> Self {
        Self {
            raw_defs: Vec::new(),
            fun_sigs: Vec::new(),
            union_types: Vec::new(),
            struct_types: Vec::new(),
        }
    }
}

pub(crate) struct MonomorphizedProgram<'bump> {
    tops: Vec<TopLevel<'bump>>,
    codegen: CodegenState<'bump>,
}

struct ErasedProgram<'bump> {
    tops: Vec<TopLevel<'bump>>,
}

/// The compiler orchestrator — owns the bump allocator, term arena, and
/// coordinates parsing, constraint checking, and evaluation.
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
        let content = read_source_file(file)?;
        self.process_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn process_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.process_str(source, "<str>")
    }

    fn process_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("parse error: {}", e.message), e.span)
                .with_source(file, content)
        })?;
        for top in tops {
            self.process_top_level(top)
                .map_err(|d| d.with_source_if_missing(file, content))?;
        }
        Ok(())
    }

    /// Process a source file, collect top-level items, and check constraints.
    pub fn collect_file(&mut self, file: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        let content = read_source_file(file)?;
        self.collect_str(&content, file)
    }

    /// Process source code from a string (for testing).
    pub fn collect_file_str(&mut self, source: &str) -> Result<(), Diagnostic> {
        self.quiet = true;
        self.collect_str(source, "<str>")
    }

    fn collect_str(&mut self, content: &str, file: &str) -> Result<(), Diagnostic> {
        let parsed = self.parse_program_for_collection(content, file)?;
        for top in &parsed.tops {
            self.process_top_level(top.clone())
                .map_err(|d| d.with_source_if_missing(file, content))?;
        }
        let (union_names, struct_names) = self.build_name_sets(&parsed.tops);
        let codegen = self.collect_codegen_state(&parsed.tops, &union_names, &struct_names)?;
        let monomorphized = self.monomorphize_for_codegen(parsed.tops, codegen)?;
        self.apply_codegen_state(monomorphized.codegen);

        let eraser = Eraser::new(self.arena, self.checker.builtins.clone());
        let erased = self.erase_and_collect_tops(monomorphized.tops, &eraser);
        self.tops.extend(erased.tops);
        Ok(())
    }

    fn parse_program_for_collection(
        &self,
        content: &str,
        file: &str,
    ) -> Result<ParsedProgram<'bump>, Diagnostic> {
        let tops = parse_program(content, self.bump, self.arena).map_err(|e| {
            Diagnostic::with_span(format!("parse error: {}", e.message), e.span)
                .with_source(file, content)
        })?;
        Ok(ParsedProgram { tops })
    }

    /// Build sets of union and struct constraint names from the top-level definitions.
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

    /// Collect the codegen-facing inputs from the original un-erased tops.
    fn collect_codegen_state(
        &self,
        tops: &[TopLevel<'bump>],
        union_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<CodegenState<'bump>, Diagnostic> {
        let mut state = CodegenState::empty();
        for top in tops {
            if let TopLevel::TLDef(name, params, m_ret, body, _) = top {
                if matches!(body, Term::UnionDef(..)) {
                    state.union_types.push((name, body));
                } else if matches!(body, Term::StructDef(..)) {
                    state.struct_types.push((name, body));
                }
                if !params.is_empty()
                    && !matches!(body, Term::UnionDef(..) | Term::StructDef(..))
                    && Self::refinement_parts(body).is_none()
                {
                    let semantics = SemanticQueries::new(self.checker.builtins());
                    if params
                        .iter()
                        .any(|(_, c)| c.is_some_and(|t| semantics.is_type_parameter_constraint(t)))
                    {
                        continue;
                    }
                    let sig = FunSig::from_func(params, *m_ret, body, union_names, struct_names)?;
                    state.fun_sigs.push((name, sig));
                }
            }
        }

        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
        for top in tops {
            if let TopLevel::TLDef(name, params, m_ret, body_term, span) = top {
                if matches!(body_term, Term::UnionDef(..) | Term::StructDef(..)) {
                    continue;
                }
                let term = self.env.get(name).copied().unwrap_or(*body_term);
                let resolved = self.subst_top_level(term);
                let desugared = desugarer.desugar(resolved);
                state.raw_defs.push(TopLevel::TLDef(
                    name,
                    params,
                    *m_ret,
                    desugared,
                    span.clone(),
                ));
            }
        }
        Ok(state)
    }

    /// Erase, resolve, and filter top-level definitions. Skips union/struct
    /// typedefs (including generic ones) and drops zero-param type aliases after erasure.
    fn erase_and_collect_tops(
        &self,
        tops: Vec<TopLevel<'bump>>,
        eraser: &Eraser<'bump>,
    ) -> ErasedProgram<'bump> {
        let tops = tops
            .into_iter()
            .filter_map(|top| match top {
                TopLevel::TLDef(_name, _params, _m_ret, Term::UnionDef(..) | Term::StructDef(..), _) =>
                {
                    None
                }
                TopLevel::TLDef(name, params, m_ret, body_term, span) => {
                    let semantics = SemanticQueries::new(self.checker.builtins());
                    if params
                        .iter()
                        .any(|(_, c)| c.is_some_and(|t| semantics.is_type_parameter_constraint(t)))
                    {
                        return None;
                    }
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
            .collect();
        ErasedProgram { tops }
    }

    fn apply_codegen_state(&mut self, state: CodegenState<'bump>) {
        self.raw_defs = state.raw_defs;
        self.fun_sigs = state.fun_sigs;
        self.union_types = state.union_types;
        self.struct_types = state.struct_types;
    }

    /// Evaluate an expression string (for `--eval`).
    pub fn eval_expr(&self, expr: &str) -> Result<(), Diagnostic> {
        let term = parse_expr_top(expr, self.bump, self.arena).map_err(|err| {
            Diagnostic::with_span(format!("--eval parse error: {}", err.message), err.span)
                .with_source("--eval", expr)
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

    /// Get a single explicit codegen input view.
    pub fn codegen_input(&self) -> CodegenInput<'_, 'bump> {
        CodegenInput {
            tops: &self.tops,
            raw_defs: &self.raw_defs,
            fun_sigs: &self.fun_sigs,
            union_types: &self.union_types,
            struct_types: &self.struct_types,
        }
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
        let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
        let desugarer = crate::core::debruijn::Desugarer::new(self.arena);
        let func_body = params.iter().rfold(
            desugarer.desugar_with_names(body, &names),
            |b, &(_pn, _)| self.arena.lam(b),
        );
        let default = self.arena.builtin(self.arena.alloc_str("data"));
        let ret = m_ret
            .map(|t| desugarer.desugar_with_names(t, &names))
            .unwrap_or(default);
        let func_constraint = params
            .iter()
            .enumerate()
            .rev()
            .fold(ret, |b, (idx, &(pn, mc))| {
                let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                let dom = mc
                    .map(|t| desugarer.desugar_with_names(t, &dom_env))
                    .unwrap_or(default);
                self.arena.pi(pn, dom, b)
            });
        self.arena.annot(func_body, func_constraint)
    }

    /// Process a single top-level item.
    fn process_top_level(&mut self, top: TopLevel<'bump>) -> Result<(), Diagnostic> {
        match top {
            TopLevel::TLDef(name, params, _m_ret, body, span) => {
                let universe = classify(self.checker.builtins(), &empty_ctx(), body);
                if universe == Some(Universe::UProp) {
                    if self.register_prop_definition(name, params, _m_ret, body) {
                        return Ok(());
                    }
                }

                let previous = if self.has_type_parameter(params) {
                    self.env.insert(name, body)
                } else {
                    self.env.insert(name, self.definition_signature(body))
                };
                if !self.has_type_parameter(params)
                    && let Err(err) = self.checker.check(
                        &empty_ctx(),
                        self.resolve_all(body),
                        self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
                    )
                {
                    if let Some(prev) = previous {
                        self.env.insert(name, prev);
                    } else {
                        self.env.remove(name);
                    }
                    return Err(Diagnostic::with_span(
                        format!("definition {} failed: {}", name, err),
                        span,
                    ));
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
                            format!("check failed: {}", err),
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
                            format!("theorem check failed: {}", err),
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
                self.checker
                    .check(
                        &empty_ctx(),
                        resolved,
                        self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
                    )
                    .map_err(|err| {
                        Diagnostic::with_span(format!("show check failed: {}", err), _span.clone())
                    })?;
                let self_name = self.extract_func_name(_term);
                let mut ev = Evaluator::new(self.arena);
                if let Some(n) = self_name {
                    ev.set_self_name(n);
                }
                match ev.eval(resolved) {
                    Err(err) => {
                        return Err(Diagnostic::with_span(format!("show error: {}", err), _span));
                    }
                    Ok(val) => println!("{}", PrettyPrinter::pretty(val)),
                }
            }
            TopLevel::TLExpr(_term, _span) => {
                if self.quiet {
                    return Ok(());
                }
                let resolved = self.resolve_all(_term);
                self.checker
                    .check(
                        &empty_ctx(),
                        resolved,
                        self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA)),
                    )
                    .map_err(|err| {
                        Diagnostic::with_span(format!("eval check failed: {}", err), _span.clone())
                    })?;
                let self_name = self.extract_func_name(_term);
                let mut ev = Evaluator::new(self.arena);
                if let Some(n) = self_name {
                    ev.set_self_name(n);
                }
                match ev.eval(resolved) {
                    Err(err) => {
                        return Err(Diagnostic::with_span(format!("eval error: {}", err), _span));
                    }
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

    fn has_type_parameter(&self, params: &[(Name<'bump>, Option<&'bump Term<'bump>>)]) -> bool {
        params.iter().any(|(_, c)| {
            matches!(
                c,
                Some(Term::Builtin("prop" | "theorem" | "proof"))
                    | Some(Term::Named("prop" | "theorem" | "proof"))
                    | Some(Term::Universe(
                        Universe::UProp | Universe::UTheorem | Universe::UProof
                    ))
            )
        })
    }

    fn definition_signature(&self, body: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match body {
            Term::Annot(_, constraint) => {
                let stub = self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA));
                self.arena.annot(stub, constraint)
            }
            _ => body,
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
