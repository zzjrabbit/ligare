pub mod builtin;
pub mod context;

use crate::checker::builtin::check_builtin;
use crate::checker::context::{
    ConstraintTable, Context, add_refine, add_theorem, expand_constraint, extend_ctx,
    extend_ctx_term, lookup_refine,
};
use crate::core::desugar::Desugarer;
use crate::core::eval::Evaluator;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, PrimOp, Term, Universe};

/// Common string constants to avoid repeated heap allocation.
const BOOL: &str = "bool";
const AND: &str = "and";
const OR: &str = "or";
const NOT: &str = "not";
const AND_INTRO: &str = "∧-intro";
const AND_ELIM_LEFT: &str = "∧-elim-left";
const EXPECTED_LAMBDA: &str = "Expected a lambda";

/// The type checker — bundles arena, constraint table, and checking logic.
///
/// Maintains a constraint table that is mutated when refinement definitions
/// are encountered (via `add_refinement`).  Individual `check` calls may
/// create temporary table clones without mutating the persistent state.
pub struct TypeChecker<'bump> {
    arena: &'bump TermArena<'bump>,
    evaluator: Evaluator<'bump>,
    desugarer: Desugarer<'bump>,
    table: ConstraintTable<'bump>,
}

impl<'bump> TypeChecker<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            evaluator: Evaluator::new(arena),
            desugarer: Desugarer::new(arena),
            table: vec![],
        }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Add a refinement definition to the persistent constraint table.
    pub fn add_refinement(
        &mut self,
        name: Name<'bump>,
        parent: &'bump Term<'bump>,
        predicate: &'bump Term<'bump>,
    ) {
        self.table.insert(0, (name, parent, predicate));
    }

    /// Get a reference to the persistent constraint table.
    pub fn table(&self) -> &ConstraintTable<'bump> {
        &self.table
    }

    /// Check a term against a constraint.
    pub fn check(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let desugared = self.desugarer.desugar(term);
        match desugared {
            Term::Var(i) => self.check_var(ctx, *i, constraint),
            Term::Annot(t, c) => {
                self.check(ctx, t, c)?;
                self.check(ctx, t, constraint)
            }
            Term::ByProof(t, _proof) => self.check(ctx, t, constraint),
            Term::Refine(name, parent, p) => {
                let new_table = add_refine(name, parent, p, &self.table);
                let checker = Self::with_table(self.arena, &new_table);
                checker.check(ctx, constraint, constraint)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => {
                self.check_if(ctx, cond, tbranch, fbranch, constraint)
            }
            Term::ProofBlock(proof_term) => {
                let evald = self.evaluator.eval(term)?;
                self.prove_with(ctx, evald, constraint, proof_term)
            }
            Term::Let(_name, val, body, mconstr) => {
                self.check_let(ctx, val, body, *mconstr, constraint)
            }
            _ => self.check_by_constraint(ctx, desugared, constraint),
        }
    }

    /// Create a temporary checker with a different table (for sub-checks).
    fn with_table(arena: &'bump TermArena<'bump>, table: &ConstraintTable<'bump>) -> Self {
        Self {
            arena,
            evaluator: Evaluator::new(arena),
            desugarer: Desugarer::new(arena),
            table: table.clone(),
        }
    }

    // ── private checking subroutines ──

    fn check_var(
        &self,
        ctx: &Context<'bump>,
        i: usize,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let expected = ctx
            .lookup(i)
            .ok_or_else(|| format!("Unbound variable index: {}", i))?;
        let expected_val = self.evaluator.eval(expected)?;
        let constraint_val = self.evaluator.eval(constraint)?;
        if expected_val == constraint_val || self.is_refinement_of(expected_val, constraint_val) {
            Ok(())
        } else {
            Err(format!(
                "Constraint mismatch for variable: expected {:?}, but got {:?}",
                expected_val, constraint_val
            ))
        }
    }

    fn check_if(
        &self,
        ctx: &Context<'bump>,
        cond: &'bump Term<'bump>,
        tbranch: &'bump Term<'bump>,
        fbranch: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let bool_name = self.arena.alloc_str(BOOL);
        self.check(ctx, cond, self.arena.builtin(bool_name))?;
        let ctx_t = add_theorem("_", cond, ctx);
        let ctx_f = add_theorem("_", self.not_term(cond), ctx);
        self.check(&ctx_t, tbranch, constraint)?;
        self.check(&ctx_f, fbranch, constraint)
    }

    fn check_let(
        &self,
        ctx: &Context<'bump>,
        val: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        mconstr: Option<&'bump Term<'bump>>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        if let Some(c) = mconstr {
            self.check(ctx, val, c)?;
        }
        let new_ctx = extend_ctx_term(constraint, ctx);
        self.check(&new_ctx, body, constraint)
    }

    fn check_by_constraint(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        if let Term::Refine(name, parent, p) = constraint {
            let new_table = add_refine(name, parent, p, &self.table);
            let checker = Self::with_table(self.arena, &new_table);
            checker.check(ctx, term, parent)?;
            return self.prove_auto(ctx, term, p);
        }

        let norm = self.evaluator.eval(constraint)?;
        match norm {
            Term::Builtin(name) => {
                if let Some(builtin_checker) = check_builtin(name) {
                    let evald = self.evaluator.eval(term)?;
                    builtin_checker(evald)
                } else if let Some((parent, pred)) = lookup_refine(name, &self.table) {
                    self.check(ctx, term, parent)?;
                    self.prove_auto(ctx, term, pred)
                } else {
                    Err(format!("Unknown builtin: {}", name))
                }
            }
            Term::Pi("", a, b) => self.check_arrow(ctx, term, a, b),
            Term::Pi(name, a, b) => self.check_pi(ctx, term, name, a, b),
            Term::Universe(Universe::UData) => Ok(()),
            Term::Var(j) => Err(format!(
                "Variable {} is a data term, cannot be used as a constraint",
                j
            )),
            Term::App(app_and, a) => self.try_check_logical_op(ctx, term, app_and, a, norm),
            _ => {
                let cname = self.constraint_name(norm);
                if let Some((parent, pred)) = lookup_refine(cname, &self.table) {
                    self.check(ctx, term, parent)?;
                    self.prove_auto(ctx, term, pred)
                } else {
                    Err(format!("Cannot use {:?} as a constraint", norm))
                }
            }
        }
    }

    fn try_check_logical_op(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        head: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
        norm: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let Term::App(builtin, b) = head else {
            return self.check_app_constraint(ctx, term, norm);
        };
        let Term::Builtin(name) = *builtin else {
            return self.check_app_constraint(ctx, term, norm);
        };
        match *name {
            AND => {
                self.check(ctx, term, arg)?;
                self.check(ctx, term, b)
            }
            OR => self
                .check(ctx, term, arg)
                .or_else(|_| self.check(ctx, term, b)),
            NOT => Ok(()),
            _ => self.check_app_constraint(ctx, term, norm),
        }
    }

    fn check_arrow(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Result<(), String> {
        self.check_pi_impl(ctx, t, a, b, None)
    }

    fn check_pi(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        name: Name<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Result<(), String> {
        self.check_pi_impl(ctx, t, a, b, Some(name))
    }

    fn check_pi_impl(
        &self,
        ctx: &Context<'bump>,
        t: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
        name: Option<Name<'bump>>,
    ) -> Result<(), String> {
        let t_val = self.evaluator.eval(t)?;
        let Term::Lam(body) = t_val else {
            return Err(EXPECTED_LAMBDA.to_string());
        };
        let new_ctx = match name {
            Some(n) if !n.is_empty() => extend_ctx(n, a, ctx),
            _ => extend_ctx_term(a, ctx),
        };
        self.check(&new_ctx, body, b)
    }

    fn check_app_constraint(
        &self,
        ctx: &Context<'bump>,
        term: &'bump Term<'bump>,
        constraint: &'bump Term<'bump>,
    ) -> Result<(), String> {
        if let Some(expanded) = expand_constraint(self.arena, &self.table, constraint) {
            return self.check(ctx, term, expanded);
        }

        if let Term::App(f, a) = constraint {
            let cname = self.constraint_name(f);
            if let Some((parent, body)) = lookup_refine(cname, &self.table)
                && matches!(parent, Term::Universe(Universe::UData))
            {
                return self.check(ctx, term, self.arena.app(body, a));
            }
        }

        Err(format!("Cannot use {:?} as a constraint", constraint))
    }

    fn constraint_name<'a>(&self, t: &Term<'a>) -> &'a str {
        match t {
            Term::Builtin(n) => n,
            Term::Refine(n, _, _) => n,
            _ => "?",
        }
    }

    fn is_refinement_of(&self, t1: &'bump Term<'bump>, t2: &'bump Term<'bump>) -> bool {
        if t1 == t2 {
            return true;
        }
        match t1 {
            Term::Builtin(n) | Term::Refine(n, _, _) => lookup_refine(n, &self.table)
                .map(|(parent, _)| self.is_refinement_of(parent, t2))
                .unwrap_or(false),
            _ => false,
        }
    }

    /// Wrap a term in a boolean negation.
    fn not_term(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        let body = self.arena.if_then_else(
            self.arena.var(0),
            self.arena.lit_bool(false),
            self.arena.lit_bool(true),
        );
        self.arena.app(self.arena.lam(body), t)
    }

    // ── Proof search ──

    fn prove_auto(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        pred: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let instantiated = self.subst_ref_param(subject, pred);
        let instantiated_val = self.evaluator.eval(instantiated)?;
        match instantiated_val {
            Term::LitBool(true) => Ok(()),
            Term::LitBool(false) => Err(format!("Predicate does not hold for {:?}", subject)),
            _ if self.search_ctx(ctx, subject, pred) => Ok(()),
            _ => self.try_simple_derive(pred, ctx, subject),
        }
    }

    fn subst_ref_param(
        &self,
        subj: &'bump Term<'bump>,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::RefParam => subj,
            Term::App(f, a) => {
                let f2 = self.subst_ref_param(subj, f);
                let a2 = self.subst_ref_param(subj, a);
                self.arena.app(f2, a2)
            }
            Term::Lam(b) => {
                let b2 = self.subst_ref_param(subj, b);
                self.arena.lam(b2)
            }
            Term::Let(n, v, b, mc) => {
                let v2 = self.subst_ref_param(subj, v);
                let b2 = self.subst_ref_param(subj, b);
                let mc2 = mc.map(|c| self.subst_ref_param(subj, c));
                self.arena.let_(n, v2, b2, mc2)
            }
            Term::IfThenElse(c, th, el) => {
                let c2 = self.subst_ref_param(subj, c);
                let th2 = self.subst_ref_param(subj, th);
                let el2 = self.subst_ref_param(subj, el);
                self.arena.if_then_else(c2, th2, el2)
            }
            Term::Annot(inner, c) => {
                let inner2 = self.subst_ref_param(subj, inner);
                let c2 = self.subst_ref_param(subj, c);
                self.arena.annot(inner2, c2)
            }
            Term::ByProof(inner, p) => {
                let inner2 = self.subst_ref_param(subj, inner);
                let p2 = self.subst_ref_param(subj, p);
                self.arena.by_proof(inner2, p2)
            }
            Term::Refine(n, par, p) => {
                let par2 = self.subst_ref_param(subj, par);
                let p2 = self.subst_ref_param(subj, p);
                self.arena.refine(n, par2, p2)
            }
            _ => t,
        }
    }

    fn search_ctx(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        target: &'bump Term<'bump>,
    ) -> bool {
        ctx.iter()
            .flat_map(|entry| &entry.theorems)
            .any(|thm| self.eval_eq(subject, thm, target))
    }

    fn eval_eq(
        &self,
        subject: &'bump Term<'bump>,
        t1: &'bump Term<'bump>,
        t2: &'bump Term<'bump>,
    ) -> bool {
        let v1 = self.evaluator.eval(self.subst_ref_param(subject, t1));
        let v2 = self.evaluator.eval(self.subst_ref_param(subject, t2));
        matches!((v1, v2), (Ok(a), Ok(b)) if a == b)
    }

    fn try_simple_derive(
        &self,
        pred: &'bump Term<'bump>,
        ctx: &Context<'bump>,
        _subject: &'bump Term<'bump>,
    ) -> Result<(), String> {
        let Some((a, b)) = self.try_match_neq(pred) else {
            return Err("Automatic proof failed: provide a manual proof with `by`".to_string());
        };
        let gt = self
            .arena
            .app(self.arena.app(self.arena.prim_op(PrimOp::Gt), a), b);
        let found = ctx
            .iter()
            .flat_map(|entry| &entry.theorems)
            .any(|thm| self.eval_eq_simple(gt, thm));
        if found {
            Ok(())
        } else {
            Err(format!("Cannot prove {:?}", pred))
        }
    }

    fn try_match_neq(
        &self,
        t: &'bump Term<'bump>,
    ) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
        let Term::App(neq_app, b) = t else {
            return None;
        };
        let Term::App(prim, a) = *neq_app else {
            return None;
        };
        if !matches!(prim, Term::PrimOp(PrimOp::Neq)) {
            return None;
        }
        Some((a, b))
    }

    fn eval_eq_simple(&self, t1: &'bump Term<'bump>, t2: &'bump Term<'bump>) -> bool {
        matches!(
            (self.evaluator.eval(t1), self.evaluator.eval(t2)),
            (Ok(a), Ok(b)) if a == b
        )
    }

    fn try_split_conj_proof<'t>(
        &self,
        goal: &'t Term<'t>,
        proof: &'t Term<'t>,
    ) -> Option<(&'t Term<'t>, &'t Term<'t>, &'t Term<'t>, &'t Term<'t>)> {
        let Term::App(and_app, b) = goal else {
            return None;
        };
        let Term::App(builtin, a) = *and_app else {
            return None;
        };
        let Term::Builtin(name) = *builtin else {
            return None;
        };
        if *name != AND {
            return None;
        }

        let Term::App(and_intro, pb) = proof else {
            return None;
        };
        let Term::App(builtin2, pa) = *and_intro else {
            return None;
        };
        let Term::Builtin(n2) = *builtin2 else {
            return None;
        };
        if *n2 != AND_INTRO {
            return None;
        }

        Some((a, pa, b, pb))
    }

    fn prove_with(
        &self,
        ctx: &Context<'bump>,
        subject: &'bump Term<'bump>,
        goal: &'bump Term<'bump>,
        proof: &'bump Term<'bump>,
    ) -> Result<(), String> {
        if let Some((a, pa, b, pb)) = self.try_split_conj_proof(goal, proof) {
            self.prove_with(ctx, subject, a, pa)?;
            return self.prove_with(ctx, subject, b, pb);
        }

        match proof {
            Term::Builtin(name) if *name == AND_ELIM_LEFT => Ok(()),
            Term::LitBool(true) => Ok(()),
            Term::AutoProof => self.prove_auto(ctx, subject, goal),
            Term::ProofBlock(inner) => self.prove_with(ctx, subject, goal, inner),
            _ => Err("Cannot use this term as a proof".to_string()),
        }
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn check<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    term: &'bump Term<'bump>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    let checker = TypeChecker {
        arena,
        evaluator: Evaluator::new(arena),
        desugarer: Desugarer::new(arena),
        table: table.clone(),
    };
    checker.check(ctx, term, constraint)
}
