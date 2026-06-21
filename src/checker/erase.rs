//! Term erasure — removes proof-irrelevant terms.
//!
//! After type-checking, all terms classified as `prop`, `theorem`, or
//! `proof` are erased, leaving only `data` terms for code generation.
//!
//! ## Approach
//!
//! Structural terms (`Let`, `If`, `Annot`, `ByProof`) always recurse
//! into children.  Leaf and semi-leaf terms use universe classification
//! to decide whether to keep or replace with `0` (the unit value).
//!
//! ## OOP design
//!
//! `Eraser` holds a reference to the term arena and exposes `erase(&self, t)`.
//! This avoids threading the arena through every recursive call and keeps
//! the interface consistent with the rest of the checker module.

use crate::checker::context::Context;
use crate::core::classify::classify;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, Term, Universe};

/// Erases proof-irrelevant subterms from a term tree.
///
/// Holds a reference to the term arena so that allocation helpers
/// (`lit_int`, `let_`, `app`, etc.) are always available without
/// passing the arena explicitly at each call site.
pub struct Eraser<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> Eraser<'bump> {
    /// Create a new eraser backed by the given arena.
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    /// The unit value used to replace erased terms.
    fn unit(&self) -> &'bump Term<'bump> {
        self.arena.lit_int(0)
    }

    /// Check whether a term is the erasure unit value (structural check,
    /// not pointer equality).
    fn is_unit(t: &Term<'_>) -> bool {
        matches!(t, Term::LitInt(0))
    }

    /// Erase all non-`data` subterms, returning a term that contains only
    /// runtime-relevant `data` computation.
    pub fn erase(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            // ── Structural terms — always recurse into children ──
            Term::Let(name, val, body, _mconstr) => {
                let ev = self.erase(val);
                let eb = self.erase(body);
                self.arena.let_(*name, ev, eb, None)
            }

            Term::IfThenElse(cond, tbranch, fbranch) => {
                let ec = self.erase(cond);
                let et = self.erase(tbranch);
                let ef = self.erase(fbranch);
                self.arena.if_then_else(ec, et, ef)
            }

            Term::Annot(inner, _) => self.erase(inner),

            Term::ByProof(Some(inner), _) => self.erase(inner),
            Term::ByProof(None, _) | Term::AutoProof => self.unit(),

            // ── Application — keep only if the function is data-level ──
            Term::App(f, a) => {
                if classify(&Context::empty(), f) == Some(Universe::UData) {
                    self.arena.app(self.erase(f), self.erase(a))
                } else {
                    self.unit()
                }
            }

            // ── Func — erase parameter constraints and return type ──
            Term::Func(fname, params, m_ret, body) => {
                // Erase each constraint; if it becomes unit, drop to None.
                let erased_params: Vec<(Name<'bump>, Option<&'bump Term<'bump>>)> = params
                    .iter()
                    .map(|(n, mc)| {
                        let ec = mc.map(|c| self.erase(c));
                        (*n, ec.filter(|c| !Self::is_unit(c)))
                    })
                    .collect();
                let erased_ret = m_ret.map(|r| self.erase(r)).filter(|r| !Self::is_unit(r));
                let erased_body = self.erase(body);
                self.arena.func(
                    *fname,
                    self.arena.alloc_slice(&erased_params),
                    erased_ret,
                    erased_body,
                )
            }

            // ── Pi / Refine — prop-level, erase ──
            Term::Pi(..) => self.unit(),
            // Refinement: keep the parent type (it's a type name, not
            // runtime data — the C backend filters it out).  Erase the
            // predicate.
            Term::Refine(_, parent, _pred) => parent,

            // ── Universe — keep only UData ──
            Term::Universe(Universe::UData) => t,
            Term::Universe(_) => self.unit(),

            // ── Builtin — keep only data-classified builtins ──
            Term::Builtin(_) => {
                if classify(&Context::empty(), t) == Some(Universe::UData) {
                    t
                } else {
                    self.unit()
                }
            }

            // ── Leaves — all data, keep as-is ──
            Term::LitInt(_)
            | Term::LitBool(_)
            | Term::Lam(_)
            | Term::PrimOp(_)
            | Term::RefParam
            | Term::This
            | Term::Var(_) => t,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::syntax::Tactic;
    use bumpalo::Bump;

    fn setup() -> (&'static Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        (b, TermArena::new(b))
    }

    fn s<'bump>(arena: &TermArena<'bump>, s: &str) -> crate::core::syntax::Name<'bump> {
        arena.alloc_str(s)
    }

    // ── Data leaves survive ──

    #[test]
    fn lit_int_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.lit_int(42));
        assert_eq!(*t, *arena.lit_int(42));
    }

    #[test]
    fn lit_bool_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.lit_bool(true));
        assert_eq!(*t, *arena.lit_bool(true));
    }

    #[test]
    fn lam_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.lam(arena.lit_int(1)));
        assert_eq!(*t, *arena.lam(arena.lit_int(1)));
    }

    #[test]
    fn var_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.var(0));
        assert_eq!(*t, *arena.var(0));
    }

    #[test]
    fn app_of_data_survives() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let add = arena.prim_op(crate::core::syntax::PrimOp::Add);
        let app = arena.app(arena.app(add, arena.lit_int(1)), arena.lit_int(2));
        let t = eraser.erase(app);
        assert!(!matches!(*t, Term::LitInt(0)));
    }

    // ── Proof / prop leaves vanish ──

    #[test]
    fn auto_proof_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.auto_proof());
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn by_proof_none_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
        let t = eraser.erase(arena.by_proof(None, tactics));
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn by_proof_some_keeps_subject() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let tactics = arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]);
        let term = arena.by_proof(Some(arena.lit_int(42)), tactics);
        let t = eraser.erase(term);
        assert_eq!(*t, *arena.lit_int(42));
    }

    #[test]
    fn pi_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let pi = arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        );
        let t = eraser.erase(pi);
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn refine_keeps_parent() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let refine = arena.refine(
            s(&arena, "nat"),
            arena.builtin(s(&arena, "int")),
            arena.lit_bool(true),
        );
        // Parent type is kept as-is (not re-erased — it's a type name).
        let t = eraser.erase(refine);
        assert_eq!(*t, *arena.builtin(s(&arena, "int")));
    }

    #[test]
    fn annot_erases_constraint() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let annot = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")));
        let t = eraser.erase(annot);
        assert_eq!(*t, *arena.lit_int(5));
    }

    // ── Structural terms ──

    #[test]
    fn let_keeps_binding() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let term = arena.let_(
            s(&arena, "x"),
            arena.by_proof(
                Some(arena.lit_int(5)),
                arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]),
            ),
            arena.var(0),
            Some(arena.builtin(s(&arena, "int"))),
        );
        // After erasure: let x = 5 in x  (proof and constraint gone)
        let t = eraser.erase(term);
        let expected = arena.let_(s(&arena, "x"), arena.lit_int(5), arena.var(0), None);
        assert_eq!(*t, *expected);
    }

    #[test]
    fn if_erases_branches() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let term = arena.if_then_else(
            arena.lit_bool(true),
            arena.by_proof(
                Some(arena.lit_int(10)),
                arena.alloc_slice(&[Tactic::Exact(arena.lit_bool(true))]),
            ),
            arena.lit_int(20),
        );
        let t = eraser.erase(term);
        let expected =
            arena.if_then_else(arena.lit_bool(true), arena.lit_int(10), arena.lit_int(20));
        assert_eq!(*t, *expected);
    }

    #[test]
    fn func_erases_param_constraints() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let func = arena.func(
            s(&arena, "f"),
            arena.alloc_slice(&[(s(&arena, "x"), Some(arena.builtin(s(&arena, "int"))))]),
            Some(arena.builtin(s(&arena, "int"))),
            arena.var(0),
        );
        let t = eraser.erase(func);
        // Parameter constraint and return type become None (erased to unit).
        let expected = arena.func(
            s(&arena, "f"),
            arena.alloc_slice(&[(s(&arena, "x"), None)]),
            None,
            arena.var(0),
        );
        assert_eq!(*t, *expected);
    }

    #[test]
    fn builtin_proof_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.builtin(s(&arena, "proof")));
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn builtin_int_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        let t = eraser.erase(arena.builtin(s(&arena, "int")));
        // `int` is prop-classified, so it vanishes
        assert_eq!(*t, *arena.lit_int(0));
    }

    #[test]
    fn app_of_logic_vanishes() {
        let (_b, arena) = setup();
        let eraser = Eraser::new(&arena);
        // `∧ true false` — and is prop-classified
        let and_term = arena.app(
            arena.app(arena.builtin(s(&arena, "and")), arena.lit_bool(true)),
            arena.lit_bool(false),
        );
        let t = eraser.erase(and_term);
        assert_eq!(*t, *arena.lit_int(0));
    }
}
