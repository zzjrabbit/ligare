use std::fmt;

use crate::config::{UNIVERSE_DATA, UNIVERSE_PROOF, UNIVERSE_PROP, UNIVERSE_THEOREM};
use crate::core::pool::TermArena;

/// A name in the AST, arena-allocated for zero-copy sharing.
pub type Name<'bump> = &'bump str;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Universe {
    UData,
    UProp,
    UTheorem,
    UProof,
}

impl fmt::Display for Universe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Universe::UData => write!(f, "{UNIVERSE_DATA}"),
            Universe::UProp => write!(f, "{UNIVERSE_PROP}"),
            Universe::UTheorem => write!(f, "{UNIVERSE_THEOREM}"),
            Universe::UProof => write!(f, "{UNIVERSE_PROOF}"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod_,
    Eq,
    Lt,
    Gt,
    Le,
    Ge,
    Neq,
}

impl fmt::Display for PrimOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimOp::Add => write!(f, "+"),
            PrimOp::Sub => write!(f, "-"),
            PrimOp::Mul => write!(f, "*"),
            PrimOp::Div => write!(f, "/"),
            PrimOp::Mod_ => write!(f, "%"),
            PrimOp::Eq => write!(f, "=="),
            PrimOp::Lt => write!(f, "<"),
            PrimOp::Gt => write!(f, ">"),
            PrimOp::Le => write!(f, "<="),
            PrimOp::Ge => write!(f, ">="),
            PrimOp::Neq => write!(f, "/="),
        }
    }
}

impl PrimOp {
    /// Compute the result of this primitive operation on two integer operands.
    /// Division and modulo by zero return `LitInt(0)`.
    pub fn apply(&self, x: i64, y: i64) -> Term<'static> {
        match self {
            PrimOp::Add => Term::LitInt(x.wrapping_add(y)),
            PrimOp::Sub => Term::LitInt(x.wrapping_sub(y)),
            PrimOp::Mul => Term::LitInt(x.wrapping_mul(y)),
            PrimOp::Div => {
                if y == 0 {
                    Term::LitInt(0)
                } else {
                    Term::LitInt(x / y)
                }
            }
            PrimOp::Mod_ => {
                if y == 0 {
                    Term::LitInt(0)
                } else {
                    Term::LitInt(x % y)
                }
            }
            PrimOp::Eq => Term::LitBool(x == y),
            PrimOp::Lt => Term::LitBool(x < y),
            PrimOp::Gt => Term::LitBool(x > y),
            PrimOp::Le => Term::LitBool(x <= y),
            PrimOp::Ge => Term::LitBool(x >= y),
            PrimOp::Neq => Term::LitBool(x != y),
        }
    }
}

/// The core Term, arena-allocated via bumpalo.
///
/// All recursive positions use `&'bump Term<'bump>` references instead of
/// `Box<Term>`, eliminating per-node heap allocations.  The entire term tree
/// lives in a single bump arena for fast allocation and excellent cache
/// locality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term<'bump> {
    Var(usize),
    App(&'bump Term<'bump>, &'bump Term<'bump>),
    Lam(&'bump Term<'bump>),
    LitInt(i64),
    LitBool(bool),
    PrimOp(PrimOp),
    Universe(Universe),
    Builtin(Name<'bump>),
    Pi(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Let(
        Name<'bump>,
        &'bump Term<'bump>,
        &'bump Term<'bump>,
        Option<&'bump Term<'bump>>,
    ),
    IfThenElse(&'bump Term<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Refine(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Annot(&'bump Term<'bump>, &'bump Term<'bump>),
    ByProof(&'bump Term<'bump>, &'bump Term<'bump>),
    AutoProof,
    RefParam,
    This,
    Func(
        Name<'bump>,
        &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        Option<&'bump Term<'bump>>,
        &'bump [Term<'bump>],
        &'bump [Term<'bump>],
        &'bump Term<'bump>,
    ),
    ProofBlock(&'bump Term<'bump>),
}

// ── TermVisitor: a trait for polymorphic term traversal ──

/// A visitor that walks over a `Term` tree, allowing custom logic at each node.
///
/// Implementors override the methods for the variants they care about;
/// the default implementations simply recurse into children.
///
/// The `walk` method drives the traversal.  Because Term nodes are arena-allocated
/// and immutable, the visitor returns `Option<&'bump Term<'bump>>` — `Some(new)` to
/// replace the node, or `None` to keep it unchanged.
pub trait TermVisitor<'bump> {
    /// The arena used for allocating replacement nodes.
    fn arena(&self) -> &TermArena<'bump>;

    fn visit_var(&self, _i: usize) -> Option<&'bump Term<'bump>> {
        None
    }
    fn visit_lam(&self, body: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        let b = self.walk(body);
        Some(self.arena().lam(b))
    }
    fn visit_app(
        &self,
        f: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let f2 = self.walk(f);
        let a2 = self.walk(a);
        Some(self.arena().app(f2, a2))
    }
    fn visit_pi(
        &self,
        name: Name<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let a2 = self.walk(a);
        let b2 = self.walk(b);
        Some(self.arena().pi(name, a2, b2))
    }
    fn visit_let(
        &self,
        name: Name<'bump>,
        val: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        mconstr: Option<&'bump Term<'bump>>,
    ) -> Option<&'bump Term<'bump>> {
        let v2 = self.walk(val);
        let mc2 = mconstr.map(|c| self.walk(c));
        let b2 = self.walk(body);
        Some(self.arena().let_(name, v2, b2, mc2))
    }
    fn visit_if(
        &self,
        cond: &'bump Term<'bump>,
        th: &'bump Term<'bump>,
        el: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let c2 = self.walk(cond);
        let th2 = self.walk(th);
        let el2 = self.walk(el);
        Some(self.arena().if_then_else(c2, th2, el2))
    }
    fn visit_annot(
        &self,
        t: &'bump Term<'bump>,
        c: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let t2 = self.walk(t);
        let c2 = self.walk(c);
        Some(self.arena().annot(t2, c2))
    }
    fn visit_by_proof(
        &self,
        t: &'bump Term<'bump>,
        p: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let t2 = self.walk(t);
        let p2 = self.walk(p);
        Some(self.arena().by_proof(t2, p2))
    }
    fn visit_refine(
        &self,
        name: Name<'bump>,
        parent: &'bump Term<'bump>,
        pred: &'bump Term<'bump>,
    ) -> Option<&'bump Term<'bump>> {
        let par2 = self.walk(parent);
        let p2 = self.walk(pred);
        Some(self.arena().refine(name, par2, p2))
    }
    fn visit_proof_block(&self, inner: &'bump Term<'bump>) -> Option<&'bump Term<'bump>> {
        let i2 = self.walk(inner);
        Some(self.arena().proof_block(i2))
    }
    fn visit_builtin(&self, _name: Name<'bump>) -> Option<&'bump Term<'bump>> {
        None
    }
    fn visit_ref_param(&self) -> Option<&'bump Term<'bump>> {
        None
    }
    fn visit_this(&self) -> Option<&'bump Term<'bump>> {
        None
    }

    /// Walk the entire term tree, dispatching to the appropriate visitor method.
    fn walk(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Var(i) => self.visit_var(*i).unwrap_or(t),
            Term::Lam(body) => self.visit_lam(body).unwrap_or(t),
            Term::App(f, a) => self.visit_app(f, a).unwrap_or(t),
            Term::Pi(n, a, b) => self.visit_pi(n, a, b).unwrap_or(t),
            Term::Let(n, v, b, mc) => self.visit_let(n, v, b, *mc).unwrap_or(t),
            Term::IfThenElse(c, th, el) => self.visit_if(c, th, el).unwrap_or(t),
            Term::Annot(inner, ct) => self.visit_annot(inner, ct).unwrap_or(t),
            Term::ByProof(inner, p) => self.visit_by_proof(inner, p).unwrap_or(t),
            Term::Refine(n, par, p) => self.visit_refine(n, par, p).unwrap_or(t),
            Term::ProofBlock(inner) => self.visit_proof_block(inner).unwrap_or(t),
            Term::Builtin(n) => self.visit_builtin(*n).unwrap_or(t),
            Term::RefParam => self.visit_ref_param().unwrap_or(t),
            Term::This => self.visit_this().unwrap_or(t),
            // Other leaf nodes — keep as-is
            _ => t,
        }
    }
}

#[cfg(test)]
#[allow(clippy::redundant_clone)]
mod tests {
    use super::*;
    use crate::core::pool::TermArena;

    fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(bumpalo::Bump::new()));
        (b, TermArena::new(b))
    }

    fn s<'a>(arena: &TermArena<'a>, name: &str) -> &'a str {
        arena.alloc_str(name)
    }

    // ── PrimOp::apply ──

    #[test]
    fn primop_add() {
        assert_eq!(PrimOp::Add.apply(3, 5), Term::LitInt(8));
    }

    #[test]
    fn primop_sub() {
        assert_eq!(PrimOp::Sub.apply(10, 3), Term::LitInt(7));
    }

    #[test]
    fn primop_sub_negative_result() {
        assert_eq!(PrimOp::Sub.apply(3, 10), Term::LitInt(-7));
    }

    #[test]
    fn primop_mul() {
        assert_eq!(PrimOp::Mul.apply(4, 5), Term::LitInt(20));
    }

    #[test]
    fn primop_mul_with_zero() {
        assert_eq!(PrimOp::Mul.apply(0, 100), Term::LitInt(0));
    }

    #[test]
    fn primop_mul_negative() {
        assert_eq!(PrimOp::Mul.apply(-3, 4), Term::LitInt(-12));
    }

    #[test]
    fn primop_div() {
        assert_eq!(PrimOp::Div.apply(10, 3), Term::LitInt(3));
    }

    #[test]
    fn primop_div_by_zero() {
        assert_eq!(PrimOp::Div.apply(10, 0), Term::LitInt(0));
    }

    #[test]
    fn primop_div_negative() {
        assert_eq!(PrimOp::Div.apply(-10, 3), Term::LitInt(-3));
    }

    #[test]
    fn primop_mod() {
        assert_eq!(PrimOp::Mod_.apply(10, 3), Term::LitInt(1));
    }

    #[test]
    fn primop_mod_by_zero() {
        assert_eq!(PrimOp::Mod_.apply(10, 0), Term::LitInt(0));
    }

    #[test]
    fn primop_mod_negative() {
        assert_eq!(PrimOp::Mod_.apply(-10, 3), Term::LitInt(-1));
    }

    #[test]
    fn primop_eq_true() {
        assert_eq!(PrimOp::Eq.apply(5, 5), Term::LitBool(true));
    }

    #[test]
    fn primop_eq_false() {
        assert_eq!(PrimOp::Eq.apply(5, 3), Term::LitBool(false));
    }

    #[test]
    fn primop_lt_true() {
        assert_eq!(PrimOp::Lt.apply(3, 5), Term::LitBool(true));
    }

    #[test]
    fn primop_lt_false() {
        assert_eq!(PrimOp::Lt.apply(5, 3), Term::LitBool(false));
    }

    #[test]
    fn primop_lt_same() {
        assert_eq!(PrimOp::Lt.apply(5, 5), Term::LitBool(false));
    }

    #[test]
    fn primop_gt_true() {
        assert_eq!(PrimOp::Gt.apply(5, 3), Term::LitBool(true));
    }

    #[test]
    fn primop_gt_false() {
        assert_eq!(PrimOp::Gt.apply(3, 5), Term::LitBool(false));
    }

    #[test]
    fn primop_le_true() {
        assert_eq!(PrimOp::Le.apply(3, 5), Term::LitBool(true));
    }

    #[test]
    fn primop_le_same() {
        assert_eq!(PrimOp::Le.apply(5, 5), Term::LitBool(true));
    }

    #[test]
    fn primop_le_false() {
        assert_eq!(PrimOp::Le.apply(5, 3), Term::LitBool(false));
    }

    #[test]
    fn primop_ge_true() {
        assert_eq!(PrimOp::Ge.apply(5, 3), Term::LitBool(true));
    }

    #[test]
    fn primop_ge_same() {
        assert_eq!(PrimOp::Ge.apply(5, 5), Term::LitBool(true));
    }

    #[test]
    fn primop_ge_false() {
        assert_eq!(PrimOp::Ge.apply(3, 5), Term::LitBool(false));
    }

    #[test]
    fn primop_neq_true() {
        assert_eq!(PrimOp::Neq.apply(5, 3), Term::LitBool(true));
    }

    #[test]
    fn primop_neq_false() {
        assert_eq!(PrimOp::Neq.apply(5, 5), Term::LitBool(false));
    }

    // ── PrimOp Display ──

    #[test]
    fn primop_display_all() {
        assert_eq!(PrimOp::Add.to_string(), "+");
        assert_eq!(PrimOp::Sub.to_string(), "-");
        assert_eq!(PrimOp::Mul.to_string(), "*");
        assert_eq!(PrimOp::Div.to_string(), "/");
        assert_eq!(PrimOp::Mod_.to_string(), "%");
        assert_eq!(PrimOp::Eq.to_string(), "==");
        assert_eq!(PrimOp::Lt.to_string(), "<");
        assert_eq!(PrimOp::Gt.to_string(), ">");
        assert_eq!(PrimOp::Le.to_string(), "<=");
        assert_eq!(PrimOp::Ge.to_string(), ">=");
        assert_eq!(PrimOp::Neq.to_string(), "/=");
    }

    // ── Universe Display ──

    #[test]
    fn universe_display_all() {
        assert_eq!(Universe::UData.to_string(), "data");
        assert_eq!(Universe::UProp.to_string(), "prop");
        assert_eq!(Universe::UTheorem.to_string(), "theorem");
        assert_eq!(Universe::UProof.to_string(), "proof");
    }

    // ── TermVisitor: ReplaceThis ──

    struct ReplaceThisVisitor<'bump> {
        arena: &'bump TermArena<'bump>,
        self_term: &'bump Term<'bump>,
    }

    impl<'bump> TermVisitor<'bump> for ReplaceThisVisitor<'bump> {
        fn arena(&self) -> &TermArena<'bump> {
            self.arena
        }
        fn visit_this(&self) -> Option<&'bump Term<'bump>> {
            Some(self.self_term)
        }
    }

    #[test]
    fn visitor_replace_this_in_app() {
        let (_b, arena) = a();
        let self_term = arena.lit_int(42);
        let body = arena.app(arena.this_(), arena.lit_int(1));
        let v = ReplaceThisVisitor {
            arena: &arena,
            self_term,
        };
        let result = v.walk(body);
        assert_eq!(*result, Term::App(arena.lit_int(42), arena.lit_int(1)));
    }

    #[test]
    fn visitor_replace_this_in_lam_body() {
        let (_b, arena) = a();
        let self_term = arena.lit_int(7);
        let lam = arena.lam(arena.this_());
        let v = ReplaceThisVisitor {
            arena: &arena,
            self_term,
        };
        let result = v.walk(lam);
        assert_eq!(*result, Term::Lam(arena.lit_int(7)));
    }

    #[test]
    fn visitor_replace_this_in_if_branches() {
        let (_b, arena) = a();
        let self_term = arena.lit_int(100);
        let body = arena.if_then_else(arena.lit_bool(true), arena.this_(), arena.lit_int(0));
        let v = ReplaceThisVisitor {
            arena: &arena,
            self_term,
        };
        let result = v.walk(body);
        assert_eq!(
            *result,
            Term::IfThenElse(arena.lit_bool(true), arena.lit_int(100), arena.lit_int(0))
        );
    }

    #[test]
    fn visitor_replace_this_leaf_unchanged() {
        let (_b, arena) = a();
        let v = ReplaceThisVisitor {
            arena: &arena,
            self_term: arena.lit_int(1),
        };
        assert_eq!(*v.walk(arena.var(0)), Term::Var(0));
        assert_eq!(*v.walk(arena.lit_int(5)), Term::LitInt(5));
        assert_eq!(*v.walk(arena.lit_bool(false)), Term::LitBool(false));
        assert_eq!(*v.walk(arena.ref_param()), Term::RefParam);
        assert_eq!(*v.walk(arena.auto_proof()), Term::AutoProof);
    }

    // ── TermVisitor: SubstRefParam ──

    struct SubstRefParamVisitor<'bump> {
        arena: &'bump TermArena<'bump>,
        subj: &'bump Term<'bump>,
    }

    impl<'bump> TermVisitor<'bump> for SubstRefParamVisitor<'bump> {
        fn arena(&self) -> &TermArena<'bump> {
            self.arena
        }
        fn visit_ref_param(&self) -> Option<&'bump Term<'bump>> {
            Some(self.subj)
        }
    }

    #[test]
    fn visitor_subst_refparam_in_predicate() {
        let (_b, arena) = a();
        let subj = arena.lit_int(5);
        let pred = arena.app(
            arena.app(arena.prim_op(PrimOp::Ge), arena.ref_param()),
            arena.lit_int(0),
        );
        let v = SubstRefParamVisitor {
            arena: &arena,
            subj,
        };
        let result = v.walk(pred);
        let expected = arena.app(
            arena.app(arena.prim_op(PrimOp::Ge), arena.lit_int(5)),
            arena.lit_int(0),
        );
        assert_eq!(*result, *expected);
    }

    #[test]
    fn visitor_subst_refparam_in_lam() {
        let (_b, arena) = a();
        let subj = arena.lit_int(7);
        let lam = arena.lam(arena.ref_param());
        let v = SubstRefParamVisitor {
            arena: &arena,
            subj,
        };
        let result = v.walk(lam);
        assert_eq!(*result, Term::Lam(arena.lit_int(7)));
    }

    #[test]
    fn visitor_subst_refparam_leaf_unchanged() {
        let (_b, arena) = a();
        let v = SubstRefParamVisitor {
            arena: &arena,
            subj: arena.lit_int(1),
        };
        assert_eq!(*v.walk(arena.lit_int(42)), Term::LitInt(42));
        assert_eq!(*v.walk(arena.lit_bool(true)), Term::LitBool(true));
        assert_eq!(*v.walk(arena.this_()), Term::This);
        assert_eq!(*v.walk(arena.auto_proof()), Term::AutoProof);
    }

    #[test]
    fn visitor_subst_refparam_in_refine() {
        let (_b, arena) = a();
        let subj = arena.lit_int(3);
        let pred = arena.app(
            arena.app(arena.prim_op(PrimOp::Neq), arena.ref_param()),
            arena.lit_int(0),
        );
        let refine = arena.refine(s(&arena, ""), arena.builtin(s(&arena, "int")), pred);
        let v = SubstRefParamVisitor {
            arena: &arena,
            subj,
        };
        let result = v.walk(refine);
        let expected_pred = arena.app(
            arena.app(arena.prim_op(PrimOp::Neq), arena.lit_int(3)),
            arena.lit_int(0),
        );
        assert_eq!(
            *result,
            Term::Refine("", arena.builtin("int"), expected_pred)
        );
    }

    // ── Default visitor: identity traversal ──

    struct IdentityVisitor<'bump> {
        arena: &'bump TermArena<'bump>,
    }

    impl<'bump> TermVisitor<'bump> for IdentityVisitor<'bump> {
        fn arena(&self) -> &TermArena<'bump> {
            self.arena
        }
    }

    #[test]
    fn visitor_identity_preserves_term() {
        let (_b, arena) = a();
        let term = arena.app(
            arena.lam(bin_test(
                &arena,
                PrimOp::Add,
                arena.var(0),
                arena.lit_int(1),
            )),
            arena.lit_int(5),
        );
        let v = IdentityVisitor { arena: &arena };
        let result = v.walk(term);
        assert_eq!(*result, *term);
    }

    #[test]
    fn visitor_identity_preserves_refine() {
        let (_b, arena) = a();
        let pred = arena.lam(bin_test(
            &arena,
            PrimOp::Ge,
            arena.ref_param(),
            arena.lit_int(0),
        ));
        let refine = arena.refine(s(&arena, "nat"), arena.builtin(s(&arena, "int")), pred);
        let v = IdentityVisitor { arena: &arena };
        let result = v.walk(refine);
        assert_eq!(*result, *refine);
    }

    fn bin_test<'bump>(
        arena: &TermArena<'bump>,
        op: PrimOp,
        l: &'bump Term<'bump>,
        r: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        arena.app(arena.app(arena.prim_op(op), l), r)
    }
}
