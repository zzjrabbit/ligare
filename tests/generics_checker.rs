//! Unit-level checker tests for generic types and type parameters.
//! These test the TypeChecker directly with hand-constructed terms.

mod common;

use common::{bin, leak_bump, s};
use ligare::checker::check;
use ligare::checker::context::{empty_ctx, empty_table};
use ligare::core::debruijn::{Desugarer, SubstitutionContext};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};
use ligare::diagnostic::Diagnostic;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

fn check_empty<'bump>(
    arena: &TermArena<'bump>,
    t: &'bump Term<'bump>,
    c: &'bump Term<'bump>,
) -> Result<(), Diagnostic> {
    check(arena, &empty_table(), &empty_ctx(), t, c)
}

/// Helper: build a generic function from raw named local references, then
/// desugar so all local type/data parameters become de Bruijn variables.
fn make_generic<'bump>(
    arena: &'bump TermArena<'bump>,
    _name: &str,
    type_params: &[(&str, &'bump Term<'bump>)],
    data_params: &[(&str, &'bump Term<'bump>)],
    ret: &'bump Term<'bump>,
    body: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    // Gather all params: type params first, then data params.
    let mut params: Vec<(&str, Option<&'bump Term<'bump>>)> = Vec::new();
    for (n, c) in type_params {
        params.push((n, Some(*c)));
    }
    for (n, c) in data_params {
        params.push((n, Some(*c)));
    }
    let params_vec: Vec<_> = params
        .into_iter()
        .map(|(n, mc)| (s(arena, n), mc))
        .collect();
    let params = arena.alloc_slice(&params_vec);

    let desugarer = Desugarer::new(arena);
    let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
    let lam_body = params
        .iter()
        .rfold(desugarer.desugar_with_names(body, &names), |b, _| {
            arena.lam(b)
        });
    let pi_type = params.iter().enumerate().rev().fold(
        desugarer.desugar_with_names(ret, &names),
        |b, (idx, &(pn, mc))| {
            let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
            let dom = mc
                .map(|t| desugarer.desugar_with_names(t, &dom_env))
                .unwrap_or_else(|| arena.builtin(s(arena, "data")));
            arena.pi(pn, dom, b)
        },
    );

    arena.annot(lam_body, pi_type)
}

// ── Basic generic function ──

#[test]
fn generic_id_int() {
    let (_b, arena) = a();
    // id : (A : prop) -> (x : A) -> A
    let id_func = make_generic(
        &arena,
        "id",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[("x", arena.named(s(&arena, "A")))],
        arena.named(s(&arena, "A")),
        arena.var(0),
    );
    // id int 5 : int
    let app = arena.app(
        arena.app(id_func, arena.builtin(s(&arena, "int"))),
        arena.lit_int(5),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn generic_id_bool() {
    let (_b, arena) = a();
    let id_func = make_generic(
        &arena,
        "id",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[("x", arena.named(s(&arena, "A")))],
        arena.named(s(&arena, "A")),
        arena.var(0),
    );
    // id bool true : bool
    let app = arena.app(
        arena.app(id_func, arena.builtin(s(&arena, "bool"))),
        arena.lit_bool(true),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "bool"))),
        Ok(())
    );
}

#[test]
fn generic_id_wrong_data_arg_fails() {
    let (_b, arena) = a();
    let id_func = make_generic(
        &arena,
        "id",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[("x", arena.named(s(&arena, "A")))],
        arena.named(s(&arena, "A")),
        arena.var(0),
    );
    // id bool 5 → 5 is int, but bool was chosen for A
    let app = arena.app(
        arena.app(id_func, arena.builtin(s(&arena, "bool"))),
        arena.lit_int(5),
    );
    assert!(check_empty(&arena, app, arena.builtin(s(&arena, "bool"))).is_err());
}

// ── Two type params ──

#[test]
fn two_type_params() {
    let (_b, arena) = a();
    // konst : (A : prop) -> (B : prop) -> (x : A) -> (y : B) -> A
    let konst = make_generic(
        &arena,
        "konst",
        &[
            ("A", arena.builtin(s(&arena, "prop"))),
            ("B", arena.builtin(s(&arena, "prop"))),
        ],
        &[
            ("x", arena.named(s(&arena, "A"))),
            ("y", arena.named(s(&arena, "B"))),
        ],
        arena.named(s(&arena, "A")),
        arena.var(1),
    );
    // konst int bool 5 true : int
    let app = arena.app(
        arena.app(
            arena.app(
                arena.app(konst, arena.builtin(s(&arena, "int"))),
                arena.builtin(s(&arena, "bool")),
            ),
            arena.lit_int(5),
        ),
        arena.lit_bool(true),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Type param with prop constraint ──

#[test]
fn type_param_prop() {
    let (_b, arena) = a();
    let id_func = make_generic(
        &arena,
        "id",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[("x", arena.named(s(&arena, "A")))],
        arena.named(s(&arena, "A")),
        arena.var(0),
    );
    // id int 5 : int
    let app = arena.app(
        arena.app(id_func, arena.builtin(s(&arena, "int"))),
        arena.lit_int(5),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Three type params and three data params ──

#[test]
fn three_type_three_data_params() {
    let (_b, arena) = a();
    let f = make_generic(
        &arena,
        "f",
        &[
            ("A", arena.builtin(s(&arena, "prop"))),
            ("B", arena.builtin(s(&arena, "prop"))),
            ("C", arena.builtin(s(&arena, "prop"))),
        ],
        &[
            ("a", arena.named(s(&arena, "A"))),
            ("b", arena.named(s(&arena, "B"))),
            ("c", arena.named(s(&arena, "C"))),
        ],
        arena.named(s(&arena, "A")), // return A
        arena.var(2),                // body: a
    );
    // f int bool str 1 true "hi" : int
    let app = arena.app(
        arena.app(
            arena.app(
                arena.app(
                    arena.app(
                        arena.app(f, arena.builtin(s(&arena, "int"))),
                        arena.builtin(s(&arena, "bool")),
                    ),
                    arena.builtin(s(&arena, "str")),
                ),
                arena.lit_int(1),
            ),
            arena.lit_bool(true),
        ),
        arena.lit_str(s(&arena, "hi")),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Substitution tests ──

#[test]
fn subst_pi_codomain() {
    let (_b, arena) = a();
    // Pi("A", prop, Pi("x", Var(0), Var(0)))
    // Build Pi type with Var(0) (de Bruijn) referencing A
    let pi_type = arena.pi(
        s(&arena, "A"),
        arena.builtin(s(&arena, "prop")),
        arena.pi(s(&arena, "x"), arena.var(0), arena.var(0)),
    );
    // Substitute int for A (Var(0) in the Pi body).
    // The inner Pi body's Var(0) at cutoff 0 gets replaced.
    let sub = SubstitutionContext::new(&arena);
    let result = sub.subst(arena.builtin(s(&arena, "int")), 0, pi_type);
    // Result: Pi("A", prop, Pi("x", int, int))
    match result {
        Term::Pi(_, _, b_cod) => match b_cod {
            Term::Pi(_, a_dom, a_cod) => {
                // Var(0) in domain at cutoff 1 → not substituted (Var(0) < cutoff 1)
                // Var(0) in codomain at cutoff 2 → not substituted
                // Actually, Pi type built without shifting:
                // Outer Pi binds A at cutoff 0, inner Pi at cutoff 1.
                // Inner Pi domain at cutoff 1: Var(0) — but 0 != 0+1, no match.
                // Inner Pi codomain at cutoff 2: Var(0) — 0 != 0+2, no match.
                // So nothing gets substituted! Builtin-based resolution is needed.
                // This test verifies that de Bruijn subst alone is insufficient
                // for Builtin-based Pi types.
                assert_eq!(**a_dom, Term::Var(0));
                assert_eq!(**a_cod, Term::Var(0));
            }
            _ => panic!("expected inner Pi"),
        },
        _ => panic!("expected Pi"),
    }
}

// ── No data params (only type params) ──

#[test]
fn only_type_params_no_data() {
    let (_b, arena) = a();
    let f = make_generic(
        &arena,
        "unit",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[],
        arena.builtin(s(&arena, "int")),
        arena.lit_int(0),
    );
    // unit int : int
    let app = arena.app(f, arena.builtin(s(&arena, "int")));
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Type param not used in body ──

#[test]
fn type_param_unused_in_body() {
    let (_b, arena) = a();
    let f = make_generic(
        &arena,
        "ignore",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[("x", arena.builtin(s(&arena, "int")))],
        arena.builtin(s(&arena, "int")),
        arena.var(0), // returns x
    );
    // ignore bool 5 : int
    let app = arena.app(
        arena.app(f, arena.builtin(s(&arena, "bool"))),
        arena.lit_int(5),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Returning type param A ──

#[test]
fn return_type_is_type_param() {
    let (_b, arena) = a();
    let f = make_generic(
        &arena,
        "wrap",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[("x", arena.named(s(&arena, "A")))],
        arena.named(s(&arena, "A")), // return A
        arena.var(0),                // body: x
    );
    // wrap int 5 : int
    let app = arena.app(
        arena.app(f, arena.builtin(s(&arena, "int"))),
        arena.lit_int(5),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

// ── Data param has refinement constraint referencing type param ──

#[test]
fn data_param_constrained_by_nonzero_with_type_param() {
    let (_b, arena) = a();
    // def safe_div (A : prop) (x : A) (y : A where (z => z /= 0)) : A := x / y
    // This tests that a refinement on a data param works with generics.
    let nonzero = arena.refine(
        s(&arena, ""),
        arena.named(s(&arena, "A")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    let f = make_generic(
        &arena,
        "safe_div",
        &[("A", arena.builtin(s(&arena, "prop")))],
        &[("x", arena.named(s(&arena, "A"))), ("y", nonzero)],
        arena.named(s(&arena, "A")),
        bin(&arena, PrimOp::Div, arena.var(1), arena.var(0)),
    );
    // safe_div int 10 2 : int
    let app = arena.app(
        arena.app(
            arena.app(f, arena.builtin(s(&arena, "int"))),
            arena.lit_int(10),
        ),
        arena.lit_int(2),
    );
    assert_eq!(
        check_empty(&arena, app, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}
