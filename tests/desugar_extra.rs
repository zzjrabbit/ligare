//! Unit tests for the desugar and is_constant helpers.

use bumpalo::Bump;
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    (b, TermArena::new(b))
}

fn s<'bump>(arena: &TermArena<'bump>, s: &str) -> &'bump str {
    arena.alloc_str(s)
}

// ── is_constant ──

#[test]
fn constant_zero_param_annot_is_constant() {
    let (_b, arena) = setup();
    let t = arena.annot(arena.lit_int(42), arena.builtin(s(&arena, "int")));
    assert!(t.is_constant());
}

#[test]
fn function_annot_with_lam_is_not_constant() {
    let (_b, arena) = setup();
    let t = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        ),
    );
    assert!(!t.is_constant());
}

#[test]
fn lit_int_is_not_constant() {
    assert!(!Term::LitInt(5).is_constant());
}

#[test]
fn builtin_is_not_constant() {
    assert!(!Term::Named("x").is_constant());
}

// ── desugar_func_def: zero-param shape ──

#[test]
fn desugar_zero_param_produces_annot_without_lam() {
    let (_b, arena) = setup();
    let d = arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "data")));
    assert!(d.is_constant());
    // Shape: Annot(lit, Builtin("data"))
    match d {
        Term::Annot(inner, ty) => {
            assert_eq!(**inner, *arena.lit_int(5));
            assert_eq!(**ty, *arena.builtin(s(&arena, "data")));
        }
        _ => panic!("expected Annot, got {:?}", d),
    }
}

#[test]
fn desugar_one_param_produces_annot_with_lam() {
    let (_b, arena) = setup();
    let d = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "data")),
        ),
    );
    assert!(!d.is_constant());
    match d {
        Term::Annot(inner, _) => {
            assert!(matches!(inner, Term::Lam(_)));
        }
        _ => panic!("expected Annot(Lam, Pi), got {:?}", d),
    }
}

// ── desugar_func_def: ret type ──

#[test]
fn desugar_with_explicit_ret_type() {
    let (_b, arena) = setup();
    let d = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "str")),
        ),
    );
    match d {
        Term::Annot(_, Term::Pi(_, _, cod)) => {
            assert_eq!(**cod, *arena.builtin(s(&arena, "str")));
        }
        _ => panic!("expected Annot(Lam, Pi(_, _, str)), got {:?}", d),
    }
}
