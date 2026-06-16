mod common;

use common::{bin, leak_bump, parse, s};
use ligare::core::eval::eval;
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn integer_identity() {
    let (_b, arena) = a();
    assert_eq!(*eval(&arena, &Term::LitInt(42)).unwrap(), Term::LitInt(42));
}

#[test]
fn arithmetic() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("1 + 2 * 3", b, &arena)).unwrap(),
        Term::LitInt(7)
    );
}

#[test]
fn if_true() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("if true then 10 else 20", b, &arena)).unwrap(),
        Term::LitInt(10)
    );
}

#[test]
fn if_false() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("if false then 10 else 20", b, &arena)).unwrap(),
        Term::LitInt(20)
    );
}

#[test]
fn let_() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("let x := 5 in x + 3", b, &arena)).unwrap(),
        Term::LitInt(8)
    );
}

#[test]
fn beta_reduction() {
    let (b, arena) = a();
    assert_eq!(
        *eval(&arena, parse("(\\x. x + 1) 5", b, &arena)).unwrap(),
        Term::LitInt(6)
    );
}

#[test]
fn annot_strips_annotation() {
    let (_b, arena) = a();
    assert_eq!(
        *eval(
            &arena,
            arena.annot(arena.lit_int(42), arena.builtin(s(&arena, "int")))
        )
        .unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn by_proof_strips_proof() {
    let (_b, arena) = a();
    assert_eq!(
        *eval(
            &arena,
            arena.by_proof(arena.lit_int(42), arena.lit_bool(true))
        )
        .unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn arithmetic_on_bool_fails() {
    let (_b, arena) = a();
    let result = eval(
        &arena,
        bin(&arena, PrimOp::Add, arena.lit_bool(true), arena.lit_int(1)),
    );
    assert!(result.is_err());
}

#[test]
fn nested_if() {
    let (b, arena) = a();
    assert_eq!(
        *eval(
            &arena,
            parse("if (if true then false else true) then 1 else 2", b, &arena)
        )
        .unwrap(),
        Term::LitInt(2)
    );
}
