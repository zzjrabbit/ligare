mod common;

use common::{leak_bump, parse, parse_constraint, s};
use ligare::checker::check;
use ligare::checker::context::{empty_ctx, empty_table};
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

fn check_empty<'bump>(
    arena: &TermArena<'bump>,
    t: &'bump Term<'bump>,
    c: &'bump Term<'bump>,
) -> Result<(), String> {
    check(arena, &empty_table(), &empty_ctx(), t, c)
}

#[test]
fn int_literal() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(&arena, &Term::LitInt(5), arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}

#[test]
fn bool_literal() {
    let (_b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            &Term::LitBool(true),
            arena.builtin(s(&arena, "bool"))
        ),
        Ok(())
    );
}

#[test]
fn int_fails_for_bool() {
    let (_b, arena) = a();
    assert!(check_empty(&arena, &Term::LitInt(5), arena.builtin(s(&arena, "bool"))).is_err());
}

#[test]
fn lambda_int_to_int() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("\\x. x", b, &arena),
            parse_constraint("int -> int", b, &arena)
        ),
        Ok(())
    );
}

#[test]
fn lambda_bool_to_int_with_if() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("\\x. (if x then 0 else 1)", b, &arena),
            parse_constraint("bool -> int", b, &arena)
        ),
        Ok(())
    );
}

#[test]
fn if_branches_checked() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("if true then 5 else 3", b, &arena),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

#[test]
fn let_with_constraint() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("let x : int := 5 in x", b, &arena),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

#[test]
fn unknown_constraint_fails() {
    let (_b, arena) = a();
    assert!(check_empty(&arena, &Term::LitInt(5), arena.builtin(s(&arena, "foo"))).is_err());
}

#[test]
fn let_with_by_check() {
    let (b, arena) = a();
    assert_eq!(
        check_empty(
            &arena,
            parse("let x : int by true := 5 in x", b, &arena),
            arena.builtin(s(&arena, "int"))
        ),
        Ok(())
    );
}

#[test]
fn refinement_auto_proof() {
    let (b, arena) = a();
    let term = parse("let y : int where (x => x >= 0) := 42 in y", b, &arena);
    assert_eq!(
        check_empty(&arena, term, arena.builtin(s(&arena, "int"))),
        Ok(())
    );
}
