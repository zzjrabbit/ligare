mod common;

use common::{parse, parse_constraint};
use ligare::checker::checker::check;
use ligare::checker::context::{empty_ctx, empty_table};
use ligare::core::syntax::Term;

fn check_empty(t: &Term, c: &Term) -> Result<(), String> {
    check(&empty_table(), &empty_ctx(), t, c)
}

#[test]
fn int_literal() {
    assert_eq!(
        check_empty(&Term::LitInt(5), &Term::Builtin("int".to_string())),
        Ok(())
    );
}

#[test]
fn bool_literal() {
    assert_eq!(
        check_empty(&Term::LitBool(true), &Term::Builtin("bool".to_string())),
        Ok(())
    );
}

#[test]
fn int_fails_for_bool() {
    assert!(check_empty(&Term::LitInt(5), &Term::Builtin("bool".to_string())).is_err());
}

#[test]
fn lambda_int_to_int() {
    assert_eq!(
        check_empty(&parse("\\x. x"), &parse_constraint("int -> int")),
        Ok(())
    );
}

#[test]
fn lambda_bool_to_int_with_if() {
    assert_eq!(
        check_empty(
            &parse("\\x. (if x then 0 else 1)"),
            &parse_constraint("bool -> int")
        ),
        Ok(())
    );
}

#[test]
fn if_branches_checked() {
    assert_eq!(
        check_empty(
            &parse("if true then 5 else 3"),
            &Term::Builtin("int".to_string())
        ),
        Ok(())
    );
}

#[test]
fn let_with_constraint() {
    assert_eq!(
        check_empty(
            &parse("let x : int := 5 in x"),
            &Term::Builtin("int".to_string())
        ),
        Ok(())
    );
}

#[test]
fn unknown_constraint_fails() {
    assert!(check_empty(&Term::LitInt(5), &Term::Builtin("foo".to_string())).is_err());
}

#[test]
fn let_with_by_check() {
    assert_eq!(
        check_empty(
            &parse("let x : int by true := 5 in x"),
            &Term::Builtin("int".to_string())
        ),
        Ok(())
    );
}

#[test]
fn refinement_auto_proof() {
    let term = parse("let y : int where (x => x >= 0) := 42 in y");
    assert_eq!(
        check_empty(&term, &Term::Builtin("int".to_string())),
        Ok(())
    );
}
