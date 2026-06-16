mod common;

use common::{bin, parse};
use ligare::core::eval::eval;
use ligare::core::syntax::{PrimOp, Term};

#[test]
fn integer_identity() {
    assert_eq!(eval(&Term::LitInt(42)).unwrap(), Term::LitInt(42));
}

#[test]
fn arithmetic() {
    assert_eq!(eval(&parse("1 + 2 * 3")).unwrap(), Term::LitInt(7));
}

#[test]
fn if_true() {
    assert_eq!(
        eval(&parse("if true then 10 else 20")).unwrap(),
        Term::LitInt(10)
    );
}

#[test]
fn if_false() {
    assert_eq!(
        eval(&parse("if false then 10 else 20")).unwrap(),
        Term::LitInt(20)
    );
}

#[test]
fn let_() {
    assert_eq!(
        eval(&parse("let x := 5 in x + 3")).unwrap(),
        Term::LitInt(8)
    );
}

#[test]
fn beta_reduction() {
    assert_eq!(eval(&parse("(\\x. x + 1) 5")).unwrap(), Term::LitInt(6));
}

#[test]
fn annot_strips_annotation() {
    assert_eq!(
        eval(&Term::Annot(
            Box::new(Term::LitInt(42)),
            Box::new(Term::Builtin("int".to_string()))
        ))
        .unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn by_proof_strips_proof() {
    assert_eq!(
        eval(&Term::ByProof(
            Box::new(Term::LitInt(42)),
            Box::new(Term::LitBool(true))
        ))
        .unwrap(),
        Term::LitInt(42)
    );
}

#[test]
fn arithmetic_on_bool_fails() {
    let result = eval(&bin(PrimOp::Add, Term::LitBool(true), Term::LitInt(1)));
    assert!(result.is_err());
}

#[test]
fn nested_if() {
    assert_eq!(
        eval(&parse("if (if true then false else true) then 1 else 2")).unwrap(),
        Term::LitInt(2)
    );
}
