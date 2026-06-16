mod common;

use common::bin;
use ligare::core::syntax::{PrimOp, Term};
use ligare::pretty::pretty;

#[test]
fn integer() {
    assert_eq!(pretty(&Term::LitInt(42)), "42");
}

#[test]
fn lambda() {
    assert_eq!(pretty(&Term::Lam(Box::new(Term::Var(0)))), "λ. $0");
}

#[test]
fn if_() {
    assert_eq!(
        pretty(&Term::IfThenElse(
            Box::new(Term::LitBool(true)),
            Box::new(Term::LitInt(1)),
            Box::new(Term::LitInt(0))
        )),
        "if true then 1 else 0"
    );
}

#[test]
fn let_() {
    assert_eq!(
        pretty(&Term::Let(
            "x".to_string(),
            Box::new(Term::LitInt(5)),
            Box::new(Term::Var(0)),
            None
        )),
        "let x = 5 in $0"
    );
}

#[test]
fn annot() {
    assert_eq!(
        pretty(&Term::Annot(
            Box::new(Term::LitInt(5)),
            Box::new(Term::Builtin("int".to_string()))
        )),
        "(5 : int)"
    );
}

#[test]
fn refine() {
    assert_eq!(
        pretty(&Term::Refine(
            "".to_string(),
            Box::new(Term::Builtin("int".to_string())),
            Box::new(bin(PrimOp::Ge, Term::RefParam, Term::LitInt(0)))
        )),
        "int where (x => ((>= x) 0))"
    );
}
