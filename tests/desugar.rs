mod common;

use common::bin;
use ligare::core::desugar::desugar;
use ligare::core::syntax::{PrimOp, Term};

#[test]
fn func_one_param_no_ret() {
    assert_eq!(
        desugar(&Term::Func(
            "id".to_string(),
            vec![(
                "x".to_string(),
                Some(Box::new(Term::Builtin("int".to_string())))
            )],
            None,
            vec![],
            vec![],
            Box::new(Term::Var(0)),
        )),
        Term::Annot(
            Box::new(Term::Lam(Box::new(Term::Var(0)))),
            Box::new(Term::Pi(
                "x".to_string(),
                Box::new(Term::Builtin("int".to_string())),
                Box::new(Term::Builtin("data".to_string()))
            )),
        )
    );
}

#[test]
fn func_one_param_with_ret() {
    assert_eq!(
        desugar(&Term::Func(
            "f".to_string(),
            vec![(
                "x".to_string(),
                Some(Box::new(Term::Builtin("int".to_string())))
            )],
            Some(Box::new(Term::Builtin("int".to_string()))),
            vec![],
            vec![],
            Box::new(bin(PrimOp::Add, Term::Var(0), Term::LitInt(1))),
        )),
        Term::Annot(
            Box::new(Term::Lam(Box::new(bin(
                PrimOp::Add,
                Term::Var(0),
                Term::LitInt(1)
            )))),
            Box::new(Term::Pi(
                "x".to_string(),
                Box::new(Term::Builtin("int".to_string())),
                Box::new(Term::Builtin("int".to_string()))
            )),
        )
    );
}

#[test]
fn func_two_params() {
    assert_eq!(
        desugar(&Term::Func(
            "add".to_string(),
            vec![
                (
                    "a".to_string(),
                    Some(Box::new(Term::Builtin("int".to_string())))
                ),
                (
                    "b".to_string(),
                    Some(Box::new(Term::Builtin("int".to_string())))
                ),
            ],
            Some(Box::new(Term::Builtin("int".to_string()))),
            vec![],
            vec![],
            Box::new(bin(PrimOp::Add, Term::Var(1), Term::Var(0))),
        )),
        Term::Annot(
            Box::new(Term::Lam(Box::new(Term::Lam(Box::new(bin(
                PrimOp::Add,
                Term::Var(1),
                Term::Var(0)
            )))))),
            Box::new(Term::Pi(
                "b".to_string(),
                Box::new(Term::Builtin("int".to_string())),
                Box::new(Term::Pi(
                    "a".to_string(),
                    Box::new(Term::Builtin("int".to_string())),
                    Box::new(Term::Builtin("int".to_string())),
                )),
            )),
        )
    );
}

#[test]
fn func_no_constraint() {
    assert_eq!(
        desugar(&Term::Func(
            "id".to_string(),
            vec![("x".to_string(), None)],
            None,
            vec![],
            vec![],
            Box::new(Term::Var(0)),
        )),
        Term::Annot(
            Box::new(Term::Lam(Box::new(Term::Var(0)))),
            Box::new(Term::Pi(
                "x".to_string(),
                Box::new(Term::Builtin("data".to_string())),
                Box::new(Term::Builtin("data".to_string()))
            )),
        )
    );
}
