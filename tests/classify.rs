use ligare::checker::context::empty_ctx;
use ligare::core::classify::classify;
use ligare::core::syntax::{Term, Universe};

#[test]
fn lit_int_is_data() {
    assert_eq!(
        classify(&empty_ctx(), &Term::LitInt(42)),
        Some(Universe::UData)
    );
}

#[test]
fn lit_bool_is_data() {
    assert_eq!(
        classify(&empty_ctx(), &Term::LitBool(true)),
        Some(Universe::UData)
    );
}

#[test]
fn lam_is_data() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Lam(Box::new(Term::Var(0)))),
        Some(Universe::UData)
    );
}

#[test]
fn pi_is_prop() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Pi(
                "".to_string(),
                Box::new(Term::Builtin("int".to_string())),
                Box::new(Term::Builtin("bool".to_string()))
            )
        ),
        Some(Universe::UProp)
    );
}

#[test]
fn auto_proof_is_proof() {
    assert_eq!(
        classify(&empty_ctx(), &Term::AutoProof),
        Some(Universe::UProof)
    );
}

#[test]
fn universe_uprop_is_prop() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Universe(Universe::UProp)),
        Some(Universe::UProp)
    );
}

#[test]
fn int_builtin_is_prop() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Builtin("int".to_string())),
        Some(Universe::UProp)
    );
}

#[test]
fn and_is_prop() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Builtin("and".to_string())),
        Some(Universe::UProp)
    );
}

#[test]
fn annot_keeps_inner_universe() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Annot(
                Box::new(Term::LitInt(5)),
                Box::new(Term::Builtin("int".to_string()))
            )
        ),
        Some(Universe::UData)
    );
}

#[test]
fn by_proof_keeps_inner_universe() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::ByProof(Box::new(Term::LitInt(5)), Box::new(Term::AutoProof))
        ),
        Some(Universe::UData)
    );
}

#[test]
fn if_then_else_is_data() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::IfThenElse(
                Box::new(Term::LitBool(true)),
                Box::new(Term::LitInt(1)),
                Box::new(Term::LitInt(0))
            )
        ),
        Some(Universe::UData)
    );
}

#[test]
fn func_is_data() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Func(
                "f".to_string(),
                vec![(
                    "x".to_string(),
                    Some(Box::new(Term::Builtin("int".to_string())))
                )],
                None,
                vec![],
                vec![],
                Box::new(Term::Var(0))
            )
        ),
        Some(Universe::UData)
    );
}

#[test]
fn let_is_body_universe() {
    assert_eq!(
        classify(
            &empty_ctx(),
            &Term::Let(
                "x".to_string(),
                Box::new(Term::LitInt(5)),
                Box::new(Term::Var(0)),
                None
            )
        ),
        None
    );
}

#[test]
fn unknown_builtin_is_nothing() {
    assert_eq!(
        classify(&empty_ctx(), &Term::Builtin("unknown".to_string())),
        None
    );
}
