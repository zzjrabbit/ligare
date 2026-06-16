mod common;

use common::bin;
use ligare::core::syntax::{PrimOp, Term};
use ligare::front::parser::{TopLevel, parse_def_top, parse_expr_top, parse_program};

#[test]
fn integer_literal() {
    assert_eq!(parse_expr_top("42").unwrap(), Term::LitInt(42));
}

#[test]
fn boolean_literal() {
    assert_eq!(parse_expr_top("true").unwrap(), Term::LitBool(true));
}

#[test]
fn simple_addition() {
    assert_eq!(
        parse_expr_top("1 + 2").unwrap(),
        bin(PrimOp::Add, Term::LitInt(1), Term::LitInt(2))
    );
}

#[test]
fn comparison() {
    assert_eq!(
        parse_expr_top("3 < 5").unwrap(),
        bin(PrimOp::Lt, Term::LitInt(3), Term::LitInt(5))
    );
}

#[test]
fn equality() {
    assert_eq!(
        parse_expr_top("1 = 2").unwrap(),
        bin(PrimOp::Eq, Term::LitInt(1), Term::LitInt(2))
    );
}

#[test]
fn negative_number() {
    assert_eq!(
        parse_expr_top("-5").unwrap(),
        Term::App(
            Box::new(Term::App(
                Box::new(Term::PrimOp(PrimOp::Sub)),
                Box::new(Term::LitInt(0)),
            )),
            Box::new(Term::LitInt(5)),
        )
    );
}

#[test]
fn if_expression() {
    assert_eq!(
        parse_expr_top("if true then 1 else 0").unwrap(),
        Term::IfThenElse(
            Box::new(Term::LitBool(true)),
            Box::new(Term::LitInt(1)),
            Box::new(Term::LitInt(0)),
        )
    );
}

#[test]
fn let_expression() {
    assert_eq!(
        parse_expr_top("let x := 5 in x").unwrap(),
        Term::Let(
            "x".to_string(),
            Box::new(Term::LitInt(5)),
            Box::new(Term::Var(0)),
            None,
        )
    );
}

#[test]
fn let_with_constraint() {
    assert_eq!(
        parse_expr_top("let x : int := 5 in x").unwrap(),
        Term::Let(
            "x".to_string(),
            Box::new(Term::LitInt(5)),
            Box::new(Term::Var(0)),
            Some(Box::new(Term::Builtin("int".to_string()))),
        )
    );
}

#[test]
fn lambda() {
    assert_eq!(
        parse_expr_top("\\x. x").unwrap(),
        Term::Lam(Box::new(Term::Var(0)))
    );
}

#[test]
fn annot_expression() {
    assert_eq!(
        parse_expr_top("(5 : int)").unwrap(),
        Term::Annot(
            Box::new(Term::LitInt(5)),
            Box::new(Term::Builtin("int".to_string())),
        )
    );
}

#[test]
fn arrow_type() {
    assert_eq!(
        parse_expr_top("int -> bool").unwrap(),
        Term::Pi(
            "".to_string(),
            Box::new(Term::Builtin("int".to_string())),
            Box::new(Term::Builtin("bool".to_string())),
        )
    );
}

#[test]
fn dependent_arrow_type() {
    assert_eq!(
        parse_expr_top("(x: int) -> x").unwrap(),
        Term::Pi(
            "x".to_string(),
            Box::new(Term::Builtin("int".to_string())),
            Box::new(Term::Var(0)),
        )
    );
}

#[test]
fn unbound_name_becomes_builtin() {
    assert_eq!(
        parse_expr_top("foo").unwrap(),
        Term::Builtin("foo".to_string())
    );
}

#[test]
fn refine_expression() {
    assert_eq!(
        parse_expr_top("int where (x => x >= 0)").unwrap(),
        Term::Refine(
            "".to_string(),
            Box::new(Term::Builtin("int".to_string())),
            Box::new(bin(PrimOp::Ge, Term::RefParam, Term::LitInt(0))),
        )
    );
}

#[test]
fn refine_in_let_annotation() {
    assert!(parse_expr_top("let y : int where (x => x >= 0) := 42 in y").is_ok());
}

#[test]
fn refine_in_def_annotation() {
    assert!(parse_def_top("def f (a : int where (x => x > 0)) : int := a").is_ok());
}

#[test]
fn def_refinement() {
    let result = parse_def_top("def nat := int where (x => x >= 0)");
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "nat");
    assert_eq!(
        term,
        Term::Refine(
            "".to_string(),
            Box::new(Term::Builtin("int".to_string())),
            Box::new(bin(PrimOp::Ge, Term::RefParam, Term::LitInt(0))),
        )
    );
}

#[test]
fn program_with_def_and_check() {
    let result = parse_program("def x : int := 5\n#check x : int");
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 2);
    assert!(matches!(tops[0], TopLevel::TLDef(..)));
    assert!(matches!(tops[1], TopLevel::TLCheck(..)));
}

#[test]
fn program_with_expr() {
    let result = parse_program("1 + 2\n#check 3 : int");
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 2);
    assert!(matches!(tops[0], TopLevel::TLExpr(..)));
    assert!(matches!(tops[1], TopLevel::TLCheck(..)));
}

#[test]
fn func_one_param() {
    assert!(parse_expr_top("func f (x: int) : int := x + 1").is_ok());
}

#[test]
fn func_three_params() {
    assert!(parse_expr_top("func f (a: int) (b: int) (c: int) : int := a").is_ok());
}

#[test]
fn and_prop_parses() {
    assert_eq!(
        parse_expr_top("∧ true false").unwrap(),
        Term::App(
            Box::new(Term::App(
                Box::new(Term::Builtin("and".to_string())),
                Box::new(Term::LitBool(true)),
            )),
            Box::new(Term::LitBool(false)),
        )
    );
}

#[test]
fn or_prop_parses() {
    assert_eq!(
        parse_expr_top("∨ true false").unwrap(),
        Term::App(
            Box::new(Term::App(
                Box::new(Term::Builtin("or".to_string())),
                Box::new(Term::LitBool(true)),
            )),
            Box::new(Term::LitBool(false)),
        )
    );
}

#[test]
fn not_prop_parses() {
    assert_eq!(
        parse_expr_top("¬ true").unwrap(),
        Term::App(
            Box::new(Term::Builtin("not".to_string())),
            Box::new(Term::LitBool(true)),
        )
    );
}

#[test]
fn and_in_expression() {
    assert_eq!(
        parse_expr_top("∧ int bool").unwrap(),
        Term::App(
            Box::new(Term::App(
                Box::new(Term::Builtin("and".to_string())),
                Box::new(Term::Builtin("int".to_string())),
            )),
            Box::new(Term::Builtin("bool".to_string())),
        )
    );
}

#[test]
fn let_with_by() {
    assert_eq!(
        parse_expr_top("let x : int by true := 5 in x").unwrap(),
        Term::Let(
            "x".to_string(),
            Box::new(Term::ByProof(
                Box::new(Term::LitInt(5)),
                Box::new(Term::LitBool(true)),
            )),
            Box::new(Term::Var(0)),
            Some(Box::new(Term::Builtin("int".to_string()))),
        )
    );
}

#[test]
fn def_simple() {
    let result = parse_def_top("def x : int := 5");
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "x");
    assert_eq!(
        term,
        Term::Annot(
            Box::new(Term::LitInt(5)),
            Box::new(Term::Builtin("int".to_string())),
        )
    );
}

#[test]
fn def_with_params() {
    let result = parse_def_top("def add (a : int) (b : int) : int := a + b");
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "add");
    assert_eq!(
        term,
        Term::Annot(
            Box::new(Term::Lam(Box::new(Term::Lam(Box::new(bin(
                PrimOp::Add,
                Term::Var(1),
                Term::Var(0)
            )))))),
            Box::new(Term::Builtin("int".to_string())),
        )
    );
}

#[test]
fn def_no_ret() {
    let result = parse_def_top("def x := 5");
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "x");
    assert_eq!(term, Term::LitInt(5));
}
