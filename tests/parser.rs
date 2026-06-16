mod common;

use bumpalo::Bump;
use common::{bin, leak_bump, parse, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{PrimOp, Term};
use ligare::front::parser::{TopLevel, parse_def_top, parse_expr_top, parse_program};

fn a() -> (&'static Bump, TermArena<'static>) {
    let b = leak_bump();
    let a = TermArena::new(b);
    (b, a)
}

#[test]
fn integer_literal() {
    let (b, a) = a();
    assert_eq!(*parse("42", b, &a), Term::LitInt(42));
}

#[test]
fn boolean_literal() {
    let (b, a) = a();
    assert_eq!(*parse("true", b, &a), Term::LitBool(true));
}

#[test]
fn simple_addition() {
    let (b, arena) = a();
    assert_eq!(
        *parse("1 + 2", b, &arena),
        *bin(&arena, PrimOp::Add, arena.lit_int(1), arena.lit_int(2))
    );
}

#[test]
fn comparison() {
    let (b, arena) = a();
    assert_eq!(
        *parse("3 < 5", b, &arena),
        *bin(&arena, PrimOp::Lt, arena.lit_int(3), arena.lit_int(5))
    );
}

#[test]
fn equality() {
    let (b, arena) = a();
    assert_eq!(
        *parse("1 = 2", b, &arena),
        *bin(&arena, PrimOp::Eq, arena.lit_int(1), arena.lit_int(2))
    );
}

#[test]
fn negative_number() {
    let (b, arena) = a();
    let sub = arena.app(arena.prim_op(PrimOp::Sub), arena.lit_int(0));
    assert_eq!(*parse("-5", b, &arena), *arena.app(sub, arena.lit_int(5)));
}

#[test]
fn if_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("if true then 1 else 0", b, &arena),
        *arena.if_then_else(arena.lit_bool(true), arena.lit_int(1), arena.lit_int(0))
    );
}

#[test]
fn let_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("let x := 5 in x", b, &arena),
        *arena.let_(s(&arena, "x"), arena.lit_int(5), arena.var(0), None)
    );
}

#[test]
fn let_with_constraint() {
    let (b, arena) = a();
    assert_eq!(
        *parse("let x : int := 5 in x", b, &arena),
        *arena.let_(
            s(&arena, "x"),
            arena.lit_int(5),
            arena.var(0),
            Some(arena.builtin(s(&arena, "int")))
        )
    );
}

#[test]
fn lambda() {
    let (b, a) = a();
    assert_eq!(*parse("\\x. x", b, &a), Term::Lam(&Term::Var(0)));
}

#[test]
fn annot_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("(5 : int)", b, &arena),
        *arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")))
    );
}

#[test]
fn arrow_type() {
    let (b, arena) = a();
    assert_eq!(
        *parse("int -> bool", b, &arena),
        *arena.pi(
            s(&arena, ""),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "bool"))
        )
    );
}

#[test]
fn dependent_arrow_type() {
    let (b, arena) = a();
    assert_eq!(
        *parse("(x: int) -> x", b, &arena),
        *arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.var(0)
        )
    );
}

#[test]
fn unbound_name_becomes_builtin() {
    let (b, arena) = a();
    assert_eq!(*parse("foo", b, &arena), *arena.builtin(s(&arena, "foo")));
}

#[test]
fn refine_expression() {
    let (b, arena) = a();
    assert_eq!(
        *parse("int where (x => x >= 0)", b, &arena),
        *arena.refine(
            s(&arena, ""),
            arena.builtin(s(&arena, "int")),
            bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0))
        )
    );
}

#[test]
fn refine_in_let_annotation() {
    let (b, arena) = a();
    let t = parse_expr_top("let y : int where (x => x >= 0) := 42 in y", b, &arena);
    assert!(t.is_ok());
}

#[test]
fn refine_in_def_annotation() {
    let (b, arena) = a();
    let t = parse_def_top("def f (a : int where (x => x > 0)) : int := a", b, &arena);
    assert!(t.is_ok());
}

#[test]
fn def_refinement() {
    let (b, arena) = a();
    let result = parse_def_top("def nat := int where (x => x >= 0)", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "nat");
    assert_eq!(
        *term,
        *arena.refine(
            s(&arena, ""),
            arena.builtin(s(&arena, "int")),
            bin(&arena, PrimOp::Ge, arena.ref_param(), arena.lit_int(0))
        )
    );
}

#[test]
fn program_with_def_and_check() {
    let (b, arena) = a();
    let result = parse_program("def x : int := 5\n#check x : int", b, &arena);
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 2);
    assert!(matches!(tops[0], TopLevel::TLDef(..)));
    assert!(matches!(tops[1], TopLevel::TLCheck(..)));
}

#[test]
fn program_with_expr() {
    let (b, arena) = a();
    let result = parse_program("1 + 2\n#check 3 : int", b, &arena);
    assert!(result.is_ok());
    let tops = result.unwrap();
    assert_eq!(tops.len(), 2);
    assert!(matches!(tops[0], TopLevel::TLExpr(..)));
    assert!(matches!(tops[1], TopLevel::TLCheck(..)));
}

#[test]
fn func_one_param() {
    let (b, arena) = a();
    assert!(parse_expr_top("func f (x: int) : int := x + 1", b, &arena).is_ok());
}

#[test]
fn func_three_params() {
    let (b, arena) = a();
    assert!(parse_expr_top("func f (a: int) (b: int) (c: int) : int := a", b, &arena).is_ok());
}

#[test]
fn and_prop_parses() {
    let (b, arena) = a();
    let and_term = arena.builtin(s(&arena, "and"));
    assert_eq!(
        *parse("∧ true false", b, &arena),
        *arena.app(
            arena.app(and_term, arena.lit_bool(true)),
            arena.lit_bool(false)
        )
    );
}

#[test]
fn or_prop_parses() {
    let (b, arena) = a();
    let or_term = arena.builtin(s(&arena, "or"));
    assert_eq!(
        *parse("∨ true false", b, &arena),
        *arena.app(
            arena.app(or_term, arena.lit_bool(true)),
            arena.lit_bool(false)
        )
    );
}

#[test]
fn not_prop_parses() {
    let (b, arena) = a();
    assert_eq!(
        *parse("¬ true", b, &arena),
        *arena.app(arena.builtin(s(&arena, "not")), arena.lit_bool(true))
    );
}

#[test]
fn and_in_expression() {
    let (b, arena) = a();
    let and_term = arena.builtin(s(&arena, "and"));
    let int_term = arena.builtin(s(&arena, "int"));
    let bool_term = arena.builtin(s(&arena, "bool"));
    assert_eq!(
        *parse("∧ int bool", b, &arena),
        *arena.app(arena.app(and_term, int_term), bool_term)
    );
}

#[test]
fn let_with_by() {
    let (b, arena) = a();
    assert_eq!(
        *parse("let x : int by true := 5 in x", b, &arena),
        *arena.let_(
            s(&arena, "x"),
            arena.by_proof(arena.lit_int(5), arena.lit_bool(true)),
            arena.var(0),
            Some(arena.builtin(s(&arena, "int")))
        )
    );
}

#[test]
fn def_simple() {
    let (b, arena) = a();
    let result = parse_def_top("def x : int := 5", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "x");
    assert_eq!(
        *term,
        *arena.annot(arena.lit_int(5), arena.builtin(s(&arena, "int")))
    );
}

#[test]
fn def_with_params() {
    let (b, arena) = a();
    let result = parse_def_top("def add (a : int) (b : int) : int := a + b", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "add");
    let inner = bin(&arena, PrimOp::Add, arena.var(1), arena.var(0));
    assert_eq!(
        *term,
        *arena.annot(arena.lam(arena.lam(inner)), arena.builtin(s(&arena, "int")))
    );
}

#[test]
fn def_no_ret() {
    let (b, arena) = a();
    let result = parse_def_top("def x := 5", b, &arena);
    assert!(result.is_ok());
    let (name, term) = result.unwrap();
    assert_eq!(name, "x");
    assert_eq!(*term, Term::LitInt(5));
}
