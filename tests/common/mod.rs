#![allow(dead_code)]

use ligare::core::syntax::{PrimOp, Term};
use ligare::front::parser::parse_expr_top;

pub fn bin(op: PrimOp, l: Term, r: Term) -> Term {
    Term::App(
        Box::new(Term::App(Box::new(Term::PrimOp(op)), Box::new(l))),
        Box::new(r),
    )
}

pub fn parse(input: &str) -> Term {
    parse_expr_top(input).unwrap_or_else(|e| panic!("parse error in test: {}", e))
}

pub fn parse_constraint(input: &str) -> Term {
    parse_expr_top(input).unwrap_or_else(|e| panic!("parse constraint error: {}", e))
}
