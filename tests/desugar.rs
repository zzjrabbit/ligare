mod common;

use common::{bin, leak_bump, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::PrimOp;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn func_one_param_no_ret() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "data")),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_one_param_with_ret() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1))),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.builtin(s(&arena, "int")),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_two_params() {
    let (_bump, arena) = a();
    let inner = bin(&arena, PrimOp::Add, arena.var(1), arena.var(0));
    let term = arena.annot(
        arena.lam(arena.lam(inner)),
        arena.pi(
            s(&arena, "a"),
            arena.builtin(s(&arena, "int")),
            arena.pi(
                s(&arena, "b"),
                arena.builtin(s(&arena, "int")),
                arena.builtin(s(&arena, "int")),
            ),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_two_params_refinement() {
    let (_bump, arena) = a();
    let refine = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    let inner = bin(&arena, PrimOp::Div, arena.var(1), arena.var(0));
    let term = arena.annot(
        arena.lam(arena.lam(inner)),
        arena.pi(
            s(&arena, "a"),
            arena.builtin(s(&arena, "int")),
            arena.pi(s(&arena, "b"), refine, arena.builtin(s(&arena, "int"))),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_three_params_order() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(arena.lam(arena.lam(arena.var(2)))),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "int")),
            arena.pi(
                s(&arena, "y"),
                arena.builtin(s(&arena, "bool")),
                arena.pi(
                    s(&arena, "z"),
                    arena.builtin(s(&arena, "int")),
                    arena.builtin(s(&arena, "int")),
                ),
            ),
        ),
    );
    assert!(!term.is_constant());
}

#[test]
fn func_no_constraint() {
    let (_bump, arena) = a();
    let term = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            s(&arena, "x"),
            arena.builtin(s(&arena, "data")),
            arena.builtin(s(&arena, "data")),
        ),
    );
    assert!(!term.is_constant());
}
