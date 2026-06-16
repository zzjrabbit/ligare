mod common;

use common::{bin, leak_bump, s};
use ligare::core::desugar::desugar;
use ligare::core::pool::TermArena;
use ligare::core::syntax::PrimOp;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn func_one_param_no_ret() {
    let (_bump, arena) = a();
    let func = arena.func(
        s(&arena, "id"),
        arena.alloc_slice(&[(s(&arena, "x"), Some(arena.builtin(s(&arena, "int"))))]),
        None,
        &[],
        &[],
        arena.var(0),
    );
    assert_eq!(
        *desugar(&arena, func),
        *arena.annot(
            arena.lam(arena.var(0)),
            arena.pi(
                s(&arena, "x"),
                arena.builtin(s(&arena, "int")),
                arena.builtin(s(&arena, "data"))
            )
        )
    );
}

#[test]
fn func_one_param_with_ret() {
    let (_bump, arena) = a();
    let func = arena.func(
        s(&arena, "f"),
        arena.alloc_slice(&[(s(&arena, "x"), Some(arena.builtin(s(&arena, "int"))))]),
        Some(arena.builtin(s(&arena, "int"))),
        &[],
        &[],
        bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1)),
    );
    assert_eq!(
        *desugar(&arena, func),
        *arena.annot(
            arena.lam(bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1))),
            arena.pi(
                s(&arena, "x"),
                arena.builtin(s(&arena, "int")),
                arena.builtin(s(&arena, "int"))
            )
        )
    );
}

#[test]
fn func_two_params() {
    let (_bump, arena) = a();
    let params = &[
        (s(&arena, "a"), Some(arena.builtin(s(&arena, "int")))),
        (s(&arena, "b"), Some(arena.builtin(s(&arena, "int")))),
    ];
    let func = arena.func(
        s(&arena, "add"),
        arena.alloc_slice(params),
        Some(arena.builtin(s(&arena, "int"))),
        &[],
        &[],
        bin(&arena, PrimOp::Add, arena.var(1), arena.var(0)),
    );
    let inner = bin(&arena, PrimOp::Add, arena.var(1), arena.var(0));
    assert_eq!(
        *desugar(&arena, func),
        *arena.annot(
            arena.lam(arena.lam(inner)),
            arena.pi(
                s(&arena, "b"),
                arena.builtin(s(&arena, "int")),
                arena.pi(
                    s(&arena, "a"),
                    arena.builtin(s(&arena, "int")),
                    arena.builtin(s(&arena, "int"))
                )
            )
        )
    );
}

#[test]
fn func_no_constraint() {
    let (_bump, arena) = a();
    let func = arena.func(
        s(&arena, "id"),
        arena.alloc_slice(&[(s(&arena, "x"), None)]),
        None,
        &[],
        &[],
        arena.var(0),
    );
    assert_eq!(
        *desugar(&arena, func),
        *arena.annot(
            arena.lam(arena.var(0)),
            arena.pi(
                s(&arena, "x"),
                arena.builtin(s(&arena, "data")),
                arena.builtin(s(&arena, "data"))
            )
        )
    );
}
