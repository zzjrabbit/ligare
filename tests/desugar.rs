mod common;

use common::{bin, leak_bump, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::{FuncDef, PrimOp};

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn func_one_param_no_ret() {
    let (_bump, arena) = a();
    let func_def = arena.bump().alloc(FuncDef {
        name: s(&arena, "id"),
        params: arena.alloc_slice(&[(s(&arena, "x"), Some(arena.builtin(s(&arena, "int"))))]),
        ret: None,
        body: arena.var(0),
    });
    assert_eq!(
        *arena.desugar_func_def(func_def),
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
    let func_def = arena.bump().alloc(FuncDef {
        name: s(&arena, "f"),
        params: arena.alloc_slice(&[(s(&arena, "x"), Some(arena.builtin(s(&arena, "int"))))]),
        ret: Some(arena.builtin(s(&arena, "int"))),
        body: bin(&arena, PrimOp::Add, arena.var(0), arena.lit_int(1)),
    });
    assert_eq!(
        *arena.desugar_func_def(func_def),
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
    let func_def = arena.bump().alloc(FuncDef {
        name: s(&arena, "add"),
        params: arena.alloc_slice(params),
        ret: Some(arena.builtin(s(&arena, "int"))),
        body: bin(&arena, PrimOp::Add, arena.var(1), arena.var(0)),
    });
    let inner = bin(&arena, PrimOp::Add, arena.var(1), arena.var(0));
    assert_eq!(
        *arena.desugar_func_def(func_def),
        *arena.annot(
            arena.lam(arena.lam(inner)),
            arena.pi(
                s(&arena, "a"),
                arena.builtin(s(&arena, "int")),
                arena.pi(
                    s(&arena, "b"),
                    arena.builtin(s(&arena, "int")),
                    arena.builtin(s(&arena, "int"))
                )
            )
        )
    );
}

#[test]
fn func_two_params_refinement() {
    let (_bump, arena) = a();
    let refine = arena.refine(
        s(&arena, ""),
        arena.builtin(s(&arena, "int")),
        bin(&arena, PrimOp::Neq, arena.ref_param(), arena.lit_int(0)),
    );
    let params = &[
        (s(&arena, "a"), Some(arena.builtin(s(&arena, "int")))),
        (s(&arena, "b"), Some(refine)),
    ];
    let func_def = arena.bump().alloc(FuncDef {
        name: s(&arena, "sdiv"),
        params: arena.alloc_slice(params),
        ret: Some(arena.builtin(s(&arena, "int"))),
        body: bin(&arena, PrimOp::Div, arena.var(1), arena.var(0)),
    });
    let inner = bin(&arena, PrimOp::Div, arena.var(1), arena.var(0));
    assert_eq!(
        *arena.desugar_func_def(func_def),
        *arena.annot(
            arena.lam(arena.lam(inner)),
            arena.pi(
                s(&arena, "a"),
                arena.builtin(s(&arena, "int")),
                arena.pi(s(&arena, "b"), refine, arena.builtin(s(&arena, "int")))
            )
        )
    );
}

#[test]
fn func_three_params_order() {
    let (_bump, arena) = a();
    let params = &[
        (s(&arena, "x"), Some(arena.builtin(s(&arena, "int")))),
        (s(&arena, "y"), Some(arena.builtin(s(&arena, "bool")))),
        (s(&arena, "z"), Some(arena.builtin(s(&arena, "int")))),
    ];
    let func_def = arena.bump().alloc(FuncDef {
        name: s(&arena, "f"),
        params: arena.alloc_slice(params),
        ret: Some(arena.builtin(s(&arena, "int"))),
        body: arena.var(2),
    });
    assert_eq!(
        *arena.desugar_func_def(func_def),
        *arena.annot(
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
                        arena.builtin(s(&arena, "int"))
                    )
                )
            )
        )
    );
}

#[test]
fn func_no_constraint() {
    let (_bump, arena) = a();
    let func_def = arena.bump().alloc(FuncDef {
        name: s(&arena, "id"),
        params: arena.alloc_slice(&[(s(&arena, "x"), None)]),
        ret: None,
        body: arena.var(0),
    });
    assert_eq!(
        *arena.desugar_func_def(func_def),
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
