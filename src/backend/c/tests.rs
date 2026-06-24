//! Tests for the C code generation backend.
//!
//! Tests cover literals, constants, functions (with and without FunSig),
//! function calls, let bindings, and union/struct codegen.

use crate::backend::c::{CEmitter, CodeGenerator};
use crate::backend::ir::{CType, FunSig};
use crate::core::pool::TermArena;
use crate::core::syntax::{PrimOp, Term};
use crate::front::parser::TopLevel;
use bumpalo::Bump;

// ── Test helpers ──

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    (b, TermArena::new(b))
}

fn sig(name: &str, param_types: Vec<CType>, ret_type: CType) -> (&str, FunSig) {
    let leaked: &'static str = Box::leak(name.to_string().into_boxed_str());
    (
        leaked,
        FunSig {
            param_types,
            ret_type,
        },
    )
}

fn emit(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
    let emitter = CEmitter::new(&[], &[], fun_sigs).unwrap();
    emitter.generate(tops, tops, &[], &[]).unwrap()
}

fn emit_with_types(
    tops: &[TopLevel<'_>],
    raw_defs: &[TopLevel<'_>],
    fun_sigs: &[(&str, FunSig)],
    union_types: &[(&str, &Term<'_>)],
    struct_types: &[(&str, &Term<'_>)],
) -> String {
    let emitter = CEmitter::new(struct_types, union_types, fun_sigs).unwrap();
    emitter
        .generate(tops, raw_defs, struct_types, union_types)
        .unwrap()
}

// ── Literals ──

#[test]
fn int_literal_uses_ld() {
    let (_b, arena) = setup();
    let c = emit(&[TopLevel::TLShow(arena.lit_int(42), 0..0)], &[]);
    assert!(c.contains("42"));
    assert!(c.contains("%ld"));
}

#[test]
fn str_literal_uses_s() {
    let (_b, arena) = setup();
    let c = emit(
        &[TopLevel::TLShow(arena.lit_str(arena.alloc_str("hi")), 0..0)],
        &[],
    );
    assert!(c.contains("\"hi\""));
    assert!(c.contains("%s"));
}

#[test]
fn bool_literal_emits_0_or_1() {
    let (_b, arena) = setup();
    let c = emit(&[TopLevel::TLShow(arena.lit_bool(true), 0..0)], &[]);
    assert!(c.contains("(int64_t)(1)"));
}

// ── Constants ──

#[test]
fn int_const_def() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("x");
    let c = emit(
        &[TopLevel::TLDef(name, &[], None, arena.lit_int(5), 0..0)],
        &[],
    );
    assert!(c.contains("const int64_t x = 5;"));
}

#[test]
fn str_const_def() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("g");
    let c = emit(
        &[TopLevel::TLDef(
            name,
            &[],
            None,
            arena.lit_str(arena.alloc_str("hi")),
            0..0,
        )],
        &[],
    );
    assert!(c.contains("const char* g"));
    assert!(c.contains("\"hi\""));
}

// ── Functions (no FunSig, lam-tree) ──

#[test]
fn lam_function_defaults_to_int64_params_and_return() {
    let (_b, arena) = setup();
    let body = arena.app(
        arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
        arena.var(0),
    );
    let lam = arena.lam(arena.lam(body));
    let name = arena.alloc_str("add");
    let c = emit(&[TopLevel::TLDef(name, &[], None, lam, 0..0)], &[]);
    assert!(c.contains("int64_t add(int64_t arg_0, int64_t arg_1)"));
}

#[test]
fn lam_returning_str_infers_str_return_type() {
    let (_b, arena) = setup();
    let lam = arena.lam(arena.lit_str(arena.alloc_str("hi")));
    let name = arena.alloc_str("greet");
    let c = emit(&[TopLevel::TLDef(name, &[], None, lam, 0..0)], &[]);
    assert!(c.contains("const char* greet(int64_t arg_0)"));
    assert!(c.contains("\"hi\""));
}

// ── Functions WITH FunSig ──

#[test]
fn func_with_str_param_uses_const_char_ptr() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("echo");
    let params: &[(
        crate::core::syntax::Name,
        Option<&crate::core::syntax::Term>,
    )] = arena.alloc_slice(&[(
        arena.alloc_str("s"),
        Some(arena.builtin(arena.alloc_str("str"))),
    )]);
    let desugared = arena.annot(
        arena.lam(arena.var(0)),
        arena.pi(
            arena.alloc_str("s"),
            arena.builtin(arena.alloc_str("str")),
            arena.builtin(arena.alloc_str("str")),
        ),
    );
    let sigs = &[sig("echo", vec![CType::Str], CType::Str)];
    let c = emit(
        &[TopLevel::TLDef(
            name,
            params,
            Some(arena.builtin(arena.alloc_str("str"))),
            desugared,
            0..0,
        )],
        sigs,
    );
    assert!(c.contains("const char* echo(const char* s)"));
}

#[test]
fn func_with_mixed_params() {
    let (_b, arena) = setup();
    let name = arena.alloc_str("f");
    let params: &[(
        crate::core::syntax::Name,
        Option<&crate::core::syntax::Term>,
    )] = arena.alloc_slice(&[
        (
            arena.alloc_str("a"),
            Some(arena.builtin(arena.alloc_str("int"))),
        ),
        (
            arena.alloc_str("b"),
            Some(arena.builtin(arena.alloc_str("str"))),
        ),
    ]);
    let desugared = arena.annot(
        arena.lam(arena.lam(arena.var(1))),
        arena.pi(
            arena.alloc_str("a"),
            arena.builtin(arena.alloc_str("int")),
            arena.pi(
                arena.alloc_str("b"),
                arena.builtin(arena.alloc_str("str")),
                arena.builtin(arena.alloc_str("int")),
            ),
        ),
    );
    let sigs = &[sig("f", vec![CType::Int64, CType::Str], CType::Int64)];
    let c = emit(
        &[TopLevel::TLDef(
            name,
            params,
            Some(arena.builtin(arena.alloc_str("int"))),
            desugared,
            0..0,
        )],
        sigs,
    );
    assert!(c.contains("int64_t f(int64_t a, const char* b)"));
}

// ── Function calls ──

#[test]
fn call_to_function_uses_fun_sig_return_type() {
    let (_b, arena) = setup();
    let fn_name = arena.alloc_str("greet");
    let def = TopLevel::TLDef(
        fn_name,
        &[],
        Some(arena.builtin(arena.alloc_str("str"))),
        arena.annot(
            arena.lit_str(arena.alloc_str("hi")),
            arena.builtin(arena.alloc_str("str")),
        ),
        0..0,
    );
    let sig = FunSig {
        param_types: vec![],
        ret_type: CType::Str,
    };
    let show = TopLevel::TLShow(arena.builtin(fn_name), 0..0);
    let tops = &[def, show];
    let c = emit(tops, &[(fn_name, sig)]);
    assert!(c.contains("%s"));
    assert!(c.contains("const char* greet"));
}

#[test]
fn emit_undefined_func_call_still_emits() {
    let (_b, arena) = setup();
    let n = arena.alloc_str("s");
    let call = arena.app(arena.builtin(n), arena.lit_str(arena.alloc_str("hi")));
    let tops = &[TopLevel::TLShow(call, 0..0)];
    let c = emit(tops, &[]);
    assert!(c.contains("s("));
}

#[test]
fn emit_let_str_printf_format() {
    let (_b, arena) = setup();
    let term = arena.let_(
        arena.alloc_str("s"),
        arena.lit_str(arena.alloc_str("hi")),
        arena.var(0),
        None,
    );
    let c = emit(&[TopLevel::TLShow(term, 0..0)], &[]);
    assert!(c.contains("%s"));
    assert!(c.contains("const char* s"));
}

#[test]
fn emit_multiple_defs_and_outputs() {
    let (_b, arena) = setup();
    let tops = &[
        TopLevel::TLDef(arena.alloc_str("a"), &[], None, arena.lit_int(1), 0..0),
        TopLevel::TLDef(
            arena.alloc_str("b"),
            &[],
            None,
            arena.lit_str(arena.alloc_str("two")),
            0..0,
        ),
        TopLevel::TLShow(arena.lit_int(3), 0..0),
        TopLevel::TLShow(arena.lit_str(arena.alloc_str("four")), 0..0),
    ];
    let c = emit(tops, &[]);
    assert!(c.contains("const int64_t a = 1;"));
    assert!(c.contains("const char* b = \"two\";"));
    assert!(c.contains("%ld"));
    assert!(c.contains("%s"));
}

// ── Union codegen ──

/// Build a union typedef with empty and payload variants.
#[test]
fn union_typedef_with_recursive_field() {
    let (_b, arena) = setup();
    let nat_name = arena.alloc_str("Nat");
    let zero_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
    let succ_fields: &[(crate::core::syntax::Name, &crate::core::syntax::Term)] =
        arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
    let succ_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Succ"), succ_fields);
    let variants: &[(
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    )] = arena.alloc_slice(&[zero_variant, succ_variant]);
    let nat_udef = arena.union_def(nat_name, variants);
    let union_types: &[(&str, &crate::core::syntax::Term)] =
        arena.bump().alloc([(nat_name, nat_udef)]);

    let top_name = arena.alloc_str("zero");
    let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
    let tops = &[TopLevel::TLDef(
        top_name,
        &[],
        Some(arena.builtin(nat_name)),
        zero_v,
        0..0,
    )];

    let c = emit_with_types(tops, &[], &[], union_types, &[]);
    // Typedef uses struct pointer for recursive field
    assert!(
        c.contains("struct Nat* pred;"),
        "expected struct Nat* pred; in:\n{c}"
    );
    // Empty variant uses proper initializer
    assert!(c.contains(".Zero = {0}"), "expected .Zero = {{0}} in:\n{c}");
    // Constant declaration uses union type name
    assert!(
        c.contains("const Nat zero ="),
        "expected const Nat zero in:\n{c}"
    );
}

/// Recursive variant construction emits address-of.
#[test]
fn union_recursive_variant_emits_address_of() {
    let (_b, arena) = setup();
    let nat_name = arena.alloc_str("Nat");
    let zero_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
    let succ_fields: &[(crate::core::syntax::Name, &crate::core::syntax::Term)] =
        arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
    let succ_variant: (
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    ) = (arena.alloc_str("Succ"), succ_fields);
    let variants: &[(
        crate::core::syntax::Name,
        &[(crate::core::syntax::Name, &crate::core::syntax::Term)],
    )] = arena.alloc_slice(&[zero_variant, succ_variant]);
    let nat_udef = arena.union_def(nat_name, variants);
    let union_types: &[(&str, &crate::core::syntax::Term)] =
        arena.bump().alloc([(nat_name, nat_udef)]);

    // Build: Succ(Zero)
    let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
    let one_v = arena.variant(nat_name, 1, arena.alloc_slice(&[zero_v]));
    let tops = &[TopLevel::TLDef(
        arena.alloc_str("one"),
        &[],
        Some(arena.builtin(nat_name)),
        one_v,
        0..0,
    )];

    let c = emit_with_types(tops, &[], &[], union_types, &[]);
    // Recursive reference must emit & (address-of) for the pointer field
    assert!(
        c.contains("&((Nat)"),
        "expected &((Nat){{...}}) for recursive field in:\n{c}"
    );
}
