//! Parser tests for generic definitions and type applications.

use common::{leak_bump, s};
use ligare::core::pool::TermArena;
use ligare::core::syntax::Term;
use ligare::front::parser::parse_def_top;

mod common;

fn a() -> (&'static bumpalo::Bump, TermArena<'static>) {
    let b = leak_bump();
    (b, TermArena::new(b))
}

#[test]
fn parse_generic_id_definition() {
    let (b, arena) = a();
    let result = parse_def_top("def id (A : prop) (x : A) : A := x", b, &arena);
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, m_ret, body) = result.unwrap();
    assert_eq!(name, s(&arena, "id"));
    assert_eq!(params.len(), 2);
    // First param: A : prop
    assert_eq!(params[0].0, s(&arena, "A"));
    // Second param: x : A (should be Builtin("A"))
    assert_eq!(params[1].0, s(&arena, "x"));
    if let Some(ty) = params[1].1 {
        assert!(
            matches!(ty, Term::Builtin(name) | Term::Named(name) if *name == "A"),
            "x's type should be Named(\"A\"), got: {:?}",
            ty
        );
    } else {
        panic!("x should have a type annotation");
    }
    // Return type should be A (Builtin)
    if let Some(ret) = m_ret {
        assert!(
            matches!(ret, Term::Builtin(name) | Term::Named(name) if *name == "A"),
            "Return type should be Named(\"A\"), got: {:?}",
            ret
        );
    } else {
        panic!("should have return type");
    }
    // Body is now in desugared form: Annot(NamedLam("A", NamedLam("x", Named("x"))), Pi(...))
    match body {
        Term::Annot(lam_body, _pi) => match lam_body {
            Term::NamedLam(name_a, inner) => {
                assert_eq!(*name_a, s(&arena, "A"));
                match inner {
                    Term::NamedLam(name_x, Term::Named(name)) => {
                        assert_eq!(*name_x, s(&arena, "x"));
                        assert_eq!(*name, s(&arena, "x"));
                    }
                    _ => panic!("Expected NamedLam(\"x\", Named(\"x\")), got: {:?}", inner),
                }
            }
            _ => panic!("Expected NamedLam, got: {:?}", lam_body),
        },
        _ => panic!("Expected Annot, got: {:?}", body),
    }
}

#[test]
fn parse_generic_two_type_params() {
    let (b, arena) = a();
    let result = parse_def_top(
        "def konst (A : prop) (B : prop) (x : A) (y : B) : A := x",
        b,
        &arena,
    );
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, _body) = result.unwrap();
    assert_eq!(name, s(&arena, "konst"));
    assert_eq!(params.len(), 4);
    // A : prop
    assert_eq!(params[0].0, s(&arena, "A"));
    // B : prop
    assert_eq!(params[1].0, s(&arena, "B"));
    // x : A (Builtin("A"))
    assert_eq!(params[2].0, s(&arena, "x"));
    if let Some(ty) = params[2].1 {
        assert!(
            matches!(ty, Term::Builtin(name) | Term::Named(name) if *name == "A"),
            "x's type should be Named(\"A\"), got: {:?}",
            ty
        );
    }
    // y : B (Builtin("B"))
    assert_eq!(params[3].0, s(&arena, "y"));
    if let Some(ty) = params[3].1 {
        assert!(
            matches!(ty, Term::Builtin(name) | Term::Named(name) if *name == "B"),
            "y's type should be Named(\"B\"), got: {:?}",
            ty
        );
    }
}

#[test]
fn parse_generic_with_prop_param() {
    let (b, arena) = a();
    let result = parse_def_top("def wrap (A : prop) (x : A) : A := x", b, &arena);
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, _body) = result.unwrap();
    assert_eq!(name, s(&arena, "wrap"));
    assert_eq!(params.len(), 2);
}

#[test]
fn parse_generic_union_definition() {
    let (b, arena) = a();
    let result = parse_def_top(
        "def Option (A : prop) : prop := union\n  | None\n  | Some of (val : A)\n",
        b,
        &arena,
    );
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, body) = result.unwrap();
    assert_eq!(name, s(&arena, "Option"));
    assert_eq!(params.len(), 1);
    assert_eq!(params[0].0, s(&arena, "A"));
    // Body should be UnionDef
    assert!(matches!(body, Term::UnionDef(..)));
}

#[test]
fn parse_generic_struct_definition() {
    let (b, arena) = a();
    let result = parse_def_top(
        "def Pair (A : prop) (B : prop) : prop := struct\n  fst : A\n  snd : B\n",
        b,
        &arena,
    );
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, body) = result.unwrap();
    assert_eq!(name, s(&arena, "Pair"));
    assert_eq!(params.len(), 2);
    assert!(matches!(body, Term::StructDef(..)));
}

#[test]
fn parse_generic_only_type_params_no_data() {
    let (b, arena) = a();
    let result = parse_def_top("def unit (A : prop) : int := 0", b, &arena);
    assert!(result.is_ok(), "Parse error: {:?}", result.err());
    let (name, params, _m_ret, _body) = result.unwrap();
    assert_eq!(name, s(&arena, "unit"));
    assert_eq!(params.len(), 1);
}

#[test]
fn parse_generic_desugared_form() {
    let (b, arena) = a();
    let result = parse_def_top("def id (A : prop) (x : A) : A := x", b, &arena);
    let (_, _params, _m_ret, body) = result.unwrap();
    // Body is in raw parser form: Annot(NamedLam("A", NamedLam("x", Named("x"))), Pi(...))
    // Type refs are Named, not de Bruijn Var.
    match body {
        Term::Annot(lam_body, ty) => {
            match lam_body {
                Term::NamedLam(name_a, inner) => {
                    assert_eq!(*name_a, s(&arena, "A"));
                    match inner {
                        Term::NamedLam(name_x, Term::Named(name)) => {
                            assert_eq!(*name_x, s(&arena, "x"));
                            assert_eq!(*name, s(&arena, "x"));
                        }
                        _ => panic!(
                            "Expected NamedLam(\"x\", Named(\"x\")), got inner: {:?}",
                            inner
                        ),
                    }
                }
                _ => panic!("Expected NamedLam, got: {:?}", lam_body),
            }
            match ty {
                Term::Pi(name_a, dom_a, cod) => {
                    assert_eq!(**name_a, *s(&arena, "A"));
                    assert_eq!(**dom_a, Term::Builtin(s(&arena, "prop")));
                    match cod {
                        Term::Pi(name_x, dom_x, cod_x) => {
                            assert_eq!(**name_x, *s(&arena, "x"));
                            // Raw parser output: param refs are Named, not de Bruijn Var.
                            assert_eq!(
                                **dom_x,
                                Term::Named(s(&arena, "A")),
                                "dom_x should be Named(\"A\")"
                            );
                            assert_eq!(
                                **cod_x,
                                Term::Named(s(&arena, "A")),
                                "cod_x should be Named(\"A\")"
                            );
                        }
                        _ => panic!("Expected inner Pi, got: {:?}", cod),
                    }
                }
                _ => panic!("Expected Pi, got: {:?}", ty),
            }
        }
        _ => panic!("Expected Annot, got: {:?}", body),
    }
}
