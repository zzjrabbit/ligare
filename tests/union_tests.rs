//! Integration tests for union types and pattern matching.
//! These tests exercise the full parse → check → eval pipeline.

use bumpalo::Bump;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    let a = TermArena::new(b);
    (b, a)
}

#[test]
fn union_definition_and_variant_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\n#check Red : Color\n#check Green : Color\n"
            )
            .is_ok()
    );
}

#[test]
fn union_with_payload_check() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := union\n  | None\n  | Some of (val : int)\n#check Some 5 : Option\n#check None : Option\n"
            )
            .is_ok()
    );
}

#[test]
fn match_reduces_on_variant() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\n#check (match Red with | Red => 1 | Green => 2 | Blue => 3) : int\n"
            )
            .is_ok()
    );
}

#[test]
fn eval_match() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\n  | Blue\n#show match Red with | Red => 42 | Green => 0 | Blue => 0\n"
            )
            .is_ok()
    );
}

#[test]
fn match_with_binding_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := union\n  | None\n  | Some of (val : int)\n#show match Some 5 with | None => -1 | Some x => x\n"
            )
            .is_ok()
    );
}

#[test]
fn match_none_eval() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Option : prop := union\n  | None\n  | Some of (val : int)\n#show match None with | None => 0 | Some x => 1\n"
            )
            .is_ok()
    );
}

#[test]
fn wrong_variant_type_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str("def Color : prop := union\n  | Red\n  | Green\n#check Red : int\n")
            .is_err()
    );
}

#[test]
fn wrong_union_member_fails() {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    assert!(
        compiler
            .process_file_str(
                "def Color : prop := union\n  | Red\n  | Green\ndef Shape : prop := union\n  | Circle\n  | Square\n#check Circle : Color\n"
            )
            .is_err()
    );
}
