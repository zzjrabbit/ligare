//! End-to-end coverage for the top-level examples mirrored from `test.lig`.

use bumpalo::Bump;
use ligare::compiler::Compiler;
use ligare::core::pool::TermArena;

fn setup() -> (&'static Bump, TermArena<'static>) {
    let b = Box::leak(Box::new(Bump::new()));
    (b, TermArena::new(b))
}

fn process_ok(source: &str) {
    let (bump, arena) = setup();
    let mut compiler = Compiler::new(bump, &arena);
    let result = compiler.process_file_str(source);
    assert!(result.is_ok(), "Error: {:?}", result.err());
}

#[test]
fn test_lig_fixture_runs_end_to_end() {
    process_ok(include_str!("fixtures/test.lig"));
}

#[test]
fn sdiv_refinement_parameter_checks_from_source() {
    process_ok(
        "def sdiv (a : int) (b : int where (x => x /= 0)) := a / b\n\
         #check sdiv 1 1 : int\n",
    );
}

#[test]
fn theorem_names_remain_available_to_later_terms() {
    process_ok(
        "def Nat := int where (x => x >= 0)\n\
         theorem zero_is_nat : Nat := 0 by\n  exact true\n\
         theorem identity : int -> int := \\x. x\n\
         #check zero_is_nat : Nat\n\
         #check identity 5 : int\n",
    );
}

#[test]
fn theorem_with_fun_syntax_checks_from_source() {
    process_ok(
        "theorem add_one : int -> int := fun x => x + 1\n\
         #check add_one 5 : int\n",
    );
}

#[test]
fn top_level_string_definition_application_and_show() {
    process_ok(
        "def some_sth : str := \"hello\"\n\
         def some_fn (s : str) := s\n\
         #check some_fn some_sth : str\n\
         #check \"hello\" : data\n\
         #show some_fn some_sth\n",
    );
}
