mod common;

use common::{bin, parse, parse_constraint};
use ligare::checker::checker::check;
use ligare::checker::context::{add_refine, empty_ctx, empty_table};
use ligare::core::syntax::{PrimOp, Term};

fn nat_def() -> (String, Term, Term) {
    (
        "nat".to_string(),
        Term::Builtin("int".to_string()),
        bin(PrimOp::Ge, Term::RefParam, Term::LitInt(0)),
    )
}

fn pos_def() -> (String, Term, Term) {
    (
        "pos".to_string(),
        Term::Builtin("int".to_string()),
        bin(PrimOp::Gt, Term::RefParam, Term::LitInt(0)),
    )
}

fn check_with(refs: &[(String, Term, Term)], t: &Term, c: &Term) -> Result<(), String> {
    let table = refs.iter().fold(empty_table(), |tbl, (n, p, pr)| {
        add_refine(n.clone(), p.clone(), pr.clone(), &tbl)
    });
    check(&table, &empty_ctx(), t, c)
}

#[test]
fn nat_accepts_5() {
    assert_eq!(
        check_with(
            &[nat_def()],
            &Term::LitInt(5),
            &Term::Builtin("nat".to_string())
        ),
        Ok(())
    );
}

#[test]
fn nat_rejects_negative_1() {
    assert!(
        check_with(
            &[nat_def()],
            &parse("-1"),
            &Term::Builtin("nat".to_string())
        )
        .is_err()
    );
}

#[test]
fn nat_accepts_0() {
    assert_eq!(
        check_with(
            &[nat_def()],
            &Term::LitInt(0),
            &Term::Builtin("nat".to_string())
        ),
        Ok(())
    );
}

#[test]
fn pos_rejects_0() {
    assert!(
        check_with(
            &[pos_def()],
            &Term::LitInt(0),
            &Term::Builtin("pos".to_string())
        )
        .is_err()
    );
}

#[test]
fn pos_accepts_3() {
    assert_eq!(
        check_with(
            &[pos_def()],
            &Term::LitInt(3),
            &Term::Builtin("pos".to_string())
        ),
        Ok(())
    );
}

#[test]
fn nat_is_subtype_of_int_variable_check() {
    assert_eq!(
        check_with(
            &[nat_def()],
            &parse("\\x. x"),
            &parse_constraint("nat -> int")
        ),
        Ok(())
    );
}

#[test]
fn pos_is_subtype_of_int_parent_chain() {
    assert_eq!(
        check_with(
            &[pos_def()],
            &parse("\\x. x"),
            &parse_constraint("pos -> int")
        ),
        Ok(())
    );
}
