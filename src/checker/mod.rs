pub mod builtin;
pub mod context;

use crate::checker::builtin::check_builtin;
use crate::checker::context::{
    ConstraintTable, Context, add_refine, add_theorem, expand_constraint, extend_ctx,
    extend_ctx_term, lookup_refine,
};
use crate::core::desugar::desugar;
use crate::core::eval::eval;
use crate::core::pool::TermArena;
use crate::core::syntax::{Name, PrimOp, Term, Universe};

// Common string constants to avoid repeated heap allocation.
const BOOL: &str = "bool";
const AND: &str = "and";
const OR: &str = "or";
const NOT: &str = "not";
const AND_INTRO: &str = "∧-intro";
const AND_ELIM_LEFT: &str = "∧-elim-left";
const EXPECTED_LAMBDA: &str = "Expected a lambda";

/// Main entry for checking a term against a constraint.
pub fn check<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    term: &'bump Term<'bump>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    let desugared = desugar(arena, term);
    match desugared {
        Term::Var(i) => check_var(arena, table, ctx, *i, constraint),
        Term::Annot(t, c) => {
            check(arena, table, ctx, t, c)?;
            check(arena, table, ctx, t, constraint)
        }
        Term::ByProof(t, _proof) => check(arena, table, ctx, t, constraint),
        Term::Refine(name, parent, p) => {
            let new_table = add_refine(name, parent, p, table);
            check(arena, &new_table, ctx, constraint, constraint)
        }
        Term::IfThenElse(cond, tbranch, fbranch) => {
            check_if(arena, table, ctx, cond, tbranch, fbranch, constraint)
        }
        Term::ProofBlock(proof_term) => {
            let evald = eval(arena, term)?;
            prove_with(arena, table, ctx, evald, constraint, proof_term)
        }
        Term::Let(_name, val, body, mconstr) => {
            check_let(arena, table, ctx, val, body, *mconstr, constraint)
        }
        _ => check_by_constraint(arena, table, ctx, desugared, constraint),
    }
}

fn check_var<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    i: usize,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    let expected = ctx
        .lookup(i)
        .ok_or_else(|| format!("Unbound variable index: {}", i))?;
    let expected_val = eval(arena, expected)?;
    let constraint_val = eval(arena, constraint)?;
    if expected_val == constraint_val || is_refinement_of(table, expected_val, constraint_val) {
        Ok(())
    } else {
        Err(format!(
            "Constraint mismatch for variable: expected {:?}, but got {:?}",
            expected_val, constraint_val
        ))
    }
}

fn check_if<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    cond: &'bump Term<'bump>,
    tbranch: &'bump Term<'bump>,
    fbranch: &'bump Term<'bump>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    let bool_name = arena.alloc_str(BOOL);
    check(arena, table, ctx, cond, arena.builtin(bool_name))?;
    let ctx_t = add_theorem("_", cond, ctx);
    let ctx_f = add_theorem("_", not_term(arena, cond), ctx);
    check(arena, table, &ctx_t, tbranch, constraint)?;
    check(arena, table, &ctx_f, fbranch, constraint)
}

fn check_let<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    val: &'bump Term<'bump>,
    body: &'bump Term<'bump>,
    mconstr: Option<&'bump Term<'bump>>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    if let Some(c) = mconstr {
        check(arena, table, ctx, val, c)?;
    }
    let new_ctx = extend_ctx_term(constraint, ctx);
    check(arena, table, &new_ctx, body, constraint)
}

fn check_by_constraint<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    term: &'bump Term<'bump>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    // Handle Refine constraint without evaluating the unsubstituted predicate
    if let Term::Refine(name, parent, p) = constraint {
        let new_table = add_refine(name, parent, p, table);
        check(arena, &new_table, ctx, term, parent)?;
        return prove_auto(arena, ctx, term, p);
    }

    let norm = eval(arena, constraint)?;
    match norm {
        Term::Builtin(name) => {
            if let Some(checker) = check_builtin(name) {
                let evald = eval(arena, term)?;
                checker(evald)
            } else if let Some((parent, pred)) = lookup_refine(name, table) {
                check(arena, table, ctx, term, parent)?;
                prove_auto(arena, ctx, term, pred)
            } else {
                Err(format!("Unknown builtin: {}", name))
            }
        }
        Term::Pi(name, a, b) if name.is_empty() => check_arrow(arena, table, ctx, term, a, b),
        Term::Pi(name, a, b) => check_pi(arena, table, ctx, term, name, a, b),
        Term::Universe(Universe::UData) => Ok(()),
        Term::Var(j) => Err(format!(
            "Variable {} is a data term, cannot be used as a constraint",
            j
        )),
        Term::App(app_and, a) => try_check_logical_op(arena, table, ctx, term, app_and, a, norm),
        _ => {
            let cname = constraint_name(norm);
            if let Some((parent, pred)) = lookup_refine(cname, table) {
                check(arena, table, ctx, term, parent)?;
                prove_auto(arena, ctx, term, pred)
            } else {
                Err(format!("Cannot use {:?} as a constraint", norm))
            }
        }
    }
}

/// Try to check a term against a logical connective (and / or / not).
fn try_check_logical_op<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    term: &'bump Term<'bump>,
    head: &'bump Term<'bump>,
    arg: &'bump Term<'bump>,
    norm: &'bump Term<'bump>,
) -> Result<(), String> {
    let Term::App(builtin, b) = head else {
        return check_app_constraint(arena, table, ctx, term, norm);
    };
    let Term::Builtin(name) = *builtin else {
        return check_app_constraint(arena, table, ctx, term, norm);
    };
    match *name {
        AND => {
            check(arena, table, ctx, term, arg)?;
            check(arena, table, ctx, term, b)
        }
        OR => check(arena, table, ctx, term, arg).or_else(|_| check(arena, table, ctx, term, b)),
        NOT => Ok(()),
        _ => check_app_constraint(arena, table, ctx, term, norm),
    }
}

fn check_arrow<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    t: &'bump Term<'bump>,
    a: &'bump Term<'bump>,
    b: &'bump Term<'bump>,
) -> Result<(), String> {
    check_pi_impl(arena, table, ctx, t, a, b, None)
}

fn check_pi<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    t: &'bump Term<'bump>,
    name: Name<'bump>,
    a: &'bump Term<'bump>,
    b: &'bump Term<'bump>,
) -> Result<(), String> {
    check_pi_impl(arena, table, ctx, t, a, b, Some(name))
}

/// Shared implementation for arrow and dependent Pi checking.
fn check_pi_impl<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    t: &'bump Term<'bump>,
    a: &'bump Term<'bump>,
    b: &'bump Term<'bump>,
    name: Option<Name<'bump>>,
) -> Result<(), String> {
    let t_val = eval(arena, t)?;
    let Term::Lam(body) = t_val else {
        return Err(EXPECTED_LAMBDA.to_string());
    };
    let new_ctx = match name {
        Some(n) if !n.is_empty() => extend_ctx(n, a, ctx),
        _ => extend_ctx_term(a, ctx),
    };
    check(arena, table, &new_ctx, body, b)
}

fn check_app_constraint<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    term: &'bump Term<'bump>,
    constraint: &'bump Term<'bump>,
) -> Result<(), String> {
    if let Some(expanded) = expand_constraint(arena, table, constraint) {
        return check(arena, table, ctx, term, expanded);
    }

    if let Term::App(f, a) = constraint {
        let cname = constraint_name(f);
        if let Some((parent, body)) = lookup_refine(cname, table)
            && matches!(parent, Term::Universe(Universe::UData))
        {
            return check(arena, table, ctx, term, arena.app(body, a));
        }
    }

    Err(format!("Cannot use {:?} as a constraint", constraint))
}

fn constraint_name<'a>(t: &Term<'a>) -> &'a str {
    match t {
        Term::Builtin(n) => n,
        Term::Refine(n, _, _) => n,
        _ => "?",
    }
}

fn is_refinement_of<'bump>(
    table: &ConstraintTable<'bump>,
    t1: &'bump Term<'bump>,
    t2: &'bump Term<'bump>,
) -> bool {
    if t1 == t2 {
        return true;
    }
    match t1 {
        Term::Builtin(n) | Term::Refine(n, _, _) => lookup_refine(n, table)
            .map(|(parent, _)| is_refinement_of(table, parent, t2))
            .unwrap_or(false),
        _ => false,
    }
}

/// Wrap a term in a boolean negation.
fn not_term<'bump>(arena: &TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    let body = arena.if_then_else(arena.var(0), arena.lit_bool(false), arena.lit_bool(true));
    arena.app(arena.lam(body), t)
}

// ---- Proof search ----

fn prove_auto<'bump>(
    arena: &TermArena<'bump>,
    ctx: &Context<'bump>,
    subject: &'bump Term<'bump>,
    pred: &'bump Term<'bump>,
) -> Result<(), String> {
    let instantiated = subst_ref_param(arena, subject, pred);
    let instantiated_val = eval(arena, instantiated)?;
    match instantiated_val {
        Term::LitBool(true) => Ok(()),
        Term::LitBool(false) => Err(format!("Predicate does not hold for {:?}", subject)),
        _ if search_ctx(arena, ctx, subject, pred) => Ok(()),
        _ => try_simple_derive(arena, pred, ctx, subject),
    }
}

fn subst_ref_param<'bump>(
    arena: &TermArena<'bump>,
    subj: &'bump Term<'bump>,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    match t {
        Term::RefParam => subj,
        Term::App(f, a) => {
            let f2 = subst_ref_param(arena, subj, f);
            let a2 = subst_ref_param(arena, subj, a);
            arena.app(f2, a2)
        }
        Term::Lam(b) => {
            let b2 = subst_ref_param(arena, subj, b);
            arena.lam(b2)
        }
        Term::Let(n, v, b, mc) => {
            let v2 = subst_ref_param(arena, subj, v);
            let b2 = subst_ref_param(arena, subj, b);
            let mc2 = mc.map(|c| subst_ref_param(arena, subj, c));
            arena.let_(n, v2, b2, mc2)
        }
        Term::IfThenElse(c, th, el) => {
            let c2 = subst_ref_param(arena, subj, c);
            let th2 = subst_ref_param(arena, subj, th);
            let el2 = subst_ref_param(arena, subj, el);
            arena.if_then_else(c2, th2, el2)
        }
        Term::Annot(inner, c) => {
            let inner2 = subst_ref_param(arena, subj, inner);
            let c2 = subst_ref_param(arena, subj, c);
            arena.annot(inner2, c2)
        }
        Term::ByProof(inner, p) => {
            let inner2 = subst_ref_param(arena, subj, inner);
            let p2 = subst_ref_param(arena, subj, p);
            arena.by_proof(inner2, p2)
        }
        Term::Refine(n, par, p) => {
            let par2 = subst_ref_param(arena, subj, par);
            let p2 = subst_ref_param(arena, subj, p);
            arena.refine(n, par2, p2)
        }
        _ => t,
    }
}

fn search_ctx<'bump>(
    arena: &TermArena<'bump>,
    ctx: &Context<'bump>,
    subject: &'bump Term<'bump>,
    target: &'bump Term<'bump>,
) -> bool {
    ctx.iter()
        .flat_map(|entry| &entry.theorems)
        .any(|thm| eval_eq(arena, subject, thm, target))
}

fn eval_eq<'bump>(
    arena: &TermArena<'bump>,
    subject: &'bump Term<'bump>,
    t1: &'bump Term<'bump>,
    t2: &'bump Term<'bump>,
) -> bool {
    let v1 = eval(arena, subst_ref_param(arena, subject, t1));
    let v2 = eval(arena, subst_ref_param(arena, subject, t2));
    matches!((v1, v2), (Ok(a), Ok(b)) if a == b)
}

/// Check whether `pred` is of the form `a /= b`. If so, look through
/// the context for an `a > b` theorem as a way to prove inequality.
fn try_simple_derive<'bump>(
    arena: &TermArena<'bump>,
    pred: &'bump Term<'bump>,
    ctx: &Context<'bump>,
    _subject: &'bump Term<'bump>,
) -> Result<(), String> {
    let Some((a, b)) = try_match_neq(pred) else {
        return Err("Automatic proof failed: provide a manual proof with `by`".to_string());
    };
    let gt = arena.app(arena.app(arena.prim_op(PrimOp::Gt), a), b);
    let found = ctx
        .iter()
        .flat_map(|entry| &entry.theorems)
        .any(|thm| eval_eq_simple(arena, gt, thm));
    if found {
        Ok(())
    } else {
        Err(format!("Cannot prove {:?}", pred))
    }
}

/// If `t` is `(_ /= _)`, return the two operands.
fn try_match_neq<'bump>(t: &'bump Term<'bump>) -> Option<(&'bump Term<'bump>, &'bump Term<'bump>)> {
    let Term::App(neq_app, b) = t else {
        return None;
    };
    let Term::App(prim, a) = *neq_app else {
        return None;
    };
    if !matches!(prim, Term::PrimOp(PrimOp::Neq)) {
        return None;
    }
    Some((a, b))
}

fn eval_eq_simple<'bump>(
    arena: &TermArena<'bump>,
    t1: &'bump Term<'bump>,
    t2: &'bump Term<'bump>,
) -> bool {
    matches!((eval(arena, t1), eval(arena, t2)), (Ok(a), Ok(b)) if a == b)
}

/// Try to destructure a conjunction goal with an ∧-intro proof.
fn try_split_conj_proof<'t>(
    goal: &'t Term<'t>,
    proof: &'t Term<'t>,
) -> Option<(&'t Term<'t>, &'t Term<'t>, &'t Term<'t>, &'t Term<'t>)> {
    let Term::App(and_app, b) = goal else {
        return None;
    };
    let Term::App(builtin, a) = *and_app else {
        return None;
    };
    let Term::Builtin(name) = *builtin else {
        return None;
    };
    if *name != AND {
        return None;
    }

    let Term::App(and_intro, pb) = proof else {
        return None;
    };
    let Term::App(builtin2, pa) = *and_intro else {
        return None;
    };
    let Term::Builtin(n2) = *builtin2 else {
        return None;
    };
    if *n2 != AND_INTRO {
        return None;
    }

    Some((a, pa, b, pb))
}

fn prove_with<'bump>(
    arena: &TermArena<'bump>,
    table: &ConstraintTable<'bump>,
    ctx: &Context<'bump>,
    subject: &'bump Term<'bump>,
    goal: &'bump Term<'bump>,
    proof: &'bump Term<'bump>,
) -> Result<(), String> {
    if let Some((a, pa, b, pb)) = try_split_conj_proof(goal, proof) {
        prove_with(arena, table, ctx, subject, a, pa)?;
        return prove_with(arena, table, ctx, subject, b, pb);
    }

    match proof {
        Term::Builtin(name) if *name == AND_ELIM_LEFT => Ok(()),
        Term::LitBool(true) => Ok(()),
        Term::AutoProof => prove_auto(arena, ctx, subject, goal),
        Term::ProofBlock(inner) => prove_with(arena, table, ctx, subject, goal, inner),
        _ => Err("Cannot use this term as a proof".to_string()),
    }
}
