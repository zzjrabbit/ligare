use crate::checker::builtin::check_builtin;
use crate::checker::context::{
    ConstraintTable, Context, add_refine, add_theorem, expand_constraint, extend_ctx,
    extend_ctx_term, lookup_refine,
};
use crate::core::desugar::desugar;
use crate::core::eval::eval;
use crate::core::syntax::{PrimOp, Term, Universe};

/// Main entry for checking a term against a constraint.
pub fn check(
    table: &ConstraintTable,
    ctx: &Context,
    term: &Term,
    constraint: &Term,
) -> Result<(), String> {
    let desugared = desugar(term);
    match &desugared {
        Term::Var(i) => check_var(table, ctx, *i, constraint),
        Term::Annot(t, c) => {
            check(table, ctx, t, c)?;
            check(table, ctx, t, constraint)
        }
        Term::ByProof(t, _proof) => check(table, ctx, t, constraint),
        Term::Refine(name, parent, p) => {
            let new_table = add_refine(
                name.clone(),
                parent.as_ref().clone(),
                p.as_ref().clone(),
                table,
            );
            check(&new_table, ctx, constraint, constraint)
        }
        Term::IfThenElse(cond, tbranch, fbranch) => {
            check_if(table, ctx, cond, tbranch, fbranch, constraint)
        }
        Term::ProofBlock(proof_term) => {
            let evald = eval(term)?;
            prove_with(table, ctx, &evald, constraint, proof_term)
        }
        Term::Let(_name, val, body, mconstr) => {
            check_let(table, ctx, val, body, mconstr.as_deref(), constraint)
        }
        _ => check_by_constraint(table, ctx, &desugared, constraint),
    }
}

fn check_var(
    table: &ConstraintTable,
    ctx: &Context,
    i: usize,
    constraint: &Term,
) -> Result<(), String> {
    let expected = lookup_ctx(ctx, i).ok_or_else(|| format!("Unbound variable index: {}", i))?;
    let expected_val = eval(&expected)?;
    let constraint_val = eval(constraint)?;
    if expected_val == constraint_val || is_refinement_of(table, &expected_val, &constraint_val) {
        Ok(())
    } else {
        Err(format!(
            "Constraint mismatch for variable: expected {:?}, but got {:?}",
            expected_val, constraint_val
        ))
    }
}

fn check_if(
    table: &ConstraintTable,
    ctx: &Context,
    cond: &Term,
    tbranch: &Term,
    fbranch: &Term,
    constraint: &Term,
) -> Result<(), String> {
    check(table, ctx, cond, &Term::Builtin("bool".to_string()))?;
    let ctx_t = add_theorem("_", cond.clone(), ctx);
    let ctx_f = add_theorem("_", not_term(cond), ctx);
    check(table, &ctx_t, tbranch, constraint)?;
    check(table, &ctx_f, fbranch, constraint)
}

fn check_let(
    table: &ConstraintTable,
    ctx: &Context,
    val: &Term,
    body: &Term,
    mconstr: Option<&Term>,
    constraint: &Term,
) -> Result<(), String> {
    if let Some(c) = mconstr {
        check(table, ctx, val, c)?;
    }
    let new_ctx = extend_ctx("_".to_string(), constraint.clone(), ctx);
    check(table, &new_ctx, body, constraint)
}

fn check_by_constraint(
    table: &ConstraintTable,
    ctx: &Context,
    term: &Term,
    constraint: &Term,
) -> Result<(), String> {
    // Handle Refine constraint without evaluating the unsubstituted predicate
    if let Term::Refine(name, parent, p) = constraint {
        let new_table = add_refine(
            name.clone(),
            parent.as_ref().clone(),
            p.as_ref().clone(),
            table,
        );
        check(&new_table, ctx, term, parent)?;
        return prove_auto(ctx, term, p);
    }

    let norm = eval(constraint)?;
    match &norm {
        Term::Builtin(name) => {
            if let Some(checker) = check_builtin(name) {
                let evald = eval(term)?;
                checker(&evald)
            } else if let Some((parent, pred)) = lookup_refine(name, table) {
                check(table, ctx, term, &parent)?;
                prove_auto(ctx, term, &pred)
            } else {
                Err(format!("Unknown builtin: {}", name))
            }
        }
        Term::Pi(name, a, b) if name.is_empty() => check_arrow(table, ctx, term, a, b),
        Term::Pi(name, a, b) => check_pi(table, ctx, term, name, a, b),
        Term::Universe(Universe::UData) => Ok(()),
        Term::Var(j) => Err(format!(
            "Variable {} is a data term, cannot be used as a constraint",
            j
        )),
        Term::App(app_and, a) => {
            if let Term::App(builtin, b) = app_and.as_ref() {
                if let Term::Builtin(name) = builtin.as_ref() {
                    match name.as_str() {
                        "and" => {
                            check(table, ctx, term, a)?;
                            check(table, ctx, term, b)
                        }
                        "or" => {
                            if check(table, ctx, term, a).is_ok() {
                                Ok(())
                            } else {
                                check(table, ctx, term, b)
                            }
                        }
                        "not" => Ok(()),
                        _ => check_app_constraint(table, ctx, term, &norm),
                    }
                } else {
                    check_app_constraint(table, ctx, term, &norm)
                }
            } else {
                check_app_constraint(table, ctx, term, &norm)
            }
        }
        _ => {
            let cname = constraint_name(&norm);
            if let Some((parent, pred)) = lookup_refine(&cname, table) {
                check(table, ctx, term, &parent)?;
                prove_auto(ctx, term, &pred)
            } else {
                Err(format!("Cannot use {:?} as a constraint", norm))
            }
        }
    }
}

fn check_arrow(
    table: &ConstraintTable,
    ctx: &Context,
    t: &Term,
    a: &Term,
    b: &Term,
) -> Result<(), String> {
    let t_val = eval(t)?;
    match t_val {
        Term::Lam(body) => {
            let new_ctx = extend_ctx_term(a.clone(), ctx);
            check(table, &new_ctx, &body, b)
        }
        _ => Err("Expected a lambda".to_string()),
    }
}

fn check_pi(
    table: &ConstraintTable,
    ctx: &Context,
    t: &Term,
    name: &str,
    a: &Term,
    b: &Term,
) -> Result<(), String> {
    let t_val = eval(t)?;
    match t_val {
        Term::Lam(body) => {
            let new_ctx = extend_ctx(name.to_string(), a.clone(), ctx);
            check(table, &new_ctx, &body, b)
        }
        _ => Err("Expected a lambda".to_string()),
    }
}

fn check_app_constraint(
    table: &ConstraintTable,
    ctx: &Context,
    term: &Term,
    constraint: &Term,
) -> Result<(), String> {
    if let Some(expanded) = expand_constraint(table, constraint) {
        return check(table, ctx, term, &expanded);
    }

    if let Term::App(f, a) = constraint {
        let cname = constraint_name(f);
        if let Some((parent, body)) = lookup_refine(&cname, table) {
            if matches!(parent, Term::Universe(Universe::UData)) {
                return check(table, ctx, term, &Term::App(Box::new(body), a.clone()));
            }
        }
    }

    Err(format!("Cannot use {:?} as a constraint", constraint))
}

fn constraint_name(t: &Term) -> String {
    match t {
        Term::Builtin(n) => n.clone(),
        Term::Refine(n, _, _) => n.clone(),
        _ => "?".to_string(),
    }
}

fn is_refinement_of(table: &ConstraintTable, t1: &Term, t2: &Term) -> bool {
    if t1 == t2 {
        return true;
    }
    match t1 {
        Term::Builtin(n) => {
            if let Some((parent, _)) = lookup_refine(n, table) {
                is_refinement_of(table, &parent, t2)
            } else {
                false
            }
        }
        Term::Refine(n, _, _) => is_refinement_of(table, &Term::Builtin(n.clone()), t2),
        _ => false,
    }
}

fn not_term(t: &Term) -> Term {
    Term::App(
        Box::new(Term::Lam(Box::new(Term::IfThenElse(
            Box::new(Term::Var(0)),
            Box::new(Term::LitBool(false)),
            Box::new(Term::LitBool(true)),
        )))),
        Box::new(t.clone()),
    )
}

// ---- Proof search ----

fn prove_auto(ctx: &Context, subject: &Term, pred: &Term) -> Result<(), String> {
    let instantiated = subst_ref_param(subject, pred);
    let instantiated_val = eval(&instantiated)?;
    match instantiated_val {
        Term::LitBool(true) => Ok(()),
        Term::LitBool(false) => Err(format!("Predicate does not hold for {:?}", subject)),
        _ => {
            if search_ctx(ctx, subject, pred).is_some() {
                Ok(())
            } else {
                try_simple_derive(pred, ctx, subject)
            }
        }
    }
}

fn subst_ref_param(subj: &Term, t: &Term) -> Term {
    match t {
        Term::RefParam => subj.clone(),
        Term::App(f, a) => Term::App(
            Box::new(subst_ref_param(subj, f)),
            Box::new(subst_ref_param(subj, a)),
        ),
        Term::Lam(b) => Term::Lam(Box::new(subst_ref_param(subj, b))),
        Term::Let(n, v, b, mc) => Term::Let(
            n.clone(),
            Box::new(subst_ref_param(subj, v)),
            Box::new(subst_ref_param(subj, b)),
            mc.as_ref().map(|c| Box::new(subst_ref_param(subj, c))),
        ),
        Term::IfThenElse(c, th, el) => Term::IfThenElse(
            Box::new(subst_ref_param(subj, c)),
            Box::new(subst_ref_param(subj, th)),
            Box::new(subst_ref_param(subj, el)),
        ),
        Term::Annot(inner, c) => Term::Annot(
            Box::new(subst_ref_param(subj, inner)),
            Box::new(subst_ref_param(subj, c)),
        ),
        Term::ByProof(inner, p) => Term::ByProof(
            Box::new(subst_ref_param(subj, inner)),
            Box::new(subst_ref_param(subj, p)),
        ),
        Term::Refine(n, par, p) => Term::Refine(
            n.clone(),
            Box::new(subst_ref_param(subj, par)),
            Box::new(subst_ref_param(subj, p)),
        ),
        other => other.clone(),
    }
}

fn search_ctx(ctx: &Context, subject: &Term, target: &Term) -> Option<Term> {
    for entry in ctx.iter() {
        for thm in &entry.theorems {
            if eval_eq(subject, thm, target) {
                return Some(thm.clone());
            }
        }
    }
    None
}

fn eval_eq(subject: &Term, t1: &Term, t2: &Term) -> bool {
    let v1 = eval(&subst_ref_param(subject, t1));
    let v2 = eval(&subst_ref_param(subject, t2));
    match (v1, v2) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}

fn lookup_ctx(ctx: &Context, i: usize) -> Option<Term> {
    ctx.lookup(i)
}

fn try_simple_derive(pred: &Term, ctx: &Context, _subject: &Term) -> Result<(), String> {
    if let Term::App(neq_app, b) = pred {
        if let Term::App(prim, a) = neq_app.as_ref() {
            if matches!(prim.as_ref(), Term::PrimOp(PrimOp::Neq)) {
                let gt = Term::App(
                    Box::new(Term::App(Box::new(Term::PrimOp(PrimOp::Gt)), a.clone())),
                    b.clone(),
                );
                for entry in ctx.iter() {
                    for thm in &entry.theorems {
                        if eval_eq_simple(&gt, thm) {
                            return Ok(());
                        }
                    }
                }
                return Err(format!("Cannot prove {:?}", pred));
            }
        }
    }
    Err("Automatic proof failed: provide a manual proof with `by`".to_string())
}

fn eval_eq_simple(t1: &Term, t2: &Term) -> bool {
    match (eval(t1), eval(t2)) {
        (Ok(a), Ok(b)) => a == b,
        _ => false,
    }
}

fn prove_with(
    table: &ConstraintTable,
    ctx: &Context,
    subject: &Term,
    goal: &Term,
    proof: &Term,
) -> Result<(), String> {
    match goal {
        Term::App(and_app, b) => {
            if let Term::App(builtin, a) = and_app.as_ref() {
                if let Term::Builtin(name) = builtin.as_ref() {
                    if name == "and" {
                        match proof {
                            Term::App(and_intro, pb) => {
                                if let Term::App(builtin2, pa) = and_intro.as_ref() {
                                    if let Term::Builtin(n2) = builtin2.as_ref() {
                                        if n2 == "∧-intro" {
                                            prove_with(table, ctx, subject, a, pa)?;
                                            return prove_with(table, ctx, subject, b, pb);
                                        }
                                    }
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
        }
        _ => {}
    }

    match proof {
        Term::Builtin(name) if name == "∧-elim-left" => Ok(()),
        Term::LitBool(true) => Ok(()),
        Term::AutoProof => prove_auto(ctx, subject, goal),
        Term::ProofBlock(inner) => prove_with(table, ctx, subject, goal, inner),
        _ => Err("Cannot use this term as a proof".to_string()),
    }
}
