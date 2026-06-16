use crate::core::debruijn::beta;
use crate::core::desugar::desugar;
use crate::core::syntax::{PrimOp, Term};

/// Evaluate a term to normal form.
pub fn eval(t: &Term) -> Result<Term, String> {
    match t {
        Term::App(f, a) => {
            let f_inner = f.as_ref();
            match f_inner {
                Term::Lam(body) => {
                    let replaced_body = replace_this_in_lam(f, body);
                    let reduced = beta(&replaced_body, a);
                    eval(&reduced)
                }
                Term::App(prim, first) => {
                    if matches!(prim.as_ref(), Term::PrimOp(_)) {
                        let a_val = eval(a)?;
                        let first_val = eval(first)?;
                        match (&first_val, &a_val) {
                            (Term::LitInt(x), Term::LitInt(y)) => {
                                eval(&arith(prim_op_to_op(prim)?, *x, *y))
                            }
                            _ => Err("arithmetic on non-integer".to_string()),
                        }
                    } else {
                        let f_val = eval(f)?;
                        if matches!(&f_val, Term::Lam(_)) {
                            eval(&Term::App(Box::new(f_val), a.clone()))
                        } else {
                            Ok(Term::App(Box::new(f_val), a.clone()))
                        }
                    }
                }
                _ => {
                    let f_val = eval(f)?;
                    if matches!(&f_val, Term::Lam(_)) {
                        eval(&Term::App(Box::new(f_val), a.clone()))
                    } else {
                        Ok(Term::App(Box::new(f_val), a.clone()))
                    }
                }
            }
        }
        Term::Lam(_) => Ok(t.clone()),
        Term::Let(_name, val, body, _mconstr) => {
            let reduced = beta(body, val);
            eval(&reduced)
        }
        Term::IfThenElse(cond, tbranch, fbranch) => {
            let cond_val = eval(cond)?;
            match cond_val {
                Term::LitBool(true) => eval(tbranch),
                Term::LitBool(false) => eval(fbranch),
                _ => Ok(Term::IfThenElse(
                    Box::new(cond_val),
                    tbranch.clone(),
                    fbranch.clone(),
                )),
            }
        }
        Term::Annot(inner, _) => eval(inner),
        Term::ByProof(inner, _) => eval(inner),
        Term::Refine(name, parent, p) => {
            let parent_val = eval(parent)?;
            let p_val = eval(p)?;
            Ok(Term::Refine(
                name.clone(),
                Box::new(parent_val),
                Box::new(p_val),
            ))
        }
        Term::AutoProof => Ok(Term::AutoProof),
        Term::RefParam => Ok(Term::RefParam),
        Term::This => Ok(Term::This),
        Term::Func { .. } => {
            let desugared = desugar(t);
            eval(&desugared)
        }
        Term::ProofBlock(inner) => eval(inner),
        other => Ok(other.clone()),
    }
}

/// Replace all `This` in a term with the self-reference (the Lam itself).
fn replace_this_in_lam(lam: &Term, body: &Term) -> Term {
    replace_this(lam, body)
}

fn replace_this(self_term: &Term, t: &Term) -> Term {
    match t {
        Term::This => self_term.clone(),
        Term::App(f, a) => Term::App(
            Box::new(replace_this(self_term, f)),
            Box::new(replace_this(self_term, a)),
        ),
        Term::Lam(b) => Term::Lam(Box::new(replace_this(self_term, b))),
        Term::Let(n, v, b, mc) => Term::Let(
            n.clone(),
            Box::new(replace_this(self_term, v)),
            Box::new(replace_this(self_term, b)),
            mc.as_ref().map(|c| Box::new(replace_this(self_term, c))),
        ),
        Term::IfThenElse(c, th, el) => Term::IfThenElse(
            Box::new(replace_this(self_term, c)),
            Box::new(replace_this(self_term, th)),
            Box::new(replace_this(self_term, el)),
        ),
        Term::Annot(inner, c) => Term::Annot(
            Box::new(replace_this(self_term, inner)),
            Box::new(replace_this(self_term, c)),
        ),
        Term::ByProof(inner, p) => Term::ByProof(
            Box::new(replace_this(self_term, inner)),
            Box::new(replace_this(self_term, p)),
        ),
        Term::Refine(n, par, p) => Term::Refine(
            n.clone(),
            Box::new(replace_this(self_term, par)),
            Box::new(replace_this(self_term, p)),
        ),
        Term::Pi(n, a, b) => Term::Pi(
            n.clone(),
            Box::new(replace_this(self_term, a)),
            Box::new(replace_this(self_term, b)),
        ),
        Term::ProofBlock(inner) => Term::ProofBlock(Box::new(replace_this(self_term, inner))),
        other => other.clone(),
    }
}

fn prim_op_to_op(term: &Term) -> Result<PrimOp, String> {
    match term {
        Term::PrimOp(op) => Ok(*op),
        _ => Err("expected PrimOp".to_string()),
    }
}

fn arith(op: PrimOp, x: i64, y: i64) -> Term {
    match op {
        PrimOp::Add => Term::LitInt(x + y),
        PrimOp::Sub => Term::LitInt(x - y),
        PrimOp::Mul => Term::LitInt(x * y),
        PrimOp::Div => {
            if y == 0 {
                Term::LitInt(0) // division by zero in spec, but we just do it
            } else {
                Term::LitInt(x / y)
            }
        }
        PrimOp::Mod_ => {
            if y == 0 {
                Term::LitInt(0)
            } else {
                Term::LitInt(x % y)
            }
        }
        PrimOp::Eq => Term::LitBool(x == y),
        PrimOp::Lt => Term::LitBool(x < y),
        PrimOp::Gt => Term::LitBool(x > y),
        PrimOp::Le => Term::LitBool(x <= y),
        PrimOp::Ge => Term::LitBool(x >= y),
        PrimOp::Neq => Term::LitBool(x != y),
    }
}
