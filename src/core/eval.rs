use crate::core::debruijn::beta;
use crate::core::desugar::desugar;
use crate::core::pool::TermArena;
use crate::core::syntax::{PrimOp, Term};

/// Evaluate a term to normal form.  May allocate intermediate terms
/// in the arena; the result lives in the arena.
pub fn eval<'bump>(
    arena: &TermArena<'bump>,
    t: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    match t {
        Term::App(f, a) => eval_app(arena, f, a),
        Term::Lam(_) => Ok(t),
        Term::Let(_name, val, body, _mconstr) => {
            let b = beta(arena, body, val);
            eval(arena, b)
        }
        Term::IfThenElse(cond, tbranch, fbranch) => eval_if(arena, cond, tbranch, fbranch),
        Term::Annot(inner, _) => eval(arena, inner),
        Term::ByProof(inner, _) => eval(arena, inner),
        Term::Refine(name, parent, p) => {
            let parent_val = eval(arena, parent)?;
            let p_val = eval(arena, p)?;
            Ok(arena.refine(name, parent_val, p_val))
        }
        Term::AutoProof => Ok(t),
        Term::RefParam => Ok(t),
        Term::This => Ok(t),
        Term::Func { .. } => {
            let d = desugar(arena, t);
            eval(arena, d)
        }
        Term::ProofBlock(inner) => eval(arena, inner),
        // Leaf values
        Term::Pi(_, _, _)
        | Term::Var(_)
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::Builtin(_) => Ok(t),
    }
}

fn eval_app<'bump>(
    arena: &TermArena<'bump>,
    f: &'bump Term<'bump>,
    a: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    match f {
        Term::Lam(body) => {
            let body2 = replace_this(arena, f, body);
            let b = beta(arena, body2, a);
            eval(arena, b)
        }
        Term::App(prim, first) if is_prim_op(prim) => {
            let a_val = eval(arena, a)?;
            let first_val = eval(arena, first)?;
            eval_arith(arena, prim, first_val, a_val)
        }
        _ => {
            let f_val = eval(arena, f)?;
            if matches!(f_val, Term::Lam(_)) {
                let app = arena.app(f_val, a);
                eval(arena, app)
            } else {
                Ok(arena.app(f_val, a))
            }
        }
    }
}

/// Replace all `This` references in a term with the self-reference (the Lam itself).
fn replace_this<'bump>(
    arena: &TermArena<'bump>,
    self_term: &'bump Term<'bump>,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    match t {
        Term::This => self_term,
        Term::App(f, a) => {
            let f2 = replace_this(arena, self_term, f);
            let a2 = replace_this(arena, self_term, a);
            arena.app(f2, a2)
        }
        Term::Lam(b) => {
            let b2 = replace_this(arena, self_term, b);
            arena.lam(b2)
        }
        Term::Let(n, v, b, mc) => {
            let v2 = replace_this(arena, self_term, v);
            let b2 = replace_this(arena, self_term, b);
            let mc2 = mc.map(|c| replace_this(arena, self_term, c));
            arena.let_(n, v2, b2, mc2)
        }
        Term::IfThenElse(c, th, el) => {
            let c2 = replace_this(arena, self_term, c);
            let th2 = replace_this(arena, self_term, th);
            let el2 = replace_this(arena, self_term, el);
            arena.if_then_else(c2, th2, el2)
        }
        Term::Annot(inner, c) => {
            let inner2 = replace_this(arena, self_term, inner);
            let c2 = replace_this(arena, self_term, c);
            arena.annot(inner2, c2)
        }
        Term::ByProof(inner, p) => {
            let inner2 = replace_this(arena, self_term, inner);
            let p2 = replace_this(arena, self_term, p);
            arena.by_proof(inner2, p2)
        }
        Term::Refine(n, par, p) => {
            let par2 = replace_this(arena, self_term, par);
            let p2 = replace_this(arena, self_term, p);
            arena.refine(n, par2, p2)
        }
        Term::Pi(n, a, b) => {
            let a2 = replace_this(arena, self_term, a);
            let b2 = replace_this(arena, self_term, b);
            arena.pi(n, a2, b2)
        }
        Term::ProofBlock(inner) => {
            let inner2 = replace_this(arena, self_term, inner);
            arena.proof_block(inner2)
        }
        // Leaf nodes — return as-is
        _ => t,
    }
}

fn is_prim_op(t: &Term<'_>) -> bool {
    matches!(t, Term::PrimOp(_))
}

fn eval_if<'bump>(
    arena: &TermArena<'bump>,
    cond: &'bump Term<'bump>,
    tbranch: &'bump Term<'bump>,
    fbranch: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    let cond_val = eval(arena, cond)?;
    match cond_val {
        Term::LitBool(true) => eval(arena, tbranch),
        Term::LitBool(false) => eval(arena, fbranch),
        _ => Ok(arena.if_then_else(cond_val, tbranch, fbranch)),
    }
}

fn eval_arith<'bump>(
    arena: &TermArena<'bump>,
    prim: &Term<'_>,
    x: &Term<'_>,
    y: &Term<'_>,
) -> Result<&'bump Term<'bump>, String> {
    match (x, y) {
        (Term::LitInt(x), Term::LitInt(y)) => {
            let Term::PrimOp(op) = prim else {
                return Err("expected PrimOp".to_string());
            };
            let t = arith_result(*op, *x, *y);
            Ok(arena.alloc(t))
        }
        _ => Err("arithmetic on non-integer".to_string()),
    }
}

/// Compute the integer/bool result of a primitive operation.
fn arith_result(op: PrimOp, x: i64, y: i64) -> Term<'static> {
    match op {
        PrimOp::Add => Term::LitInt(x.wrapping_add(y)),
        PrimOp::Sub => Term::LitInt(x.wrapping_sub(y)),
        PrimOp::Mul => Term::LitInt(x.wrapping_mul(y)),
        PrimOp::Div => {
            if y == 0 {
                Term::LitInt(0)
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
