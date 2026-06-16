use crate::core::syntax::{Term, Universe};

#[allow(dead_code)]
use crate::checker::builtin::classify_builtin;
use crate::checker::context::Context;

/// Classify a term's universe.
pub fn classify(ctx: &Context, t: &Term) -> Option<Universe> {
    match t {
        Term::LitInt(_) => Some(Universe::UData),
        Term::LitBool(_) => Some(Universe::UData),
        Term::Lam(_) => Some(Universe::UData),
        Term::App(f, _) => classify(ctx, f),
        Term::PrimOp(_) => Some(Universe::UData),
        Term::Universe(u) => Some(*u),
        Term::AutoProof => Some(Universe::UProof),
        Term::RefParam => Some(Universe::UData),
        Term::This => Some(Universe::UData),
        Term::Func { .. } => Some(Universe::UData),
        Term::Var(i) => {
            let ty = ctx.lookup(*i)?;
            classify(ctx, &ty)
        }
        Term::Annot(t, _) => classify(ctx, t),
        Term::ByProof(t, _) => classify(ctx, t),
        Term::Let(_, _, body, _) => classify(ctx, body),
        Term::IfThenElse(_, t, _) => classify(ctx, t),
        Term::ProofBlock(t) => classify(ctx, t),
        Term::Pi(_, _, _) => Some(Universe::UProp),
        Term::Refine(_, _, _) => Some(Universe::UProp),
        Term::Builtin(name) => classify_builtin(name),
    }
}
