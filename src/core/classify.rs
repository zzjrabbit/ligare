use crate::core::syntax::{Term, Universe};

use crate::checker::builtin::classify_builtin;
use crate::checker::context::Context;

/// Classifies terms into universes (UData, UProp, UTheorem, UProof).
///
/// A standalone struct that operates on terms and contexts without
/// requiring its own mutable state — purely a decision-making object.
pub struct Classifier;

impl Classifier {
    /// Classify a term's universe.
    pub fn classify(ctx: &Context<'_>, t: &Term<'_>) -> Option<Universe> {
        match t {
            Term::LitInt(_) => Some(Universe::UData),
            Term::LitBool(_) => Some(Universe::UData),
            Term::Lam(_) => Some(Universe::UData),
            Term::App(f, _) => Self::classify(ctx, f),
            Term::PrimOp(_) => Some(Universe::UData),
            Term::Universe(u) => Some(*u),
            Term::AutoProof => Some(Universe::UProof),
            Term::RefParam => Some(Universe::UData),
            Term::This => Some(Universe::UData),
            Term::Func { .. } => Some(Universe::UData),
            Term::Var(i) => {
                let ty = ctx.lookup(*i)?;
                Self::classify(ctx, ty)
            }
            Term::Annot(t, _) => Self::classify(ctx, t),
            Term::ByProof(t, _) => Self::classify(ctx, t),
            Term::Let(_, _, body, _) => Self::classify(ctx, body),
            Term::IfThenElse(_, t, _) => Self::classify(ctx, t),
            Term::ProofBlock(t) => Self::classify(ctx, t),
            Term::Pi(_, _, _) => Some(Universe::UProp),
            Term::Refine(_, _, _) => Some(Universe::UProp),
            Term::Builtin(name) => classify_builtin(name),
        }
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn classify(ctx: &Context<'_>, t: &Term<'_>) -> Option<Universe> {
    Classifier::classify(ctx, t)
}
