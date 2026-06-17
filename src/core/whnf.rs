//! Weak Head Normal Form (WHNF) evaluator.
//!
//! WHNF stops at constructors and does not evaluate under binders or
//! force evaluation of non-strict arguments.  This is the evaluator used
//! by the type checker — it normalizes types and constraints without
//! computing runtime values (e.g. recursive function calls).
//!
//! Key differences from the strong evaluator (`eval`):
//! - `This` is left untouched — recursive calls are NOT unrolled.
//! - PrimOp applications only reduce when both operands are already
//!   `LitInt` (no eager argument evaluation).
//! - Argument terms in `App(f, a)` are never forced when `f` is not a
//!   `Lam` or `PrimOp` application.

use crate::core::pool::{SubstitutionContext, TermArena};
use crate::core::syntax::{PrimOp, Term};

/// Weak Head Normal Form evaluator.
///
/// Encapsulates the arena and substitution context, providing a clean
/// interface for type-checking purposes where full normalisation is
/// neither needed nor desirable.
pub struct WhnfEvaluator<'bump> {
    arena: &'bump TermArena<'bump>,
    sub: SubstitutionContext<'bump>,
}

impl<'bump> WhnfEvaluator<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self {
            arena,
            sub: SubstitutionContext::new(arena),
        }
    }

    /// Access the underlying arena.
    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Access the substitution context.
    pub fn substitution(&self) -> &SubstitutionContext<'bump> {
        &self.sub
    }

    /// Evaluate a term to Weak Head Normal Form.
    ///
    /// May allocate intermediate terms in the arena; the result lives in the arena.
    pub fn whnf(&self, t: &'bump Term<'bump>) -> Result<&'bump Term<'bump>, String> {
        match t {
            Term::App(f, a) => self.whnf_app(f, a),
            Term::Lam(_) => Ok(t),
            Term::Let(_name, val, body, _mconstr) => {
                let b = self.sub.beta(body, val);
                self.whnf(b)
            }
            Term::IfThenElse(cond, tbranch, fbranch) => self.whnf_if(cond, tbranch, fbranch),
            Term::Annot(inner, _) => self.whnf(inner),
            Term::ByProof(inner, _) => self.whnf(inner),
            // Refinement / constraint: evaluate children so the type-level
            // structure is exposed (this is safe — parent is typically int,
            // predicate is a λ which is already WHNF).
            Term::Refine(name, parent, p) => {
                let parent_val = self.whnf(parent)?;
                let p_val = self.whnf(p)?;
                Ok(self.arena.refine(name, parent_val, p_val))
            }
            Term::Func { .. } => {
                let d = crate::core::desugar::Desugarer::new(self.arena).desugar(t);
                self.whnf(d)
            }
            Term::ProofBlock(inner) => self.whnf(inner),
            // Leaf values — already in WHNF
            Term::Pi(_, _, _)
            | Term::Var(_)
            | Term::LitInt(_)
            | Term::LitBool(_)
            | Term::PrimOp(_)
            | Term::Universe(_)
            | Term::Builtin(_)
            | Term::AutoProof
            | Term::RefParam
            | Term::This => Ok(t),
        }
    }

    // ── private helpers ──

    fn whnf_app(
        &self,
        f: &'bump Term<'bump>,
        a: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        match f {
            // Standard β-reduction for anonymous lambdas.
            // NOTE: we do NOT call replace_this — so recursive calls via
            // `This` are left as `App(This, …)` and stop here.
            Term::Lam(body) => {
                let b = self.sub.beta(body, a);
                self.whnf(b)
            }
            // PrimOp applications: only reduce when both operands have
            // already been forced to LitInt.  This avoids eager
            // computation of recursive calls like `fib(n-1) + fib(n-2)`.
            Term::App(prim, first) if self.is_prim_op(prim) => {
                let a_val = self.whnf(a)?;
                let first_val = self.whnf(first)?;
                match (first_val, a_val) {
                    (Term::LitInt(x), Term::LitInt(y)) => {
                        let Term::PrimOp(op) = *prim else {
                            unreachable!()
                        };
                        Ok(self.arena.alloc(Self::arith_result(*op, *x, *y)))
                    }
                    _ => {
                        // Arguments are not yet literals — stop here.
                        // Build an App with the WHNF-reduced children
                        // so the caller can inspect the structure.
                        let prim2 = self.arena.prim_op(if let Term::PrimOp(op) = *prim {
                            *op
                        } else {
                            unreachable!()
                        });
                        let f2 = self.arena.app(prim2, first_val);
                        Ok(self.arena.app(f2, a_val))
                    }
                }
            }
            _ => {
                let f_val = self.whnf(f)?;
                if matches!(f_val, Term::Lam(_)) {
                    let app = self.arena.app(f_val, a);
                    self.whnf(app)
                } else {
                    // f is not a λ — stop, return the application as-is.
                    Ok(self.arena.app(f_val, a))
                }
            }
        }
    }

    fn is_prim_op(&self, t: &Term<'_>) -> bool {
        matches!(t, Term::PrimOp(_))
    }

    fn whnf_if(
        &self,
        cond: &'bump Term<'bump>,
        tbranch: &'bump Term<'bump>,
        fbranch: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, String> {
        let cond_val = self.whnf(cond)?;
        match cond_val {
            Term::LitBool(true) => self.whnf(tbranch),
            Term::LitBool(false) => self.whnf(fbranch),
            _ => Ok(self.arena.if_then_else(cond_val, tbranch, fbranch)),
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
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn whnf<'bump>(
    arena: &'bump TermArena<'bump>,
    t: &'bump Term<'bump>,
) -> Result<&'bump Term<'bump>, String> {
    WhnfEvaluator::new(arena).whnf(t)
}
