use crate::core::pool::TermArena;
use crate::core::syntax::Term;

/// Substitution: replace de Bruijn index `i` with `s` in term `t`.
/// Allocates the result in the arena.
pub fn subst<'bump>(
    arena: &TermArena<'bump>,
    s: &'bump Term<'bump>,
    i: usize,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    subst_cutoff(arena, s, i, 0, t)
}

fn subst_cutoff<'bump>(
    arena: &TermArena<'bump>,
    s: &'bump Term<'bump>,
    i: usize,
    cutoff: usize,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    match t {
        Term::Var(j) => {
            if *j == i + cutoff {
                shift(arena, cutoff as i32, 0, s)
            } else {
                t
            }
        }
        Term::Lam(body) => {
            let b = subst_cutoff(arena, s, i, cutoff + 1, body);
            arena.lam(b)
        }
        Term::App(f, a) => {
            let f2 = subst_cutoff(arena, s, i, cutoff, f);
            let a2 = subst_cutoff(arena, s, i, cutoff, a);
            arena.app(f2, a2)
        }
        Term::Pi(n, a, b) => {
            let a2 = subst_cutoff(arena, s, i, cutoff, a);
            let b2 = subst_cutoff(arena, s, i, cutoff + 1, b);
            arena.pi(n, a2, b2)
        }
        Term::Let(n, v, b, mc) => {
            let v2 = subst_cutoff(arena, s, i, cutoff, v);
            let b2 = subst_cutoff(arena, s, i, cutoff + 1, b);
            let mc2 = mc.map(|c| subst_cutoff(arena, s, i, cutoff, c));
            arena.let_(n, v2, b2, mc2)
        }
        Term::IfThenElse(c, th, el) => {
            let c2 = subst_cutoff(arena, s, i, cutoff, c);
            let th2 = subst_cutoff(arena, s, i, cutoff, th);
            let el2 = subst_cutoff(arena, s, i, cutoff, el);
            arena.if_then_else(c2, th2, el2)
        }
        Term::Annot(inner, ct) => {
            let inner2 = subst_cutoff(arena, s, i, cutoff, inner);
            let ct2 = subst_cutoff(arena, s, i, cutoff, ct);
            arena.annot(inner2, ct2)
        }
        Term::ByProof(inner, p) => {
            let inner2 = subst_cutoff(arena, s, i, cutoff, inner);
            let p2 = subst_cutoff(arena, s, i, cutoff, p);
            arena.by_proof(inner2, p2)
        }
        Term::Refine(n, par, p) => {
            let par2 = subst_cutoff(arena, s, i, cutoff, par);
            let p2 = subst_cutoff(arena, s, i, cutoff, p);
            arena.refine(n, par2, p2)
        }
        Term::Func(fname, params, m_ret, pre, post, body) => {
            let params2 = params
                .iter()
                .map(|(nm, mc)| {
                    let mc2 = mc.map(|c| subst_cutoff(arena, s, i, cutoff, c));
                    (*nm, mc2)
                })
                .collect::<Vec<_>>();
            let params_slice = arena.alloc_slice(&params2);
            let m_ret2 = m_ret.map(|c| subst_cutoff(arena, s, i, cutoff, c));
            let pre2: Vec<_> = pre
                .iter()
                .map(|t| *subst_cutoff(arena, s, i, cutoff, t))
                .collect();
            let pre_slice = arena.alloc_slice(&pre2);
            let post2: Vec<_> = post
                .iter()
                .map(|t| *subst_cutoff(arena, s, i, cutoff, t))
                .collect();
            let post_slice = arena.alloc_slice(&post2);
            let body2 = subst_cutoff(arena, s, i, cutoff + params.len(), body);
            arena.func(fname, params_slice, m_ret2, pre_slice, post_slice, body2)
        }
        Term::ProofBlock(inner) => {
            let inner2 = subst_cutoff(arena, s, i, cutoff, inner);
            arena.proof_block(inner2)
        }
        // Leaf nodes: return as-is (reference equality is fine)
        Term::This
        | Term::RefParam
        | Term::AutoProof
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::Builtin(_) => t,
    }
}

/// Shift: add `d` to all de Bruijn indices >= `cutoff`.
/// Allocates the result in the arena.
pub fn shift<'bump>(
    arena: &TermArena<'bump>,
    d: i32,
    cutoff: i32,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    match t {
        Term::Var(i) => {
            if (*i as i32) >= cutoff {
                arena.var((*i as i32 + d) as usize)
            } else {
                t
            }
        }
        Term::Lam(body) => {
            let b = shift(arena, d, cutoff + 1, body);
            arena.lam(b)
        }
        Term::App(f, a) => {
            let f2 = shift(arena, d, cutoff, f);
            let a2 = shift(arena, d, cutoff, a);
            arena.app(f2, a2)
        }
        Term::Pi(n, a, b) => {
            let a2 = shift(arena, d, cutoff, a);
            let b2 = shift(arena, d, cutoff + 1, b);
            arena.pi(n, a2, b2)
        }
        Term::Let(n, v, b, mc) => {
            let v2 = shift(arena, d, cutoff, v);
            let b2 = shift(arena, d, cutoff + 1, b);
            let mc2 = mc.map(|c| shift(arena, d, cutoff, c));
            arena.let_(n, v2, b2, mc2)
        }
        Term::IfThenElse(c, th, el) => {
            let c2 = shift(arena, d, cutoff, c);
            let th2 = shift(arena, d, cutoff, th);
            let el2 = shift(arena, d, cutoff, el);
            arena.if_then_else(c2, th2, el2)
        }
        Term::Annot(inner, ct) => {
            let inner2 = shift(arena, d, cutoff, inner);
            let ct2 = shift(arena, d, cutoff, ct);
            arena.annot(inner2, ct2)
        }
        Term::ByProof(inner, p) => {
            let inner2 = shift(arena, d, cutoff, inner);
            let p2 = shift(arena, d, cutoff, p);
            arena.by_proof(inner2, p2)
        }
        Term::Refine(n, par, p) => {
            let par2 = shift(arena, d, cutoff, par);
            let p2 = shift(arena, d, cutoff, p);
            arena.refine(n, par2, p2)
        }
        Term::Func(fname, params, m_ret, pre, post, body) => {
            let params2 = params
                .iter()
                .map(|(nm, mc)| {
                    let mc2 = mc.map(|c| shift(arena, d, cutoff, c));
                    (*nm, mc2)
                })
                .collect::<Vec<_>>();
            let params_slice = arena.alloc_slice(&params2);
            let m_ret2 = m_ret.map(|c| shift(arena, d, cutoff, c));
            let pre2: Vec<_> = pre.iter().map(|t| *shift(arena, d, cutoff, t)).collect();
            let pre_slice = arena.alloc_slice(&pre2);
            let post2: Vec<_> = post.iter().map(|t| *shift(arena, d, cutoff, t)).collect();
            let post_slice = arena.alloc_slice(&post2);
            let body2 = shift(arena, d, cutoff + params.len() as i32, body);
            arena.func(fname, params_slice, m_ret2, pre_slice, post_slice, body2)
        }
        Term::ProofBlock(inner) => {
            let inner2 = shift(arena, d, cutoff, inner);
            arena.proof_block(inner2)
        }
        // Leaf nodes
        Term::RefParam
        | Term::This
        | Term::AutoProof
        | Term::LitInt(_)
        | Term::LitBool(_)
        | Term::PrimOp(_)
        | Term::Universe(_)
        | Term::Builtin(_) => t,
    }
}

/// Beta-reduction: substitute arg into the body of a lambda.
pub fn beta<'bump>(
    arena: &TermArena<'bump>,
    lam_body: &'bump Term<'bump>,
    arg: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    let shifted_arg = shift(arena, 1, 0, arg);
    let substituted = subst(arena, shifted_arg, 0, lam_body);
    shift(arena, -1, 0, substituted)
}
