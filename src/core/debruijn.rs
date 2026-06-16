use crate::core::syntax::Term;

/// Substitution: replace de Bruijn index `i` with `s` in term `t`.
pub fn subst(s: &Term, i: usize, t: &Term) -> Term {
    subst_cutoff(s, i, 0, t)
}

fn subst_cutoff(s: &Term, i: usize, cutoff: usize, t: &Term) -> Term {
    match t {
        Term::Var(j) => {
            if *j == i + cutoff {
                shift(cutoff as i32, 0, s)
            } else {
                Term::Var(*j)
            }
        }
        Term::Lam(body) => Term::Lam(Box::new(subst_cutoff(s, i, cutoff + 1, body))),
        Term::App(f, a) => Term::App(
            Box::new(subst_cutoff(s, i, cutoff, f)),
            Box::new(subst_cutoff(s, i, cutoff, a)),
        ),
        Term::Pi(n, a, b) => Term::Pi(
            n.clone(),
            Box::new(subst_cutoff(s, i, cutoff, a)),
            Box::new(subst_cutoff(s, i, cutoff + 1, b)),
        ),
        Term::Let(n, v, b, mc) => Term::Let(
            n.clone(),
            Box::new(subst_cutoff(s, i, cutoff, v)),
            Box::new(subst_cutoff(s, i, cutoff + 1, b)),
            mc.as_ref().map(|c| Box::new(subst_cutoff(s, i, cutoff, c))),
        ),
        Term::IfThenElse(c, th, el) => Term::IfThenElse(
            Box::new(subst_cutoff(s, i, cutoff, c)),
            Box::new(subst_cutoff(s, i, cutoff, th)),
            Box::new(subst_cutoff(s, i, cutoff, el)),
        ),
        Term::Annot(t, ct) => Term::Annot(
            Box::new(subst_cutoff(s, i, cutoff, t)),
            Box::new(subst_cutoff(s, i, cutoff, ct)),
        ),
        Term::ByProof(t, p) => Term::ByProof(
            Box::new(subst_cutoff(s, i, cutoff, t)),
            Box::new(subst_cutoff(s, i, cutoff, p)),
        ),
        Term::Refine(n, par, p) => Term::Refine(
            n.clone(),
            Box::new(subst_cutoff(s, i, cutoff, par)),
            Box::new(subst_cutoff(s, i, cutoff, p)),
        ),
        Term::This => Term::This,
        Term::Func(fname, params, m_ret, pre, post, body) => Term::Func(
            fname.clone(),
            params
                .iter()
                .map(|(nm, mc)| {
                    (
                        nm.clone(),
                        mc.as_ref().map(|c| Box::new(subst_cutoff(s, i, cutoff, c))),
                    )
                })
                .collect(),
            m_ret
                .as_ref()
                .map(|c| Box::new(subst_cutoff(s, i, cutoff, c))),
            pre.iter().map(|t| subst_cutoff(s, i, cutoff, t)).collect(),
            post.iter().map(|t| subst_cutoff(s, i, cutoff, t)).collect(),
            Box::new(subst_cutoff(s, i, cutoff + params.len(), body)),
        ),
        Term::ProofBlock(t) => Term::ProofBlock(Box::new(subst_cutoff(s, i, cutoff, t))),
        other => other.clone(),
    }
}

/// Shift: add `d` to all de Bruijn indices >= `cutoff`.
pub fn shift(d: i32, cutoff: i32, t: &Term) -> Term {
    match t {
        Term::Var(i) => {
            if (*i as i32) >= cutoff {
                Term::Var((*i as i32 + d) as usize)
            } else {
                Term::Var(*i)
            }
        }
        Term::Lam(body) => Term::Lam(Box::new(shift(d, cutoff + 1, body))),
        Term::App(f, a) => Term::App(Box::new(shift(d, cutoff, f)), Box::new(shift(d, cutoff, a))),
        Term::Pi(n, a, b) => Term::Pi(
            n.clone(),
            Box::new(shift(d, cutoff, a)),
            Box::new(shift(d, cutoff + 1, b)),
        ),
        Term::Let(n, v, b, mc) => Term::Let(
            n.clone(),
            Box::new(shift(d, cutoff, v)),
            Box::new(shift(d, cutoff + 1, b)),
            mc.as_ref().map(|c| Box::new(shift(d, cutoff, c))),
        ),
        Term::IfThenElse(c, th, el) => Term::IfThenElse(
            Box::new(shift(d, cutoff, c)),
            Box::new(shift(d, cutoff, th)),
            Box::new(shift(d, cutoff, el)),
        ),
        Term::Annot(t, ct) => Term::Annot(
            Box::new(shift(d, cutoff, t)),
            Box::new(shift(d, cutoff, ct)),
        ),
        Term::ByProof(t, p) => {
            Term::ByProof(Box::new(shift(d, cutoff, t)), Box::new(shift(d, cutoff, p)))
        }
        Term::Refine(n, par, p) => Term::Refine(
            n.clone(),
            Box::new(shift(d, cutoff, par)),
            Box::new(shift(d, cutoff, p)),
        ),
        Term::Func(fname, params, m_ret, pre, post, body) => Term::Func(
            fname.clone(),
            params
                .iter()
                .map(|(nm, mc)| {
                    (
                        nm.clone(),
                        mc.as_ref().map(|c| Box::new(shift(d, cutoff, c))),
                    )
                })
                .collect(),
            m_ret.as_ref().map(|c| Box::new(shift(d, cutoff, c))),
            pre.iter().map(|t| shift(d, cutoff, t)).collect(),
            post.iter().map(|t| shift(d, cutoff, t)).collect(),
            Box::new(shift(d, cutoff + params.len() as i32, body)),
        ),
        Term::ProofBlock(t) => Term::ProofBlock(Box::new(shift(d, cutoff, t))),
        other => other.clone(),
    }
}

/// Beta-reduction: substitute arg into the body of a lambda.
pub fn beta(lam_body: &Term, arg: &Term) -> Term {
    let shifted_arg = shift(1, 0, arg);
    let substituted = subst(&shifted_arg, 0, lam_body);
    shift(-1, 0, &substituted)
}
