use crate::core::syntax::Term;

/// Desugar `Func` nodes into lambda + Pi annotation.
pub fn desugar(t: &Term) -> Term {
    match t {
        Term::Func(_fname, params, m_ret, _preconds, _postconds, body) => {
            // Build lambda body: fold params into nested Lam
            let func_body = params
                .iter()
                .fold(body.as_ref().clone(), |b, _| Term::Lam(Box::new(b)));

            // Build Pi type annotation
            let default_constraint = Term::Builtin("data".to_string());
            let func_type = params.iter().rev().rfold(
                m_ret
                    .as_ref()
                    .map(|r| r.as_ref().clone())
                    .unwrap_or_else(|| default_constraint.clone()),
                |b, (pn, mc)| {
                    let constraint = mc
                        .as_ref()
                        .map(|c| c.as_ref().clone())
                        .unwrap_or_else(|| default_constraint.clone());
                    Term::Pi(pn.clone(), Box::new(constraint), Box::new(b))
                },
            );

            Term::Annot(Box::new(func_body), Box::new(func_type))
        }
        other => other.clone(),
    }
}
