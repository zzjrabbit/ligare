use crate::core::pool::TermArena;
use crate::core::syntax::Term;

/// Default constraint name used when no type annotation is given.
const DATA: &str = "data";

/// Desugar `Func` nodes into lambda + Pi annotation.
pub fn desugar<'bump>(arena: &TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    match t {
        Term::Func(_fname, params, m_ret, _preconds, _postconds, body) => {
            // Build lambda body: fold params into nested Lam
            let func_body = params.iter().fold(*body, |b, _| arena.lam(b));

            // Build Pi type annotation
            let default_constraint = arena.builtin(arena.alloc_str(DATA));
            let func_type =
                params
                    .iter()
                    .rev()
                    .rfold(m_ret.unwrap_or(default_constraint), |b, (pn, mc)| {
                        let constraint = mc.unwrap_or(default_constraint);
                        arena.pi(pn, constraint, b)
                    });

            arena.annot(func_body, func_type)
        }
        // Non-Func terms return as-is.
        _ => t,
    }
}
