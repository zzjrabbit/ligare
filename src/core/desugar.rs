use crate::core::pool::TermArena;
use crate::core::syntax::Term;

/// Desugars `Func` nodes into lambda + Pi annotation.
///
/// Encapsulates the arena dependency so callers don't need to thread
/// it through every call.
pub struct Desugarer<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> Desugarer<'bump> {
    /// Default constraint name used when no type annotation is given.
    const DATA: &'static str = "data";

    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Desugar a `Func` node. Non-Func terms are returned unchanged.
    pub fn desugar(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Func(_fname, params, m_ret, _preconds, _postconds, body) => {
                self.desugar_func(params, m_ret, body)
            }
            _ => t,
        }
    }

    fn desugar_func(
        &self,
        params: &'bump [(crate::core::syntax::Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: &Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        // Build lambda body: fold params into nested Lam
        let func_body = params.iter().fold(body, |b, _| self.arena.lam(b));

        // Build Pi type annotation
        let default_constraint = self.arena.builtin(self.arena.alloc_str(Self::DATA));
        let func_type =
            params
                .iter()
                .rev()
                .rfold(m_ret.unwrap_or(default_constraint), |b, (pn, mc)| {
                    let constraint = mc.unwrap_or(default_constraint);
                    self.arena.pi(pn, constraint, b)
                });

        self.arena.annot(func_body, func_type)
    }
}

/// Convenience wrapper for backward-compatible free-function style.
pub fn desugar<'bump>(arena: &'bump TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    Desugarer::new(arena).desugar(t)
}
