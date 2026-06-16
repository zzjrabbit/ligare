// De Bruijn index manipulation is now encapsulated in
// `SubstitutionContext` (see `crate::core::pool`).

use crate::core::pool::{SubstitutionContext, TermArena};
use crate::core::syntax::Term;

/// Substitute: replace de Bruijn index `i` with `s` in term `t`.
pub fn subst<'bump>(
    arena: &'bump TermArena<'bump>,
    s: &'bump Term<'bump>,
    i: usize,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    SubstitutionContext::new(arena).subst(s, i, t)
}

/// Shift: add `d` to all de Bruijn indices >= `cutoff`.
pub fn shift<'bump>(
    arena: &'bump TermArena<'bump>,
    d: i32,
    cutoff: i32,
    t: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    SubstitutionContext::new(arena).shift(d, cutoff, t)
}

/// Beta-reduction: substitute arg into the body of a lambda.
pub fn beta<'bump>(
    arena: &'bump TermArena<'bump>,
    lam_body: &'bump Term<'bump>,
    arg: &'bump Term<'bump>,
) -> &'bump Term<'bump> {
    SubstitutionContext::new(arena).beta(lam_body, arg)
}
