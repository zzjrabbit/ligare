use bumpalo::Bump;
use std::cell::RefCell;

use crate::core::syntax::{PrimOp, Term, Universe};

/// A bumpalo-backed string interner.
///
/// Uses a bump arena to allocate strings, ensuring that identical strings
/// share the same allocation without using a hash set (they're just
/// allocated once per compilation unit by the parser).
///
/// Threaded through `CompState` so the checker and evaluator can
/// use arena-allocated strings to reduce heap fragmentation.
pub struct StringPool<'bump> {
    bump: &'bump Bump,
    // Intern table: maps owned strings to their arena-allocated equivalents
    intern: RefCell<Vec<(&'bump str, &'bump str)>>,
}

impl<'bump> StringPool<'bump> {
    pub fn new(bump: &'bump Bump) -> Self {
        Self {
            bump,
            intern: RefCell::new(Vec::new()),
        }
    }

    /// Allocate a `&str` in the bump arena.
    #[inline]
    pub fn alloc_str(&self, s: &str) -> &'bump str {
        self.bump.alloc_str(s)
    }

    /// Intern a string: return a bump-allocated `&str`.
    /// Reuses an existing allocation if the same string was already interned.
    pub fn intern(&self, s: &str) -> &'bump str {
        let mut intern = self.intern.borrow_mut();
        if let Some(&(_, existing)) = intern.iter().find(|&&(_, v)| v == s) {
            return existing;
        }
        let allocated: &'bump str = self.bump.alloc_str(s);
        intern.push((allocated, allocated));
        allocated
    }

    /// Access the underlying bump allocator.
    #[inline]
    pub fn bump(&self) -> &'bump Bump {
        self.bump
    }
}

// ── Bumpalo-backed Term that mirrors syntax::Term but uses arena references ──

/// An arena-allocated variant of `Term` for use in temporary computations
/// during checking/evaluation. Converted to owned `Term` at boundaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BumpTerm<'bump> {
    Var(usize),
    App(&'bump BumpTerm<'bump>, &'bump BumpTerm<'bump>),
    Lam(&'bump BumpTerm<'bump>),
    LitInt(i64),
    LitBool(bool),
    PrimOp(PrimOp),
    Universe(Universe),
    Builtin(&'bump str),
    Pi(&'bump str, &'bump BumpTerm<'bump>, &'bump BumpTerm<'bump>),
    Let(
        &'bump str,
        &'bump BumpTerm<'bump>,
        &'bump BumpTerm<'bump>,
        Option<&'bump BumpTerm<'bump>>,
    ),
    IfThenElse(
        &'bump BumpTerm<'bump>,
        &'bump BumpTerm<'bump>,
        &'bump BumpTerm<'bump>,
    ),
    Refine(&'bump str, &'bump BumpTerm<'bump>, &'bump BumpTerm<'bump>),
    Annot(&'bump BumpTerm<'bump>, &'bump BumpTerm<'bump>),
    ByProof(&'bump BumpTerm<'bump>, &'bump BumpTerm<'bump>),
    AutoProof,
    RefParam,
    This,
    Func(
        &'bump str,
        &'bump [(&'bump str, Option<&'bump BumpTerm<'bump>>)],
        Option<&'bump BumpTerm<'bump>>,
        &'bump [BumpTerm<'bump>],
        &'bump [BumpTerm<'bump>],
        &'bump BumpTerm<'bump>,
    ),
    ProofBlock(&'bump BumpTerm<'bump>),
}

/// A bumpalo arena for constructing `BumpTerm` nodes efficiently.
///
/// During checking and evaluation, many intermediate terms are created.
/// This arena avoids individual heap allocations by allocating all
/// temporary nodes in a single bump region.
pub struct TermArena<'bump> {
    bump: &'bump Bump,
}

impl<'bump> TermArena<'bump> {
    pub fn new(bump: &'bump Bump) -> Self {
        Self { bump }
    }

    #[inline]
    fn alloc(&self, t: BumpTerm<'bump>) -> &'bump BumpTerm<'bump> {
        self.bump.alloc(t)
    }

    pub fn var(&self, i: usize) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::Var(i))
    }

    pub fn app(
        &self,
        f: &'bump BumpTerm<'bump>,
        a: &'bump BumpTerm<'bump>,
    ) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::App(f, a))
    }

    pub fn lam(&self, body: &'bump BumpTerm<'bump>) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::Lam(body))
    }

    pub fn lit_int(&self, n: i64) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::LitInt(n))
    }

    pub fn lit_bool(&self, b: bool) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::LitBool(b))
    }

    pub fn builtin(&self, name: &'bump str) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::Builtin(name))
    }

    pub fn annot(
        &self,
        t: &'bump BumpTerm<'bump>,
        c: &'bump BumpTerm<'bump>,
    ) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::Annot(t, c))
    }

    pub fn if_then_else(
        &self,
        cond: &'bump BumpTerm<'bump>,
        th: &'bump BumpTerm<'bump>,
        el: &'bump BumpTerm<'bump>,
    ) -> &'bump BumpTerm<'bump> {
        self.alloc(BumpTerm::IfThenElse(cond, th, el))
    }

    /// Convert a `BumpTerm` to an owned `Term` by recursively
    /// walking the arena-allocated graph.
    pub fn to_owned(&self, t: &BumpTerm<'bump>) -> Term {
        match t {
            BumpTerm::Var(i) => Term::Var(*i),
            BumpTerm::App(f, a) => {
                Term::App(Box::new(self.to_owned(f)), Box::new(self.to_owned(a)))
            }
            BumpTerm::Lam(b) => Term::Lam(Box::new(self.to_owned(b))),
            BumpTerm::LitInt(n) => Term::LitInt(*n),
            BumpTerm::LitBool(b) => Term::LitBool(*b),
            BumpTerm::PrimOp(op) => Term::PrimOp(*op),
            BumpTerm::Universe(u) => Term::Universe(*u),
            BumpTerm::Builtin(n) => Term::Builtin(n.to_string()),
            BumpTerm::Pi(n, a, b) => Term::Pi(
                n.to_string(),
                Box::new(self.to_owned(a)),
                Box::new(self.to_owned(b)),
            ),
            BumpTerm::Let(n, v, b, mc) => Term::Let(
                n.to_string(),
                Box::new(self.to_owned(v)),
                Box::new(self.to_owned(b)),
                mc.as_ref().map(|c| Box::new(self.to_owned(c))),
            ),
            BumpTerm::IfThenElse(c, th, el) => Term::IfThenElse(
                Box::new(self.to_owned(c)),
                Box::new(self.to_owned(th)),
                Box::new(self.to_owned(el)),
            ),
            BumpTerm::Refine(n, par, p) => Term::Refine(
                n.to_string(),
                Box::new(self.to_owned(par)),
                Box::new(self.to_owned(p)),
            ),
            BumpTerm::Annot(t, c) => {
                Term::Annot(Box::new(self.to_owned(t)), Box::new(self.to_owned(c)))
            }
            BumpTerm::ByProof(t, p) => {
                Term::ByProof(Box::new(self.to_owned(t)), Box::new(self.to_owned(p)))
            }
            BumpTerm::AutoProof => Term::AutoProof,
            BumpTerm::RefParam => Term::RefParam,
            BumpTerm::This => Term::This,
            BumpTerm::Func(name, params, m_ret, pre, post, body) => {
                let owned_params: Vec<(String, Option<Box<Term>>)> = params
                    .iter()
                    .map(|(n, mc)| {
                        (
                            n.to_string(),
                            mc.as_ref().map(|c| Box::new(self.to_owned(c))),
                        )
                    })
                    .collect();
                Term::Func(
                    name.to_string(),
                    owned_params,
                    m_ret.as_ref().map(|c| Box::new(self.to_owned(c))),
                    pre.iter().map(|t| self.to_owned(t)).collect(),
                    post.iter().map(|t| self.to_owned(t)).collect(),
                    Box::new(self.to_owned(body)),
                )
            }
            BumpTerm::ProofBlock(t) => Term::ProofBlock(Box::new(self.to_owned(t))),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_pool_basic() {
        let bump = Bump::new();
        let pool = StringPool::new(&bump);

        let a = pool.alloc_str("hello");
        let b = pool.alloc_str("hello");
        assert_eq!(a, b);
    }

    #[test]
    fn test_string_pool_intern() {
        let bump = Bump::new();
        let pool = StringPool::new(&bump);

        let a = pool.intern("world");
        let b = pool.intern("world");
        assert_eq!(a, b);
        // Should be the same pointer since it was interned
        assert_eq!(a.as_ptr(), b.as_ptr());
    }
}
