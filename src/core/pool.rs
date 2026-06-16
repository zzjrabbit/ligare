use bumpalo::Bump;
use std::cell::RefCell;

use crate::core::syntax::{Name, PrimOp, Term, Universe};

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
    /// Intern table: caches previously allocated strings so identical
    /// strings share the same bump-allocated pointer.
    intern: RefCell<Vec<&'bump str>>,
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
        let intern = self.intern.borrow();
        if let Some(&existing) = intern.iter().find(|&&v| v == s) {
            return existing;
        }
        drop(intern);
        let allocated: &'bump str = self.bump.alloc_str(s);
        self.intern.borrow_mut().push(allocated);
        allocated
    }

    /// Access the underlying bump allocator.
    #[inline]
    pub fn bump(&self) -> &'bump Bump {
        self.bump
    }
}

// ── TermArena: fast bump-allocated Term construction ──

/// A bumpalo arena for constructing `Term` nodes efficiently.
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

    /// Allocate a `Term` directly into the arena.
    #[inline]
    pub fn alloc(&self, t: Term<'bump>) -> &'bump Term<'bump> {
        self.bump.alloc(t)
    }

    /// Allocate a `&str` into the arena.
    #[inline]
    pub fn alloc_str(&self, s: &str) -> &'bump str {
        self.bump.alloc_str(s)
    }

    /// Allocate a copy of a slice into the arena.
    #[inline]
    pub fn alloc_slice<T: Copy>(&self, data: &[T]) -> &'bump [T] {
        if data.is_empty() {
            return &[];
        }
        self.bump.alloc_slice_copy(data)
    }

    // ── leaf constructors ──

    pub fn var(&self, i: usize) -> &'bump Term<'bump> {
        self.alloc(Term::Var(i))
    }

    pub fn lit_int(&self, n: i64) -> &'bump Term<'bump> {
        self.alloc(Term::LitInt(n))
    }

    pub fn lit_bool(&self, b: bool) -> &'bump Term<'bump> {
        self.alloc(Term::LitBool(b))
    }

    pub fn prim_op(&self, op: PrimOp) -> &'bump Term<'bump> {
        self.alloc(Term::PrimOp(op))
    }

    pub fn universe(&self, u: Universe) -> &'bump Term<'bump> {
        self.alloc(Term::Universe(u))
    }

    pub fn builtin(&self, name: Name<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Builtin(name))
    }

    pub fn auto_proof(&self) -> &'bump Term<'bump> {
        self.alloc(Term::AutoProof)
    }

    pub fn ref_param(&self) -> &'bump Term<'bump> {
        self.alloc(Term::RefParam)
    }

    pub fn this_(&self) -> &'bump Term<'bump> {
        self.alloc(Term::This)
    }

    // ── recursive constructors ──

    pub fn app(&self, f: &'bump Term<'bump>, a: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::App(f, a))
    }

    pub fn lam(&self, body: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Lam(body))
    }

    pub fn pi(
        &self,
        name: Name<'bump>,
        a: &'bump Term<'bump>,
        b: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Pi(name, a, b))
    }

    pub fn let_(
        &self,
        name: Name<'bump>,
        val: &'bump Term<'bump>,
        body: &'bump Term<'bump>,
        mconstr: Option<&'bump Term<'bump>>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Let(name, val, body, mconstr))
    }

    pub fn if_then_else(
        &self,
        cond: &'bump Term<'bump>,
        th: &'bump Term<'bump>,
        el: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::IfThenElse(cond, th, el))
    }

    pub fn refine(
        &self,
        name: Name<'bump>,
        parent: &'bump Term<'bump>,
        pred: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Refine(name, parent, pred))
    }

    pub fn annot(&self, t: &'bump Term<'bump>, c: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::Annot(t, c))
    }

    pub fn by_proof(&self, t: &'bump Term<'bump>, p: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::ByProof(t, p))
    }

    pub fn func(
        &self,
        name: Name<'bump>,
        params: &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        pre: &'bump [Term<'bump>],
        post: &'bump [Term<'bump>],
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.alloc(Term::Func(name, params, m_ret, pre, post, body))
    }

    pub fn proof_block(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.alloc(Term::ProofBlock(t))
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
