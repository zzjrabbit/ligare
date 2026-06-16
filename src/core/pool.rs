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

    /// Access the underlying bump allocator.
    #[inline]
    pub fn bump(&self) -> &'bump Bump {
        self.bump
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

// ── SubstitutionContext: encapsulates debruijn operations ──

/// Encapsulates de Bruijn index substitution and shifting operations.
///
/// These operations traverse the term tree and allocate new nodes in the
/// arena as needed.  By bundling the arena reference, callers avoid
/// passing it as a separate argument to every function.
pub struct SubstitutionContext<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> SubstitutionContext<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }

    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    /// Substitute: replace de Bruijn index `i` with `s` in term `t`.
    pub fn subst(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        self.subst_cutoff(s, i, 0, t)
    }

    fn subst_cutoff(
        &self,
        s: &'bump Term<'bump>,
        i: usize,
        cutoff: usize,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::Var(j) => {
                if *j == i + cutoff {
                    self.shift(cutoff as i32, 0, s)
                } else {
                    t
                }
            }
            Term::Lam(body) => {
                let b = self.subst_cutoff(s, i, cutoff + 1, body);
                self.arena.lam(b)
            }
            Term::App(f, a) => {
                let f2 = self.subst_cutoff(s, i, cutoff, f);
                let a2 = self.subst_cutoff(s, i, cutoff, a);
                self.arena.app(f2, a2)
            }
            Term::Pi(n, a, b) => {
                let a2 = self.subst_cutoff(s, i, cutoff, a);
                let b2 = self.subst_cutoff(s, i, cutoff + 1, b);
                self.arena.pi(n, a2, b2)
            }
            Term::Let(n, v, b, mc) => {
                let v2 = self.subst_cutoff(s, i, cutoff, v);
                let b2 = self.subst_cutoff(s, i, cutoff + 1, b);
                let mc2 = mc.map(|c| self.subst_cutoff(s, i, cutoff, c));
                self.arena.let_(n, v2, b2, mc2)
            }
            Term::IfThenElse(c, th, el) => {
                let c2 = self.subst_cutoff(s, i, cutoff, c);
                let th2 = self.subst_cutoff(s, i, cutoff, th);
                let el2 = self.subst_cutoff(s, i, cutoff, el);
                self.arena.if_then_else(c2, th2, el2)
            }
            Term::Annot(inner, ct) => {
                let inner2 = self.subst_cutoff(s, i, cutoff, inner);
                let ct2 = self.subst_cutoff(s, i, cutoff, ct);
                self.arena.annot(inner2, ct2)
            }
            Term::ByProof(inner, p) => {
                let inner2 = self.subst_cutoff(s, i, cutoff, inner);
                let p2 = self.subst_cutoff(s, i, cutoff, p);
                self.arena.by_proof(inner2, p2)
            }
            Term::Refine(n, par, p) => {
                let par2 = self.subst_cutoff(s, i, cutoff, par);
                let p2 = self.subst_cutoff(s, i, cutoff, p);
                self.arena.refine(n, par2, p2)
            }
            Term::Func(fname, params, m_ret, pre, post, body) => {
                let params2 = params
                    .iter()
                    .map(|(nm, mc)| {
                        let mc2 = mc.map(|c| self.subst_cutoff(s, i, cutoff, c));
                        (*nm, mc2)
                    })
                    .collect::<Vec<_>>();
                let params_slice = self.arena.alloc_slice(&params2);
                let m_ret2 = m_ret.map(|c| self.subst_cutoff(s, i, cutoff, c));
                let pre2: Vec<_> = pre
                    .iter()
                    .map(|t| *self.subst_cutoff(s, i, cutoff, t))
                    .collect();
                let pre_slice = self.arena.alloc_slice(&pre2);
                let post2: Vec<_> = post
                    .iter()
                    .map(|t| *self.subst_cutoff(s, i, cutoff, t))
                    .collect();
                let post_slice = self.arena.alloc_slice(&post2);
                let body2 = self.subst_cutoff(s, i, cutoff + params.len(), body);
                self.arena
                    .func(fname, params_slice, m_ret2, pre_slice, post_slice, body2)
            }
            Term::ProofBlock(inner) => {
                let inner2 = self.subst_cutoff(s, i, cutoff, inner);
                self.arena.proof_block(inner2)
            }
            // Leaf nodes: return as-is
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
    pub fn shift(&self, d: i32, cutoff: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        match t {
            Term::Var(i) => {
                if (*i as i32) >= cutoff {
                    self.arena.var((*i as i32 + d) as usize)
                } else {
                    t
                }
            }
            Term::Lam(body) => {
                let b = self.shift(d, cutoff + 1, body);
                self.arena.lam(b)
            }
            Term::App(f, a) => {
                let f2 = self.shift(d, cutoff, f);
                let a2 = self.shift(d, cutoff, a);
                self.arena.app(f2, a2)
            }
            Term::Pi(n, a, b) => {
                let a2 = self.shift(d, cutoff, a);
                let b2 = self.shift(d, cutoff + 1, b);
                self.arena.pi(n, a2, b2)
            }
            Term::Let(n, v, b, mc) => {
                let v2 = self.shift(d, cutoff, v);
                let b2 = self.shift(d, cutoff + 1, b);
                let mc2 = mc.map(|c| self.shift(d, cutoff, c));
                self.arena.let_(n, v2, b2, mc2)
            }
            Term::IfThenElse(c, th, el) => {
                let c2 = self.shift(d, cutoff, c);
                let th2 = self.shift(d, cutoff, th);
                let el2 = self.shift(d, cutoff, el);
                self.arena.if_then_else(c2, th2, el2)
            }
            Term::Annot(inner, ct) => {
                let inner2 = self.shift(d, cutoff, inner);
                let ct2 = self.shift(d, cutoff, ct);
                self.arena.annot(inner2, ct2)
            }
            Term::ByProof(inner, p) => {
                let inner2 = self.shift(d, cutoff, inner);
                let p2 = self.shift(d, cutoff, p);
                self.arena.by_proof(inner2, p2)
            }
            Term::Refine(n, par, p) => {
                let par2 = self.shift(d, cutoff, par);
                let p2 = self.shift(d, cutoff, p);
                self.arena.refine(n, par2, p2)
            }
            Term::Func(fname, params, m_ret, pre, post, body) => {
                let params2 = params
                    .iter()
                    .map(|(nm, mc)| {
                        let mc2 = mc.map(|c| self.shift(d, cutoff, c));
                        (*nm, mc2)
                    })
                    .collect::<Vec<_>>();
                let params_slice = self.arena.alloc_slice(&params2);
                let m_ret2 = m_ret.map(|c| self.shift(d, cutoff, c));
                let pre2: Vec<_> = pre.iter().map(|t| *self.shift(d, cutoff, t)).collect();
                let pre_slice = self.arena.alloc_slice(&pre2);
                let post2: Vec<_> = post.iter().map(|t| *self.shift(d, cutoff, t)).collect();
                let post_slice = self.arena.alloc_slice(&post2);
                let body2 = self.shift(d, cutoff + params.len() as i32, body);
                self.arena
                    .func(fname, params_slice, m_ret2, pre_slice, post_slice, body2)
            }
            Term::ProofBlock(inner) => {
                let inner2 = self.shift(d, cutoff, inner);
                self.arena.proof_block(inner2)
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
    pub fn beta(
        &self,
        lam_body: &'bump Term<'bump>,
        arg: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let shifted_arg = self.shift(1, 0, arg);
        let substituted = self.subst(shifted_arg, 0, lam_body);
        self.shift(-1, 0, substituted)
    }

    /// Shift that preserves `RefParam` (leaves it untouched).
    pub fn shift_preserve_refparam(&self, d: i32, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.shift_refparam_cutoff(d, 0, t)
    }

    fn shift_refparam_cutoff(
        &self,
        d: i32,
        cutoff: i32,
        t: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        match t {
            Term::RefParam => t,
            Term::Var(i) => {
                if (*i as i32) >= cutoff {
                    self.arena.var((*i as i32 + d) as usize)
                } else {
                    t
                }
            }
            _ => self.shift(d, cutoff, t),
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
