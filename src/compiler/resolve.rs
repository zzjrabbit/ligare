//! Name resolution and substitution passes.
//!
//! Functions that walk the AST to resolve `Builtin`/`Named` references
//! to their definitions, convert variant/struct constructor applications,
//! and perform top-level substitution.

use crate::core::syntax::{Name, Term};
use crate::diagnostic::Diagnostic;

/// Result of collecting variant constructor args: (union_name, variant_index, field_specs, args).
pub type VariantWithArgs<'bump> = (
    Name<'bump>,
    usize,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);

/// Result of collecting struct constructor args: (struct_name, field_specs, args).
pub type StructWithArgs<'bump> = (
    Name<'bump>,
    &'bump [(Name<'bump>, &'bump Term<'bump>)],
    Vec<&'bump Term<'bump>>,
);

use super::Compiler;

impl<'bump> Compiler<'bump> {
    /// Resolve ALL free `Builtin(name)`/`Named(name)` references from the env
    /// (constants AND functions). Used for eval paths where function bodies
    /// need to be available.
    ///
    /// Local binders must become de Bruijn indices before global substitution,
    /// otherwise a global definition named `x` could capture `fun x => ...`.
    pub fn resolve_all(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.try_resolve_all(term)
            .expect("resolve_all failed; use try_resolve_all for parser terms")
    }

    pub fn try_resolve_all(
        &self,
        term: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, Diagnostic> {
        let term = self.checker.desugar_with_context(term)?;
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t
                && let Some(def) = self.env.get(name)
            {
                return Some(def);
            }
            None
        });
        // Also resolve variant apps, struct constructors, and zero-arg constructors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                // Zero-arg struct constructor
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
                // Struct projector
                if let Some(_idx) = self.checker.lookup_struct_proj(name) {
                    // Can't resolve without subject — leave as-is
                }
            }
            None
        });
        Ok(t)
    }

    /// Extract the function name from a term if it's a recursive call.
    /// Only returns `Some(name)` if the head is a `Builtin(name)` that
    /// maps to a function (i.e., has `Lam` body) in the env.
    pub fn extract_func_name(&self, term: &'bump Term<'bump>) -> Option<Name<'bump>> {
        let mut head = term;
        while let Term::App(f, _) = head {
            head = f;
        }
        if let Term::Builtin(name) | Term::Global(name) = head
            && let Some(def) = self.env.get(name)
        {
            if def.is_constant() {
                return None; // constants don't need self-reference
            }
            return Some(name);
        }
        None
    }

    /// Substitute known top-level definitions into a term (O(1) lookup).
    /// Also resolves variant/struct constructors to their term forms.
    /// Uses `is_constant()` to distinguish constants from functions.
    pub fn subst_top_level(&self, term: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // First pass: resolve env lookups for constants only
        let t = self.arena.map(term, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t
                && let Some(def) = self.env.get(name)
                && def.is_constant()
            {
                return Some(def);
            }
            None
        });
        // Second pass: resolve variant apps, struct constructors, and projectors
        let t = self.resolve_variant_apps(t);
        let t = self.resolve_struct_ctors(t);
        let t = self.resolve_struct_projs(t);
        // Third pass: resolve remaining zero-arg variant/struct constructors
        self.arena.map(t, &|t| {
            if let Term::Builtin(name) | Term::Global(name) = t {
                if let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
                    && field_specs.is_empty()
                {
                    return Some(self.arena.variant(uname, idx, &[]));
                }
                if let Some((sname, fields)) = self.checker.lookup_struct_ctor(name)
                    && fields.is_empty()
                {
                    return Some(self.arena.struct_cons(sname, &[]));
                }
            }
            None
        })
    }

    /// Convert `App*(Builtin(name), args...)` to `Variant(union, idx, args)`.
    pub fn resolve_variant_apps(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        // Try top-level first
        if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(t)
            && args.len() == field_specs.len()
        {
            let v = self
                .arena
                .variant(uname, idx, self.arena.alloc_slice(&args));
            // Recurse into payload to resolve nested constructors
            return self.resolve_variant_apps(v);
        }
        self.arena.map(t, &|node| {
            if let Some((uname, idx, field_specs, args)) = self.collect_variant_args(node)
                && args.len() == field_specs.len()
            {
                let v = self
                    .arena
                    .variant(uname, idx, self.arena.alloc_slice(&args));
                return Some(self.resolve_variant_apps(v));
            }
            None
        })
    }

    /// Unwrap an App chain to find a variant constructor and collect its args.
    pub fn collect_variant_args(&self, t: &'bump Term<'bump>) -> Option<VariantWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((uname, idx, field_specs)) = self.checker.lookup_variant(name)
        {
            return Some((uname, idx, field_specs, args));
        }
        None
    }

    /// Convert `App*(Named("name.mk"), args...)` to `StructCons(name, args)`.
    pub fn resolve_struct_ctors(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        if let Some((sname, field_specs, args)) = self.collect_struct_args(t)
            && args.len() == field_specs.len()
        {
            let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
            return self.resolve_struct_ctors(sc);
        }
        self.arena.map(t, &|node| {
            if let Some((sname, field_specs, args)) = self.collect_struct_args(node)
                && args.len() == field_specs.len()
            {
                let sc = self.arena.struct_cons(sname, self.arena.alloc_slice(&args));
                return Some(self.resolve_struct_ctors(sc));
            }
            None
        })
    }

    /// Unwrap an App chain to find a struct constructor (Name.mk) and collect its args.
    pub fn collect_struct_args(&self, t: &'bump Term<'bump>) -> Option<StructWithArgs<'bump>> {
        let mut args: Vec<&'bump Term<'bump>> = Vec::new();
        let mut current = t;
        while let Term::App(f, a) = current {
            args.push(*a);
            current = f;
        }
        args.reverse();
        if let Term::Builtin(name) | Term::Global(name) = current
            && let Some((sname, field_specs)) = self.checker.lookup_struct_ctor(name)
        {
            return Some((sname, field_specs, args));
        }
        None
    }

    /// Convert `App(Builtin("Name.field"), arg)` to `StructProj(arg, idx)`.
    pub fn resolve_struct_projs(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        self.arena.map(t, &|node| {
            if let Term::App(f, arg) = node
                && let Term::Builtin(name) | Term::Global(name) = f
                && let Some(idx) = self.checker.lookup_struct_proj(name)
            {
                let arg = self.resolve_struct_ctors(self.resolve_struct_projs(arg));
                return Some(self.arena.struct_proj(arg, idx));
            }
            None
        })
    }
}
