//! Minimal IR types for C code generation.
//!
//! `CType` maps term-level data to C declarations.
//! `FunSig` records the erased C types of function parameters and return
//! values, populated during erasure and consumed by the C backend.

/// Concrete C type — only the data-relevant ones.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CType {
    Int64,
    Str,
}

impl CType {
    pub fn c_name(self) -> &'static str {
        match self {
            CType::Int64 => "int64_t",
            CType::Str => "const char*",
        }
    }
}

/// Erased C signature of a named function.
///
/// Parameter constraints like `: int` / `: str` are stripped during
/// erasure, but we capture their C types here so the C backend can emit
/// correct parameter declarations.
#[derive(Debug, Clone)]
pub struct FunSig {
    pub param_types: Vec<CType>,
    pub ret_type: CType,
}

impl FunSig {
    /// Extract a function's C signature from its FuncDef representation,
    /// before erasure strips the constraint information.
    ///
    /// When the return type annotation is missing, the return C type is
    /// inferred structurally from the body (matching what `emit_fun` does).
    pub fn from_func(
        params: &[(
            crate::core::syntax::Name<'_>,
            Option<&crate::core::syntax::Term<'_>>,
        )],
        m_ret: Option<&crate::core::syntax::Term<'_>>,
        body: &crate::core::syntax::Term<'_>,
    ) -> Self {
        let param_types: Vec<CType> = params
            .iter()
            .map(|(_, mc)| mc.map_or(CType::Int64, constraint_to_ctype))
            .collect();
        let ret_type = match m_ret {
            Some(t) => constraint_to_ctype(t),
            None => infer_ret_ctype(body, &param_types),
        };
        FunSig {
            param_types,
            ret_type,
        }
    }
}

/// Infer the C return type from a term body, given the parameter C types
/// (in declaration order, i.e. left-to-right).  This mirrors the type
/// inference that `emit_fun` does during code generation.
fn infer_ret_ctype(body: &crate::core::syntax::Term<'_>, param_types: &[CType]) -> CType {
    match body {
        crate::core::syntax::Term::Var(i) => param_types.get(*i).copied().unwrap_or(CType::Int64),
        crate::core::syntax::Term::LitStr(_) => CType::Str,
        crate::core::syntax::Term::Lam(inner) => {
            // Lambda wrapping: the inner body determines the return type.
            // Push a dummy Int64 for the lambda parameter and recurse.
            let mut extended: Vec<CType> = vec![CType::Int64];
            extended.extend_from_slice(param_types);
            infer_ret_ctype(inner, &extended)
        }
        _ => CType::Int64,
    }
}

/// Map a constraint Term to its C type.  Only recognizes builtin type
/// names; everything else defaults to Int64 (the constraint checker
/// already validated correctness, so this is just a hint for codegen).
pub fn constraint_to_ctype(t: &crate::core::syntax::Term<'_>) -> CType {
    match t {
        crate::core::syntax::Term::Builtin(name) if *name == "str" => CType::Str,
        _ => CType::Int64,
    }
}
