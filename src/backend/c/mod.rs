//! C code generation backend — fully OOP design.
//!
//! Architecture:
//! ```text
//! CodeGenerator (trait)
//!   └── CEmitter (orchestrator)
//!         ├── TypeAnalyzer   — type maps, typedef emission, TypeMapper impl
//!         ├── NameResolver   — escaping, collection, lambda analysis
//!         ├── ExpressionEmitter — Term → C expression translation
//!         ├── MatchEmitter   — match → switch translation
//!         └── EmitCtx        — mutable per-expression state
//! ```
//!
//! Usage:
//! ```ignore
//! use ligare::backend::c::{CEmitter, CodeGenerator};
//! let emitter = CEmitter::new(struct_types, union_types, fun_sigs)?;
//! let c_source = emitter.generate(tops, raw_defs, struct_types, union_types)?;
//! ```

pub mod context;
pub mod emitter;
pub mod expr;
pub mod match_emit;
pub mod names;
pub mod types;

#[cfg(test)]
mod tests;

// ── Re-exports for convenience ──

pub use context::EmitCtx;
pub use emitter::{CEmitter, CodeGenerator};
pub use expr::ExpressionEmitter;
pub use match_emit::MatchEmitter;
pub use names::NameResolver;
pub use types::{StructInfo, TypeAnalyzer, TypeMapper, UnionInfo, VariantInfo};

use crate::backend::ir::FunSig;
use crate::core::syntax::Term;
use crate::front::parser::TopLevel;

/// Convenience wrapper: produce a complete C source file.
///
/// Maintains backward compatibility with the old free-function API.
/// For new code, prefer constructing a `CEmitter` directly.
pub fn emit_c(
    tops: &[TopLevel<'_>],
    raw_defs: &[TopLevel<'_>],
    fun_sigs: &[(&str, FunSig)],
    union_types: &[(&str, &Term<'_>)],
    struct_types: &[(&str, &Term<'_>)],
) -> Result<String, String> {
    let emitter = CEmitter::new(struct_types, union_types, fun_sigs)?;
    emitter.generate(tops, raw_defs, struct_types, union_types)
}
