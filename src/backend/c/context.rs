//! Mutable emission context for C code generation.
//!
//! `EmitCtx` tracks the De Bruijn environment (bound variable names and
//! their C types) during a single expression walk.  Methods encapsulate
//! the push/pop protocol.

use crate::backend::ir::CType;

/// Mutable emission state threaded through a single expression walk.
///
/// Follows the OOP principle of bundling state with its mutators.
#[derive(Debug, Clone)]
pub struct EmitCtx {
    /// De Bruijn index → C variable name (index 0 = most recently bound).
    bound: Vec<String>,
    /// De Bruijn index → C type (same ordering as `bound`).
    var_types: Vec<CType>,
    /// `Some(name)` when inside a recursive function body.
    pub self_name: Option<String>,
}

impl EmitCtx {
    /// Create a new empty emission context.
    pub fn new() -> Self {
        Self {
            bound: Vec::new(),
            var_types: Vec::new(),
            self_name: None,
        }
    }

    /// Create a context from a parameter list (reversed De Bruijn order).
    pub fn from_params(params: &[String], param_types: &[CType]) -> Self {
        Self {
            bound: params.iter().rev().map(|s| s.to_string()).collect(),
            var_types: param_types.iter().rev().cloned().collect(),
            self_name: None,
        }
    }

    /// Push a new binding onto the context.
    pub fn push_binding(&mut self, name: String, ty: CType) {
        self.bound.insert(0, name);
        self.var_types.insert(0, ty);
    }

    /// Pop the most recent binding.
    pub fn pop_binding(&mut self) {
        self.bound.remove(0);
        self.var_types.remove(0);
    }

    /// Look up the C type of a De Bruijn variable by index.
    pub fn type_of(&self, index: usize) -> CType {
        self.var_types.get(index).cloned().unwrap_or(CType::Int64)
    }

    /// Look up the C variable name by De Bruijn index.
    pub fn name_of(&self, index: usize) -> &str {
        &self.bound[index]
    }

    /// Get a snapshot of the current bindings (for branch contexts).
    pub fn snapshot(&self) -> Self {
        self.clone()
    }
}
