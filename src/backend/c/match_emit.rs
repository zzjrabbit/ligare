//! Match block emission for C code generation.
//!
//! `MatchEmitter` converts structured match plans into C `switch` blocks
//! with proper bind declarations.

use crate::backend::c::names::NameResolver;
use crate::backend::c::types::UnionInfo;
use crate::backend::c::value::{MatchBind, MatchPlan};
use std::collections::HashMap;

/// Emits match expressions as C `switch` blocks.
///
/// References the union map (via `&HashMap`) for field-name resolution
/// when emitting bind declarations.
pub struct MatchEmitter {
    names: NameResolver,
}

impl MatchEmitter {
    /// Create a new match emitter.
    pub fn new() -> Self {
        Self {
            names: NameResolver::new(),
        }
    }

    /// Emit a match as a standard C switch block (not GCC expression).
    /// Uses `union_map` to emit declarations for bound variables.
    pub fn emit(
        &self,
        plan: &MatchPlan,
        counter: u32,
        union_map: &HashMap<String, UnionInfo>,
    ) -> String {
        let scrut_ty = plan.scrut_type.c_name();
        let ret_name = plan.ret_type.c_name();
        let s_var = self.names.scrut_temp(counter);
        let r_var = self.names.result_temp(counter);
        let mut out = String::new();
        out.push_str(&format!(
            "    {scrut_ty} {s_var} = {};\n",
            plan.scrut_code.as_str()
        ));
        out.push_str(&format!("    {ret_name} {r_var};\n"));
        out.push_str(&format!("    switch ({s_var}.tag) {{\n"));
        for case in &plan.cases {
            let bind_decls =
                self.build_bind_decls(&scrut_ty, case.variant_idx, &s_var, &case.binds, union_map);
            out.push_str(&format!(
                "    case {}: {{ {bind_decls}{r_var} = {}; }} break;\n",
                case.variant_idx,
                case.body_code.as_str()
            ));
        }
        out.push_str(&format!(
            "    default: {r_var} = {}; break;\n",
            plan.ret_type.c_default_value()
        ));
        out.push_str("    }\n");
        out
    }

    /// Emit a match as a GCC-style statement expression.
    pub fn emit_expr(
        &self,
        plan: &MatchPlan,
        counter: u32,
        union_map: &HashMap<String, UnionInfo>,
    ) -> String {
        let block = self.emit(plan, counter, union_map);
        let r_var = self.names.result_temp(counter);
        format!("({{\n{block}    {r_var};\n}})")
    }

    /// Build bind declarations for a match case, looking up field names
    /// from the union info. Skips wildcard binds (named "_" or empty).
    fn build_bind_decls(
        &self,
        scrut_ty: &str,
        case_idx: usize,
        s_var: &str,
        binds: &[MatchBind],
        union_map: &HashMap<String, UnionInfo>,
    ) -> String {
        if binds.is_empty() {
            return String::new();
        }
        if let Some(info) = union_map.get(scrut_ty)
            && let Some(vi) = info.variants.get(case_idx)
        {
            return binds
                .iter()
                .enumerate()
                .filter(|(_, bind)| !bind.name.is_empty() && bind.name.as_str() != "_")
                .map(|(j, bind)| {
                    let field_name = vi
                        .fields
                        .get(j)
                        .map(|(fnm, _)| fnm.as_str())
                        .unwrap_or(bind.name.as_str());
                    format!(
                        "{} {} = {s_var}.data.{}.{field_name}; ",
                        bind.ctype.c_name(),
                        bind.name,
                        vi.name
                    )
                })
                .collect::<Vec<_>>()
                .join("");
        }
        String::new()
    }
}

impl Default for MatchEmitter {
    fn default() -> Self {
        Self::new()
    }
}
