//! Match block emission for C code generation.
//!
//! `MatchEmitter` converts match sentinels (encoded as `match__...` strings)
//! into standard C `switch` blocks with proper bind declarations.

use crate::backend::c::names::NameResolver;
use crate::backend::c::types::UnionInfo;
use crate::backend::ir::CType;
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
        code: &str,
        ret_ty: &CType,
        counter: u32,
        union_map: &HashMap<String, UnionInfo>,
    ) -> String {
        // Format: match__<scrut_type>__<scrut>__<ret_ty>__<idx>__<n>__<name>__<type>__...__<body>__...
        let parts: Vec<&str> = code.split("__").collect();
        if parts.len() < 5 {
            return "    return 0;\n".to_string();
        }
        let scrut_ty = parts[1];
        let scrut = parts[2];
        let ret_name = ret_ty.c_name();
        let s_var = self.names.scrut_temp(counter);
        let r_var = self.names.result_temp(counter);
        let mut out = String::new();
        out.push_str(&format!("    {scrut_ty} {s_var} = {scrut};\n"));
        out.push_str(&format!("    {ret_name} {r_var};\n"));
        out.push_str(&format!("    switch ({s_var}.tag) {{\n"));
        let mut i: usize = 4;
        while i + 1 < parts.len() {
            let case_idx: usize = parts[i].parse().unwrap_or(0);
            i += 1;
            let bind_count: usize = parts[i].parse().unwrap_or(0);
            i += 1;
            let mut bind_names: Vec<String> = Vec::new();
            let mut bind_types: Vec<String> = Vec::new();
            for _ in 0..bind_count {
                if i < parts.len() {
                    bind_names.push(parts[i].to_string());
                    i += 1;
                }
                if i < parts.len() {
                    bind_types.push(parts[i].to_string());
                    i += 1;
                }
            }
            let bind_decls = self.build_bind_decls(
                scrut_ty,
                case_idx,
                &s_var,
                &bind_names,
                &bind_types,
                union_map,
            );
            let case_code = if i < parts.len() {
                parts[i].replace('\x1e', ", ")
            } else {
                String::from("0")
            };
            i += 1;
            out.push_str(&format!(
                "    case {}: {{ {bind_decls}{r_var} = {}; }} break;\n",
                case_idx, case_code
            ));
        }
        out.push_str(&format!("    default: {r_var} = 0; break;\n"));
        out.push_str("    }\n");
        out
    }

    /// Build bind declarations for a match case, looking up field names
    /// from the union info. Skips wildcard binds (named "_" or empty).
    fn build_bind_decls(
        &self,
        scrut_ty: &str,
        case_idx: usize,
        s_var: &str,
        bind_names: &[String],
        bind_types: &[String],
        union_map: &HashMap<String, UnionInfo>,
    ) -> String {
        if bind_names.is_empty() {
            return String::new();
        }
        if let Some(info) = union_map.get(scrut_ty) {
            if let Some(vi) = info.variants.get(case_idx) {
                return bind_names
                    .iter()
                    .zip(bind_types.iter())
                    .enumerate()
                    .filter(|(_, (bname, _))| !bname.is_empty() && bname.as_str() != "_")
                    .map(|(j, (bname, bty))| {
                        let escaped_name = self.names.escape(bname);
                        let field_name = vi
                            .fields
                            .get(j)
                            .map(|(fnm, _)| fnm.as_str())
                            .unwrap_or(bname.as_str());
                        format!(
                            "{bty} {escaped_name} = {s_var}.data.{}.{field_name}; ",
                            vi.name
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("");
            }
        }
        String::new()
    }
}

impl Default for MatchEmitter {
    fn default() -> Self {
        Self::new()
    }
}
