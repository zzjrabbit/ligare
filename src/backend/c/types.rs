//! Type system for C code generation.
//!
//! Defines the `TypeMapper` trait for Ligare→C type resolution and the
//! `TypeAnalyzer` struct that builds type maps, analyzes dependencies,
//! and emits typedefs — all as methods on a single cohesive object.

use crate::backend::ir::CType;
use crate::core::syntax::{Name, Term};
use std::collections::{HashMap, HashSet};

// ── Type info structs ──

/// Info about a union variant for C codegen.
#[derive(Debug, Clone)]
pub struct VariantInfo {
    pub name: String,
    pub fields: Vec<(String, CType)>,
}

/// Union type info for C codegen.
#[derive(Debug, Clone)]
pub struct UnionInfo {
    pub variants: Vec<VariantInfo>,
}

/// Struct type info for C codegen.
#[derive(Debug, Clone)]
pub struct StructInfo {
    pub fields: Vec<(String, CType)>,
}

// ── TypeMapper trait ──

/// Maps Ligare type constraints to C types.
///
/// This trait abstracts the type resolution strategy, allowing different
/// backends or testing scenarios to plug in custom mappings.
pub trait TypeMapper {
    /// Map a constraint Term to its C type.
    fn constraint_to_ctype(&self, t: &Term<'_>) -> Result<CType, String>;

    /// Returns true if the constraint represents a type-level universe
    /// (data, prop, theorem, proof).
    fn is_type_universe(&self, t: &Term<'_>) -> bool;
}

// ── TypeAnalyzer ──

/// Analyzes and emits C type definitions.
///
/// Owns the type name sets and the built maps; all type-related operations
/// are methods on this struct (OOP encapsulation).
pub struct TypeAnalyzer {
    /// Set of union type names.
    pub union_names: HashSet<String>,
    /// Set of struct type names.
    pub struct_names: HashSet<String>,
    /// Union type info keyed by name.
    pub union_map: HashMap<String, UnionInfo>,
    /// Struct type info keyed by name.
    pub struct_map: HashMap<String, StructInfo>,
}

impl TypeAnalyzer {
    /// Build a type analyzer from raw type definitions.
    pub fn new(
        struct_types: &[(&str, &Term<'_>)],
        union_types: &[(&str, &Term<'_>)],
    ) -> Result<Self, String> {
        let union_names: HashSet<String> = union_types.iter().map(|(n, _)| n.to_string()).collect();
        let struct_names: HashSet<String> =
            struct_types.iter().map(|(n, _)| n.to_string()).collect();
        let union_map = Self::build_union_map(union_types, &union_names, &struct_names)?;
        let struct_map = Self::build_struct_map(struct_types, &union_names, &struct_names)?;
        Ok(Self {
            union_names,
            struct_names,
            union_map,
            struct_map,
        })
    }

    // ── Map builders (private) ──

    fn build_struct_map(
        struct_types: &[(&str, &Term<'_>)],
        union_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<HashMap<String, StructInfo>, String> {
        let mut map = HashMap::new();
        for (name, sdef) in struct_types {
            if let Term::StructDef(_, fields) = sdef {
                let fs: Vec<(String, CType)> = fields
                    .iter()
                    .map(|(fnm, fc)| {
                        Self::constraint_to_ctype_static(fc, union_names, struct_names)
                            .map(|ct| (fnm.to_string(), ct))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                map.insert(name.to_string(), StructInfo { fields: fs });
            }
        }
        Ok(map)
    }

    fn build_union_map(
        union_types: &[(&str, &Term<'_>)],
        union_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<HashMap<String, UnionInfo>, String> {
        let mut map = HashMap::new();
        for (name, udef) in union_types {
            if let Term::UnionDef(_, variants) = udef {
                let mut vis = Vec::new();
                for (vname, fields) in variants.iter() {
                    let fs: Vec<(String, CType)> = fields
                        .iter()
                        .map(|(fnm, fc)| {
                            Self::constraint_to_ctype_static(fc, union_names, struct_names)
                                .map(|ct| (fnm.to_string(), ct))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    vis.push(VariantInfo {
                        name: vname.to_string(),
                        fields: fs,
                    });
                }
                map.insert(name.to_string(), UnionInfo { variants: vis });
            }
        }
        Ok(map)
    }

    // ── Type dependency analysis ──

    /// Extract type dependencies from a type definition (struct or union).
    pub fn type_dependencies(&self, def: &Term<'_>) -> HashSet<String> {
        let mut deps = HashSet::new();
        let fields: Option<&[(Name<'_>, &Term<'_>)]> = match def {
            Term::StructDef(_, f) => Some(*f),
            Term::UnionDef(_, variants) => {
                let all: Vec<_> = variants
                    .iter()
                    .flat_map(|(_, fields)| fields.iter().map(|(n, t)| (*n, *t)))
                    .collect();
                if all.is_empty() {
                    return deps;
                }
                for (_name, fty) in &all {
                    self.collect_type_refs(fty, &mut deps);
                }
                return deps;
            }
            _ => return deps,
        };
        if let Some(fs) = fields {
            for (_name, fty) in fs {
                self.collect_type_refs(fty, &mut deps);
            }
        }
        deps
    }

    /// Recursively collect user-defined type names from a constraint term.
    fn collect_type_refs(&self, t: &Term<'_>, deps: &mut HashSet<String>) {
        match t {
            Term::Builtin(name) | Term::Named(name) => {
                let s = name.to_string();
                if self.union_names.contains(&s) || self.struct_names.contains(&s) {
                    deps.insert(s);
                }
            }
            Term::Pi(_, a, b) => {
                self.collect_type_refs(a, deps);
                self.collect_type_refs(b, deps);
            }
            Term::App(f, a) => {
                self.collect_type_refs(f, deps);
                self.collect_type_refs(a, deps);
            }
            _ => {}
        }
    }

    // ── Typedef emission ──

    /// Emit a C typedef for a union type (tagged union).
    pub fn emit_union_typedef(&self, name: &str, udef: &Term<'_>) -> Result<String, String> {
        let Term::UnionDef(_, variants) = udef else {
            return Ok(String::new());
        };
        let mut out = format!("// {name}\n");
        out.push_str(&format!("typedef struct {name} {{\n"));
        out.push_str("    int tag;\n");
        out.push_str("    union {\n");
        for (vname, fields) in variants.iter() {
            if fields.is_empty() {
                out.push_str(&format!("        struct {{ char _empty; }} {vname};\n"));
            } else {
                out.push_str("        struct { ");
                for (fname, fty) in fields.iter() {
                    let is_self_ref =
                        matches!(fty, Term::Builtin(tn) | Term::Named(tn) if *tn == name);
                    if is_self_ref {
                        out.push_str(&format!("struct {}* {}; ", name, fname));
                    } else {
                        let cty = self.constraint_to_ctype(fty)?;
                        out.push_str(&format!("{} {}; ", cty.c_name(), fname));
                    }
                }
                out.push_str(&format!("}} {vname};\n"));
            }
        }
        out.push_str("    } data;\n");
        out.push_str(&format!("}} {name};\n"));
        Ok(out)
    }

    /// Emit a C typedef for a struct type (product type with named fields).
    pub fn emit_struct_typedef(&self, name: &str, sdef: &Term<'_>) -> Result<String, String> {
        let Term::StructDef(_, fields) = sdef else {
            return Ok(String::new());
        };
        let mut out = format!("// struct {name}\n");
        out.push_str(&format!("typedef struct {name} {{\n"));
        for (fname, fty) in fields.iter() {
            let cty = self.constraint_to_ctype(fty)?;
            out.push_str(&format!("    {} {};\n", cty.c_name(), fname));
        }
        out.push_str(&format!("}} {name};\n"));
        Ok(out)
    }

    /// Emit a struct typedef using pointers for union-typed fields (for cyclic deps).
    pub fn emit_struct_typedef_ptr(&self, name: &str, sdef: &Term<'_>) -> Result<String, String> {
        let Term::StructDef(_, fields) = sdef else {
            return Ok(String::new());
        };
        let mut out = format!("// struct {name} (ptr cycle)\n");
        out.push_str(&format!("typedef struct {name} {{\n"));
        for (fname, fty) in fields.iter() {
            let cty = self.constraint_to_ctype(fty)?;
            if matches!(cty, CType::Union(_)) {
                out.push_str(&format!("    {}* {};\n", cty.c_name(), fname));
            } else {
                out.push_str(&format!("    {} {};\n", cty.c_name(), fname));
            }
        }
        out.push_str(&format!("}} {name};\n"));
        Ok(out)
    }

    /// Emit forward declarations and topological-sorted type definitions.
    pub fn emit_type_declarations(
        &self,
        out: &mut String,
        struct_types: &[(&str, &Term<'_>)],
        union_types: &[(&str, &Term<'_>)],
    ) -> Result<(), String> {
        // Forward declarations
        for (name, _) in struct_types {
            out.push_str(&format!("typedef struct {name} {name};\n"));
        }
        for (name, _) in union_types {
            out.push_str(&format!("typedef struct {name} {name};\n"));
        }
        out.push('\n');

        // Topological sort
        let mut emitted: HashSet<String> = HashSet::new();
        let mut remaining: Vec<(&str, &Term<'_>, bool)> = Vec::new();
        for (n, s) in struct_types {
            remaining.push((n, *s, true));
        }
        for (n, u) in union_types {
            remaining.push((n, *u, false));
        }

        let mut changed = true;
        while changed && !remaining.is_empty() {
            changed = false;
            let mut next: Vec<(&str, &Term<'_>, bool)> = Vec::new();
            for (name, def, is_struct) in remaining.drain(..) {
                let deps = self.type_dependencies(def);
                let all_deps_emitted = deps.iter().all(|d| emitted.contains(d.as_str()));
                if all_deps_emitted || deps.is_empty() {
                    if is_struct {
                        out.push_str(&self.emit_struct_typedef(name, def)?);
                    } else {
                        out.push_str(&self.emit_union_typedef(name, def)?);
                    }
                    out.push('\n');
                    emitted.insert(name.to_string());
                    changed = true;
                } else {
                    next.push((name, def, is_struct));
                }
            }
            remaining = next;
        }

        // Handle cyclic dependencies
        if !remaining.is_empty() {
            for (name, def, is_struct) in remaining {
                if is_struct {
                    out.push_str(&self.emit_struct_typedef_ptr(name, def)?);
                } else {
                    out.push_str(&self.emit_union_typedef(name, def)?);
                }
                out.push('\n');
            }
        }
        Ok(())
    }

    // ── Static helper (for map construction during Self::new) ──

    fn constraint_to_ctype_static(
        t: &Term<'_>,
        union_names: &HashSet<String>,
        struct_names: &HashSet<String>,
    ) -> Result<CType, String> {
        crate::backend::ir::constraint_to_ctype(t, union_names, struct_names)
    }
}

// ── TypeMapper implementation ──

impl TypeMapper for TypeAnalyzer {
    fn constraint_to_ctype(&self, t: &Term<'_>) -> Result<CType, String> {
        crate::backend::ir::constraint_to_ctype(t, &self.union_names, &self.struct_names)
    }

    fn is_type_universe(&self, t: &Term<'_>) -> bool {
        crate::backend::ir::is_type_universe(t)
    }
}
