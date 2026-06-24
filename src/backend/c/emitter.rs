//! Main C code emitter — the orchestrator.
//!
//! `CEmitter` is the central coordinator for C code generation.  It
//! aggregates all sub-components (`TypeAnalyzer`, `NameResolver`,
//! `ExpressionEmitter`, `MatchEmitter`) and implements the `CodeGenerator`
//! trait, following the OOP composite pattern.

use crate::backend::c::context::EmitCtx;
use crate::backend::c::expr::ExpressionEmitter;
use crate::backend::c::match_emit::MatchEmitter;
use crate::backend::c::names::NameResolver;
use crate::backend::c::types::{TypeAnalyzer, TypeMapper};
use crate::backend::ir::{CType, FunSig};
use crate::core::syntax::{Name, Term};
use crate::front::parser::TopLevel;
use std::collections::HashSet;

/// Generates complete C source code from Ligare top-level items.
///
/// This trait is the public contract for code generation — different
/// backends can implement it for different target languages.
pub trait CodeGenerator {
    /// Generate a complete source file.
    fn generate(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        struct_types: &[(&str, &Term<'_>)],
        union_types: &[(&str, &Term<'_>)],
    ) -> Result<String, String>;
}

/// The C code emitter — orchestrates all sub-components.
///
/// Follows the OOP composite pattern:
/// - `type_analyzer` owns the type maps and handles typedef emission
/// - `name_resolver` handles escaping and on-demand name collection
/// - `expr_emitter` handles expression → C translation (stateless service)
/// - `match_emitter` handles match → switch translation
/// - `fun_sigs` provides return-type inference for function calls
pub struct CEmitter<'a> {
    /// Function signatures for type inference.
    fun_sigs: &'a [(&'a str, FunSig)],
    /// Type analysis and typedef emission.
    type_analyzer: TypeAnalyzer,
    /// Name resolution and escaping.
    name_resolver: NameResolver,
    /// Expression translation (stateless service object).
    expr_emitter: ExpressionEmitter<'a>,
    /// Match block translation.
    match_emitter: MatchEmitter,
}

impl<'a> CEmitter<'a> {
    /// Create a new emitter from the compilation context.
    ///
    /// Builds all sub-components and wires them together.
    pub fn new(
        struct_types: &[(&str, &Term<'_>)],
        union_types: &[(&str, &Term<'_>)],
        fun_sigs: &'a [(&'a str, FunSig)],
    ) -> Result<Self, String> {
        let type_analyzer = TypeAnalyzer::new(struct_types, union_types)?;
        let expr_emitter = ExpressionEmitter::new(fun_sigs);
        Ok(Self {
            fun_sigs,
            type_analyzer,
            name_resolver: NameResolver::new(),
            expr_emitter,
            match_emitter: MatchEmitter::new(),
        })
    }

    // ── Helpers for map access ──

    fn union_map(&self) -> &std::collections::HashMap<String, crate::backend::c::types::UnionInfo> {
        &self.type_analyzer.union_map
    }

    fn struct_map(
        &self,
    ) -> &std::collections::HashMap<String, crate::backend::c::types::StructInfo> {
        &self.type_analyzer.struct_map
    }

    // ── Definition emission ──

    /// Emit a top-level definition as a C function or constant.
    fn emit_def(
        &self,
        name: &str,
        params: &[(Name<'_>, Option<&Term<'_>>)],
        body: &Term<'_>,
    ) -> Result<String, String> {
        if params.is_empty() {
            let arity = self.name_resolver.count_lams(body);
            if arity == 0 {
                let mut ctx = EmitCtx::new();
                let (code, ctype) = self.expr_emitter.emit_expr(
                    body,
                    &mut ctx,
                    self.union_map(),
                    self.struct_map(),
                )?;
                Ok(format!(
                    "const {} {} = {};\n",
                    ctype.c_name(),
                    self.name_resolver.escape(name),
                    code
                ))
            } else {
                let pns: Vec<String> = (0..arity)
                    .map(|i| self.name_resolver.anon_param(i))
                    .collect();
                let peeled = self.name_resolver.peel_lams(body, arity);
                let param_types = vec![CType::Int64; arity];
                self.emit_fun(name, &pns, &param_types, peeled)
            }
        } else {
            // Filter out type-level (generic) params
            let data_params: Vec<_> = params
                .iter()
                .filter(|(_, mc)| !mc.is_some_and(|c| self.type_analyzer.is_type_universe(c)))
                .collect();
            let pns: Vec<String> = data_params
                .iter()
                .map(|(n, _)| self.name_resolver.escape(n))
                .collect();
            let param_types: Vec<CType> = self
                .fun_sigs
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, sig)| sig.param_types.clone())
                .unwrap_or_else(|| vec![CType::Int64; data_params.len()]);
            let peeled = self.name_resolver.peel_lams(body, params.len());
            self.emit_fun(name, &pns, &param_types, peeled)
        }
    }

    /// Emit a C function with named parameters and a Term body.
    fn emit_fun(
        &self,
        name: &str,
        params: &[String],
        param_types: &[CType],
        body: &Term<'_>,
    ) -> Result<String, String> {
        let cps: Vec<String> = params
            .iter()
            .zip(param_types.iter())
            .map(|(p, ty)| format!("{} {}", ty.c_name(), self.name_resolver.escape(p)))
            .collect();
        let mut ctx = EmitCtx::from_params(params, param_types);
        ctx.self_name = Some(name.to_string());
        let (body_code, ret_ty) =
            self.expr_emitter
                .emit_expr(body, &mut ctx, self.union_map(), self.struct_map())?;
        let return_stmt = if body_code.starts_with("match__") {
            let block =
                self.match_emitter
                    .emit(&body_code, &ret_ty, 0, &self.type_analyzer.union_map);
            format!("{block}    return {};\n", self.name_resolver.result_temp(0))
        } else {
            format!("    return {};\n", body_code)
        };
        Ok(format!(
            "{} {}({}) {{\n{}}}\n",
            ret_ty.c_name(),
            self.name_resolver.escape(name),
            cps.join(", "),
            return_stmt
        ))
    }

    /// Emit a printf statement for the given expression and C type.
    fn emit_printf(&self, out: &mut String, expr: &str, ctype: &CType) {
        match ctype {
            CType::Str => out.push_str(&format!("    printf(\"%s\\n\", {});\n", expr)),
            CType::Int64 => {
                out.push_str(&format!("    printf(\"%ld\\n\", (int64_t)({}));\n", expr))
            }
            CType::Union(_) => out.push_str(&format!("    printf(\"%d\\n\", ({}).tag);\n", expr)),
            CType::Struct(_) => out.push_str("    printf(\"<struct>\\n\");\n"),
        }
    }
}

impl<'a> CodeGenerator for CEmitter<'a> {
    fn generate(
        &self,
        tops: &[TopLevel<'_>],
        raw_defs: &[TopLevel<'_>],
        struct_types: &[(&str, &Term<'_>)],
        union_types: &[(&str, &Term<'_>)],
    ) -> Result<String, String> {
        let mut out =
            String::from("#include <stdio.h>\n#include <stdint.h>\n#include <stddef.h>\n\n");

        // Emit type declarations via TypeAnalyzer
        self.type_analyzer
            .emit_type_declarations(&mut out, struct_types, union_types)?;

        // Collect output expressions
        let mut outputs: Vec<&Term<'_>> = Vec::new();
        for top in tops {
            match top {
                TopLevel::TLShow(term, _) | TopLevel::TLExpr(term, _) => outputs.push(term),
                _ => {}
            }
        }

        // Emit constants unconditionally
        for top in tops {
            if let TopLevel::TLDef(name, params, _m_ret, body, _) = top
                && params.is_empty()
                && self.name_resolver.count_lams(body) == 0
            {
                out.push_str(&self.emit_def(name, params, body)?);
                out.push('\n');
            }
        }

        // On-demand codegen for functions
        let called_names: HashSet<String> = if outputs.is_empty() {
            self.name_resolver.all_def_names(raw_defs)
        } else {
            self.name_resolver.collect_called_names(&outputs, raw_defs)
        };

        for raw_def in raw_defs {
            if let TopLevel::TLDef(name, params, _m_ret, body, _) = raw_def {
                if params.is_empty() && self.name_resolver.count_lams(body) == 0 {
                    continue;
                }
                if called_names.contains(*name) {
                    out.push_str(&self.emit_def(name, params, body)?);
                    out.push('\n');
                }
            }
        }

        // Emit main function
        if !outputs.is_empty() {
            out.push_str("int main(void) {\n");
            let mut match_counter: u32 = 0;
            for term in &outputs {
                let mut ctx = EmitCtx::new();
                let (expr, ctype) = self.expr_emitter.emit_expr(
                    term,
                    &mut ctx,
                    self.union_map(),
                    self.struct_map(),
                )?;
                if expr.starts_with("match__") {
                    let block = self.match_emitter.emit(
                        &expr,
                        &ctype,
                        match_counter,
                        &self.type_analyzer.union_map,
                    );
                    match_counter += 1;
                    out.push_str(&block);
                    let r_var = self.name_resolver.result_temp(match_counter - 1);
                    self.emit_printf(&mut out, &r_var, &ctype);
                } else {
                    self.emit_printf(&mut out, &expr, &ctype);
                }
            }
            out.push_str("    return 0;\n}\n");
        } else {
            out.push_str("int main(void) {\n    return 0;\n}\n");
        }
        Ok(out)
    }
}
