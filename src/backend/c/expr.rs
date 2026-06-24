//! C expression emission.
//!
//! `ExpressionEmitter` translates Ligare `Term` nodes into C expressions.
//! It is a stateless service object — maps are passed at call time for clean
//! ownership semantics.

use crate::backend::c::context::EmitCtx;
use crate::backend::c::names::NameResolver;
use crate::backend::c::types::{StructInfo, UnionInfo};
use crate::backend::ir::{CType, FunSig};
use crate::core::syntax::{PrimOp, Term};
use crate::diagnostic::Diagnostic;
use std::collections::{HashMap, HashSet};

/// Translates Ligare `Term` nodes into C expressions.
///
/// Stateless service object — holds only function signatures and name resolver.
/// Type maps are passed at call time to avoid self-referential borrows.
pub struct ExpressionEmitter<'a> {
    /// Function signatures for return-type inference.
    fun_sigs: &'a [(&'a str, FunSig)],
    /// Name resolver for escaping.
    names: NameResolver,
}

impl<'a> ExpressionEmitter<'a> {
    /// Create a new expression emitter.
    pub fn new(fun_sigs: &'a [(&'a str, FunSig)]) -> Self {
        Self {
            fun_sigs,
            names: NameResolver::new(),
        }
    }

    // ── Main entry ──

    /// Emit a Term as a C expression, returning the emitted code and its C type.
    pub fn emit_expr(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<(String, CType), Diagnostic> {
        match term {
            Term::LitInt(n) => Ok((n.to_string(), CType::Int64)),
            Term::LitBool(b) => Ok((if *b { "1" } else { "0" }.into(), CType::Int64)),
            Term::LitStr(s) => Ok((format!("\"{}\"", s), CType::Str)),

            Term::Var(i) => Ok((ctx.name_of(*i).to_string(), ctx.type_of(*i))),

            Term::Let(name, val, body, _) => {
                let escaped_name = self.names.escape(name);
                let (v, val_ty) = self.emit_expr(val, ctx, union_map, struct_map)?;
                let ty_name = val_ty.c_name();
                ctx.push_binding(escaped_name.clone(), val_ty.clone());
                let (b, body_ty) = self.emit_expr(body, ctx, union_map, struct_map)?;
                ctx.pop_binding();
                Ok((
                    format!("({{ {} {} = {}; {}; }})", ty_name, escaped_name, v, b),
                    body_ty,
                ))
            }

            Term::Lam(body) => {
                ctx.push_binding(self.names.anon_param(0), CType::Int64);
                let (b, ret_ty) = self.emit_expr(body, ctx, union_map, struct_map)?;
                ctx.pop_binding();
                Ok((b, ret_ty))
            }

            Term::IfThenElse(c, t, f) => {
                let (cc, _) = self.emit_expr(c, ctx, union_map, struct_map)?;
                let (ct, t_ty) = self.emit_expr(t, ctx, union_map, struct_map)?;
                let (cf, _) = self.emit_expr(f, ctx, union_map, struct_map)?;
                Ok((format!("({}) ? ({}) : ({})", cc, ct, cf), t_ty))
            }

            Term::App(_, _) => self.emit_app(term, ctx, union_map, struct_map),

            Term::Annot(inner, _) => self.emit_expr(inner, ctx, union_map, struct_map),

            Term::Builtin(name) | Term::Named(name) => {
                let ty = self
                    .fun_sigs
                    .iter()
                    .find(|(n, _)| *n == *name)
                    .map(|(_, sig)| sig.ret_type.clone())
                    .unwrap_or(CType::Int64);
                Ok((self.names.escape(name), ty))
            }

            Term::UnionDef(..) => Ok((String::new(), CType::Int64)),
            Term::StructDef(..) => Ok((String::new(), CType::Int64)),

            Term::StructCons(sname, field_values) => {
                self.emit_struct_cons(sname, field_values, ctx, union_map, struct_map)
            }
            Term::StructProj(subject, idx) => {
                self.emit_struct_proj(subject, *idx, ctx, union_map, struct_map)
            }
            Term::Variant(uname, idx, payloads) => {
                self.emit_variant(uname, *idx, payloads, ctx, union_map, struct_map)
            }
            Term::Match(_scrut, branches) => {
                self.emit_match(_scrut, branches, ctx, union_map, struct_map)
            }

            _ => Err(Diagnostic::new(format!(
                "emit_expr: unrecognized term {:?}",
                term
            ))),
        }
    }

    // ── Sub-emitters ──

    fn emit_struct_cons(
        &self,
        sname: &str,
        field_values: &[&Term<'_>],
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<(String, CType), Diagnostic> {
        let type_name: String = sname.to_string();
        let field_codes: Vec<String> = field_values
            .iter()
            .map(|v| {
                let (code, _) = self.emit_expr(v, ctx, union_map, struct_map)?;
                Ok(code)
            })
            .collect::<Result<Vec<_>, Diagnostic>>()?;
        Ok((
            format!("(({}){{ {} }})", type_name, field_codes.join(", ")),
            CType::Struct(type_name),
        ))
    }

    fn emit_struct_proj(
        &self,
        subject: &Term<'_>,
        idx: usize,
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<(String, CType), Diagnostic> {
        let (scode, sty) = self.emit_expr(subject, ctx, union_map, struct_map)?;
        if let CType::Struct(ref sname) = sty
            && let Some(info) = struct_map.get(sname)
            && let Some((fname, ftype)) = info.fields.get(idx)
        {
            return Ok((format!("({}).{}", scode, fname), ftype.clone()));
        }
        Ok((format!("({})._f{}", scode, idx), CType::Int64))
    }

    fn emit_variant(
        &self,
        uname: &str,
        idx: usize,
        payloads: &[&Term<'_>],
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<(String, CType), Diagnostic> {
        let type_name: String = uname.to_string();
        let data_init =
            self.variant_data_init(&type_name, idx, payloads, ctx, union_map, struct_map)?;
        Ok((
            format!(
                "(({}){{ .tag = {}, .data = {} }})",
                type_name, idx, data_init
            ),
            CType::Union(type_name),
        ))
    }

    fn variant_data_init(
        &self,
        type_name: &str,
        idx: usize,
        payloads: &[&Term<'_>],
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<String, Diagnostic> {
        if let Some(info) = union_map.get(type_name) {
            if let Some(vi) = info.variants.get(idx) {
                if vi.fields.is_empty() {
                    return Ok(format!("{{ .{} = {{0}} }}", vi.name));
                }
                let field_inits: Vec<String> = vi
                    .fields
                    .iter()
                    .zip(payloads.iter())
                    .map(|((fnm, fty), p)| {
                        let (code, pty) = self.emit_expr(p, ctx, union_map, struct_map)?;
                        let is_rec = if let CType::Union(un) = fty {
                            un == type_name
                        } else if let CType::Union(ref un) = pty {
                            un == type_name
                        } else {
                            false
                        };
                        Ok(if is_rec {
                            format!(".{} = &{}", fnm, code)
                        } else {
                            format!(".{} = {}", fnm, code)
                        })
                    })
                    .collect::<Result<Vec<_>, Diagnostic>>()?;
                return Ok(format!(
                    "{{ .{} = {{ {} }} }}",
                    vi.name,
                    field_inits.join(", ")
                ));
            }
        }
        Ok(String::from("{0}"))
    }

    fn emit_match(
        &self,
        scrut: &Term<'_>,
        branches: &[(
            usize,
            &[(crate::core::syntax::Name<'_>, &Term<'_>)],
            &Term<'_>,
        )],
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<(String, CType), Diagnostic> {
        let (sc, sc_ty) = self.emit_expr(scrut, ctx, union_map, struct_map)?;
        let mut parts = vec!["match".to_string(), sc_ty.c_name(), sc];
        let mut ret_ty = CType::Int64;
        for (idx, binds, body) in branches.iter() {
            let mut branch_ctx = ctx.snapshot();
            for (name, _) in binds.iter().rev() {
                branch_ctx.push_binding(self.names.escape(name), CType::Int64);
            }
            let (bc, bty) = self.emit_expr(body, &mut branch_ctx, union_map, struct_map)?;
            ret_ty = bty;
            let escaped = bc.replace(',', "\x1e");
            parts.push(idx.to_string());
            parts.push(binds.len().to_string());
            for (_name, ty) in binds.iter() {
                parts.push(self.names.escape(_name));
                let un: HashSet<String> = union_map.keys().cloned().collect();
                let sn: HashSet<String> = struct_map.keys().cloned().collect();
                let cty = crate::backend::ir::constraint_to_ctype(ty, &un, &sn)?;
                parts.push(cty.c_name());
            }
            parts.push(escaped);
        }
        let ty_str = ret_ty.c_name();
        parts.insert(3, ty_str);
        Ok((parts.join("__"), ret_ty))
    }

    // ── Function call emission ──

    pub fn emit_app(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<(String, CType), Diagnostic> {
        let Term::App(f, a) = term else {
            unreachable!()
        };
        if let Term::App(prim, left) = *f
            && let Term::PrimOp(op) = *prim
        {
            let (ls, _) = self.emit_expr(left, ctx, union_map, struct_map)?;
            let (rs, _) = self.emit_expr(a, ctx, union_map, struct_map)?;
            return Ok((self.emit_binop(*op, &ls, &rs), CType::Int64));
        }
        if matches!(*f, Term::PrimOp(_)) {
            let (as_, ty) = self.emit_expr(a, ctx, union_map, struct_map)?;
            return Ok((as_, ty));
        }
        let (func, args) = self.collect_call_args(term, ctx, union_map, struct_map)?;
        let param_count = self
            .fun_sigs
            .iter()
            .find(|(n, _)| *n == func)
            .map(|(_, sig)| sig.param_types.len())
            .unwrap_or(0);
        let trimmed: Vec<String> = if args.len() > param_count {
            args[args.len() - param_count..].to_vec()
        } else {
            args
        };
        let ret_ty = self
            .fun_sigs
            .iter()
            .find(|(n, _)| *n == func)
            .map(|(_, sig)| sig.ret_type.clone())
            .unwrap_or(CType::Int64);
        Ok((format!("{}({})", func, trimmed.join(", ")), ret_ty))
    }

    fn collect_call_args(
        &self,
        term: &Term<'_>,
        ctx: &mut EmitCtx,
        union_map: &HashMap<String, UnionInfo>,
        struct_map: &HashMap<String, StructInfo>,
    ) -> Result<(String, Vec<String>), Diagnostic> {
        match term {
            Term::App(f, a) => {
                let (func, mut args) = self.collect_call_args(f, ctx, union_map, struct_map)?;
                let (as_, _) = self.emit_expr(a, ctx, union_map, struct_map)?;
                args.push(as_);
                Ok((func, args))
            }
            _ => {
                let (s, _) = self.emit_expr(term, ctx, union_map, struct_map)?;
                Ok((s, Vec::new()))
            }
        }
    }

    /// Emit a binary operator as a C expression.
    pub fn emit_binop(&self, op: PrimOp, left: &str, right: &str) -> String {
        match op {
            PrimOp::Add => format!("({left} + {right})"),
            PrimOp::Sub => format!("({left} - {right})"),
            PrimOp::Mul => format!("({left} * {right})"),
            PrimOp::Div => format!("({left} / {right})"),
            PrimOp::Mod_ => format!("({left} % {right})"),
            PrimOp::Eq => format!("({left} == {right})"),
            PrimOp::Neq => format!("({left} != {right})"),
            PrimOp::Lt => format!("({left} < {right})"),
            PrimOp::Gt => format!("({left} > {right})"),
            PrimOp::Le => format!("({left} <= {right})"),
            PrimOp::Ge => format!("({left} >= {right})"),
        }
    }
}
