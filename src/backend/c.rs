//! C code generation backend.
//!
//! Generates straightforward C from erased `Term` trees.  C type
//! inference happens directly during emission via a `var_types` stack
//! that mirrors De Bruijn binding structure.

use crate::backend::ir::{CType, FunSig, constraint_to_ctype};
use crate::core::syntax::{FuncDef, PrimOp, Term};
use crate::front::parser::TopLevel;
use std::collections::{HashMap, HashSet};

/// Info about a union variant for C codegen.
#[allow(dead_code)]
struct VariantInfo {
    name: String,
    fields: Vec<(String, CType)>,
}

/// Union type info for C codegen.
#[allow(dead_code)]
struct UnionInfo {
    variants: Vec<VariantInfo>,
}

/// Build a map from union name to its variant info.
fn build_union_map(union_types: &[(&str, &Term<'_>)]) -> HashMap<String, UnionInfo> {
    let mut map = HashMap::new();
    let union_names: HashSet<String> = union_types.iter().map(|(n, _)| n.to_string()).collect();
    for (name, udef) in union_types {
        if let Term::UnionDef(_, variants) = udef {
            let mut vis = Vec::new();
            for (vname, fields) in variants.iter() {
                let fs: Vec<(String, CType)> = fields
                    .iter()
                    .map(|(fnm, fc)| (fnm.to_string(), constraint_to_ctype(fc, &union_names)))
                    .collect();
                vis.push(VariantInfo {
                    name: vname.to_string(),
                    fields: fs,
                });
            }
            map.insert(name.to_string(), UnionInfo { variants: vis });
        }
    }
    map
}

/// Emit a complete C source file from a list of top-level items.
pub fn emit_c(
    tops: &[TopLevel<'_>],
    fun_sigs: &[(&str, FunSig)],
    union_types: &[(&str, &Term<'_>)],
) -> String {
    let mut out = String::from("#include <stdio.h>\n#include <stdint.h>\n#include <stddef.h>\n\n");

    // Emit union type definitions
    let union_names: HashSet<String> = union_types.iter().map(|(n, _)| n.to_string()).collect();
    for (name, udef) in union_types {
        out.push_str(&emit_union_typedef(name, udef, &union_names));
        out.push('\n');
    }

    let union_map = build_union_map(union_types);

    let mut defs: Vec<(&str, &FuncDef<'_>)> = Vec::new();
    let mut outputs: Vec<&Term<'_>> = Vec::new();

    for top in tops {
        match top {
            TopLevel::TLDef(name, func_def) => {
                defs.push((name, func_def));
            }
            TopLevel::TLShow(term) | TopLevel::TLExpr(term) => outputs.push(term),
            _ => {}
        }
    }

    for (name, func_def) in &defs {
        out.push_str(&emit_def(name, func_def, fun_sigs, &union_map));
        out.push('\n');
    }

    if !outputs.is_empty() {
        out.push_str("int main(void) {\n");
        for term in &outputs {
            let (expr, ctype) = emit_expr(term, &[], &mut Vec::new(), None, fun_sigs, &union_map);
            // Handle match sentinels at top level (not inside a function)
            if expr.starts_with("match__") {
                let block = emit_match_block(&expr, &ctype);
                out.push_str(&block);
                // Print the result
                match ctype {
                    CType::Str => out.push_str(&format!("    printf(\"%s\\n\", _r);\n")),
                    CType::Int64 => out.push_str("    printf(\"%ld\\n\", (int64_t)_r);\n"),
                    CType::Union(_) => out.push_str("    printf(\"%d\\n\", _r.tag);\n"),
                }
            } else {
                match ctype {
                    CType::Str => {
                        out.push_str(&format!("    printf(\"%s\\n\", {});\n", expr));
                    }
                    CType::Int64 => {
                        out.push_str(&format!("    printf(\"%ld\\n\", (int64_t)({}));\n", expr));
                    }
                    CType::Union(_) => {
                        out.push_str(&format!("    printf(\"%d\\n\", ({}).tag);\n", expr));
                    }
                }
            }
        }
        out.push_str("    return 0;\n}\n");
    }
    out
}

/// Emit a C typedef for a union type (tagged union).
fn emit_union_typedef(name: &str, udef: &Term<'_>, union_names: &HashSet<String>) -> String {
    let Term::UnionDef(_, variants) = udef else {
        return String::new();
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
                // Recursive reference if: Builtin(name) or This (subst_this replaces self-refs).
                let is_self_ref =
                    matches!(fty, Term::Builtin(tn) if *tn == name) || matches!(fty, Term::This);
                if is_self_ref {
                    out.push_str(&format!("struct {}* {}; ", name, fname));
                } else {
                    let cty = constraint_to_ctype(fty, union_names);
                    out.push_str(&format!("{} {}; ", cty.c_name(), fname));
                }
            }
            out.push_str(&format!("}} {vname};\n"));
        }
    }
    out.push_str("    } data;\n");
    out.push_str(&format!("}} {name};\n"));
    out
}

/// Emit a top-level definition as a C function or constant.
fn emit_def(
    name: &str,
    func_def: &FuncDef<'_>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
) -> String {
    let params = func_def.params;
    let body = func_def.body;
    if params.is_empty() {
        let arity = count_lams(body);
        if arity == 0 {
            let (code, ctype) = emit_expr(body, &[], &mut Vec::new(), None, fun_sigs, union_map);
            format!("const {} {} = {};\n", ctype.c_name(), name, code)
        } else {
            let pns: Vec<String> = (0..arity).map(|i| format!("arg_{}", i)).collect();
            let peeled = peel_lams(body, arity);
            let param_types = vec![CType::Int64; arity];
            emit_fun(name, &pns, &param_types, peeled, fun_sigs, union_map)
        }
    } else {
        let pns: Vec<String> = params.iter().map(|(n, _)| n.to_string()).collect();
        let param_types: Vec<CType> = fun_sigs
            .iter()
            .find(|(n, _)| *n == name)
            .map(|(_, sig)| sig.param_types.clone())
            .unwrap_or_else(|| vec![CType::Int64; params.len()]);
        let peeled = peel_lams(body, params.len());
        emit_fun(name, &pns, &param_types, peeled, fun_sigs, union_map)
    }
}

/// Emit a C function with named parameters and a Term body.
///
/// `params` are the parameter names; `param_types` are the corresponding C types.
/// De Bruijn index 0 = rightmost (last) parameter.
fn emit_fun(
    name: &str,
    params: &[String],
    param_types: &[CType],
    body: &Term<'_>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
) -> String {
    let cps: Vec<String> = params
        .iter()
        .zip(param_types.iter())
        .map(|(p, ty)| format!("{} {p}", ty.c_name()))
        .collect();
    let bd: Vec<String> = params.iter().rev().cloned().collect();
    let mut var_types: Vec<CType> = param_types.iter().rev().cloned().collect();
    let (body_code, ret_ty) = emit_expr(body, &bd, &mut var_types, Some(name), fun_sigs, union_map);
    // If the body is a match, wrap it as a proper C block instead of
    // GCC statement expression.
    let return_stmt = if body_code.starts_with("match__") {
        // body_code is: "match__<scrut>__<ret_ty>__case0code__case1code__..."
        // Parse it out and emit as a switch block.
        let block = emit_match_block(&body_code, &ret_ty);
        format!("{block}    return _r;\n")
    } else {
        format!("    return {};\n", body_code)
    };
    format!(
        "{} {}({}) {{\n{}}}\n",
        ret_ty.c_name(),
        name,
        cps.join(", "),
        return_stmt
    )
}

/// Emit a match as a standard C switch block (not GCC expression).
fn emit_match_block(code: &str, ret_ty: &CType) -> String {
    // Format: match__<scrut_type>__<scrut>__<ret_ty>__<idx>__<body>__...
    let parts: Vec<&str> = code.split("__").collect();
    if parts.len() < 5 {
        return format!("    return 0;\n");
    }
    let scrut_ty = parts[1];
    let scrut = parts[2];
    let ret_name = ret_ty.c_name();
    let mut out = String::new();
    out.push_str(&format!("    {scrut_ty} _s = {scrut};\n"));
    out.push_str(&format!("    {ret_name} _r;\n"));
    out.push_str("    switch (_s.tag) {\n");
    for i in (4..parts.len()).step_by(2) {
        if i + 1 < parts.len() {
            let case_idx = parts[i];
            let case_code = parts[i + 1].replace('\x1e', ", ");
            out.push_str(&format!(
                "    case {}: _r = {}; break;\n",
                case_idx, case_code
            ));
        }
    }
    out.push_str(&format!("    default: _r = 0; break;\n"));
    out.push_str("    }\n");
    out
}

fn count_lams(term: &Term<'_>) -> usize {
    match term {
        Term::Lam(body) => 1 + count_lams(body),
        _ => 0,
    }
}

fn peel_lams<'a>(term: &'a Term<'a>, n: usize) -> &'a Term<'a> {
    let mut t = term;
    for _ in 0..n {
        if let Term::Lam(body) = t {
            t = body;
        }
    }
    t
}

/// Emit a Term as a C expression, returning the emitted code and its C type.
///
/// `bound` holds the C variable names in De Bruijn order (index 0 = most
/// recently bound).  `var_types` holds the C types in the same De Bruijn
/// order — the two stacks are kept in sync by push/pop at binder sites.
/// `self_name` is `Some(name)` inside a recursive function body (so `This`
/// can emit the function name).
fn emit_expr(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
) -> (String, CType) {
    match term {
        Term::LitInt(n) => (n.to_string(), CType::Int64),
        Term::LitBool(b) => (if *b { "1" } else { "0" }.into(), CType::Int64),
        Term::LitStr(s) => (format!("\"{}\"", s), CType::Str),

        Term::Var(i) => {
            let ty = var_types.get(*i).cloned().unwrap_or(CType::Int64);
            (bound[*i].clone(), ty)
        }

        Term::Let(name, val, body, _) => {
            let (v, val_ty) = emit_expr(val, bound, var_types, self_name, fun_sigs, union_map);
            let ty_name = val_ty.c_name();
            var_types.insert(0, val_ty);
            let mut ext: Vec<String> = vec![(*name).to_string()];
            ext.extend_from_slice(bound);
            let (b, body_ty) = emit_expr(body, &ext, var_types, self_name, fun_sigs, union_map);
            var_types.remove(0);
            (
                format!("({{ {} {} = {}; {}; }})", ty_name, name, v, b),
                body_ty,
            )
        }

        Term::Lam(body) => {
            var_types.insert(0, CType::Int64);
            let (b, ret_ty) = emit_expr(body, bound, var_types, self_name, fun_sigs, union_map);
            var_types.remove(0);
            // Lambda wrapping is done by emit_fun via emit_def.
            // We return the body code + return type for inference.
            (b, ret_ty)
        }

        Term::IfThenElse(c, t, f) => {
            let (cc, _) = emit_expr(c, bound, var_types, self_name, fun_sigs, union_map);
            let (ct, t_ty) = emit_expr(t, bound, var_types, self_name, fun_sigs, union_map);
            let (cf, _) = emit_expr(f, bound, var_types, self_name, fun_sigs, union_map);
            (format!("({}) ? ({}) : ({})", cc, ct, cf), t_ty)
        }

        // Function calls: look up the called function's return type.
        Term::App(_, _) => emit_app(term, bound, var_types, self_name, fun_sigs, union_map),

        Term::Annot(inner, _) => emit_expr(inner, bound, var_types, self_name, fun_sigs, union_map),
        Term::This => (self_name.unwrap_or("__self__").into(), CType::Int64),
        Term::Builtin(name) => {
            let ty = fun_sigs
                .iter()
                .find(|(n, _)| *n == *name)
                .map(|(_, sig)| sig.ret_type.clone())
                .unwrap_or(CType::Int64);
            ((*name).to_string(), ty)
        }
        Term::UnionDef(..) => (String::new(), CType::Int64),
        Term::Variant(uname, idx, payloads) => {
            let type_name: String = uname.to_string();
            // Look up variant info for field names
            let data_init = if let Some(info) = union_map.get(&type_name) {
                if let Some(vi) = info.variants.get(*idx) {
                    if vi.fields.is_empty() {
                        format!("{{ .{} = {{0}} }}", vi.name)
                    } else {
                        let field_inits: Vec<String> = vi
                            .fields
                            .iter()
                            .zip(payloads.iter())
                            .map(|((fnm, fty), p)| {
                                let (code, pty) =
                                    emit_expr(p, bound, var_types, self_name, fun_sigs, union_map);
                                // Recursive field? Check field type AND payload type.
                                let is_rec = if let CType::Union(un) = fty {
                                    un == &type_name
                                } else if let CType::Union(ref un) = pty {
                                    un == &type_name
                                } else {
                                    false
                                };
                                if is_rec {
                                    format!(".{} = &{}", fnm, code)
                                } else {
                                    format!(".{} = {}", fnm, code)
                                }
                            })
                            .collect();
                        format!("{{ .{} = {{ {} }} }}", vi.name, field_inits.join(", "))
                    }
                } else {
                    String::from("{0}")
                }
            } else {
                String::from("{0}")
            };
            (
                format!(
                    "(({}){{ .tag = {}, .data = {} }})",
                    type_name, idx, data_init
                ),
                CType::Union(type_name),
            )
        }
        Term::Match(_scrut, branches) => {
            // Emit as "match__<scrut_type>__<scrut>__<ret_ty>__<idx>__<body>__..."
            let (sc, sc_ty) = emit_expr(_scrut, bound, var_types, self_name, fun_sigs, union_map);
            let mut parts = vec!["match".to_string(), sc_ty.c_name(), sc];
            let mut ret_ty = CType::Int64;
            for (idx, binds, body) in branches.iter() {
                let mut ext = bound.to_vec();
                let mut ext_types = var_types.clone();
                for (name, _) in binds.iter().rev() {
                    ext.insert(0, (*name).to_string());
                    ext_types.insert(0, CType::Int64);
                }
                let (bc, bty) =
                    emit_expr(body, &ext, &mut ext_types, self_name, fun_sigs, union_map);
                ret_ty = bty;
                let escaped = bc.replace(',', "\x1e");
                parts.push(idx.to_string());
                parts.push(escaped);
            }
            let ty_str = ret_ty.c_name();
            parts.insert(3, ty_str);
            (parts.join("__"), ret_ty)
        }
        _ => ("0".into(), CType::Int64),
    }
}

fn emit_app(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
) -> (String, CType) {
    let Term::App(f, a) = term else {
        unreachable!()
    };
    // Binary operators: (prim left) right  →  PrimOp applied to two args.
    if let Term::App(prim, left) = *f
        && let Term::PrimOp(op) = *prim
    {
        let (ls, _) = emit_expr(left, bound, var_types, self_name, fun_sigs, union_map);
        let (rs, _) = emit_expr(a, bound, var_types, self_name, fun_sigs, union_map);
        return (emit_binop(*op, &ls, &rs), CType::Int64);
    }
    // Unary / partial application: just emit the argument.
    if matches!(*f, Term::PrimOp(_)) {
        let (as_, ty) = emit_expr(a, bound, var_types, self_name, fun_sigs, union_map);
        return (as_, ty);
    }
    // Function call.
    let mut args: Vec<String> = Vec::new();
    let func = collect_call_args(
        term, bound, var_types, self_name, fun_sigs, union_map, &mut args,
    );
    let ret_ty = fun_sigs
        .iter()
        .find(|(n, _)| *n == func)
        .map(|(_, sig)| sig.ret_type.clone())
        .unwrap_or(CType::Int64);
    (format!("{}({})", func, args.join(", ")), ret_ty)
}

fn collect_call_args(
    term: &Term<'_>,
    bound: &[String],
    var_types: &mut Vec<CType>,
    self_name: Option<&str>,
    fun_sigs: &[(&str, FunSig)],
    union_map: &HashMap<String, UnionInfo>,
    args: &mut Vec<String>,
) -> String {
    match term {
        Term::App(f, a) => {
            let func = collect_call_args(f, bound, var_types, self_name, fun_sigs, union_map, args);
            let (as_, _) = emit_expr(a, bound, var_types, self_name, fun_sigs, union_map);
            args.push(as_);
            func
        }
        _ => {
            let (s, _) = emit_expr(term, bound, var_types, self_name, fun_sigs, union_map);
            s
        }
    }
}

fn emit_binop(op: PrimOp, left: &str, right: &str) -> String {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::backend::ir::FunSig;
    use crate::core::pool::TermArena;
    use crate::core::syntax::{Name, PrimOp};
    use bumpalo::Bump;

    fn setup() -> (&'static Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(Bump::new()));
        (b, TermArena::new(b))
    }

    fn sig(name: &str, param_types: Vec<CType>, ret_type: CType) -> (&str, FunSig) {
        let leaked: &'static str = Box::leak(name.to_string().into_boxed_str());
        (
            leaked,
            FunSig {
                param_types,
                ret_type,
            },
        )
    }

    fn emit(tops: &[TopLevel<'_>], fun_sigs: &[(&str, FunSig)]) -> String {
        emit_c(tops, fun_sigs, &[])
    }

    // ── Literals ──

    #[test]
    fn int_literal_uses_ld() {
        let (_b, arena) = setup();
        let c = emit(&[TopLevel::TLShow(arena.lit_int(42))], &[]);
        assert!(c.contains("42"));
        assert!(c.contains("%ld"));
    }

    #[test]
    fn str_literal_uses_s() {
        let (_b, arena) = setup();
        let c = emit(
            &[TopLevel::TLShow(arena.lit_str(arena.alloc_str("hi")))],
            &[],
        );
        assert!(c.contains("\"hi\""));
        assert!(c.contains("%s"));
    }

    #[test]
    fn bool_literal_emits_0_or_1() {
        let (_b, arena) = setup();
        let c = emit(&[TopLevel::TLShow(arena.lit_bool(true))], &[]);
        assert!(c.contains("(int64_t)(1)"));
    }

    // ── Constants ──

    #[test]
    fn int_const_def() {
        let (_b, arena) = setup();
        let func_def = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("x"),
            params: &[],
            ret: None,
            body: arena.lit_int(5),
        });
        let c = emit(&[TopLevel::TLDef(arena.alloc_str("x"), func_def)], &[]);
        assert!(c.contains("const int64_t x = 5;"));
    }

    #[test]
    fn str_const_def() {
        let (_b, arena) = setup();
        let func_def = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("g"),
            params: &[],
            ret: None,
            body: arena.lit_str(arena.alloc_str("hi")),
        });
        let c = emit(&[TopLevel::TLDef(arena.alloc_str("g"), func_def)], &[]);
        assert!(c.contains("const char* g"));
        assert!(c.contains("\"hi\""));
    }

    // ── Functions (no FunSig, lam-tree) ──

    #[test]
    fn lam_function_defaults_to_int64_params_and_return() {
        let (_b, arena) = setup();
        let body = arena.app(
            arena.app(arena.prim_op(PrimOp::Add), arena.var(1)),
            arena.var(0),
        );
        let lam = arena.lam(arena.lam(body));
        let func_def = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("add"),
            params: &[],
            ret: None,
            body: lam,
        });
        let c = emit(&[TopLevel::TLDef(arena.alloc_str("add"), func_def)], &[]);
        assert!(c.contains("int64_t add(int64_t arg_0, int64_t arg_1)"));
    }

    #[test]
    fn lam_returning_str_infers_str_return_type() {
        let (_b, arena) = setup();
        let lam = arena.lam(arena.lit_str(arena.alloc_str("hi")));
        let func_def = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("greet"),
            params: &[],
            ret: None,
            body: lam,
        });
        let c = emit(&[TopLevel::TLDef(arena.alloc_str("greet"), func_def)], &[]);
        assert!(c.contains("const char* greet(int64_t arg_0)"));
        assert!(c.contains("\"hi\""));
    }

    // ── Functions WITH FunSig ──

    #[test]
    fn func_with_str_param_uses_const_char_ptr() {
        let (_b, arena) = setup();
        let func_def = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("echo"),
            params: arena.alloc_slice(&[(
                arena.alloc_str("s"),
                Some(arena.builtin(arena.alloc_str("str"))),
            )]),
            ret: Some(arena.builtin(arena.alloc_str("str"))),
            body: arena.var(0),
        });
        let sigs = &[sig("echo", vec![CType::Str], CType::Str)];
        let c = emit(&[TopLevel::TLDef(arena.alloc_str("echo"), func_def)], sigs);
        assert!(c.contains("const char* echo(const char* s)"));
    }

    #[test]
    fn func_with_mixed_params() {
        let (_b, arena) = setup();
        let func_def = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("f"),
            params: arena.alloc_slice(&[
                (
                    arena.alloc_str("a"),
                    Some(arena.builtin(arena.alloc_str("int"))),
                ),
                (
                    arena.alloc_str("b"),
                    Some(arena.builtin(arena.alloc_str("str"))),
                ),
            ]),
            ret: Some(arena.builtin(arena.alloc_str("int"))),
            body: arena.var(1),
        });
        let sigs = &[sig("f", vec![CType::Int64, CType::Str], CType::Int64)];
        let c = emit(&[TopLevel::TLDef(arena.alloc_str("f"), func_def)], sigs);
        assert!(c.contains("int64_t f(int64_t a, const char* b)"));
    }

    // ── Function calls ──

    #[test]
    fn call_to_function_uses_fun_sig_return_type() {
        let (_b, arena) = setup();
        let fn_name = arena.alloc_str("greet");
        let func_def = arena.bump().alloc(FuncDef {
            name: fn_name,
            params: &[],
            ret: Some(arena.builtin(arena.alloc_str("str"))),
            body: arena.lit_str(arena.alloc_str("hi")),
        });
        let def = TopLevel::TLDef(fn_name, func_def);
        let sig = FunSig {
            param_types: vec![],
            ret_type: CType::Str,
        };
        let show = TopLevel::TLShow(arena.builtin(fn_name));
        let tops = &[def, show];
        let c = emit(tops, &[(fn_name, sig)]);
        assert!(c.contains("%s"));
        assert!(c.contains("const char* greet"));
    }

    #[test]
    fn emit_undefined_func_call_still_emits() {
        let (_b, arena) = setup();
        let n = arena.alloc_str("s");
        let call = arena.app(arena.builtin(n), arena.lit_str(arena.alloc_str("hi")));
        let tops = &[TopLevel::TLShow(call)];
        let c = emit(tops, &[]);
        assert!(c.contains("s("));
    }

    #[test]
    fn emit_let_str_printf_format() {
        let (_b, arena) = setup();
        let term = arena.let_(
            arena.alloc_str("s"),
            arena.lit_str(arena.alloc_str("hi")),
            arena.var(0),
            None,
        );
        let c = emit(&[TopLevel::TLShow(term)], &[]);
        assert!(c.contains("%s"));
        assert!(c.contains("const char* s"));
    }

    #[test]
    fn emit_multiple_defs_and_outputs() {
        let (_b, arena) = setup();
        let func_def_a = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("a"),
            params: &[],
            ret: None,
            body: arena.lit_int(1),
        });
        let func_def_b = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("b"),
            params: &[],
            ret: None,
            body: arena.lit_str(arena.alloc_str("two")),
        });
        let tops = &[
            TopLevel::TLDef(arena.alloc_str("a"), func_def_a),
            TopLevel::TLDef(arena.alloc_str("b"), func_def_b),
            TopLevel::TLShow(arena.lit_int(3)),
            TopLevel::TLShow(arena.lit_str(arena.alloc_str("four"))),
        ];
        let c = emit(tops, &[]);
        assert!(c.contains("const int64_t a = 1;"));
        assert!(c.contains("const char* b = \"two\";"));
        assert!(c.contains("%ld"));
        assert!(c.contains("%s"));
    }

    // ── Union codegen ──

    /// Build a union typedef with empty and payload variants.
    #[test]
    fn union_typedef_with_recursive_field() {
        let (_b, arena) = setup();
        let nat_name = arena.alloc_str("Nat");
        let zero_variant: (Name, &[(Name, &Term)]) =
            (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
        let succ_fields: &[(Name, &Term)] =
            arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
        let succ_variant: (Name, &[(Name, &Term)]) = (arena.alloc_str("Succ"), succ_fields);
        let variants: &[(Name, &[(Name, &Term)])] =
            arena.alloc_slice(&[zero_variant, succ_variant]);
        let nat_udef = arena.union_def(nat_name, variants);
        let union_types: &[(&str, &Term)] = arena.bump().alloc([(nat_name, nat_udef)]);

        let top_name = arena.alloc_str("zero");
        let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
        let func_def = arena.bump().alloc(FuncDef {
            name: top_name,
            params: &[],
            ret: Some(arena.builtin(nat_name)),
            body: zero_v,
        });
        let tops = &[TopLevel::TLDef(top_name, func_def)];

        let c = emit_c(tops, &[], union_types);
        // Typedef uses struct pointer for recursive field
        assert!(
            c.contains("struct Nat* pred;"),
            "expected struct Nat* pred; in:\n{c}"
        );
        // Empty variant uses proper initializer
        assert!(c.contains(".Zero = {0}"), "expected .Zero = {{0}} in:\n{c}");
        // Constant declaration uses union type name
        assert!(
            c.contains("const Nat zero ="),
            "expected const Nat zero in:\n{c}"
        );
    }

    /// Recursive variant construction emits address-of.
    #[test]
    fn union_recursive_variant_emits_address_of() {
        let (_b, arena) = setup();
        let nat_name = arena.alloc_str("Nat");
        let zero_variant: (Name, &[(Name, &Term)]) =
            (arena.alloc_str("Zero"), arena.alloc_slice(&[]));
        let succ_fields: &[(Name, &Term)] =
            arena.alloc_slice(&[(arena.alloc_str("pred"), arena.builtin(nat_name))]);
        let succ_variant: (Name, &[(Name, &Term)]) = (arena.alloc_str("Succ"), succ_fields);
        let variants: &[(Name, &[(Name, &Term)])] =
            arena.alloc_slice(&[zero_variant, succ_variant]);
        let nat_udef = arena.union_def(nat_name, variants);
        let union_types: &[(&str, &Term)] = arena.bump().alloc([(nat_name, nat_udef)]);

        // Build: Succ(Zero)
        let zero_v = arena.variant(nat_name, 0, arena.alloc_slice(&[]));
        let one_v = arena.variant(nat_name, 1, arena.alloc_slice(&[zero_v]));
        let func_def = arena.bump().alloc(FuncDef {
            name: arena.alloc_str("one"),
            params: &[],
            ret: Some(arena.builtin(nat_name)),
            body: one_v,
        });
        let tops = &[TopLevel::TLDef(arena.alloc_str("one"), func_def)];

        let c = emit_c(tops, &[], union_types);
        // Recursive reference must emit & (address-of) for the pointer field
        assert!(
            c.contains("&((Nat)"),
            "expected &((Nat){{...}}) for recursive field in:\n{c}"
        );
    }
}
