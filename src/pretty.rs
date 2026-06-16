use crate::core::syntax::{Name, Term};

pub fn pretty(t: &Term<'_>) -> String {
    match t {
        Term::Var(i) => format!("${}", i),
        Term::Lam(body) => format!("λ. {}", pretty(body)),
        Term::App(f, a) => format!("({} {})", pretty(f), pretty(a)),
        Term::LitInt(n) => n.to_string(),
        Term::Universe(u) => u.to_string(),
        Term::Pi(name, a, b) if name.is_empty() => {
            format!("({} -> {})", pretty(a), pretty(b))
        }
        Term::Pi(name, a, b) => {
            format!("(Pi {} : {} => {})", name, pretty(a), pretty(b))
        }
        Term::Builtin(s) => (*s).to_string(),
        Term::PrimOp(op) => op.to_string(),
        Term::LitBool(b) => b.to_string(),
        Term::Let(name, val, body, mconstr) => {
            let constr_str = match mconstr {
                Some(c) => format!(" : {}", pretty(c)),
                None => String::new(),
            };
            format!(
                "let {}{} = {} in {}",
                name,
                constr_str,
                pretty(val),
                pretty(body)
            )
        }
        Term::IfThenElse(cond, tbranch, fbranch) => {
            format!(
                "if {} then {} else {}",
                pretty(cond),
                pretty(tbranch),
                pretty(fbranch)
            )
        }
        Term::Refine(_name, parent, p) => {
            format!("{} where (x => {})", pretty(parent), pretty(p))
        }
        Term::Annot(inner, c) => {
            format!("({} : {})", pretty(inner), pretty(c))
        }
        Term::ByProof(inner, proof) => {
            format!("({} by {})", pretty(inner), pretty(proof))
        }
        Term::AutoProof => "auto".to_string(),
        Term::RefParam => "x".to_string(),
        Term::This => "this".to_string(),
        Term::ProofBlock(inner) => {
            format!("proof {{ {} }}", pretty(inner))
        }
        Term::Func(name, params, m_ret, preconds, postconds, body) => {
            let params_str = pretty_params(params);
            let ret_str = m_ret
                .map(|r| format!(" : {}", pretty(r)))
                .unwrap_or_default();
            let pre_str: String = preconds
                .iter()
                .map(|p| format!(" pre: {}", pretty(p)))
                .collect();
            let post_str: String = postconds
                .iter()
                .map(|p| format!(" post: {}", pretty(p)))
                .collect();
            format!(
                "func {}({}){}{}{} = {}",
                name,
                params_str,
                ret_str,
                pre_str,
                post_str,
                pretty(body)
            )
        }
    }
}

fn pretty_params(params: &[(Name<'_>, Option<&Term<'_>>)]) -> String {
    params
        .iter()
        .map(|(n, mc)| match mc {
            Some(c) => format!("{} : {}", n, pretty(c)),
            None => (*n).to_string(),
        })
        .collect::<Vec<_>>()
        .join(", ")
}
