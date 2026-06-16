use crate::core::debruijn::{shift, subst};
use crate::core::syntax::{Name, Term, Universe};

#[allow(dead_code)]
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CtxEntry {
    pub name: Name,
    pub constraint: Term,
    pub theorems: Vec<Term>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Context {
    entries: Vec<CtxEntry>,
}

impl Context {
    pub fn empty() -> Self {
        Self { entries: vec![] }
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }

    pub fn iter(&self) -> impl Iterator<Item = &CtxEntry> {
        self.entries.iter()
    }

    pub fn lookup(&self, i: usize) -> Option<Term> {
        self.entries.get(i).map(|e| e.constraint.clone())
    }

    pub fn lookup_name(&self, name: &str) -> Option<&CtxEntry> {
        self.entries.iter().find(|e| e.name == name)
    }

    pub fn extend(&self, name: Name, constraint: Term) -> Self {
        let mut entries = self.entries.clone();
        entries.insert(
            0,
            CtxEntry {
                name,
                constraint,
                theorems: vec![],
            },
        );
        Self { entries }
    }

    pub fn extend_term(&self, constraint: Term) -> Self {
        self.extend("_".to_string(), constraint)
    }

    pub fn add_theorem(&self, name: &str, thm: Term) -> Self {
        let entries: Vec<CtxEntry> = self
            .entries
            .iter()
            .map(|e| {
                if e.name == name {
                    let mut new_thms = e.theorems.clone();
                    new_thms.insert(0, thm.clone());
                    CtxEntry {
                        name: e.name.clone(),
                        constraint: e.constraint.clone(),
                        theorems: new_thms,
                    }
                } else {
                    e.clone()
                }
            })
            .collect();
        Self { entries }
    }
}

pub fn empty_ctx() -> Context {
    Context::empty()
}

pub fn extend_ctx(name: Name, constraint: Term, ctx: &Context) -> Context {
    ctx.extend(name, constraint)
}

pub fn extend_ctx_term(constraint: Term, ctx: &Context) -> Context {
    ctx.extend_term(constraint)
}

pub fn add_theorem(name: &str, thm: Term, ctx: &Context) -> Context {
    ctx.add_theorem(name, thm)
}

// ---- Constraint Table ----

pub type ConstraintTable = Vec<(Name, Term, Term)>;

pub fn empty_table() -> ConstraintTable {
    vec![]
}

pub fn add_refine(name: Name, parent: Term, p: Term, table: &ConstraintTable) -> ConstraintTable {
    let mut t = table.clone();
    t.insert(0, (name, parent, p));
    t
}

pub fn lookup_refine(name: &str, table: &ConstraintTable) -> Option<(Term, Term)> {
    table
        .iter()
        .find(|(n, _, _)| n == name)
        .map(|(_, p, pred)| (p.clone(), pred.clone()))
}

/// Expand a constraint: replace RefParam with arg.
pub fn expand_constraint(table: &ConstraintTable, constraint: &Term) -> Option<Term> {
    match constraint {
        Term::App(builtin, arg) => {
            if let Term::Builtin(name) = builtin.as_ref() {
                if let Some((parent, body)) = lookup_refine(name, table) {
                    if matches!(parent, Term::Universe(Universe::UData)) {
                        let body_shifted = shift_param(1, &body);
                        let instantiated = subst(arg, 0, &body_shifted);
                        let reduced = shift_param(-1, &instantiated);
                        return Some(reduced);
                    }
                }
            }
            None
        }
        _ => None,
    }
}

/// Shift that preserves RefParam.
pub fn shift_param(d: i32, t: &Term) -> Term {
    shift_param_cutoff(d, 0, t)
}

fn shift_param_cutoff(d: i32, cutoff: i32, t: &Term) -> Term {
    match t {
        Term::RefParam => Term::RefParam,
        Term::Var(i) => {
            if (*i as i32) >= cutoff {
                Term::Var((*i as i32 + d) as usize)
            } else {
                Term::Var(*i)
            }
        }
        other => shift(d, cutoff, other),
    }
}
