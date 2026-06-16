use std::fmt;

/// A name in the AST, arena-allocated for zero-copy sharing.
pub type Name<'bump> = &'bump str;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Universe {
    UData,
    UProp,
    UTheorem,
    UProof,
}

impl fmt::Display for Universe {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Universe::UData => write!(f, "data"),
            Universe::UProp => write!(f, "prop"),
            Universe::UTheorem => write!(f, "theorem"),
            Universe::UProof => write!(f, "proof"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PrimOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod_,
    Eq,
    Lt,
    Gt,
    Le,
    Ge,
    Neq,
}

impl fmt::Display for PrimOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PrimOp::Add => write!(f, "+"),
            PrimOp::Sub => write!(f, "-"),
            PrimOp::Mul => write!(f, "*"),
            PrimOp::Div => write!(f, "/"),
            PrimOp::Mod_ => write!(f, "%"),
            PrimOp::Eq => write!(f, "=="),
            PrimOp::Lt => write!(f, "<"),
            PrimOp::Gt => write!(f, ">"),
            PrimOp::Le => write!(f, "<="),
            PrimOp::Ge => write!(f, ">="),
            PrimOp::Neq => write!(f, "/="),
        }
    }
}

/// The core Term, arena-allocated via bumpalo.
///
/// All recursive positions use `&'bump Term<'bump>` references instead of
/// `Box<Term>`, eliminating per-node heap allocations.  The entire term tree
/// lives in a single bump arena for fast allocation and excellent cache
/// locality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Term<'bump> {
    Var(usize),
    App(&'bump Term<'bump>, &'bump Term<'bump>),
    Lam(&'bump Term<'bump>),
    LitInt(i64),
    LitBool(bool),
    PrimOp(PrimOp),
    Universe(Universe),
    Builtin(Name<'bump>),
    Pi(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Let(
        Name<'bump>,
        &'bump Term<'bump>,
        &'bump Term<'bump>,
        Option<&'bump Term<'bump>>,
    ),
    IfThenElse(&'bump Term<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Refine(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>),
    Annot(&'bump Term<'bump>, &'bump Term<'bump>),
    ByProof(&'bump Term<'bump>, &'bump Term<'bump>),
    AutoProof,
    RefParam,
    This,
    Func(
        Name<'bump>,
        &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        Option<&'bump Term<'bump>>,
        &'bump [Term<'bump>],
        &'bump [Term<'bump>],
        &'bump Term<'bump>,
    ),
    ProofBlock(&'bump Term<'bump>),
}
