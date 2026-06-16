use std::fmt;

pub type Name = String;

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

/// The core Term, using de Bruijn indices for bound variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(usize),
    App(Box<Term>, Box<Term>),
    Lam(Box<Term>),
    LitInt(i64),
    LitBool(bool),
    PrimOp(PrimOp),
    Universe(Universe),
    Builtin(Name),
    Pi(Name, Box<Term>, Box<Term>),
    Let(Name, Box<Term>, Box<Term>, Option<Box<Term>>),
    IfThenElse(Box<Term>, Box<Term>, Box<Term>),
    Refine(Name, Box<Term>, Box<Term>),
    Annot(Box<Term>, Box<Term>),
    ByProof(Box<Term>, Box<Term>),
    AutoProof,
    RefParam,
    This,
    Func(
        Name,
        Vec<(Name, Option<Box<Term>>)>,
        Option<Box<Term>>,
        Vec<Term>,
        Vec<Term>,
        Box<Term>,
    ),
    ProofBlock(Box<Term>),
}
