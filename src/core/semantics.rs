//! Shared semantic queries over terms.

use crate::checker::builtin::BuiltinRegistry;
use crate::checker::context::Context;
use crate::core::classify::classify;
use crate::core::syntax::{Term, Universe};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ConstraintKind {
    DataTop,
    TypeUniverse,
    BuiltinDataType,
    Refine,
    Pi,
    UnionType,
    StructType,
    LogicalOp,
    Unknown,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErasePolicy {
    KeepData,
    EraseToUnit,
    EraseToParent,
}

#[derive(Debug, Clone, Copy)]
pub struct SemanticQueries<'a> {
    builtins: &'a BuiltinRegistry,
}

impl<'a> SemanticQueries<'a> {
    pub fn new(builtins: &'a BuiltinRegistry) -> Self {
        Self { builtins }
    }

    pub fn universe(&self, ctx: &Context<'_>, term: &Term<'_>) -> Option<Universe> {
        classify(self.builtins, ctx, term)
    }

    pub fn constraint_kind(&self, term: &Term<'_>) -> ConstraintKind {
        match term {
            Term::Builtin(name) | Term::Named(name) if *name == "data" => ConstraintKind::DataTop,
            Term::Builtin(name) | Term::Named(name)
                if matches!(*name, "prop" | "theorem" | "proof") =>
            {
                ConstraintKind::TypeUniverse
            }
            Term::Universe(Universe::UData) => ConstraintKind::DataTop,
            Term::Universe(_) => ConstraintKind::TypeUniverse,
            Term::Builtin(name) | Term::Named(name) if matches!(*name, "int" | "bool" | "str") => {
                ConstraintKind::BuiltinDataType
            }
            Term::Builtin(name) | Term::Named(name) if matches!(*name, "and" | "or" | "not") => {
                ConstraintKind::LogicalOp
            }
            Term::Refine(..) => ConstraintKind::Refine,
            Term::Pi(..) => ConstraintKind::Pi,
            Term::UnionDef(..) => ConstraintKind::UnionType,
            Term::StructDef(..) => ConstraintKind::StructType,
            _ => ConstraintKind::Unknown,
        }
    }

    pub fn is_type_universe(&self, term: &Term<'_>) -> bool {
        matches!(
            self.constraint_kind(term),
            ConstraintKind::DataTop | ConstraintKind::TypeUniverse
        )
    }

    pub fn is_type_parameter_constraint(&self, term: &Term<'_>) -> bool {
        self.is_type_universe(term)
    }

    pub fn erase_policy(&self, term: &Term<'_>) -> ErasePolicy {
        match term {
            Term::Refine(..) => ErasePolicy::EraseToParent,
            Term::Annot(inner, _) | Term::ByProof(Some(inner), _) => self.erase_policy(inner),
            Term::App(f, _) => self.data_policy(f),
            Term::Builtin(_) | Term::Named(_) => self.data_policy(term),
            Term::ByProof(None, _)
            | Term::AutoProof
            | Term::Pi(..)
            | Term::Universe(Universe::UProp | Universe::UTheorem | Universe::UProof)
            | Term::UnionDef(..)
            | Term::StructDef(..) => ErasePolicy::EraseToUnit,
            _ => ErasePolicy::KeepData,
        }
    }

    fn data_policy(&self, term: &Term<'_>) -> ErasePolicy {
        if self.universe(&Context::empty(), term) == Some(Universe::UData) {
            ErasePolicy::KeepData
        } else {
            ErasePolicy::EraseToUnit
        }
    }
}
