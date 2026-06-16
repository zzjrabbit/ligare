use std::collections::HashMap;
use std::sync::LazyLock;

use crate::core::syntax::{Term, Universe};

pub type BuiltinChecker = fn(&Term<'_>) -> Result<(), String>;

pub struct BuiltinEntry {
    pub universe: Universe,
    pub checker: BuiltinChecker,
}

fn check_int(t: &Term<'_>) -> Result<(), String> {
    if matches!(t, Term::LitInt(_)) {
        Ok(())
    } else {
        Err("Expected an integer".to_string())
    }
}

fn check_bool(t: &Term<'_>) -> Result<(), String> {
    if matches!(t, Term::LitBool(_)) {
        Ok(())
    } else {
        Err("Expected a boolean".to_string())
    }
}

fn check_any(_t: &Term<'_>) -> Result<(), String> {
    Ok(())
}

/// Statically initialized builtin table via LazyLock, avoiding
/// repeated heap allocation on every lookup.
static BUILTINS: LazyLock<HashMap<&'static str, BuiltinEntry>> = LazyLock::new(|| {
    HashMap::from([
        (
            "int",
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_int,
            },
        ),
        (
            "bool",
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_bool,
            },
        ),
        (
            "data",
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            "theorem",
            BuiltinEntry {
                universe: Universe::UTheorem,
                checker: check_any,
            },
        ),
        (
            "proof",
            BuiltinEntry {
                universe: Universe::UProof,
                checker: check_any,
            },
        ),
        (
            "and",
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            "or",
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            "not",
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
        (
            "implies",
            BuiltinEntry {
                universe: Universe::UProp,
                checker: check_any,
            },
        ),
    ])
});

pub fn classify_builtin(name: &str) -> Option<Universe> {
    BUILTINS.get(name).map(|e| e.universe)
}

pub fn check_builtin(name: &str) -> Option<BuiltinChecker> {
    BUILTINS.get(name).map(|e| e.checker)
}
