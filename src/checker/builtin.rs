#![allow(dead_code)]

use std::collections::HashMap;

use crate::core::syntax::{Term, Universe};

pub type BuiltinChecker = fn(&Term) -> Result<(), String>;

pub struct BuiltinEntry {
    pub universe: Universe,
    pub checker: BuiltinChecker,
}

fn check_int(t: &Term) -> Result<(), String> {
    match t {
        Term::LitInt(_) => Ok(()),
        _ => Err("Expected an integer".to_string()),
    }
}

fn check_bool(t: &Term) -> Result<(), String> {
    match t {
        Term::LitBool(_) => Ok(()),
        _ => Err("Expected a boolean".to_string()),
    }
}

fn check_any(_t: &Term) -> Result<(), String> {
    Ok(())
}

fn builtins() -> HashMap<String, BuiltinEntry> {
    let mut m = HashMap::new();
    m.insert(
        "int".to_string(),
        BuiltinEntry {
            universe: Universe::UProp,
            checker: check_int,
        },
    );
    m.insert(
        "bool".to_string(),
        BuiltinEntry {
            universe: Universe::UProp,
            checker: check_bool,
        },
    );
    m.insert(
        "data".to_string(),
        BuiltinEntry {
            universe: Universe::UProp,
            checker: check_any,
        },
    );
    m.insert(
        "theorem".to_string(),
        BuiltinEntry {
            universe: Universe::UTheorem,
            checker: check_any,
        },
    );
    m.insert(
        "proof".to_string(),
        BuiltinEntry {
            universe: Universe::UProof,
            checker: check_any,
        },
    );
    m.insert(
        "and".to_string(),
        BuiltinEntry {
            universe: Universe::UProp,
            checker: check_any,
        },
    );
    m.insert(
        "or".to_string(),
        BuiltinEntry {
            universe: Universe::UProp,
            checker: check_any,
        },
    );
    m.insert(
        "not".to_string(),
        BuiltinEntry {
            universe: Universe::UProp,
            checker: check_any,
        },
    );
    m.insert(
        "implies".to_string(),
        BuiltinEntry {
            universe: Universe::UProp,
            checker: check_any,
        },
    );
    m
}

pub fn classify_builtin(name: &str) -> Option<Universe> {
    builtins().get(name).map(|e| e.universe)
}

pub fn check_builtin(name: &str) -> Option<BuiltinChecker> {
    builtins().get(name).map(|e| e.checker)
}
