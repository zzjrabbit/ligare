use crate::config::BUILTIN_DATA;
use crate::core::pool::TermArena;
use crate::core::syntax::{FuncDef, Term};

pub struct Desugarer<'bump> {
    arena: &'bump TermArena<'bump>,
}

impl<'bump> Desugarer<'bump> {
    pub fn new(arena: &'bump TermArena<'bump>) -> Self {
        Self { arena }
    }
    pub fn arena(&self) -> &'bump TermArena<'bump> {
        self.arena
    }

    pub fn desugar(&self, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
        t
    }

    pub fn desugar_func_def(&self, func_def: &FuncDef<'bump>) -> &'bump Term<'bump> {
        let FuncDef {
            name: _name,
            params,
            ret: m_ret,
            body,
        } = *func_def;
        let func_body = params.iter().fold(body, |b, _| self.arena.lam(b));
        let default = self.arena.builtin(self.arena.alloc_str(BUILTIN_DATA));
        let func_type = params
            .iter()
            .rfold(m_ret.unwrap_or(default), |b, (pn, mc)| {
                self.arena.pi(pn, mc.unwrap_or(default), b)
            });
        self.arena.annot(func_body, func_type)
    }
}

pub fn desugar<'bump>(arena: &'bump TermArena<'bump>, t: &'bump Term<'bump>) -> &'bump Term<'bump> {
    Desugarer::new(arena).desugar(t)
}

pub fn desugar_func_def<'bump>(
    arena: &'bump TermArena<'bump>,
    func_def: &FuncDef<'bump>,
) -> &'bump Term<'bump> {
    Desugarer::new(arena).desugar_func_def(func_def)
}
