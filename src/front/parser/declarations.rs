use super::{ParseError, ParsedDef, ParsedFuncBody, Parser, SpannedToken};
use crate::core::debruijn::Desugarer;
use crate::core::syntax::{Name, Tactic, Term};
use crate::front::lexer::Token;

impl<'a, 'bump> Parser<'a, 'bump> {
    pub(super) fn parse_def(&mut self) -> Result<ParsedDef<'bump>, ParseError> {
        self.expect(&Token::KwDef)?;
        let name = self.parse_decl_ident()?;
        let (params, m_ret, body) = self.parse_func_body(name)?;
        let params_slice = self.arena.alloc_slice(&params);
        let body = if matches!(body, Term::UnionDef(..) | Term::StructDef(..)) {
            body
        } else {
            self.desugar_def(name, &params, m_ret, body)
        };
        Ok((name, params_slice, m_ret, body))
    }

    pub(super) fn desugar_def(
        &self,
        _name: Name<'bump>,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let names: Vec<_> = params.iter().rev().map(|(pn, _)| *pn).collect();
        let desugarer = Desugarer::new(self.arena);
        let func_body = params
            .iter()
            .rfold(desugarer.desugar_with_names(body, &names), |b, _| {
                self.arena.lam(b)
            });
        let default = self.arena.builtin(self.pool.intern("data"));
        let ret_env = names.clone();
        let ret = m_ret
            .map(|t| desugarer.desugar_with_names(t, &ret_env))
            .unwrap_or(default);
        let func_constraint = params
            .iter()
            .enumerate()
            .rev()
            .fold(ret, |b, (idx, &(pn, mc))| {
                let dom_env: Vec<_> = params[..idx].iter().rev().map(|(n, _)| *n).collect();
                let dom = mc
                    .map(|t| desugarer.desugar_with_names(t, &dom_env))
                    .unwrap_or(default);
                self.arena.pi(pn, dom, b)
            });
        self.arena.annot(func_body, func_constraint)
    }

    pub(super) fn parse_func_body(
        &mut self,
        name: Name<'bump>,
    ) -> Result<ParsedFuncBody<'bump>, ParseError> {
        let params = self.parse_many_curried_params();
        let m_ret = self.parse_constraint_until(|tokens, i| matches!(tokens[i].0, Token::ColonEq));
        self.expect(&Token::ColonEq)?;
        let body_expr = if self.peek_token() == Some(Token::KwUnion) {
            self.parse_union_body(name)?
        } else if self.peek_token() == Some(Token::KwStruct) {
            self.parse_struct_body(name)?
        } else {
            self.parse_expr()?
        };
        Ok((params, m_ret, body_expr))
    }

    fn parse_curried_param(&mut self) -> Option<(Name<'bump>, Option<&'bump Term<'bump>>)> {
        if !self.try_expect(&Token::LParen) {
            return None;
        }
        let pname = match self.parse_decl_ident() {
            Ok(n) => n,
            Err(_) => return None,
        };
        let mconstr = self.parse_constraint_annotation();
        if !self.try_expect(&Token::RParen) {
            return None;
        }
        Some((pname, mconstr))
    }

    fn parse_many_curried_params(&mut self) -> Vec<(Name<'bump>, Option<&'bump Term<'bump>>)> {
        let mut params = Vec::new();
        while let Some(p) = self.parse_curried_param() {
            params.push(p);
        }
        params
    }

    pub(super) fn parse_constraint_annotation(&mut self) -> Option<&'bump Term<'bump>> {
        self.parse_constraint_until(|tokens, i| {
            matches!(tokens[i].0, Token::KwBy | Token::ColonEq | Token::RParen)
        })
    }

    pub(super) fn parse_constraint_until<F>(&mut self, is_delim: F) -> Option<&'bump Term<'bump>>
    where
        F: FnMut(&[SpannedToken], usize) -> bool,
    {
        self.try_parse(Token::Colon, |s| s.parse_expr_until(is_delim))
    }

    pub(super) fn parse_struct_field_constraint(
        &mut self,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_expr_until(Self::is_struct_field_constraint_delim)
    }

    pub(super) fn parse_tactic_arg(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_expr_until(Self::is_tactic_arg_delim)
    }

    pub(super) fn parse_by_proof_clause(&mut self) -> Option<&'bump [Tactic<'bump>]> {
        self.try_parse(Token::KwBy, |s| s.parse_tactics())
    }

    fn parse_union_body(&mut self, name: Name<'bump>) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwUnion)?;
        let mut variants: Vec<(Name<'bump>, Vec<(Name<'bump>, &'bump Term<'bump>)>)> = Vec::new();
        loop {
            if !self.try_expect(&Token::Bar) {
                break;
            }
            let vname = self.parse_ident()?;
            let fields: Vec<(Name<'bump>, &'bump Term<'bump>)> = if self.try_expect(&Token::KwOf) {
                let mut fs = Vec::new();
                loop {
                    if !self.try_expect(&Token::LParen) {
                        break;
                    }
                    let fname = self.parse_ident()?;
                    let fty = if self.try_expect(&Token::Colon) {
                        self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::RParen))?
                    } else {
                        self.arena.builtin(self.pool.intern("data"))
                    };
                    self.expect(&Token::RParen)?;
                    fs.push((fname, fty));
                }
                fs
            } else {
                Vec::new()
            };
            variants.push((vname, fields));
        }
        if variants.is_empty() {
            return Err(ParseError {
                message: "union must have at least one variant".into(),
                span: self.current_span(),
            });
        }
        let variants_slice: Vec<_> = variants
            .into_iter()
            .map(|(vn, fs)| (vn, self.arena.alloc_slice(&fs)))
            .collect();
        Ok(self
            .arena
            .union_def(name, self.arena.alloc_slice(&variants_slice)))
    }

    fn parse_struct_body(&mut self, name: Name<'bump>) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwStruct)?;
        let mut fields: Vec<(Name<'bump>, &'bump Term<'bump>)> = Vec::new();
        loop {
            let saved = self.pos;
            let fname = match self.parse_ident() {
                Ok(n) => n,
                Err(_) => {
                    self.pos = saved;
                    break;
                }
            };
            let fty = if self.try_expect(&Token::Colon) {
                self.parse_struct_field_constraint()?
            } else {
                self.arena.builtin(self.pool.intern("data"))
            };
            fields.push((fname, fty));
        }
        if fields.is_empty() {
            return Err(ParseError {
                message: "struct must have at least one field".into(),
                span: self.current_span(),
            });
        }
        Ok(self.arena.struct_def(name, self.arena.alloc_slice(&fields)))
    }

    pub(super) fn parse_tactics(&mut self) -> Result<&'bump [Tactic<'bump>], ParseError> {
        let mut tactics: Vec<Tactic<'bump>> = Vec::new();
        loop {
            match self.peek() {
                None
                | Some((Token::ColonEq, _))
                | Some((Token::KwIn, _))
                | Some((Token::KwThen, _))
                | Some((Token::KwElse, _))
                | Some((Token::RParen, _))
                | Some((Token::RBrace, _))
                | Some((Token::Colon, _))
                | Some((Token::KwDef, _))
                | Some((Token::HashCheck, _))
                | Some((Token::HashShow, _)) => break,
                _ => {}
            }
            let tactic = self.parse_tactic()?;
            tactics.push(tactic);
            if self.peek_token() == Some(Token::Semi) {
                self.advance();
            }
        }
        if tactics.is_empty() {
            return Err(ParseError {
                message: "Empty proof block".into(),
                span: self.current_span(),
            });
        }
        Ok(self.arena.alloc_slice(&tactics))
    }

    fn parse_tactic(&mut self) -> Result<Tactic<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::KwExact) => {
                self.advance();
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Exact(t))
            }
            Some(Token::KwApply) => {
                self.advance();
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Apply(t))
            }
            Some(Token::KwIntro) => {
                self.advance();
                let name = if let Some(Token::Ident(_)) = self.peek_token() {
                    Some(self.parse_ident()?)
                } else {
                    None
                };
                Ok(Tactic::Intro(name))
            }
            Some(Token::KwHave) => {
                self.advance();
                let name = self.parse_ident()?;
                self.expect(&Token::ColonEq)?;
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Have(name, t))
            }
            _ => {
                let t = self.parse_tactic_arg()?;
                Ok(Tactic::Exact(t))
            }
        }
    }
}
