use super::{ParseError, ParsedDef, Parser, TopLevel};
use crate::core::syntax::Term;
use crate::front::lexer::Token;

impl<'a, 'bump> Parser<'a, 'bump> {
    pub fn parse_program(&mut self) -> Result<Vec<TopLevel<'bump>>, ParseError> {
        let mut tops = Vec::new();
        while !self.is_at_end() {
            tops.push(self.parse_top_level()?);
        }
        Ok(tops)
    }

    pub fn parse_expr_top(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let t = self.parse_expr()?;
        if !self.is_at_end() {
            return Err(ParseError {
                message: "unexpected tokens after expression".into(),
                span: self.current_span(),
            });
        }
        Ok(t)
    }

    pub fn parse_def_top(&mut self) -> Result<ParsedDef<'bump>, ParseError> {
        self.parse_def()
    }

    fn parse_top_level(&mut self) -> Result<TopLevel<'bump>, ParseError> {
        while self.peek_token() == Some(Token::Newline) {
            self.advance();
        }
        let start_span = self.current_span();

        if self.peek_token() == Some(Token::KwTheorem) {
            self.advance();
            let name = self.parse_ident()?;
            let prop = if self.try_expect(&Token::Colon) {
                self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::ColonEq))?
            } else {
                self.arena.builtin(self.pool.intern("data"))
            };
            self.expect(&Token::ColonEq)?;
            let body = self.parse_expr()?;
            return Ok(TopLevel::TLTheorem(name, prop, body, start_span));
        }

        if self.peek_token() == Some(Token::KwDef) {
            let (name, params, m_ret, body) = self.parse_def()?;
            return Ok(TopLevel::TLDef(name, params, m_ret, body, start_span));
        }

        if self.peek_token() == Some(Token::HashCheck) {
            self.advance();
            let split = self.find_check_constraint_colon();
            let (term, constraint) = if let Some(split) = split {
                let term = self.parse_expr_until(|_, i| i == split)?;
                self.expect(&Token::Colon)?;
                (term, self.parse_expr()?)
            } else {
                (
                    self.parse_expr()?,
                    self.arena.builtin(self.pool.intern("data")),
                )
            };
            let (term, constraint) = if let Term::Annot(t, c) = term {
                (*t, *c)
            } else {
                (term, constraint)
            };
            return Ok(TopLevel::TLCheck(term, constraint, start_span));
        }

        if self.peek_token() == Some(Token::HashShow) {
            self.advance();
            return Ok(TopLevel::TLShow(self.parse_expr()?, start_span));
        }

        Ok(TopLevel::TLExpr(self.parse_expr()?, start_span))
    }

    fn find_check_constraint_colon(&self) -> Option<usize> {
        let mut parens = 0usize;
        let mut braces = 0usize;
        let mut last = None;
        let mut i = self.pos;
        while i < self.tokens.len() {
            match self.tokens[i].0 {
                Token::LParen => parens += 1,
                Token::RParen => parens = parens.saturating_sub(1),
                Token::LBrace => braces += 1,
                Token::RBrace => braces = braces.saturating_sub(1),
                Token::KwDef | Token::HashCheck | Token::HashShow | Token::KwTheorem
                    if parens == 0 && braces == 0 =>
                {
                    break;
                }
                Token::Colon if parens == 0 && braces == 0 => last = Some(i),
                _ => {}
            }
            i += 1;
        }
        last
    }
}
