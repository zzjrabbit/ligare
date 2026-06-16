#[allow(dead_code)]
use logos::Logos;

use bumpalo::Bump;

use crate::core::pool::StringPool;
use crate::core::syntax::{Name, PrimOp, Term};
use crate::front::lexer::Token;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopLevel {
    TLDef(Name, Term),
    TLCheck(Term, Term),
    TLExpr(Term),
}

const KEYWORDS: &[&str] = &[
    "let", "in", "if", "then", "else", "true", "false", "by", "func", "where", "def", "auto",
];

type SpannedToken = (Token, std::ops::Range<usize>);

pub struct Parser<'a> {
    tokens: &'a [SpannedToken],
    pos: usize,
    pool: &'a StringPool<'a>,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: std::ops::Range<usize>,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} at {}..{}",
            self.message, self.span.start, self.span.end
        )
    }
}

impl std::error::Error for ParseError {}

impl<'a> Parser<'a> {
    pub fn new(tokens: &'a [SpannedToken], pool: &'a StringPool<'a>) -> Self {
        Self {
            tokens,
            pos: 0,
            pool,
        }
    }

    fn peek(&self) -> Option<&SpannedToken> {
        self.tokens.get(self.pos)
    }

    fn peek_token(&self) -> Option<Token> {
        self.peek().map(|(t, _)| t.clone())
    }

    fn advance(&mut self) {
        self.pos += 1;
    }

    fn expect(&mut self, expected: Token) -> Result<(), ParseError> {
        match self.peek() {
            Some((t, span)) if *t == expected => {
                self.pos += 1;
                Ok(())
            }
            Some((t, span)) => Err(ParseError {
                message: format!("expected {:?}, found {:?}", expected, t),
                span: span.clone(),
            }),
            None => Err(ParseError {
                message: format!("expected {:?}, found EOF", expected),
                span: 0..0,
            }),
        }
    }

    fn try_expect(&mut self, expected: &Token) -> bool {
        match self.peek() {
            Some((t, _)) if t == expected => {
                self.pos += 1;
                true
            }
            _ => false,
        }
    }

    fn is_at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    // ---- Top Level ----

    pub fn parse_program(&mut self) -> Result<Vec<TopLevel>, ParseError> {
        let mut tops = Vec::new();
        while !self.is_at_end() {
            tops.push(self.parse_top_level()?);
        }
        Ok(tops)
    }

    pub fn parse_expr_top(&mut self) -> Result<Term, ParseError> {
        let t = self.parse_expr(&[])?;
        if !self.is_at_end() {
            let (_, span) = self.peek().unwrap();
            return Err(ParseError {
                message: "unexpected token after expression".into(),
                span: span.clone(),
            });
        }
        Ok(t)
    }

    pub fn parse_def_top(&mut self) -> Result<(Name, Term), ParseError> {
        let d = self.parse_def()?;
        if !self.is_at_end() {
            let (_, span) = self.peek().unwrap();
            return Err(ParseError {
                message: "unexpected token after definition".into(),
                span: span.clone(),
            });
        }
        Ok(d)
    }

    fn parse_top_level(&mut self) -> Result<TopLevel, ParseError> {
        match self.peek_token() {
            Some(Token::HashCheck) => {
                self.advance();
                let term = self.parse_expr_no_annot(&[])?;
                self.expect(Token::Colon)?;
                let constraint = self.parse_expr(&[])?;
                Ok(TopLevel::TLCheck(term, constraint))
            }
            Some(Token::KwDef) => {
                let (name, term) = self.parse_def()?;
                Ok(TopLevel::TLDef(name, term))
            }
            _ => {
                let expr = self.parse_expr(&[])?;
                Ok(TopLevel::TLExpr(expr))
            }
        }
    }

    // ---- Expressions (no annotation) for #check ----

    fn parse_expr_no_annot(&mut self, env: &[String]) -> Result<Term, ParseError> {
        self.parse_if_expr(env)
            .or_else(|_| self.parse_operators(env, true))
    }

    fn parse_app_no_annot(&mut self, env: &[String]) -> Result<Term, ParseError> {
        self.parse_let_expr(env)
            .or_else(|_| self.parse_func_expr(env))
            .or_else(|_| self.parse_dep_arrow_expr())
            .or_else(|_| {
                let t1 = self.parse_term_no_annot(env)?;
                let mut ts = Vec::new();
                while let Ok(t) = self.parse_term_no_annot(env) {
                    ts.push(t);
                }
                let mut result = t1;
                for t in ts {
                    result = Term::App(Box::new(result), Box::new(t));
                }
                Ok(result)
            })
    }

    fn parse_term_no_annot(&mut self, env: &[String]) -> Result<Term, ParseError> {
        let t = self.parse_atom(env)?;
        self.parse_refine_only(t)
    }

    fn parse_refine_only(&mut self, t: Term) -> Result<Term, ParseError> {
        match self.try_parse_refine_suffix(t.clone()) {
            Ok(t2) => self.parse_refine_only(t2),
            Err(_) => Ok(t),
        }
    }

    // ---- Definitions ----

    fn parse_def(&mut self) -> Result<(Name, Term), ParseError> {
        self.expect(Token::KwDef)?;
        let name = self.parse_ident()?;
        let params = self.parse_many_curried_params();
        let m_ret = self.parse_type_annotation(&[]);
        self.expect(Token::ColonEq)?;

        let param_names: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        let env: Vec<String> = param_names.iter().rev().cloned().collect();
        let body = self.parse_expr(&env)?;
        let body = subst_this(&name, body);

        let func_body = params.iter().fold(body, |b, _| Term::Lam(Box::new(b)));
        let result = match m_ret {
            Some(c) => Term::Annot(Box::new(func_body), Box::new(c)),
            None => func_body,
        };
        Ok((name, result))
    }

    fn parse_curried_param(&mut self) -> Option<(String, Option<Term>)> {
        if !self.try_expect(&Token::LParen) {
            return None;
        }
        let pname = match self.parse_ident() {
            Ok(n) => n,
            Err(_) => return None,
        };
        let mconstr = self.parse_type_annotation(&[]);
        if !self.try_expect(&Token::RParen) {
            return None;
        }
        Some((pname, mconstr))
    }

    fn parse_many_curried_params(&mut self) -> Vec<(String, Option<Term>)> {
        let mut params = Vec::new();
        while let Some(p) = self.parse_curried_param() {
            params.push(p);
        }
        params
    }

    // ---- Expressions ----

    fn parse_expr(&mut self, env: &[String]) -> Result<Term, ParseError> {
        self.parse_if_expr(env)
            .or_else(|_| self.parse_operators(env, false))
    }

    fn parse_if_expr(&mut self, env: &[String]) -> Result<Term, ParseError> {
        if !self.try_expect(&Token::KwIf) {
            return Err(ParseError {
                message: "not an if expression".into(),
                span: 0..0,
            });
        }
        let cond = self.parse_expr(env)?;
        self.expect(Token::KwThen)?;
        let tbranch = self.parse_expr(env)?;
        self.expect(Token::KwElse)?;
        let fbranch = self.parse_expr(env)?;
        Ok(Term::IfThenElse(
            Box::new(cond),
            Box::new(tbranch),
            Box::new(fbranch),
        ))
    }

    fn parse_operators(&mut self, env: &[String], no_annot: bool) -> Result<Term, ParseError> {
        let app = if no_annot {
            self.parse_app_no_annot(env)?
        } else {
            self.parse_app(env)?
        };
        self.parse_binop_rhs(env, app, 0, no_annot)
    }

    fn parse_app(&mut self, env: &[String]) -> Result<Term, ParseError> {
        self.parse_let_expr(env)
            .or_else(|_| self.parse_func_expr(env))
            .or_else(|_| self.parse_dep_arrow_expr())
            .or_else(|_| {
                let t1 = self.parse_term(env)?;
                let mut ts = Vec::new();
                while let Ok(t) = self.parse_term(env) {
                    ts.push(t);
                }
                let mut result = t1;
                for t in ts {
                    result = Term::App(Box::new(result), Box::new(t));
                }
                Ok(result)
            })
    }

    // ---- Let ----

    fn parse_let_expr(&mut self, env: &[String]) -> Result<Term, ParseError> {
        if !self.try_expect(&Token::KwLet) {
            return Err(ParseError {
                message: "not a let expression".into(),
                span: 0..0,
            });
        }
        let name = self.parse_ident()?;
        let m_constraint = self.parse_type_annotation(env);
        let m_proof = self.parse_by_proof_clause(env);
        self.expect(Token::ColonEq)?;
        let val = self.parse_expr(env)?;
        let val = match m_proof {
            Some(p) => Term::ByProof(Box::new(val), Box::new(p)),
            None => val,
        };
        self.expect(Token::KwIn)?;
        let mut extended_env: Vec<String> = vec![name.clone()];
        extended_env.extend_from_slice(env);
        let body = self.parse_expr(&extended_env)?;
        Ok(Term::Let(
            name,
            Box::new(val),
            Box::new(body),
            m_constraint.map(Box::new),
        ))
    }

    fn parse_type_annotation(&mut self, env: &[String]) -> Option<Term> {
        if self.peek_token() == Some(Token::Colon) {
            let saved = self.pos;
            self.advance();
            match self.parse_expr(env) {
                Ok(t) => Some(t),
                Err(_) => {
                    self.pos = saved;
                    None
                }
            }
        } else {
            None
        }
    }

    fn parse_by_proof_clause(&mut self, env: &[String]) -> Option<Term> {
        if self.peek_token() == Some(Token::KwBy) {
            let saved = self.pos;
            self.advance();
            match self.parse_term(env) {
                Ok(t) => Some(t),
                Err(_) => {
                    self.pos = saved;
                    None
                }
            }
        } else {
            None
        }
    }

    // ---- Func ----

    fn parse_func_expr(&mut self, env: &[String]) -> Result<Term, ParseError> {
        if !self.try_expect(&Token::KwFunc) {
            return Err(ParseError {
                message: "not a func expression".into(),
                span: 0..0,
            });
        }
        let fname = self.parse_ident()?;
        let params = self.parse_many_curried_params();
        let m_ret = self.parse_type_annotation(env);
        self.expect(Token::ColonEq)?;

        let param_names: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
        let mut extended_env: Vec<String> = param_names.iter().rev().cloned().collect();
        extended_env.extend_from_slice(env);
        let body = self.parse_expr(&extended_env)?;
        let body = subst_this(&fname, body);

        let boxed_params: Vec<(String, Option<Box<Term>>)> = params
            .into_iter()
            .map(|(n, mc)| (n, mc.map(Box::new)))
            .collect();
        Ok(Term::Func(
            fname,
            boxed_params,
            m_ret.map(Box::new),
            vec![],
            vec![],
            Box::new(body),
        ))
    }

    // ---- Dependent arrow: (x : A) -> B ----

    fn parse_dep_arrow_expr(&mut self) -> Result<Term, ParseError> {
        let saved = self.pos;
        if !self.try_expect(&Token::LParen) {
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        let x = match self.parse_ident() {
            Ok(n) => n,
            Err(_) => {
                self.pos = saved;
                return Err(ParseError {
                    message: "not a dep arrow".into(),
                    span: 0..0,
                });
            }
        };
        if !self.try_expect(&Token::Colon) {
            self.pos = saved;
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        let a = match self.parse_expr(&[]) {
            Ok(t) => t,
            Err(_) => {
                self.pos = saved;
                return Err(ParseError {
                    message: "not a dep arrow".into(),
                    span: 0..0,
                });
            }
        };
        if !self.try_expect(&Token::RParen) {
            self.pos = saved;
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        if !self.try_expect(&Token::ThinArrow) {
            self.pos = saved;
            return Err(ParseError {
                message: "not a dep arrow".into(),
                span: 0..0,
            });
        }
        let b = self.parse_expr(&[x.clone()])?;
        Ok(Term::Pi(x, Box::new(a), Box::new(b)))
    }

    // ---- Term ----

    fn parse_term(&mut self, env: &[String]) -> Result<Term, ParseError> {
        let t = self.parse_atom(env)?;
        self.parse_suffixes(env, t)
    }

    fn parse_suffixes(&mut self, env: &[String], t: Term) -> Result<Term, ParseError> {
        match self.try_parse_refine_suffix(t.clone()) {
            Ok(t2) => self.parse_suffixes(env, t2),
            Err(_) => {
                if self.peek_token() == Some(Token::Colon) {
                    let saved = self.pos;
                    self.advance();
                    match self.parse_expr(env) {
                        Ok(c) => self.parse_suffixes(env, Term::Annot(Box::new(t), Box::new(c))),
                        Err(_) => {
                            self.pos = saved;
                            Ok(t)
                        }
                    }
                } else {
                    Ok(t)
                }
            }
        }
    }

    // ---- Atom ----

    fn parse_atom(&mut self, env: &[String]) -> Result<Term, ParseError> {
        match self.peek_token() {
            Some(Token::IntLit(n)) => {
                self.advance();
                Ok(Term::LitInt(n))
            }
            Some(Token::True) => {
                self.advance();
                Ok(Term::LitBool(true))
            }
            Some(Token::False) => {
                self.advance();
                Ok(Term::LitBool(false))
            }
            Some(Token::AndIntro) => {
                self.advance();
                Ok(Term::Builtin("∧-intro".to_string()))
            }
            Some(Token::AndElimLeft) => {
                self.advance();
                Ok(Term::Builtin("∧-elim-left".to_string()))
            }
            Some(Token::And) => {
                self.advance();
                Ok(Term::Builtin("and".to_string()))
            }
            Some(Token::Or) => {
                self.advance();
                Ok(Term::Builtin("or".to_string()))
            }
            Some(Token::Not) => {
                self.advance();
                Ok(Term::Builtin("not".to_string()))
            }
            Some(Token::Implies) => {
                self.advance();
                Ok(Term::Builtin("implies".to_string()))
            }
            Some(Token::KwAuto) => {
                self.advance();
                Ok(Term::AutoProof)
            }
            Some(Token::Ident(_)) => Ok(self.parse_var(env)?),
            Some(Token::Backslash) | Some(Token::Lambda) => Ok(self.parse_lam(env)?),
            Some(Token::Minus) => {
                self.advance();
                let t = self.parse_atom(env)?;
                Ok(Term::App(
                    Box::new(Term::App(
                        Box::new(Term::PrimOp(PrimOp::Sub)),
                        Box::new(Term::LitInt(0)),
                    )),
                    Box::new(t),
                ))
            }
            Some(Token::LParen) => Ok(self.parse_parens(env)?),
            Some(Token::LBrace) => {
                self.advance();
                let t = self.parse_expr(env)?;
                self.expect(Token::RBrace)?;
                Ok(Term::ProofBlock(Box::new(t)))
            }
            Some(tok) => {
                let span = self.peek().map(|(_, s)| s.clone()).unwrap_or(0..0);
                Err(ParseError {
                    message: format!("unexpected token {:?}", tok),
                    span,
                })
            }
            None => Err(ParseError {
                message: "unexpected EOF".into(),
                span: 0..0,
            }),
        }
    }

    fn parse_var(&mut self, env: &[String]) -> Result<Term, ParseError> {
        let name = self.parse_ident()?;
        if let Some(i) = env.iter().position(|n| n == &name) {
            Ok(Term::Var(i))
        } else if KEYWORDS.contains(&name.as_str()) {
            Err(ParseError {
                message: format!("keyword '{}' cannot be used as identifier", name),
                span: 0..0,
            })
        } else {
            Ok(Term::Builtin(name))
        }
    }

    fn parse_ident(&mut self) -> Result<String, ParseError> {
        match self.peek() {
            Some((Token::Ident(name), _)) => {
                let interned = self.pool.intern(name);
                self.advance();
                Ok(interned.to_string())
            }
            Some((t, span)) => Err(ParseError {
                message: format!("expected identifier, found {:?}", t),
                span: span.clone(),
            }),
            None => Err(ParseError {
                message: "expected identifier, found EOF".into(),
                span: 0..0,
            }),
        }
    }

    fn parse_lam(&mut self, env: &[String]) -> Result<Term, ParseError> {
        match self.peek_token() {
            Some(Token::Backslash) | Some(Token::Lambda) => self.advance(),
            _ => {
                return Err(ParseError {
                    message: "expected lambda".into(),
                    span: 0..0,
                });
            }
        };
        let x = self.parse_ident()?;
        self.expect(Token::Dot)?;
        let mut extended_env: Vec<String> = vec![x];
        extended_env.extend_from_slice(env);
        let body = self.parse_expr(&extended_env)?;
        Ok(Term::Lam(Box::new(body)))
    }

    fn parse_parens(&mut self, env: &[String]) -> Result<Term, ParseError> {
        self.expect(Token::LParen)?;
        let t = self.parse_expr(env)?;
        self.expect(Token::RParen)?;
        Ok(t)
    }

    // ---- Refinement ----

    fn try_parse_refine_suffix(&mut self, parent: Term) -> Result<Term, ParseError> {
        if !self.try_expect(&Token::KwWhere) {
            return Err(ParseError {
                message: "not a refinement".into(),
                span: 0..0,
            });
        }
        self.expect(Token::LParen)?;
        let param_name = self.parse_ident()?;
        self.expect(Token::FatArrow)?;
        let predicate = self.parse_expr(&[param_name])?;
        self.expect(Token::RParen)?;
        Ok(Term::Refine(
            String::new(),
            Box::new(parent),
            Box::new(replace_var_zero(predicate)),
        ))
    }

    // ---- Operator precedence (Pratt-style) ----

    fn token_precedence(tok: &Token) -> Option<(i32, Associativity)> {
        match tok {
            Token::Star | Token::Slash | Token::Percent => Some((4, Associativity::Left)),
            Token::ThinArrow => Some((3, Associativity::Right)),
            Token::Plus | Token::Minus => Some((2, Associativity::Left)),
            Token::Eq
            | Token::Le
            | Token::Ge
            | Token::Neq
            | Token::Lt
            | Token::Gt
            | Token::EqEq => Some((1, Associativity::None)),
            _ => None,
        }
    }

    fn parse_binop_rhs(
        &mut self,
        env: &[String],
        mut lhs: Term,
        min_prec: i32,
        no_annot: bool,
    ) -> Result<Term, ParseError> {
        loop {
            let tok = match self.peek_token() {
                Some(t) => t,
                None => break,
            };
            let (prec, assoc) = match Self::token_precedence(&tok) {
                Some(p) => p,
                None => break,
            };
            if prec < min_prec {
                break;
            }
            let next_min = match assoc {
                Associativity::Left => prec + 1,
                Associativity::Right => prec,
                Associativity::None => prec + 1,
            };

            // Handle arrow separately (different AST node)
            if tok == Token::ThinArrow {
                self.advance();
                let rhs_atom = self.parse_app_any(env, no_annot)?;
                let rhs = self.parse_binop_rhs(env, rhs_atom, next_min, no_annot)?;
                return Ok(Term::Pi(String::new(), Box::new(lhs), Box::new(rhs)));
            }

            // Guard / against /=
            if tok == Token::Slash && self.peek_ahead_is(&Token::Eq) {
                break;
            }

            self.advance();
            let op = match &tok {
                Token::Star => PrimOp::Mul,
                Token::Slash => PrimOp::Div,
                Token::Percent => PrimOp::Mod_,
                Token::Plus => PrimOp::Add,
                Token::Minus => PrimOp::Sub,
                Token::Eq | Token::EqEq => PrimOp::Eq,
                Token::Le => PrimOp::Le,
                Token::Ge => PrimOp::Ge,
                Token::Neq => PrimOp::Neq,
                Token::Lt => PrimOp::Lt,
                Token::Gt => PrimOp::Gt,
                _ => unreachable!(),
            };

            let rhs_atom = self.parse_app_any(env, no_annot)?;
            let rhs = self.parse_binop_rhs(env, rhs_atom, next_min, no_annot)?;
            lhs = Term::App(
                Box::new(Term::App(Box::new(Term::PrimOp(op)), Box::new(lhs))),
                Box::new(rhs),
            );
        }
        Ok(lhs)
    }

    fn parse_app_any(&mut self, env: &[String], no_annot: bool) -> Result<Term, ParseError> {
        if no_annot {
            self.parse_app_no_annot(env)
        } else {
            self.parse_app(env)
        }
    }

    fn peek_ahead_is(&self, tok: &Token) -> bool {
        self.tokens
            .get(self.pos + 1)
            .map(|(t, _)| t == tok)
            .unwrap_or(false)
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
    Left,
    Right,
    None,
}

// ---- Helper functions ----

pub fn replace_var_zero(term: Term) -> Term {
    match term {
        Term::Var(0) => Term::RefParam,
        Term::App(f, a) => Term::App(
            Box::new(replace_var_zero(*f)),
            Box::new(replace_var_zero(*a)),
        ),
        Term::Lam(b) => Term::Lam(Box::new(replace_var_zero(*b))),
        Term::Let(n, v, b, mc) => Term::Let(
            n,
            Box::new(replace_var_zero(*v)),
            Box::new(replace_var_zero(*b)),
            mc.map(|c| Box::new(replace_var_zero(*c))),
        ),
        Term::IfThenElse(c, t, f) => Term::IfThenElse(
            Box::new(replace_var_zero(*c)),
            Box::new(replace_var_zero(*t)),
            Box::new(replace_var_zero(*f)),
        ),
        Term::Annot(t, c) => Term::Annot(
            Box::new(replace_var_zero(*t)),
            Box::new(replace_var_zero(*c)),
        ),
        Term::ByProof(t, p) => Term::ByProof(
            Box::new(replace_var_zero(*t)),
            Box::new(replace_var_zero(*p)),
        ),
        other => other,
    }
}

pub fn subst_this(name: &str, term: Term) -> Term {
    match term {
        Term::Builtin(n) if n == name => Term::This,
        Term::App(f, a) => Term::App(
            Box::new(subst_this(name, *f)),
            Box::new(subst_this(name, *a)),
        ),
        Term::Lam(b) => Term::Lam(Box::new(subst_this(name, *b))),
        Term::Pi(x, a, b) => Term::Pi(
            x,
            Box::new(subst_this(name, *a)),
            Box::new(subst_this(name, *b)),
        ),
        Term::Let(x, v, b, mc) => Term::Let(
            x,
            Box::new(subst_this(name, *v)),
            Box::new(subst_this(name, *b)),
            mc.map(|c| Box::new(subst_this(name, *c))),
        ),
        Term::IfThenElse(c, t, f) => Term::IfThenElse(
            Box::new(subst_this(name, *c)),
            Box::new(subst_this(name, *t)),
            Box::new(subst_this(name, *f)),
        ),
        Term::Annot(t, c) => Term::Annot(
            Box::new(subst_this(name, *t)),
            Box::new(subst_this(name, *c)),
        ),
        Term::ByProof(t, p) => Term::ByProof(
            Box::new(subst_this(name, *t)),
            Box::new(subst_this(name, *p)),
        ),
        Term::Refine(n, par, p) => Term::Refine(
            n,
            Box::new(subst_this(name, *par)),
            Box::new(subst_this(name, *p)),
        ),
        Term::Func(fn_name, params, m_ret, pre, post, body) => Term::Func(
            fn_name,
            params
                .into_iter()
                .map(|(n, mc)| (n, mc.map(|c| Box::new(subst_this(name, *c)))))
                .collect(),
            m_ret.map(|c| Box::new(subst_this(name, *c))),
            pre.into_iter().map(|t| subst_this(name, t)).collect(),
            post.into_iter().map(|t| subst_this(name, t)).collect(),
            Box::new(subst_this(name, *body)),
        ),
        Term::ProofBlock(t) => Term::ProofBlock(Box::new(subst_this(name, *t))),
        other => other,
    }
}

// ---- Public entry points ----

pub fn parse_expr_top(input: &str) -> Result<Term, String> {
    let lex = Token::lexer(input);
    let tokens: Vec<SpannedToken> = lex
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect();
    let bump = Bump::new();
    let pool = StringPool::new(&bump);
    let mut parser = Parser::new(&tokens, &pool);
    parser.parse_expr_top().map_err(|e| e.to_string())
}

pub fn parse_def_top(input: &str) -> Result<(Name, Term), String> {
    let lex = Token::lexer(input);
    let tokens: Vec<SpannedToken> = lex
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect();
    let bump = Bump::new();
    let pool = StringPool::new(&bump);
    let mut parser = Parser::new(&tokens, &pool);
    parser.parse_def_top().map_err(|e| e.to_string())
}

pub fn parse_program(input: &str) -> Result<Vec<TopLevel>, String> {
    let lex = Token::lexer(input);
    let tokens: Vec<SpannedToken> = lex
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect();
    let bump = Bump::new();
    let pool = StringPool::new(&bump);
    let mut parser = Parser::new(&tokens, &pool);
    parser.parse_program().map_err(|e| e.to_string())
}
