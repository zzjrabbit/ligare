use logos::Logos;

use bumpalo::Bump;

use crate::core::pool::{StringPool, TermArena};
use crate::core::syntax::{Name, PrimOp, Tactic, Term};
use crate::diagnostic::Span;
use crate::front::lexer::Token;

// ── AST types ──────────────────────────────────────────────────────────

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TopLevel<'bump> {
    /// name, params, ret-annotation, desugared-body (Annot(Lam(...), Pi(...))), span
    TLDef(
        Name<'bump>,
        &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
        Option<&'bump Term<'bump>>,
        &'bump Term<'bump>,
        Span,
    ),
    TLTheorem(Name<'bump>, &'bump Term<'bump>, &'bump Term<'bump>, Span),
    TLCheck(&'bump Term<'bump>, &'bump Term<'bump>, Span),
    TLShow(&'bump Term<'bump>, Span),
    TLExpr(&'bump Term<'bump>, Span),
}

// ── Constants ───────────────────────────────────────────────────────────

const KEYWORDS: &[&str] = &[
    "let", "in", "if", "then", "else", "true", "false", "by", "fun", "func", "where", "def",
    "auto", "theorem",
];

/// Names that represent language builtins (not user-defined).
const BUILTIN_NAMES: &[&str] = &[
    "int", "bool", "str", "data", "prop", "theorem", "proof", "and", "or", "not", "implies",
];

// ── Type aliases ────────────────────────────────────────────────────────

type SpannedToken = (Token, std::ops::Range<usize>);

/// Parsed top-level definition: (name, params, ret_annotation, body).
pub type ParsedDef<'bump> = (
    Name<'bump>,
    &'bump [(Name<'bump>, Option<&'bump Term<'bump>>)],
    Option<&'bump Term<'bump>>,
    &'bump Term<'bump>,
);

/// Parsed function body: (params, ret_annotation, body).
type ParsedFuncBody<'bump> = (
    Vec<(Name<'bump>, Option<&'bump Term<'bump>>)>,
    Option<&'bump Term<'bump>>,
    &'bump Term<'bump>,
);

/// Parsed match branch (with Vec instead of slice during parsing).
type ParsedMatchBranch<'bump> = (
    usize,
    Vec<(Name<'bump>, &'bump Term<'bump>)>,
    &'bump Term<'bump>,
);

// ── Expression boundaries ───────────────────────────────────────────────
//
// The parser intentionally has one expression grammar for every term. Outer
// grammar productions own their delimiters and parse the delimited token slice
// with that same expression grammar.

// ── Parser ──────────────────────────────────────────────────────────────

pub struct Parser<'a, 'bump> {
    tokens: &'a [SpannedToken],
    pos: usize,
    pool: &'a StringPool<'bump>,
    arena: &'a TermArena<'bump>,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
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

impl<'a, 'bump> Parser<'a, 'bump> {
    // ── Constructor ─────────────────────────────────────────────────

    pub fn new(
        tokens: &'a [SpannedToken],
        pool: &'a StringPool<'bump>,
        arena: &'a TermArena<'bump>,
    ) -> Self {
        Self {
            tokens,
            pos: 0,
            pool,
            arena,
        }
    }

    // ── Token stream helpers ─────────────────────────────────────────

    fn peek(&self) -> Option<&SpannedToken> {
        let mut i = self.pos;
        loop {
            match self.tokens.get(i) {
                Some((Token::Newline, _)) => i += 1,
                other => return other,
            }
        }
    }

    fn peek_token(&self) -> Option<Token> {
        self.peek().map(|(t, _)| t.clone())
    }

    fn advance(&mut self) {
        // Skip any leading Newlines
        while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
            self.pos += 1;
        }
        // Skip past the current token
        self.pos += 1;
        // Then skip any following Newlines
        while matches!(self.tokens.get(self.pos), Some((Token::Newline, _))) {
            self.pos += 1;
        }
    }

    fn expect(&mut self, expected: &Token) -> Result<(), ParseError> {
        match self.peek() {
            Some((t, span)) if t == expected => {
                self.advance();
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
        if self.peek_token().as_ref() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    fn is_at_end(&self) -> bool {
        self.pos >= self.tokens.len()
    }

    fn current_span(&self) -> Span {
        self.peek().map(|(_, s)| s.clone()).unwrap_or(0..0)
    }

    fn peek_ahead_is(&self, tok: &Token) -> bool {
        self.tokens
            .get(self.pos + 1)
            .map(|(t, _)| t == tok)
            .unwrap_or(false)
    }

    /// Generic try-parse: if `peek` matches `tok`, advance and call `parse_fn`;
    /// on error restore position. Returns `None` when `peek` doesn't match.
    fn try_parse<T>(
        &mut self,
        tok: Token,
        parse_fn: impl FnOnce(&mut Self) -> Result<T, ParseError>,
    ) -> Option<T> {
        if self.peek_token() != Some(tok) {
            return None;
        }
        let saved = self.pos;
        self.advance();
        match parse_fn(self) {
            Ok(t) => Some(t),
            Err(_) => {
                self.pos = saved;
                None
            }
        }
    }

    // ── Public entry points ───────────────────────────────────────────

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

    // ── Top-level ─────────────────────────────────────────────────────

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
            let term = self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::Colon))?;
            let constraint = if self.try_expect(&Token::Colon) {
                self.parse_expr()?
            } else {
                self.arena.builtin(self.pool.intern("data"))
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

    // ── Definitions ───────────────────────────────────────────────────

    fn parse_def(&mut self) -> Result<ParsedDef<'bump>, ParseError> {
        self.expect(&Token::KwDef)?;
        let name = self.parse_ident()?;
        let (params, m_ret, body) = self.parse_func_body(name)?;
        let params_slice = self.arena.alloc_slice(&params);
        let body = if matches!(body, Term::UnionDef(..) | Term::StructDef(..)) {
            body
        } else {
            self.desugar_def(name, &params, m_ret, body)
        };
        Ok((name, params_slice, m_ret, body))
    }

    /// Desugar a `def` body into `Annot(NamedLam(...), Pi(...))`.
    fn desugar_def(
        &self,
        _name: Name<'bump>,
        params: &[(Name<'bump>, Option<&'bump Term<'bump>>)],
        m_ret: Option<&'bump Term<'bump>>,
        body: &'bump Term<'bump>,
    ) -> &'bump Term<'bump> {
        let func_body = params
            .iter()
            .rfold(body, |b, &(pn, _)| self.arena.named_lam(pn, b));
        let default = self.arena.builtin(self.pool.intern("data"));
        let func_type = params
            .iter()
            .rfold(m_ret.unwrap_or(default), |b, &(pn, mc)| {
                self.arena.pi(pn, mc.unwrap_or(default), b)
            });
        self.arena.annot(func_body, func_type)
    }

    fn parse_func_body(&mut self, name: Name<'bump>) -> Result<ParsedFuncBody<'bump>, ParseError> {
        let params = self.parse_many_curried_params();
        let m_ret =
            self.parse_type_annotation_until(|tokens, i| matches!(tokens[i].0, Token::ColonEq));
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
        let pname = match self.parse_ident() {
            Ok(n) => n,
            Err(_) => return None,
        };
        let mconstr = self.parse_type_annotation();
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

    fn parse_type_annotation(&mut self) -> Option<&'bump Term<'bump>> {
        self.parse_type_annotation_until(|tokens, i| {
            matches!(tokens[i].0, Token::KwBy | Token::ColonEq | Token::RParen)
        })
    }

    fn parse_type_annotation_until<F>(&mut self, is_delim: F) -> Option<&'bump Term<'bump>>
    where
        F: FnMut(&[SpannedToken], usize) -> bool,
    {
        self.try_parse(Token::Colon, |s| s.parse_expr_until(is_delim))
    }

    fn parse_struct_field_type(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_expr_until(Self::is_struct_field_type_delim)
    }

    fn parse_tactic_arg(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.parse_expr_until(Self::is_tactic_arg_delim)
    }

    fn parse_by_proof_clause(&mut self) -> Option<&'bump [Tactic<'bump>]> {
        self.try_parse(Token::KwBy, |s| s.parse_tactics())
    }

    // ── Expression parsing ────────────────────────────────────────────
    //
    //  Architecture:
    //    parse_expr            → token-driven dispatch (no backtracking)
    //      ├─ KwIf             → parse_if_expr
    //      ├─ KwMatch          → parse_match_expr
    //      ├─ KwLet            → parse_let_expr
    //      ├─ KwFunc           → parse_func_expr
    //      ├─ LParen (dep-arrow)→ parse_dep_arrow_expr (single targeted rollback)
    //      └─ default          → parse_expr_bp (unified Pratt parser)
    //
    //    parse_expr_bp         → unified precedence climber
    //      ├─ parse_head       → atom + suffix loop
    //      │   ├─ parse_atom   → literals, identifiers, lambdas, parens, etc.
    //      │   └─ suffixes     → annot, by, refine, dot
    //      └─ loop: infix ops + application + suffixes (one precedence system)
    //

    fn parse_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        if self.peek_token().is_some_and(Self::is_expr_terminator) {
            return Err(ParseError {
                message: "expected expression before terminator".into(),
                span: self.current_span(),
            });
        }

        match self.peek_token() {
            Some(Token::KwIf) => self.parse_if_expr(),
            Some(Token::KwMatch) => self.parse_match_expr(),
            Some(Token::KwLet) => self.parse_let_expr(),
            Some(Token::KwFunc) => self.parse_func_expr(),
            Some(Token::LParen) => {
                // Single targeted rollback: try dep-arrow pattern `(x : A) -> B`.
                // Only triggers when we see `(`; all other forms use token-driven dispatch.
                let saved = self.pos;
                if let Ok(t) = self.parse_dep_arrow_expr() {
                    return Ok(t);
                }
                self.pos = saved;
                self.parse_expr_bp(0)
            }
            _ => self.parse_expr_bp(0),
        }
    }

    fn parse_expr_until<F>(&mut self, is_delim: F) -> Result<&'bump Term<'bump>, ParseError>
    where
        F: FnMut(&[SpannedToken], usize) -> bool,
    {
        let start = self.pos;
        let end = self.find_expr_boundary(is_delim);
        if end == start {
            return Err(ParseError {
                message: "expected expression before delimiter".into(),
                span: self.current_span(),
            });
        }

        let mut sub = Parser::new(&self.tokens[start..end], self.pool, self.arena);
        let term = sub.parse_expr_top()?;
        self.pos = end;
        Ok(term)
    }

    fn find_expr_boundary<F>(&self, mut is_delim: F) -> usize
    where
        F: FnMut(&[SpannedToken], usize) -> bool,
    {
        let mut i = self.pos;
        let mut parens = 0usize;
        let mut braces = 0usize;
        while i < self.tokens.len() {
            match self.tokens[i].0 {
                Token::LParen => parens += 1,
                Token::RParen => {
                    if parens == 0 && braces == 0 && is_delim(self.tokens, i) {
                        break;
                    }
                    parens = parens.saturating_sub(1);
                }
                Token::LBrace => braces += 1,
                Token::RBrace => {
                    if parens == 0 && braces == 0 && is_delim(self.tokens, i) {
                        break;
                    }
                    braces = braces.saturating_sub(1);
                }
                _ if parens == 0 && braces == 0 && is_delim(self.tokens, i) => break,
                _ => {}
            }
            i += 1;
        }
        i
    }

    // ── Special expression forms ──────────────────────────────────────

    fn parse_if_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwIf)?;
        let cond = self.parse_expr()?;
        self.expect(&Token::KwThen)?;
        let tbranch = self.parse_expr()?;
        self.expect(&Token::KwElse)?;
        Ok(self.arena.if_then_else(cond, tbranch, self.parse_expr()?))
    }

    fn parse_match_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwMatch)?;
        let scrutinee = self.parse_expr()?;
        self.expect(&Token::KwWith)?;
        let mut branches: Vec<ParsedMatchBranch<'bump>> = Vec::new();
        loop {
            if !self.try_expect(&Token::Bar) {
                break;
            }
            let _variant_name = self.parse_ident()?;
            let mut binds: Vec<(Name<'bump>, &'bump Term<'bump>)> = Vec::new();
            while self
                .peek_token()
                .is_some_and(|t| matches!(t, Token::Ident(_)))
            {
                let bind_name = self.parse_ident()?;
                let bind_ty = self.arena.builtin(self.pool.intern("data"));
                binds.push((bind_name, bind_ty));
            }
            self.expect(&Token::FatArrow)?;
            let body = self.parse_expr()?;
            let idx = branches.len();
            branches.push((idx, binds, body));
        }
        if branches.is_empty() {
            return Err(ParseError {
                message: "match expression must have at least one branch".into(),
                span: self.current_span(),
            });
        }
        let branches_slice: Vec<_> = branches
            .into_iter()
            .map(|(idx, b, body)| (idx, self.arena.alloc_slice(&b), body))
            .collect();
        Ok(self
            .arena
            .match_(scrutinee, self.arena.alloc_slice(&branches_slice)))
    }

    fn parse_let_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwLet)?;
        let name = self.parse_ident()?;
        if self.try_expect(&Token::LBrace) {
            return self.parse_let_destruct(name);
        }
        let m_constraint = self.parse_type_annotation();
        let m_proof = self.parse_by_proof_clause();
        self.expect(&Token::ColonEq)?;
        let val = self.parse_expr()?;
        let val = match m_proof {
            Some(tactics) => self.arena.by_proof(Some(val), tactics),
            None => val,
        };
        self.expect(&Token::KwIn)?;
        let body = self.parse_expr()?;
        Ok(self.arena.let_(name, val, body, m_constraint))
    }

    fn parse_let_destruct(
        &mut self,
        struct_name: Name<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        let mut field_names: Vec<Name<'bump>> = Vec::new();
        loop {
            let fname = self.parse_ident()?;
            field_names.push(fname);
            if !self.try_expect(&Token::Comma) {
                break;
            }
        }
        self.expect(&Token::RBrace)?;
        if field_names.is_empty() {
            return Err(ParseError {
                message: "destructuring pattern must have at least one field".into(),
                span: self.current_span(),
            });
        }
        let _m_constraint = self.parse_type_annotation();
        self.expect(&Token::ColonEq)?;
        let val = self.parse_expr()?;
        self.expect(&Token::KwIn)?;
        let mut body = self.parse_expr()?;
        for fname in field_names.iter().rev() {
            let proj_name = self.pool.intern(&format!("{}.{}", struct_name, fname));
            let proj = self.arena.app(self.arena.named(proj_name), val);
            body = self.arena.let_(fname, proj, body, None);
        }
        Ok(body)
    }

    fn parse_func_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwFunc)?;
        let name = self.parse_ident()?;
        let (params, m_ret, body) = self.parse_func_body(name)?;
        Ok(self.desugar_def(name, &params, m_ret, body))
    }

    /// Parse dependent arrow `(x : A) -> B`.
    /// The caller (parse_expr) saves/restores position on failure.
    fn parse_dep_arrow_expr(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LParen)?;
        let x = self.parse_ident()?;
        self.expect(&Token::Colon)?;
        let a = self.parse_expr_until(|tokens, i| matches!(tokens[i].0, Token::RParen))?;
        self.expect(&Token::RParen)?;
        self.expect(&Token::ThinArrow)?;
        let b = self.parse_expr()?;
        Ok(self.arena.pi(x, a, b))
    }

    // ── Unified Pratt parser (application + infix ops in one system) ──

    /// Infix binding-power table: (precedence, associativity).
    fn infix_bp(tok: &Token) -> Option<(u8, Associativity)> {
        match tok {
            Token::Star | Token::Slash | Token::Percent => Some((5, Associativity::Left)),
            Token::ThinArrow => Some((4, Associativity::Right)),
            Token::Plus | Token::Minus => Some((3, Associativity::Left)),
            Token::Eq
            | Token::Le
            | Token::Ge
            | Token::Neq
            | Token::Lt
            | Token::Gt
            | Token::EqEq => Some((2, Associativity::None)),
            _ => None,
        }
    }

    /// Returns `true` if the token can start an atom expression when
    /// seen in application (LED) position — i.e. after another expression.
    /// Excludes special forms (if/match/let/func) and top-level keywords
    /// (theorem/def/#check/#show) which are only valid at the start of
    /// a top-level item or inside parentheses.
    fn is_atom_start(tok: &Token) -> bool {
        matches!(
            tok,
            Token::IntLit(_)
                | Token::StrLit(_)
                | Token::True
                | Token::False
                | Token::Ident(_)
                | Token::Backslash
                | Token::Lambda
                | Token::KwFun
                | Token::LParen
                | Token::Minus
                | Token::KwAuto
                | Token::AndIntro
                | Token::AndElimLeft
                | Token::And
                | Token::Or
                | Token::Not
                | Token::Implies
                | Token::KwBy
        )
    }

    /// Convert an infix token to the corresponding PrimOp.
    fn token_to_primop(tok: &Token) -> PrimOp {
        match tok {
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
        }
    }

    fn is_expr_terminator(tok: Token) -> bool {
        matches!(
            tok,
            Token::ColonEq
                | Token::KwIn
                | Token::KwThen
                | Token::KwElse
                | Token::RParen
                | Token::RBrace
                | Token::Comma
                | Token::Semi
                | Token::Bar
        )
    }

    fn is_tactic_arg_delim(tokens: &[SpannedToken], i: usize) -> bool {
        matches!(
            tokens[i].0,
            Token::ColonEq
                | Token::KwIn
                | Token::KwThen
                | Token::KwElse
                | Token::RParen
                | Token::RBrace
                | Token::Colon
                | Token::Semi
                | Token::KwDef
                | Token::HashCheck
                | Token::HashShow
        )
    }

    fn is_struct_field_type_delim(tokens: &[SpannedToken], i: usize) -> bool {
        if matches!(
            tokens[i].0,
            Token::KwDef | Token::HashCheck | Token::HashShow | Token::ColonEq
        ) {
            return true;
        }
        if let Token::Ident(_) = tokens[i].0 {
            return tokens.get(i + 1).is_some_and(|(t, _)| *t == Token::Colon);
        }
        false
    }

    /// Parse an atom plus trailing suffixes (annot, by, refine, dot).
    fn parse_head(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let term = self.parse_atom()?;
        self.apply_suffixes(term)
    }

    /// Greedily apply full-expression suffix operators: `:`, `by`, `where`, `.`
    fn apply_suffixes(
        &mut self,
        mut t: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        loop {
            if self.peek_token().is_some_and(Self::is_expr_terminator) {
                break;
            }

            let changed = if self.peek_token() == Some(Token::KwWhere) {
                t = self.parse_refine_suffix(t)?;
                true
            } else if self.peek_token() == Some(Token::Colon) {
                if let Some(c) = self.try_parse(Token::Colon, |s| {
                    s.parse_expr_until(|tokens, i| {
                        matches!(tokens[i].0, Token::KwBy | Token::ColonEq | Token::RParen)
                    })
                }) {
                    t = self.arena.annot(t, c);
                    true
                } else {
                    false
                }
            } else if self.peek_token() == Some(Token::KwBy) {
                if let Some(tactics) = self.parse_by_proof_clause() {
                    t = self.arena.by_proof(Some(t), tactics);
                    true
                } else {
                    false
                }
            } else if self.peek_token() == Some(Token::Dot)
                && matches!(t, Term::Builtin(_) | Term::Named(_))
            {
                self.advance();
                let field = self.parse_ident()?;
                let base_name = match t {
                    Term::Builtin(n) | Term::Named(n) => n,
                    _ => unreachable!(),
                };
                let dotted = self.pool.intern(&format!("{}.{}", base_name, field));
                t = self.arena.named(dotted);
                true
            } else {
                false
            };
            if !changed {
                break;
            }
        }
        Ok(t)
    }

    /// Unified precedence-climbing expression parser.
    /// Handles function application (max precedence, left-associative) and
    /// infix operators in a single loop.
    fn parse_expr_bp(&mut self, min_prec: u8) -> Result<&'bump Term<'bump>, ParseError> {
        let mut lhs = self.parse_head()?;

        // Application binding power (juxtaposition) — highest in the system.
        const APP_BP: u8 = u8::MAX;

        loop {
            let Some(tok) = self.peek_token() else {
                break;
            };
            if Self::is_expr_terminator(tok.clone()) {
                break;
            }

            // 1) Infix operators
            if let Some((prec, assoc)) = Self::infix_bp(&tok) {
                if prec < min_prec {
                    break;
                }
                // Special: `/=` — check ahead that `/` is followed by `=`
                if tok == Token::Slash && self.peek_ahead_is(&Token::Eq) {
                    break;
                }
                self.advance();
                let rbp = match assoc {
                    Associativity::Left => prec + 1,
                    Associativity::Right => prec,
                    Associativity::None => prec + 1,
                };

                if tok == Token::ThinArrow {
                    let rhs = self.parse_expr_bp(rbp)?;
                    lhs = self.arena.pi(self.pool.intern(""), lhs, rhs);
                } else {
                    let op = Self::token_to_primop(&tok);
                    let rhs = self.parse_expr_bp(rbp)?;
                    lhs = self
                        .arena
                        .app(self.arena.app(self.arena.prim_op(op), lhs), rhs);
                }
                continue;
            }

            // 2) Function application (juxtaposition)
            if APP_BP >= min_prec && Self::is_atom_start(&tok) {
                match self.parse_head() {
                    Ok(arg) => {
                        lhs = self.arena.app(lhs, arg);
                        continue;
                    }
                    Err(_) => break,
                }
            }

            // 3) No more — stop
            break;
        }
        Ok(lhs)
    }

    // ── Refinement suffix ──────────────────────────────────────────

    fn parse_refine_suffix(
        &mut self,
        parent: &'bump Term<'bump>,
    ) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::KwWhere)?;
        self.expect(&Token::LParen)?;
        let param_name = self.parse_ident()?;
        self.expect(&Token::FatArrow)?;
        let predicate = self.parse_expr()?;
        self.expect(&Token::RParen)?;
        Ok(self.arena.refine(param_name, parent, predicate))
    }

    // ── Atom ───────────────────────────────────────────────────────

    fn parse_atom(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::IntLit(n)) => {
                self.advance();
                Ok(self.arena.lit_int(n))
            }
            Some(Token::StrLit(s)) => {
                self.advance();
                let name = self.pool.intern(&s);
                Ok(self.arena.lit_str(name))
            }
            Some(Token::True) => {
                self.advance();
                Ok(self.arena.lit_bool(true))
            }
            Some(Token::False) => {
                self.advance();
                Ok(self.arena.lit_bool(false))
            }
            Some(Token::AndIntro) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("∧-intro")))
            }
            Some(Token::AndElimLeft) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("∧-elim-left")))
            }
            Some(Token::And) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("and")))
            }
            Some(Token::Or) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("or")))
            }
            Some(Token::Not) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("not")))
            }
            Some(Token::Implies) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("implies")))
            }
            Some(Token::KwTheorem) => {
                self.advance();
                Ok(self.arena.builtin(self.pool.intern("theorem")))
            }
            Some(Token::KwAuto) => {
                self.advance();
                Ok(self.arena.auto_proof())
            }
            Some(Token::Ident(_)) => self.parse_var(),
            Some(Token::Backslash) | Some(Token::Lambda) => self.parse_lam(),
            Some(Token::KwFun) => self.parse_fun_lam(),
            Some(Token::Minus) => {
                self.advance();
                let t = self.parse_atom()?;
                Ok(self.arena.app(
                    self.arena
                        .app(self.arena.prim_op(PrimOp::Sub), self.arena.lit_int(0)),
                    t,
                ))
            }
            Some(Token::LParen) => self.parse_parens(),
            Some(Token::KwBy) => {
                self.advance();
                let tactics = self.parse_tactics()?;
                Ok(self.arena.by_proof(None, tactics))
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

    fn parse_var(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        let name = self.parse_ident()?;
        if KEYWORDS.contains(&name) && !matches!(name, "data" | "prop" | "theorem" | "proof") {
            Err(ParseError {
                message: format!("keyword '{}' cannot be used as identifier", name),
                span: self.current_span(),
            })
        } else if BUILTIN_NAMES.contains(&name) {
            Ok(self.arena.builtin(name))
        } else {
            Ok(self.arena.named(name))
        }
    }

    fn parse_ident(&mut self) -> Result<Name<'bump>, ParseError> {
        match self.peek() {
            Some((Token::Ident(name), _)) => {
                let n = self.pool.intern(name);
                self.advance();
                Ok(n)
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

    fn parse_lam(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        match self.peek_token() {
            Some(Token::Backslash) | Some(Token::Lambda) => self.advance(),
            _ => {
                return Err(ParseError {
                    message: "expected lambda".into(),
                    span: 0..0,
                });
            }
        };
        let mut params = vec![self.parse_ident()?];
        while self
            .peek_token()
            .is_some_and(|t| matches!(t, Token::Ident(_)))
        {
            params.push(self.parse_ident()?);
        }
        self.expect(&Token::Dot)?;
        let body = self.parse_expr()?;
        Ok(params
            .into_iter()
            .rfold(body, |b, p| self.arena.named_lam(p, b)))
    }

    fn parse_fun_lam(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.advance();
        let params = self.parse_many_fun_params()?;
        self.expect(&Token::FatArrow)?;
        let body = self.parse_expr()?;
        let func_body = params
            .iter()
            .rfold(body, |b, &(pn, _)| self.arena.named_lam(pn, b));
        let default = self.arena.builtin(self.pool.intern("data"));
        let func_type = params.iter().rfold(default, |b, &(pn, mc)| {
            self.arena.pi(pn, mc.unwrap_or(default), b)
        });
        Ok(self.arena.annot(func_body, func_type))
    }

    fn parse_many_fun_params(
        &mut self,
    ) -> Result<Vec<(Name<'bump>, Option<&'bump Term<'bump>>)>, ParseError> {
        let mut params = Vec::new();
        loop {
            match self.peek_token() {
                Some(Token::FatArrow) | None => break,
                Some(Token::LParen) => {
                    self.advance();
                    let pname = self.parse_ident()?;
                    let mconstr = self.parse_type_annotation();
                    self.expect(&Token::RParen)?;
                    params.push((pname, mconstr));
                }
                Some(Token::Ident(_)) => {
                    let pname = self.parse_ident()?;
                    params.push((pname, None));
                }
                _ => break,
            }
        }
        if params.is_empty() {
            return Err(ParseError {
                message: "fun expression must have at least one parameter".into(),
                span: self.current_span(),
            });
        }
        Ok(params)
    }

    fn parse_parens(&mut self) -> Result<&'bump Term<'bump>, ParseError> {
        self.expect(&Token::LParen)?;
        let t = self.parse_expr()?;
        self.expect(&Token::RParen)?;
        Ok(t)
    }

    // ── Union / Struct bodies ───────────────────────────────────────

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
                self.parse_struct_field_type()?
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

    // ── Tactic parsing ──────────────────────────────────────────────

    fn parse_tactics(&mut self) -> Result<&'bump [Tactic<'bump>], ParseError> {
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Associativity {
    Left,
    Right,
    None,
}

// ── Free functions ────────────────────────────────────────────────────

fn tokenize(input: &str) -> Vec<SpannedToken> {
    Token::lexer(input)
        .spanned()
        .filter_map(|(r, s)| r.ok().map(|t| (t, s)))
        .collect()
}

pub fn parse_expr_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<&'bump Term<'bump>, ParseError> {
    let pool = StringPool::new(bump);
    Parser::new(&tokenize(input), &pool, arena).parse_expr_top()
}

pub fn parse_def_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<ParsedDef<'bump>, String> {
    let pool = StringPool::new(bump);
    Parser::new(&tokenize(input), &pool, arena)
        .parse_def_top()
        .map_err(|e| e.to_string())
}

pub fn parse_program<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<Vec<TopLevel<'bump>>, ParseError> {
    let pool = StringPool::new(bump);
    Parser::new(&tokenize(input), &pool, arena).parse_program()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::core::pool::TermArena;

    fn setup() -> (&'static bumpalo::Bump, TermArena<'static>) {
        let b = Box::leak(Box::new(bumpalo::Bump::new()));
        (b, TermArena::new(b))
    }

    #[test]
    fn let_destructuring_ast() {
        let (bump, arena) = setup();
        let term = parse_expr_top("let Point{x, y} := p in x + y", bump, &arena)
            .expect("parse should succeed");

        match term {
            Term::Let(name_x, val_x, body, None) => {
                assert_eq!(name_x, &"x");
                match val_x {
                    Term::App(proj_x, arg_x) => {
                        assert_eq!(**proj_x, Term::Named(&"Point.x"));
                        assert_eq!(**arg_x, Term::Named(&"p"));
                    }
                    other => panic!("expected App for x projection, got {:?}", other),
                }
                match body {
                    Term::Let(name_y, val_y, inner_body, None) => {
                        assert_eq!(name_y, &"y");
                        match val_y {
                            Term::App(proj_y, arg_y) => {
                                assert_eq!(**proj_y, Term::Named(&"Point.y"));
                                assert_eq!(**arg_y, Term::Named(&"p"));
                            }
                            other => panic!("expected App for y projection, got {:?}", other),
                        }
                        match inner_body {
                            Term::App(op_app, rhs) => match op_app {
                                Term::App(op, lhs) => {
                                    assert_eq!(**op, Term::PrimOp(PrimOp::Add));
                                    assert_eq!(**lhs, Term::Named(&"x"));
                                    assert_eq!(**rhs, Term::Named(&"y"));
                                }
                                other => {
                                    panic!("expected App(PrimOp(Add), lhs), got {:?}", other)
                                }
                            },
                            other => panic!("expected App for addition, got {:?}", other),
                        }
                    }
                    other => panic!("expected Let for y binding, got {:?}", other),
                }
            }
            other => panic!("expected Let at top, got {:?}", other),
        }
    }

    #[test]
    fn struct_definition_ast() {
        let (bump, arena) = setup();
        let (name, params, m_ret, body) =
            parse_def_top("def Foo : prop := struct a : int b : str", bump, &arena)
                .expect("parse should succeed");

        assert_eq!(name, "Foo");
        assert!(params.is_empty());
        assert_eq!(m_ret.map(|t| *t), Some(Term::Builtin(&"prop")));

        match body {
            Term::StructDef(struct_name, fields) => {
                assert_eq!(struct_name, &"Foo");
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "a");
                assert_eq!(*fields[0].1, Term::Builtin(&"int"));
                assert_eq!(fields[1].0, "b");
                assert_eq!(*fields[1].1, Term::Builtin(&"str"));
            }
            other => panic!("expected StructDef, got {:?}", other),
        }
    }

    #[test]
    fn lambda_application_ast() {
        let (bump, arena) = setup();
        let term = parse_expr_top("\\x. x + 1", bump, &arena).expect("parse should succeed");

        match term {
            Term::NamedLam(name, body) => {
                assert_eq!(name, &"x");
                match body {
                    Term::App(op_app, rhs) => {
                        match op_app {
                            Term::App(op, lhs) => {
                                assert_eq!(**op, Term::PrimOp(PrimOp::Add));
                                assert_eq!(**lhs, Term::Named(&"x"));
                            }
                            other => panic!("expected App(PrimOp(Add), lhs), got {:?}", other),
                        }
                        assert_eq!(**rhs, Term::LitInt(1));
                    }
                    other => panic!("expected App in lam body, got {:?}", other),
                }
            }
            other => panic!("expected NamedLam, got {:?}", other),
        }
    }

    #[test]
    fn if_expression_ast() {
        let (bump, arena) = setup();
        let term =
            parse_expr_top("if true then 1 else 0", bump, &arena).expect("parse should succeed");

        match term {
            Term::IfThenElse(cond, tbranch, fbranch) => {
                assert_eq!(**cond, Term::LitBool(true));
                assert_eq!(**tbranch, Term::LitInt(1));
                assert_eq!(**fbranch, Term::LitInt(0));
            }
            other => panic!("expected IfThenElse, got {:?}", other),
        }
    }

    #[test]
    fn match_expression_ast() {
        let (bump, arena) = setup();
        let term = parse_expr_top("match x with | A => 1 | B => 2", bump, &arena)
            .expect("parse should succeed");

        match term {
            Term::Match(scrutinee, branches) => {
                assert_eq!(**scrutinee, Term::Named(&"x"));
                assert_eq!(branches.len(), 2);

                let (idx0, binds0, body0) = &branches[0];
                assert_eq!(*idx0, 0);
                assert!(binds0.is_empty());
                assert_eq!(**body0, Term::LitInt(1));

                let (idx1, binds1, body1) = &branches[1];
                assert_eq!(*idx1, 1);
                assert!(binds1.is_empty());
                assert_eq!(**body1, Term::LitInt(2));
            }
            other => panic!("expected Match, got {:?}", other),
        }
    }

    #[test]
    fn dotted_name_ast() {
        let (bump, arena) = setup();
        let term = parse_expr_top("Foo.bar", bump, &arena).expect("parse should succeed");
        assert_eq!(*term, Term::Named(&"Foo.bar"));
    }
}
