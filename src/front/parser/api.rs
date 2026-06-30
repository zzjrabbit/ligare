use logos::Logos;

use bumpalo::Bump;

use super::{ParseError, ParsedDef, Parser, SpannedToken, TopLevel};
use crate::core::pool::{StringPool, TermArena};
use crate::core::syntax::Term;
use crate::front::lexer::Token;

fn tokenize(input: &str) -> Result<Vec<SpannedToken>, ParseError> {
    Token::lexer(input)
        .spanned()
        .map(|(r, span)| match r {
            Ok(t) => Ok((t, span)),
            Err(()) => Err(ParseError {
                message: format!("invalid token `{}`", &input[span.clone()]),
                span,
            }),
        })
        .collect()
}

pub fn parse_expr_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<&'bump Term<'bump>, ParseError> {
    let pool = StringPool::new(bump);
    let tokens = tokenize(input)?;
    Parser::new(&tokens, &pool, arena).parse_expr_top()
}

pub fn parse_def_top<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<ParsedDef<'bump>, String> {
    let pool = StringPool::new(bump);
    let tokens = tokenize(input).map_err(|e| e.to_string())?;
    Parser::new(&tokens, &pool, arena)
        .parse_def_top()
        .map_err(|e| e.to_string())
}

pub fn parse_program<'bump>(
    input: &str,
    bump: &'bump Bump,
    arena: &'bump TermArena<'bump>,
) -> Result<Vec<TopLevel<'bump>>, ParseError> {
    let pool = StringPool::new(bump);
    let tokens = tokenize(input)?;
    Parser::new(&tokens, &pool, arena).parse_program()
}
