// Copyright 2018 Barret Rennie.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use std::{borrow::Cow, fmt};

use combine::{
    parser::{
        char::space,
        choice::{choice, or},
        combinator::{attempt, look_ahead},
        item::{any, eof, item, satisfy},
        range::{range, recognize},
        repeat::skip_many,
        sequence::between,
    },
    stream::{
        state::{Positioner, RangePositioner, State},
        Resetable,
    },
    ParseError, Parser, RangeStream, StreamOnce,
};

/// The position of a token in a file.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq, PartialOrd, Ord)]
pub struct LinePosition {
    /// The line the token appeared on.
    ///
    /// This is 1-indexed.
    pub line: usize,

    /// The column the token started in.
    ///
    /// This is 1-indexed.
    pub col: usize,
}

impl fmt::Display for LinePosition {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "line {} column {}", self.line, self.col)
    }
}

impl Default for LinePosition {
    fn default() -> Self {
        LinePosition { line: 1, col: 1 }
    }
}

/// A positioner for tracking a token's position in a file.
#[derive(Clone, Copy, Debug, Default)]
pub struct LinePositioner {
    /// The current position of the stream.
    state: LinePosition,
}

impl Positioner<char> for LinePositioner {
    type Position = LinePosition;

    fn position(&self) -> Self::Position {
        self.state
    }

    fn update(&mut self, item: &char) {
        if *item == '\n' {
            self.state.line += 1;
            self.state.col = 1;
        } else {
            self.state.col += 1;
        }
    }
}

impl<'a> RangePositioner<char, &'a str> for LinePositioner {
    fn update_range(&mut self, range: &&'a str) {
        for c in range.chars() {
            self.update(&c)
        }
    }
}

impl Resetable for LinePositioner {
    type Checkpoint = Self;

    fn checkpoint(&self) -> Self {
        *self
    }

    fn reset(&mut self, checkpoint: Self) {
        self.state = checkpoint.state;
    }
}

/// Tokenize the input and return an iterator over the results.
pub fn tokenize(s: &str) -> TokenIter<'_> {
    TokenIter {
        remaining: Some(State::with_positioner(s, Default::default())),
    }
}

/// An iterator of the tokens parsed from input.
pub struct TokenIter<'a> {
    /// The remaining input (if any).
    remaining: Option<State<&'a str, LinePositioner>>,
}

impl<'a> Iterator for TokenIter<'a> {
    type Item = Result<Token<'a>, <State<&'a str, LinePositioner> as StreamOnce>::Error>;

    fn next(&mut self) -> Option<Self::Item> {
        let remaining = self.remaining.take()?;

        let mut parser = or(
            skip_many(space()).with(token()).map(Some),
            eof().map(|_| None),
        );

        match parser.parse(remaining) {
            Ok((Some(tok), remaining)) => {
                self.remaining = Some(remaining);
                Some(Ok(tok))
            }
            Ok((None, _)) => {
                self.remaining = None;
                None
            }
            Err(e) => Some(Err(e)),
        }
    }
}

/// A parsed token.
#[derive(Clone, Debug, PartialEq)]
pub enum Token<'a> {
    /// An open parenthesis.
    Open,
    /// A close parenthesis.
    Close,
    /// A dot for a dotted pair.
    Dot,
    /// A boolean value.
    Bool(bool),
    /// A character value.
    Char(char),
    /// A string literal.
    Str(Cow<'a, str>),
}

/// Parse a token.
fn token<'a, I>() -> impl Parser<Input = I, Output = Token<'a>> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        item('(').map(|_| Token::Open),
        item(')').map(|_| Token::Close),
        item('.').skip(look_ahead(delimiter())).map(|_| Token::Dot),
        attempt(bool_lit()).map(Token::Bool),
        attempt(char_lit()).map(Token::Char),
        string_lit().map(Token::Str),
    ))
}

/// Parse a bool literal.
fn bool_lit<'a, I>() -> impl Parser<Input = I, Output = bool>
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    item('#').with(or(item('t').map(|_| true), item('f').map(|_| false)))
}

/// Parse a character literal.
fn char_lit<'a, I>() -> impl Parser<Input = I, Output = char> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    range("#\\")
        .with(choice((
            range("space").map(|_| ' '),
            range("newline").map(|_| '\n'),
            any(),
        )))
        .skip(look_ahead(delimiter()))
}

/// Parse a string literal.
///
/// If the string contains no escapes, this will not do any allocations.
fn string_lit<'a, I>() -> impl Parser<Input = I, Output = Cow<'a, str>> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    between(
        item('"'),
        item('"'),
        recognize(skip_many(or(
            satisfy(|c| c != '"' && c != '\\'),
            item('\\').with(satisfy(|c| c == '"' || c == '\\')),
        ))),
    )
    .map(|s: &'a str| {
        if s.find('\\').is_some() {
            let s = s
                .chars()
                .scan(false, |escaped, c| match (*escaped, c) {
                    (true, '\\') => {
                        *escaped = false;
                        Some(Some('\\'))
                    }

                    (true, '"') => {
                        *escaped = false;
                        Some(Some('"'))
                    }

                    (true, _) => unreachable!("Invalid escape sequence"),

                    (false, '\\') => {
                        *escaped = true;
                        Some(None)
                    }

                    (false, c) => {
                        *escaped = false;
                        Some(Some(c))
                    }
                })
                .filter_map(|c| c)
                .collect::<String>();
            Cow::Owned(s)
        } else {
            Cow::Borrowed(s)
        }
    })
}

/// Return whether or not a character is a delimiter.
///
/// This does not take into account EOF.
fn is_delimiter_char(c: char) -> bool {
    match c {
        c if c.is_ascii_whitespace() => true,
        '(' | ')' | '"' | ';' => true,
        _ => false,
    }
}

/// Parse a delimiter.
fn delimiter<'a, I>() -> impl Parser<Input = I, Output = ()>
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    or(satisfy(is_delimiter_char).map(|_| ()), eof())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_tokenize() {
        assert_eq!(
            tokenize("((( )))").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Open,
                Token::Open,
                Token::Open,
                Token::Close,
                Token::Close,
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("(#t#f)").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Open,
                Token::Bool(true),
                Token::Bool(false),
                Token::Close,
            ])
        );
    }

    #[test]
    fn test_token_open() {
        assert_eq!(token().parse("("), Ok((Token::Open, "")));
    }

    #[test]
    fn test_token_close() {
        assert_eq!(token().parse("("), Ok((Token::Open, "")));
    }

    #[test]
    fn test_token_dot() {
        assert_eq!(token().parse("."), Ok((Token::Dot, "")));
    }

    #[test]
    fn test_token_bool() {
        assert_eq!(token().parse("#t"), Ok((Token::Bool(true), "")));
        assert_eq!(token().parse("#f"), Ok((Token::Bool(false), "")));
    }

    #[test]
    fn test_token_char() {
        assert_eq!(token().parse("#\\space"), Ok((Token::Char(' '), "")));
        assert_eq!(token().parse("#\\newline"), Ok((Token::Char('\n'), "")));
        assert_eq!(token().parse("#\\ "), Ok((Token::Char(' '), "")));
        assert_eq!(token().parse("#\\\n"), Ok((Token::Char('\n'), "")));
        assert_eq!(token().parse("#\\a"), Ok((Token::Char('a'), "")));
        assert_eq!(token().parse("#\\4"), Ok((Token::Char('4'), "")));
        assert_eq!(token().parse("#\\*"), Ok((Token::Char('*'), "")));
    }

    #[test]
    fn test_token_string() {
        assert_eq!(
            token().parse(r#""""#),
            Ok((Token::Str(Cow::Borrowed("")), ""))
        );
        assert_eq!(
            token().parse(r#""a""#),
            Ok((Token::Str(Cow::Borrowed("a")), ""))
        );
        assert_eq!(
            token().parse(r#""\\""#),
            Ok((Token::Str(Cow::Owned("\\".into())), ""))
        );
        assert_eq!(
            token().parse(r#""\"""#),
            Ok((Token::Str(Cow::Owned("\"".into())), ""))
        );
    }
}
