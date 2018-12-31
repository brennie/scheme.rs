// Copyright 2018 Barret Rennie.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

mod number;

use std::{borrow::Cow, fmt};

use combine::{
    parser::{
        char::{space, string_cmp},
        choice::{choice, or},
        combinator::{attempt, look_ahead},
        item::{any, eof, item, satisfy, value},
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
use either::Either;

pub use self::number::Number;

include!(concat!(env!("OUT_DIR"), "/keyword.codegen.rs"));

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
    /// A quote.
    Quote,
    /// A quasiquote.
    Quasiquote,
    /// An unquote.
    Unquote,
    /// A splicing unquote.
    UnquoteSplicing,
    /// The beginning of a vector.
    BeginVector,
    /// A boolean value.
    Bool(bool),
    /// A character value.
    Char(char),
    /// A string literal.
    Str(Cow<'a, str>),
    /// An identifier.
    Ident(&'a str),
    /// A numerical literal.
    Number(Number),
    /// A syntatic keyword.
    Keyword(Keyword),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Keyword {
    /// The `quote` keyword.
    Quote,
    /// The `lambda` keyword.
    Lambda,
    /// The `if` keyword.
    If,
    /// The `set` keyword.
    Set,
    /// The `begin` keyword.
    Begin,
    /// The `cond` keyword.
    Cond,
    /// The `and` keyword.
    And,
    /// The `or` keyword.
    Or,
    /// The `case` keyword.
    Case,
    /// The `let` keyword.
    Let,
    /// The `let*` keyword.
    LetStar,
    /// The `letrec` keyword.
    LetRec,
    /// The `do` keyword.
    Do,
    /// The `delay` keyword.
    Delay,
    /// The `quasiquote` keyword.
    Quasiquote,
    /// The `else` keyword.
    Else,
    /// The `=>` keyword.
    RightArrow,
    /// The `define` keyword.
    Define,
    /// The `unquote` keyword.
    Unquote,
    /// The `unquote-splicing` keyword.
    UnquoteSplicing,
}

impl Keyword {
    /// Whether or not a keyword can begin an expression.
    pub fn is_expression_keyword(self) -> bool {
        match self {
            Keyword::Quote
            | Keyword::Lambda
            | Keyword::If
            | Keyword::Set
            | Keyword::Begin
            | Keyword::Cond
            | Keyword::And
            | Keyword::Or
            | Keyword::Case
            | Keyword::Let
            | Keyword::LetStar
            | Keyword::LetRec
            | Keyword::Do
            | Keyword::Delay
            | Keyword::Quasiquote => true,

            Keyword::Else
            | Keyword::RightArrow
            | Keyword::Define
            | Keyword::Unquote
            | Keyword::UnquoteSplicing => false,
        }
    }
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
        attempt(item('.').skip(look_ahead(delimiter()))).map(|_| Token::Dot),
        item('\'').map(|_| Token::Quote),
        item('`').map(|_| Token::Quasiquote),
        item(',').with(or(
            item('@').map(|_| Token::UnquoteSplicing),
            value(Token::Unquote),
        )),
        attempt(item('#').with(choice((
            item('t').map(|_| Token::Bool(true)),
            item('f').map(|_| Token::Bool(false)),
            item('(').map(|_| Token::BeginVector),
            char_lit_tail().map(Token::Char),
        )))),
        string_lit().map(Token::Str),
        attempt(ident_or_keyword().map(|t| match t {
            Either::Left(keyword) => Token::Keyword(keyword),
            Either::Right(ident) => Token::Ident(ident),
        })),
        number::number()
            .skip(look_ahead(delimiter()))
            .map(Token::Number),
    ))
}

/// Parse a character literal without the leading `#`.
fn char_lit_tail<'a, I>() -> impl Parser<Input = I, Output = char> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    item('\\')
        .with(choice((
            string_cmp("space", |a, b| a.eq_ignore_ascii_case(&b)).map(|_| ' '),
            string_cmp("newline", |a, b| a.eq_ignore_ascii_case(&b)).map(|_| '\n'),
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

/// Parse an identifier or keyword.
fn ident_or_keyword<'a, I>() -> impl Parser<Input = I, Output = Either<Keyword, &'a str>>
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    recognize(choice((
        satisfy(is_ident_initial_char).with(skip_many(satisfy(is_ident_subsequent_char))),
        item('+').map(|_| ()),
        item('-').map(|_| ()),
        range("...").map(|_| ()),
    )))
    .skip(look_ahead(delimiter()))
    .map(|s| match KEYWORDS.get(s) {
        Some(kw) => Either::Left(*kw),
        None => Either::Right(s),
    })
}

/// Whether or not a character can be the leading character in an identifier.
fn is_ident_initial_char(c: char) -> bool {
    c.is_ascii_alphabetic() || "!$%&*/:<=>?^_~".find(c).is_some()
}

/// Whether or not a character can be a subsequent character in an identifier.
fn is_ident_subsequent_char(c: char) -> bool {
    is_ident_initial_char(c) || c.is_ascii_digit() || "+-.@".find(c).is_some()
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
    use num_complex::Complex64;
    use num_rational::Rational;

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

        assert_eq!(
            tokenize("(define plus (lambda (x y) (+ x y)))").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Open,
                Token::Keyword(Keyword::Define),
                Token::Ident("plus"),
                Token::Open,
                Token::Keyword(Keyword::Lambda),
                Token::Open,
                Token::Ident("x"),
                Token::Ident("y"),
                Token::Close,
                Token::Open,
                Token::Ident("+"),
                Token::Ident("x"),
                Token::Ident("y"),
                Token::Close,
                Token::Close,
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("'(a b c)").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Quote,
                Token::Open,
                Token::Ident("a"),
                Token::Ident("b"),
                Token::Ident("c"),
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("`(a b ,(+ a b))").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Quasiquote,
                Token::Open,
                Token::Ident("a"),
                Token::Ident("b"),
                Token::Unquote,
                Token::Open,
                Token::Ident("+"),
                Token::Ident("a"),
                Token::Ident("b"),
                Token::Close,
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("`(a b ,@(map f '(c d)))").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Quasiquote,
                Token::Open,
                Token::Ident("a"),
                Token::Ident("b"),
                Token::UnquoteSplicing,
                Token::Open,
                Token::Ident("map"),
                Token::Ident("f"),
                Token::Quote,
                Token::Open,
                Token::Ident("c"),
                Token::Ident("d"),
                Token::Close,
                Token::Close,
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("'#(a b c)").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Quote,
                Token::BeginVector,
                Token::Ident("a"),
                Token::Ident("b"),
                Token::Ident("c"),
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("(+ 1 2 3)").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Open,
                Token::Ident("+"),
                Token::Number(Number::Integer(1)),
                Token::Number(Number::Integer(2)),
                Token::Number(Number::Integer(3)),
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("(sqrt 123.456)").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Open,
                Token::Ident("sqrt"),
                Token::Number(Number::Real(123.456)),
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("(complex? 1+1i)").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Open,
                Token::Ident("complex?"),
                Token::Number(Number::Complex(Complex64::new(1.0, 1.0))),
                Token::Close,
            ])
        );

        assert_eq!(
            tokenize("(+ 1/2 1/4 1/8)").collect::<Result<Vec<_>, _>>(),
            Ok(vec![
                Token::Open,
                Token::Ident("+"),
                Token::Number(Number::Rational(Rational::new(1, 2))),
                Token::Number(Number::Rational(Rational::new(1, 4))),
                Token::Number(Number::Rational(Rational::new(1, 8))),
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
    fn test_token_quote() {
        assert_eq!(token().parse("'"), Ok((Token::Quote, "")));
    }

    #[test]
    fn test_token_quasiquote() {
        assert_eq!(token().parse("`"), Ok((Token::Quasiquote, "")));
    }

    #[test]
    fn test_token_unquote() {
        assert_eq!(token().parse(","), Ok((Token::Unquote, "")));
    }

    #[test]
    fn test_token_unquote_splicing() {
        assert_eq!(token().parse(",@"), Ok((Token::UnquoteSplicing, "")));
    }

    #[test]
    fn test_token_begin_vector() {
        assert_eq!(token().parse("#("), Ok((Token::BeginVector, "")));
    }

    #[test]
    fn test_token_bool() {
        assert_eq!(token().parse("#t"), Ok((Token::Bool(true), "")));
        assert_eq!(token().parse("#f"), Ok((Token::Bool(false), "")));
    }

    #[test]
    fn test_token_char() {
        assert_eq!(token().parse("#\\space"), Ok((Token::Char(' '), "")));
        assert_eq!(token().parse("#\\SPACE"), Ok((Token::Char(' '), "")));
        assert_eq!(token().parse("#\\SpAcE"), Ok((Token::Char(' '), "")));
        assert_eq!(token().parse("#\\newline"), Ok((Token::Char('\n'), "")));
        assert_eq!(token().parse("#\\NEWLINE"), Ok((Token::Char('\n'), "")));
        assert_eq!(token().parse("#\\nEwLiNe"), Ok((Token::Char('\n'), "")));
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

    #[test]
    fn test_token_ident() {
        assert_eq!(
            token().parse("list->vector"),
            Ok((Token::Ident("list->vector"), ""))
        );
        assert_eq!(token().parse("<=?"), Ok((Token::Ident("<=?"), "")));
        assert_eq!(token().parse("q"), Ok((Token::Ident("q"), "")));
        assert_eq!(token().parse("soup"), Ok((Token::Ident("soup"), "")));
        assert_eq!(token().parse("V17a"), Ok((Token::Ident("V17a"), "")));
        assert_eq!(
            token().parse("a34kTMNs"),
            Ok((Token::Ident("a34kTMNs"), ""))
        );
        assert_eq!(token().parse("+"), Ok((Token::Ident("+"), "")));
        assert_eq!(token().parse("-"), Ok((Token::Ident("-"), "")));
        assert_eq!(token().parse("..."), Ok((Token::Ident("..."), "")));
        assert_eq!(
            token().parse("the-word-recursion-has-many-meanings"),
            Ok((Token::Ident("the-word-recursion-has-many-meanings"), ""))
        );
    }

    #[test]
    fn test_token_keyword() {
        assert_eq!(
            token().parse("quote"),
            Ok((Token::Keyword(Keyword::Quote), ""))
        );
        assert_eq!(
            token().parse("lambda"),
            Ok((Token::Keyword(Keyword::Lambda), ""))
        );
        assert_eq!(token().parse("if"), Ok((Token::Keyword(Keyword::If), "")));
        assert_eq!(
            token().parse("set!"),
            Ok((Token::Keyword(Keyword::Set), ""))
        );
        assert_eq!(
            token().parse("begin"),
            Ok((Token::Keyword(Keyword::Begin), ""))
        );
        assert_eq!(
            token().parse("cond"),
            Ok((Token::Keyword(Keyword::Cond), ""))
        );
        assert_eq!(token().parse("and"), Ok((Token::Keyword(Keyword::And), "")));
        assert_eq!(token().parse("or"), Ok((Token::Keyword(Keyword::Or), "")));
        assert_eq!(
            token().parse("case"),
            Ok((Token::Keyword(Keyword::Case), ""))
        );
        assert_eq!(token().parse("let"), Ok((Token::Keyword(Keyword::Let), "")));
        assert_eq!(
            token().parse("let*"),
            Ok((Token::Keyword(Keyword::LetStar), ""))
        );
        assert_eq!(
            token().parse("letrec"),
            Ok((Token::Keyword(Keyword::LetRec), ""))
        );
        assert_eq!(token().parse("do"), Ok((Token::Keyword(Keyword::Do), "")));
        assert_eq!(
            token().parse("delay"),
            Ok((Token::Keyword(Keyword::Delay), ""))
        );
        assert_eq!(
            token().parse("quasiquote"),
            Ok((Token::Keyword(Keyword::Quasiquote), ""))
        );
        assert_eq!(
            token().parse("else"),
            Ok((Token::Keyword(Keyword::Else), ""))
        );
        assert_eq!(
            token().parse("=>"),
            Ok((Token::Keyword(Keyword::RightArrow), ""))
        );
        assert_eq!(
            token().parse("define"),
            Ok((Token::Keyword(Keyword::Define), ""))
        );
        assert_eq!(
            token().parse("unquote"),
            Ok((Token::Keyword(Keyword::Unquote), ""))
        );
        assert_eq!(
            token().parse("unquote-splicing"),
            Ok((Token::Keyword(Keyword::UnquoteSplicing), ""))
        );
    }

    #[test]
    fn test_token_number() {
        assert_eq!(
            token().parse("123"),
            Ok((Token::Number(Number::Integer(123)), ""))
        );

        assert_eq!(
            token().parse("-123"),
            Ok((Token::Number(Number::Integer(-123)), ""))
        );

        assert_eq!(
            token().parse("123.456"),
            Ok((Token::Number(Number::Real(123.456)), ""))
        );

        assert_eq!(
            token().parse("-123.456"),
            Ok((Token::Number(Number::Real(-123.456)), ""))
        );

        assert_eq!(
            token().parse("#e123.456"),
            Ok((
                Token::Number(Number::Rational(Rational::new(123_456, 1000))),
                ""
            ))
        );
    }
}
