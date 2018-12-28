// Copyright 2018 Barret Rennie.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use combine::{
    parser::{choice::choice, item::item},
    ParseError, Parser, RangeStream,
};

/// A parsed token.
#[derive(Clone, Debug, PartialEq)]
pub enum Token {
    /// An open parenthesis.
    Open,
    /// A close parenthesis.
    Close,
}

/// Parse a token.
fn token<'a, I>() -> impl Parser<Input = I, Output = Token>
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    choice((
        item('(').map(|_| Token::Open),
        item(')').map(|_| Token::Close),
    ))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_token_open() {
        assert_eq!(token().parse("("), Ok((Token::Open, "")));
    }

    #[test]
    fn test_token_close() {
        assert_eq!(token().parse("("), Ok((Token::Open, "")));
    }
}
