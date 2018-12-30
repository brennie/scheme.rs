// Copyright 2018 Barret Rennie.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use combine::{
    parser::{
        choice::{optional, or},
        item::item,
    },
    ParseError, Parser, RangeStream,
};

/// Parse the sign of a number.
fn sign<'a, I>() -> impl Parser<Input = I, Output = isize>
where
    I: RangeStream<Item = char, Range = &'a str>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    optional(or(item('+').map(|_| 1), item('-').map(|_| -1))).map(|myb_sign| myb_sign.unwrap_or(1))
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_sign() {
        assert_eq!(sign().parse("+"), Ok((1, "")));
        assert_eq!(sign().parse("-"), Ok((-1, "")));
        assert_eq!(sign().parse(""), Ok((1, "")));
    }
}
