// Copyright 2018 Barret Rennie.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use combine::{
    parser::{
        choice::{choice, optional, or},
        item::{item, satisfy},
    },
    ParseError, Parser, RangeStream,
};

/// Whether a number is to be parsed into an exact representation (such as an
/// integer or a rational) or an inexact represenation (such as a float).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Exactness {
    /// An exact representation should be parsed.
    Exact,
    /// An inexact represenation should be parsed.
    Inexact,
}

/// Supported radices of number literals.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Radix {
    /// Base 2.
    Binary,
    /// Base 8.
    Octal,
    /// Base 10.
    Decimal,
    /// Base 16.
    Hexadecimal,
}

impl From<Radix> for u32 {
    fn from(radix: Radix) -> u32 {
        match radix {
            Radix::Binary => 2,
            Radix::Octal => 8,
            Radix::Decimal => 10,
            Radix::Hexadecimal => 16,
        }
    }
}

/// Parse the sign of a number.
fn sign<'a, I>() -> impl Parser<Input = I, Output = isize>
where
    I: RangeStream<Item = char, Range = &'a str>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    or(item('+').map(|_| 1), item('-').map(|_| -1))
}

/// Parse the prefix of a number.
///
/// This will indicate the radix and exactness of the number.
fn prefix<'a, I>() -> impl Parser<Input = I, Output = (Radix, Option<Exactness>)>
where
    I: RangeStream<Item = char, Range = &'a str>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let exactness_tail = || {
        or(
            satisfy(|c| c == 'e' || c == 'E').map(|_| Exactness::Exact),
            satisfy(|c| c == 'i' || c == 'I').map(|_| Exactness::Inexact),
        )
    };

    let radix_tail = || {
        choice((
            satisfy(|c| c == 'b' || c == 'B').map(|_| Radix::Binary),
            satisfy(|c| c == 'o' || c == 'O').map(|_| Radix::Octal),
            satisfy(|c| c == 'd' || c == 'D').map(|_| Radix::Decimal),
            satisfy(|c| c == 'x' || c == 'X').map(|_| Radix::Hexadecimal),
        ))
    };

    optional(
        item('#')
            .with(or(
                exactness_tail().map(|exact| (None, Some(exact))),
                radix_tail().map(|radix| (Some(radix), None)),
            ))
            .then(move |state| match state {
                (myb_radix @ Some(_), None) => optional(item('#').with(exactness_tail()))
                    .map(move |myb_exact| (myb_radix, myb_exact))
                    .left(),

                (None, myb_exact @ Some(_)) => optional(item('#').with(radix_tail()))
                    .map(move |myb_radix| (myb_radix, myb_exact))
                    .right(),

                _ => unreachable!(),
            }),
    )
    .map(|myb_state| {
        myb_state
            .map(|(myb_radix, myb_exact)| (myb_radix.unwrap_or(Radix::Decimal), myb_exact))
            .unwrap_or((Radix::Decimal, None))
    })
}

/// Parse a single digit in a given radix.
fn digit<'a, I>(radix: Radix) -> impl Parser<Input = I, Output = u32>
where
    I: RangeStream<Item = char, Range = &'a str>,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    let radix = radix.into();
    satisfy(move |c: char| c.is_digit(radix)).map(move |c: char| c.to_digit(radix).unwrap())
}

#[cfg(test)]
mod test {
    use std::char::from_digit;

    use super::*;

    #[test]
    fn test_sign() {
        assert_eq!(sign().parse("+"), Ok((1, "")));
        assert_eq!(sign().parse("-"), Ok((-1, "")));
    }

    #[test]
    fn test_prefix_simple() {
        assert_eq!(prefix().parse(""), Ok(((Radix::Decimal, None), "")));
        assert_eq!(
            prefix().parse("#e"),
            Ok(((Radix::Decimal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#E"),
            Ok(((Radix::Decimal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#i"),
            Ok(((Radix::Decimal, Some(Exactness::Inexact)), ""))
        );
        assert_eq!(
            prefix().parse("#I"),
            Ok(((Radix::Decimal, Some(Exactness::Inexact)), ""))
        );

        assert_eq!(prefix().parse("#b"), Ok(((Radix::Binary, None), "")));
        assert_eq!(prefix().parse("#B"), Ok(((Radix::Binary, None), "")));
        assert_eq!(prefix().parse("#o"), Ok(((Radix::Octal, None), "")));
        assert_eq!(prefix().parse("#O"), Ok(((Radix::Octal, None), "")));
        assert_eq!(prefix().parse("#d"), Ok(((Radix::Decimal, None), "")));
        assert_eq!(prefix().parse("#D"), Ok(((Radix::Decimal, None), "")));
        assert_eq!(prefix().parse("#x"), Ok(((Radix::Hexadecimal, None), "")));
        assert_eq!(prefix().parse("#X"), Ok(((Radix::Hexadecimal, None), "")));
    }

    #[test]
    fn test_prefix_full() {
        assert_eq!(
            prefix().parse("#b#e"),
            Ok(((Radix::Binary, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#e#b"),
            Ok(((Radix::Binary, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#b#i"),
            Ok(((Radix::Binary, Some(Exactness::Inexact)), ""))
        );
        assert_eq!(
            prefix().parse("#i#b"),
            Ok(((Radix::Binary, Some(Exactness::Inexact)), ""))
        );

        assert_eq!(
            prefix().parse("#o#e"),
            Ok(((Radix::Octal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#e#o"),
            Ok(((Radix::Octal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#o#i"),
            Ok(((Radix::Octal, Some(Exactness::Inexact)), ""))
        );
        assert_eq!(
            prefix().parse("#i#o"),
            Ok(((Radix::Octal, Some(Exactness::Inexact)), ""))
        );

        assert_eq!(
            prefix().parse("#d#e"),
            Ok(((Radix::Decimal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#e#d"),
            Ok(((Radix::Decimal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#d#i"),
            Ok(((Radix::Decimal, Some(Exactness::Inexact)), ""))
        );
        assert_eq!(
            prefix().parse("#i#d"),
            Ok(((Radix::Decimal, Some(Exactness::Inexact)), ""))
        );

        assert_eq!(
            prefix().parse("#x#e"),
            Ok(((Radix::Hexadecimal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#e#x"),
            Ok(((Radix::Hexadecimal, Some(Exactness::Exact)), ""))
        );
        assert_eq!(
            prefix().parse("#x#i"),
            Ok(((Radix::Hexadecimal, Some(Exactness::Inexact)), ""))
        );
        assert_eq!(
            prefix().parse("#i#x"),
            Ok(((Radix::Hexadecimal, Some(Exactness::Inexact)), ""))
        );
    }

    #[test]
    fn test_digit() {
        assert_eq!(digit(Radix::Binary).parse("0"), Ok((0, "")));
        assert_eq!(digit(Radix::Binary).parse("1"), Ok((1, "")));

        for i in 0..=7 {
            let input = format!("{}", from_digit(i, 8).unwrap());

            assert_eq!(digit(Radix::Octal).parse(&*input), Ok((i, "")), "i = {}", i);
        }

        for i in 0..=9 {
            let input = format!("{}", from_digit(i, 10).unwrap());

            assert_eq!(
                digit(Radix::Decimal).parse(&*input),
                Ok((i, "")),
                "i = {}",
                i
            );
        }

        for i in 0x0..=0xF {
            let input = format!("{}", from_digit(i, 16).unwrap());

            assert_eq!(
                digit(Radix::Hexadecimal).parse(&*input),
                Ok((i, "")),
                "i = {}",
                i
            );
        }
    }

}
