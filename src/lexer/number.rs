// Copyright 2018 Barret Rennie.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license <LICENSE-MIT
// or http://opensource.org/licenses/MIT>, at your option. This file may not be
// copied, modified, or distributed except according to those terms.

use combine::{
    parser::{
        choice::{choice, optional, or},
        combinator::attempt,
        item::{item, satisfy},
        range::{recognize, recognize_with_value},
        repeat::skip_many1,
    },
    ParseError, Parser, RangeStream,
};
use either::Either;
use num_complex::Complex64;
use num_rational::Rational;

/// A numerical value.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Number {
    /// A complex value
    Complex(Complex64),
    /// A real value.
    Real(f64),
    /// A rational value.
    Rational(Rational),
    /// An integer value.
    Integer(isize),
}

impl Number {
    pub(self) fn promote_to_real(self) -> f64 {
        match self {
            Number::Complex(_) => unimplemented!(),
            Number::Real(r) => r,
            Number::Rational(q) => *q.numer() as f64 / *q.denom() as f64,
            Number::Integer(z) => z as f64,
        }
    }
}

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

pub fn number<'a, I>() -> impl Parser<Input = I, Output = Number> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    prefix().then(|(radix, exactness)| complex(radix, exactness))
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

/// A parser to detect the presence of a suffix.
///
/// This parser only returns whether or not the suffix is present because it will
/// only be used to recognize input, not to create a value.
fn suffix<'a, I>() -> impl Parser<Input = I, Output = isize> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    item('e')
        .with((optional(sign()), uinteger(Radix::Decimal)))
        .map(|(sign, exp)| sign.unwrap_or(1) * exp)
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

fn complex<'a, I>(
    radix: Radix,
    exactness: Option<Exactness>,
) -> impl Parser<Input = I, Output = Number> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    or(
        (
            attempt(real(radix, exactness)),
            optional(or(
                item('@')
                    .with(real(radix, Some(Exactness::Inexact)))
                    .map(Either::Left),
                (sign(), optional(ureal(radix, Some(Exactness::Inexact))))
                    .skip(item('i'))
                    .map(Either::Right),
            )),
        )
            .map(|(r, myb_b)| match myb_b {
                Some(Either::Left(Number::Real(theta))) => {
                    Number::Complex(Complex64::from_polar(&r.promote_to_real(), &theta))
                }
                Some(Either::Right((sign, myb_im))) => {
                    let im = myb_im.unwrap_or(Number::Real(1f64)).promote_to_real();
                    Number::Complex(Complex64::new(r.promote_to_real(), sign as f64 * im))
                }
                None => r,
                _ => unreachable!(),
            }),
        (
            sign(),
            optional(ureal(radix, Some(Exactness::Inexact))).skip(item('i')),
        )
            .map(|(sign, myb_n)| {
                let im = myb_n.unwrap_or(Number::Real(1f64)).promote_to_real();
                Number::Complex(Complex64::new(0f64, sign as f64 * im))
            }),
    )
}

fn real<'a, I>(
    radix: Radix,
    exactness: Option<Exactness>,
) -> impl Parser<Input = I, Output = Number> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    (optional(sign()), ureal(radix, exactness)).map(|(sign, n)| match (sign.unwrap_or(1), n) {
        (1, _) => n,
        (-1, Number::Complex(_)) => unreachable!(),
        (-1, Number::Real(r)) => Number::Real(-r),
        (-1, Number::Rational(q)) => Number::Rational(-q),
        (-1, Number::Integer(i)) => Number::Integer(-i),
        (_, _) => unreachable!(),
    })
}

fn ureal<'a, I>(
    radix: Radix,
    exactness: Option<Exactness>,
) -> impl Parser<Input = I, Output = Number> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    type Which<'a> = Either<isize, (Option<&'a str>, Option<isize>)>;

    if radix == Radix::Decimal {
        recognize_with_value((
            uinteger(radix),
            or(
                item('/').with(uinteger(radix)).map(Either::Left),
                (
                    optional(item('.').with(recognize(skip_many1(digit(radix))))),
                    optional(suffix()),
                )
                    .map(Either::Right),
            ),
        ))
        .map(
            move |(s, (a, which)): (&'a str, (isize, Which<'a>))| match (exactness, which) {
                (Some(Exactness::Exact), Either::Left(b)) | (None, Either::Left(b)) => {
                    Number::Rational(Rational::new(a, b))
                }
                (Some(Exactness::Inexact), Either::Left(b)) => Number::Real(a as f64 / b as f64),
                (None, Either::Right((None, None))) => Number::Integer(a),
                (Some(Exactness::Inexact), Either::Right(..)) | (None, Either::Right(..)) => {
                    Number::Real(str::parse::<f64>(s).unwrap())
                }
                (Some(Exactness::Exact), Either::Right((Some(fract_s), myb_exp))) => {
                    let mut total_count = 0;
                    let mut count = 0;
                    let mut numer = a;
                    for d in fract_s.chars().map(|c| c.to_digit(10).unwrap()) {
                        count += 1;

                        if d != 0 {
                            numer *= 10isize.pow(count);
                            numer += d as isize;
                            total_count += count;
                            count = 0;
                        }
                    }

                    let mut denom = 10isize.pow(total_count);

                    if let Some(exp) = myb_exp {
                        if exp > 0 {
                            numer *= 10isize.pow(exp as u32);
                        } else {
                            denom *= 10isize.pow((-exp) as u32);
                        }
                    }

                    Number::Rational(Rational::new(numer, denom))
                }
                (Some(Exactness::Exact), Either::Right((None, Some(exp)))) => {
                    if exp > 0 {
                        Number::Integer(a * 10isize.pow(exp as u32))
                    } else {
                        Number::Rational(Rational::new(a, 10isize.pow((-exp) as u32)))
                    }
                }
                (Some(Exactness::Exact), Either::Right((None, None))) => Number::Integer(a),
            },
        )
        .left()
    } else {
        (uinteger(radix), optional(item('/').with(uinteger(radix))))
            .map(move |(a, myb_b)| match (exactness, myb_b) {
                (Some(Exactness::Exact), Some(b)) | (None, Some(b)) => {
                    Number::Rational(Rational::new(a, b))
                }
                (Some(Exactness::Exact), None) | (None, None) => Number::Integer(a),
                (Some(Exactness::Inexact), Some(b)) => Number::Real(a as f64 / b as f64),
                (Some(Exactness::Inexact), None) => Number::Real(a as f64),
            })
            .right()
    }
}

fn uinteger<'a, I>(radix: Radix) -> impl Parser<Input = I, Output = isize> + 'a
where
    I: RangeStream<Item = char, Range = &'a str> + 'a,
    I::Error: ParseError<I::Item, I::Range, I::Position>,
{
    recognize(skip_many1(digit(radix)))
        .map(move |digits| isize::from_str_radix(digits, radix.into()).unwrap())
}

#[cfg(test)]
mod test {
    use std::char::from_digit;

    use combine::error::StringStreamError;

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

    #[test]
    fn test_suffix() {
        assert_eq!(suffix().parse("e"), Err(StringStreamError::UnexpectedParse));
        assert_eq!(suffix().parse("e123"), Ok((123, "")));
        assert_eq!(suffix().parse("e+123"), Ok((123, "")));
        assert_eq!(suffix().parse("e-123"), Ok((-123, "")));
    }

    #[test]
    fn test_literal_integer() {
        assert_eq!(number().parse("123"), Ok((Number::Integer(123), "")));
        assert_eq!(number().parse("#e123"), Ok((Number::Integer(123), "")));
        assert_eq!(number().parse("#e#d123"), Ok((Number::Integer(123), "")));
        assert_eq!(number().parse("#d#e123"), Ok((Number::Integer(123), "")));
        assert_eq!(number().easy_parse("#b100"), Ok((Number::Integer(4), "")));
        assert_eq!(number().parse("#o123"), Ok((Number::Integer(0o123), "")));
        assert_eq!(number().parse("#x123"), Ok((Number::Integer(0x123), "")));

        assert_eq!(number().parse("-123"), Ok((Number::Integer(-123), "")));
        assert_eq!(number().parse("#e-123"), Ok((Number::Integer(-123), "")));
        assert_eq!(number().parse("#e-123"), Ok((Number::Integer(-123), "")));
        assert_eq!(number().parse("#b-100"), Ok((Number::Integer(-4), "")));
        assert_eq!(number().parse("#o-123"), Ok((Number::Integer(-0o123), "")));
        assert_eq!(number().parse("#x-123"), Ok((Number::Integer(-0x123), "")));

        assert_eq!(number().parse("#e123e2"), Ok((Number::Integer(12300), "")));
    }

    #[test]
    fn test_literal_rational() {
        assert_eq!(
            number().parse("123/456"),
            Ok((Number::Rational(Rational::new(123, 456)), ""))
        );

        assert_eq!(
            number().parse("-123/456"),
            Ok((Number::Rational(Rational::new(-123, 456)), ""))
        );

        assert_eq!(
            number().parse("#e123.456"),
            Ok((Number::Rational(Rational::new(123_456, 1000)), ""))
        );

        assert_eq!(
            number().parse("#e1.23e2"),
            Ok((Number::Rational(Rational::new(123, 1)), ""))
        );

        assert_eq!(
            number().parse("#e123e-2"),
            Ok((Number::Rational(Rational::new(123, 100)), ""))
        );
    }

    #[test]
    fn test_literal_real() {
        assert_eq!(number().parse("123.456"), Ok((Number::Real(123.456), "")));
        assert_eq!(number().parse("-123.456"), Ok((Number::Real(-123.456), "")));
        assert_eq!(number().parse("#i123"), Ok((Number::Real(123.0), "")));
        assert_eq!(number().parse("#i-123"), Ok((Number::Real(-123.0), "")));
        assert_eq!(number().parse("#i1/23"), Ok((Number::Real(1.0 / 23.0), "")));
        assert_eq!(number().parse("1e2"), Ok((Number::Real(1e2), "")));

        assert_eq!(number().parse("#i#b10"), Ok((Number::Real(2.0), "")));
        assert_eq!(number().parse("#i#o10"), Ok((Number::Real(8.0), "")));
        assert_eq!(number().parse("#i#x10"), Ok((Number::Real(16.0), "")));
        assert_eq!(number().parse("#i#xff"), Ok((Number::Real(255.0), "")));
    }

    #[test]
    fn test_literal_complex() {
        assert_eq!(
            number().parse("+i"),
            Ok((Number::Complex(Complex64::new(0f64, 1f64)), ""))
        );
        assert_eq!(
            number().parse("-i"),
            Ok((Number::Complex(Complex64::new(0f64, -1f64)), ""))
        );

        assert_eq!(
            number().easy_parse("1+i"),
            Ok((Number::Complex(Complex64::new(1f64, 1f64)), ""))
        );
        assert_eq!(
            number().parse("1-i"),
            Ok((Number::Complex(Complex64::new(1f64, -1f64)), ""))
        );

        assert_eq!(
            number().parse("-1+i"),
            Ok((Number::Complex(Complex64::new(-1f64, 1f64)), ""))
        );
        assert_eq!(
            number().parse("-1-i"),
            Ok((Number::Complex(Complex64::new(-1f64, -1f64)), ""))
        );

        assert_eq!(
            number().parse("123+456i"),
            Ok((Number::Complex(Complex64::new(123f64, 456f64)), "")),
        );
        assert_eq!(
            number().parse("123-456i"),
            Ok((Number::Complex(Complex64::new(123f64, -456f64)), "")),
        );
        assert_eq!(
            number().parse("-123+456i"),
            Ok((Number::Complex(Complex64::new(-123f64, 456f64)), "")),
        );
        assert_eq!(
            number().parse("-123-456i"),
            Ok((Number::Complex(Complex64::new(-123f64, -456f64)), "")),
        );

        assert_eq!(
            number().parse("1@1"),
            Ok((Number::Complex(Complex64::from_polar(&1f64, &1f64)), "")),
        );
        assert_eq!(
            number().parse("1@-1"),
            Ok((Number::Complex(Complex64::from_polar(&1f64, &-1f64)), "")),
        );
        assert_eq!(
            number().parse("-1@1"),
            Ok((Number::Complex(Complex64::from_polar(&-1f64, &1f64)), "")),
        );
        assert_eq!(
            number().parse("-1@-1"),
            Ok((Number::Complex(Complex64::from_polar(&-1f64, &-1f64)), "")),
        );

        assert_eq!(
            number().parse("#e+i"),
            Ok((Number::Complex(Complex64::new(0f64, 1f64)), "")),
        );
        assert_eq!(
            number().parse("#e-i"),
            Ok((Number::Complex(Complex64::new(0f64, -1f64)), "")),
        );
        assert_eq!(
            number().parse("#e1+1i"),
            Ok((Number::Complex(Complex64::new(1f64, 1f64)), "")),
        );
        assert_eq!(
            number().parse("#e1-1i"),
            Ok((Number::Complex(Complex64::new(1f64, -1f64)), "")),
        );
        assert_eq!(
            number().parse("#e-1+1i"),
            Ok((Number::Complex(Complex64::new(-1f64, 1f64)), "")),
        );
        assert_eq!(
            number().parse("#e-1-1i"),
            Ok((Number::Complex(Complex64::new(-1f64, -1f64)), "")),
        );
        assert_eq!(
            number().parse("#e1@1"),
            Ok((Number::Complex(Complex64::from_polar(&1f64, &1f64)), "")),
        );
        assert_eq!(
            number().parse("#e1@-1"),
            Ok((Number::Complex(Complex64::from_polar(&1f64, &-1f64)), "")),
        );
        assert_eq!(
            number().parse("#e-1@1"),
            Ok((Number::Complex(Complex64::from_polar(&-1f64, &1f64)), "")),
        );
        assert_eq!(
            number().parse("#e-1@-1"),
            Ok((Number::Complex(Complex64::from_polar(&-1f64, &-1f64)), "")),
        );
    }
}
