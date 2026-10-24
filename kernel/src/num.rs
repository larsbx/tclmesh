//! Exact canonical decimals for ordered comparison.
//!
//! The kernel, the Tcl reference (`_decimal`), and the Lean specification
//! (`spec/TclMesh/Decimal.lean`) accept the same grammar
//!
//! ```text
//! number := "-"? ("0" | [1-9][0-9]*) ("." [0-9]+)? ([eE] [+-]? [0-9]+)?
//! ```
//!
//! with the written exponent at most `MAX_EXP` in magnitude. A number denotes
//! `±mantissa · 10^exponent` exactly; two numbers are compared by scaling both
//! to the smaller exponent and comparing integers.

use std::cmp::Ordering;

pub const MAX_EXP: u32 = 1000;

#[derive(Debug, Clone, PartialEq)]
pub struct Num {
    negative: bool,
    mantissa: Big,
    exponent: i64,
}

fn split_digits(s: &str) -> (&str, &str) {
    let end = s
        .bytes()
        .position(|b| !b.is_ascii_digit())
        .unwrap_or(s.len());
    s.split_at(end)
}

/// The exponent's magnitude without leading zeros, if at most `MAX_EXP`.
fn bounded_exp(digits: &str) -> Option<i64> {
    let digits = digits.trim_start_matches('0');
    match digits.len() {
        0 => Some(0),
        1..=4 => digits
            .parse::<u32>()
            .ok()
            .filter(|e| *e <= MAX_EXP)
            .map(i64::from),
        _ => None,
    }
}

pub fn parse(text: &str) -> Option<Num> {
    let (negative, rest) = match text.strip_prefix('-') {
        Some(rest) => (true, rest),
        None => (false, text),
    };
    let (int, rest) = split_digits(rest);
    if int.is_empty() || (int.len() > 1 && int.starts_with('0')) {
        return None;
    }
    let (frac, rest) = match rest.strip_prefix('.') {
        Some(after) => match split_digits(after) {
            ("", _) => return None,
            split => split,
        },
        None => ("", rest),
    };
    let (exp, rest) = match rest.strip_prefix(['e', 'E']) {
        Some(after) => {
            let (sign, after) = match after.as_bytes().first() {
                Some(b'-') => (-1, &after[1..]),
                Some(b'+') => (1, &after[1..]),
                _ => (1, after),
            };
            match split_digits(after) {
                ("", _) => return None,
                (digits, rest) => (sign * bounded_exp(digits)?, rest),
            }
        }
        None => (0, rest),
    };
    if !rest.is_empty() {
        return None;
    }
    let mantissa = Big::from_decimal(&format!("{int}{frac}"));
    Some(Num {
        negative: negative && !mantissa.is_zero(),
        mantissa,
        exponent: exp - frac.len() as i64,
    })
}

pub fn compare(a: &Num, b: &Num) -> Ordering {
    let e = a.exponent.min(b.exponent);
    let scale = |n: &Num| {
        let mut m = n.mantissa.clone();
        for _ in 0..(n.exponent - e) {
            m.mul_add(10, 0);
        }
        m
    };
    let magnitude = scale(a).cmp(&scale(b));
    match (a.negative, b.negative) {
        (false, false) => magnitude,
        (true, true) => magnitude.reverse(),
        (false, true) => Ordering::Greater,
        (true, false) => Ordering::Less,
    }
}

/// Minimal unsigned big integer, little-endian base 2^32 limbs, no trailing zeros.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Big(Vec<u32>);

impl Big {
    fn from_decimal(digits: &str) -> Self {
        let mut b = Big(Vec::new());
        for chunk in digits.as_bytes().chunks(9) {
            let (scale, value) = chunk.iter().fold((1u64, 0u64), |(s, v), &c| {
                (s * 10, v * 10 + u64::from(c - b'0'))
            });
            b.mul_add(scale, value);
        }
        b
    }

    fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    fn mul_add(&mut self, mul: u64, add: u64) {
        let mut carry = add;
        for limb in &mut self.0 {
            let v = u64::from(*limb) * mul + carry;
            *limb = v as u32;
            carry = v >> 32;
        }
        while carry > 0 {
            self.0.push(carry as u32);
            carry >>= 32;
        }
        while self.0.last() == Some(&0) {
            self.0.pop();
        }
    }
}

impl Ord for Big {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0
            .len()
            .cmp(&other.0.len())
            .then_with(|| self.0.iter().rev().cmp(other.0.iter().rev()))
    }
}

impl PartialOrd for Big {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cmp(a: &str, b: &str) -> Ordering {
        compare(&parse(a).unwrap(), &parse(b).unwrap())
    }

    #[test]
    fn grammar_is_canonical_decimal_only() {
        for ok in [
            "0",
            "-0",
            "7",
            "-12",
            "0.5",
            "1e3",
            "1.5E-3",
            "1e1000",
            "1e-1000",
            "1e0001000",
        ] {
            assert!(parse(ok).is_some(), "{ok}");
        }
        for bad in [
            "",
            "-",
            "007",
            "00.5",
            "0x10",
            " 1",
            "1 ",
            "+1",
            "1.",
            ".5",
            "1e",
            "Inf",
            "NaN",
            "1_0",
            "1e1001",
            "1e99999999999999999999",
        ] {
            assert!(parse(bad).is_none(), "{bad}");
        }
    }

    #[test]
    fn comparison_is_exact() {
        assert_eq!(cmp("-0", "0"), Ordering::Equal);
        assert_eq!(cmp("-0.0", "0"), Ordering::Equal);
        assert_eq!(cmp("1e3", "1000"), Ordering::Equal);
        assert_eq!(cmp("0.10", "0.1"), Ordering::Equal);
        assert_eq!(cmp("1E-2", "0.01"), Ordering::Equal);
        assert_eq!(cmp("0.1", "0.10000000000000000001"), Ordering::Less);
        assert_eq!(
            cmp("9007199254740993", "9007199254740992.0"),
            Ordering::Greater
        );
        assert_eq!(
            cmp(
                "123456789012345678901234567890",
                "123456789012345678901234567891"
            ),
            Ordering::Less
        );
        assert_eq!(cmp("-2.5", "-3"), Ordering::Greater);
        assert_eq!(cmp("-50", "-6"), Ordering::Less);
        assert_eq!(cmp("1e1000", "1e999"), Ordering::Greater);
        assert_eq!(cmp("1e-1000", "0"), Ordering::Greater);
    }
}
