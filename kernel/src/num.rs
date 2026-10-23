//! Pinned numeric semantics for ordered comparison.
//!
//! Both the kernel and the Tcl reference (`_canonical_number`) accept only
//! the canonical decimal grammar
//!
//! ```text
//! number := "-"? ("0" | [1-9][0-9]*) ("." [0-9]+)? ([eE] [+-]? [0-9]+)?
//! ```
//!
//! and on it reproduce Tcl 8.6 `expr` exactly: integers compare as exact
//! arbitrary-precision values, values with a fraction or exponent compare as
//! correctly rounded IEEE doubles, and mixed comparisons are exact.

use std::cmp::Ordering;

#[derive(Debug, Clone, PartialEq)]
pub enum Num {
    /// Exact integer: sign and magnitude in decimal without leading zeros.
    Int {
        negative: bool,
        digits: String,
    },
    Double(f64),
}

pub fn parse(text: &str) -> Option<Num> {
    let b = text.as_bytes();
    let mut i = 0;
    let negative = b.first() == Some(&b'-');
    if negative {
        i += 1;
    }
    let int_start = i;
    while i < b.len() && b[i].is_ascii_digit() {
        i += 1;
    }
    let int_part = &text[int_start..i];
    if int_part.is_empty() || (int_part.len() > 1 && int_part.starts_with('0')) {
        return None;
    }
    let mut is_int = true;
    if i < b.len() && b[i] == b'.' {
        i += 1;
        let s = i;
        while i < b.len() && b[i].is_ascii_digit() {
            i += 1;
        }
        if i == s {
            return None;
        }
        is_int = false;
    }
    if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
        i += 1;
        if i < b.len() && (b[i] == b'+' || b[i] == b'-') {
            i += 1;
        }
        let s = i;
        while i < b.len() && b[i].is_ascii_digit() {
            i += 1;
        }
        if i == s {
            return None;
        }
        is_int = false;
    }
    if i != b.len() {
        return None;
    }
    if is_int {
        let zero = int_part == "0";
        Some(Num::Int {
            negative: negative && !zero,
            digits: int_part.to_owned(),
        })
    } else {
        text.parse::<f64>().ok().map(Num::Double)
    }
}

pub fn compare(a: &Num, b: &Num) -> Ordering {
    match (a, b) {
        (Num::Int { .. }, Num::Int { .. }) => cmp_int(a, b),
        (Num::Double(x), Num::Double(y)) => {
            x.partial_cmp(y).expect("canonical doubles are never NaN")
        }
        (Num::Int { negative, digits }, Num::Double(d)) => cmp_int_double(*negative, digits, *d),
        (Num::Double(d), Num::Int { negative, digits }) => {
            cmp_int_double(*negative, digits, *d).reverse()
        }
    }
}

fn cmp_int(a: &Num, b: &Num) -> Ordering {
    let (
        Num::Int {
            negative: na,
            digits: da,
        },
        Num::Int {
            negative: nb,
            digits: db,
        },
    ) = (a, b)
    else {
        unreachable!()
    };
    let magnitude = da.len().cmp(&db.len()).then_with(|| da.cmp(db));
    match (na, nb) {
        (false, false) => magnitude,
        (true, true) => magnitude.reverse(),
        (false, true) => Ordering::Greater,
        (true, false) => Ordering::Less,
    }
}

/// Exact comparison of the integer `(-1)^negative * digits` with `d`.
fn cmp_int_double(negative: bool, digits: &str, d: f64) -> Ordering {
    if d.is_infinite() {
        return if d > 0.0 {
            Ordering::Less
        } else {
            Ordering::Greater
        };
    }
    let int_sign = if digits == "0" {
        0
    } else if negative {
        -1
    } else {
        1
    };
    let dbl_sign = if d == 0.0 {
        0
    } else if d < 0.0 {
        -1
    } else {
        1
    };
    if int_sign != dbl_sign {
        return int_sign.cmp(&dbl_sign);
    }
    if int_sign == 0 {
        return Ordering::Equal;
    }
    // |d| = mantissa * 2^exponent exactly.
    let bits = d.abs().to_bits();
    let biased = ((bits >> 52) & 0x7ff) as i32;
    let fraction = bits & ((1u64 << 52) - 1);
    let (mantissa, exponent) = if biased == 0 {
        (fraction, -1074)
    } else {
        (fraction | (1u64 << 52), biased - 1075)
    };
    let mut lhs = Big::from_decimal(digits);
    let mut rhs = Big::from_u64(mantissa);
    if exponent >= 0 {
        rhs.shl(exponent as u32);
    } else {
        lhs.shl((-exponent) as u32);
    }
    let magnitude = lhs.cmp(&rhs);
    if int_sign < 0 {
        magnitude.reverse()
    } else {
        magnitude
    }
}

/// Minimal unsigned big integer, little-endian base 2^32 limbs.
#[derive(Debug, PartialEq, Eq)]
struct Big(Vec<u32>);

impl Big {
    fn from_u64(v: u64) -> Self {
        let mut b = Big(vec![v as u32, (v >> 32) as u32]);
        b.trim();
        b
    }

    fn from_decimal(digits: &str) -> Self {
        let mut b = Big(Vec::new());
        for chunk in digits.as_bytes().chunks(9) {
            let mut scale = 1u64;
            let mut value = 0u64;
            for &c in chunk {
                scale *= 10;
                value = value * 10 + u64::from(c - b'0');
            }
            b.mul_add(scale, value);
        }
        b
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
    }

    fn shl(&mut self, bits: u32) {
        let (limbs, rem) = ((bits / 32) as usize, bits % 32);
        if rem > 0 {
            let mut carry = 0u32;
            for limb in &mut self.0 {
                let v = (u64::from(*limb) << rem) | u64::from(carry);
                *limb = v as u32;
                carry = (v >> 32) as u32;
            }
            if carry > 0 {
                self.0.push(carry);
            }
        }
        self.0.splice(0..0, std::iter::repeat_n(0, limbs));
        self.trim();
    }

    fn trim(&mut self) {
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
            "0", "-0", "7", "-12", "0.5", "1e3", "1.5E-3", "1e400", "-1e400",
        ] {
            assert!(parse(ok).is_some(), "{ok}");
        }
        for bad in [
            "", "-", "007", "00.5", "0x10", " 1", "1 ", "+1", "1.", ".5", "1e", "Inf", "NaN", "1_0",
        ] {
            assert!(parse(bad).is_none(), "{bad}");
        }
    }

    #[test]
    fn integers_are_exact() {
        assert_eq!(cmp("-0", "0"), Ordering::Equal);
        assert_eq!(
            cmp(
                "123456789012345678901234567890",
                "123456789012345678901234567891"
            ),
            Ordering::Less
        );
        assert_eq!(cmp("-5", "3"), Ordering::Less);
        assert_eq!(cmp("-50", "-6"), Ordering::Less);
    }

    #[test]
    fn doubles_round_like_ieee() {
        assert_eq!(cmp("0.1", "0.10000000000000000001"), Ordering::Equal);
        assert_eq!(cmp("1e400", "1e500"), Ordering::Equal);
        assert_eq!(cmp("1e-400", "0.0"), Ordering::Equal);
    }

    #[test]
    fn mixed_comparisons_are_exact() {
        assert_eq!(
            cmp("9007199254740993", "9007199254740992.0"),
            Ordering::Greater
        );
        assert_eq!(
            cmp("9007199254740992", "9007199254740992.0"),
            Ordering::Equal
        );
        assert_eq!(cmp("3", "2.5"), Ordering::Greater);
        assert_eq!(cmp("2", "2.5"), Ordering::Less);
        assert_eq!(cmp("-3", "-2.5"), Ordering::Less);
        assert_eq!(cmp("0", "-0.0"), Ordering::Equal);
        assert_eq!(cmp("1", "1e-400"), Ordering::Greater);
        assert_eq!(cmp(&"9".repeat(400), "1e400"), Ordering::Less);
    }
}
