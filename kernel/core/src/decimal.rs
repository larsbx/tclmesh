//! Exact canonical decimals; refines `TclMesh.Decimal`.
//!
//! ```text
//! number := "-"? ("0" | [1-9][0-9]*) ("." [0-9]+)? ([eE] [+-]? [0-9]+)?
//! ```
//!
//! with the written exponent at most `MAX_EXP` in magnitude. A number is
//! `±digits · 10^(exp - frac_len)`, where `digits` holds the mantissa's decimal
//! digits without leading zeros (empty for zero).

use crate::Order;

pub const MAX_EXP: u32 = 1000;

#[cfg_attr(test, derive(Debug))]
#[derive(Clone, PartialEq, Eq)]
pub struct Dec {
    pub negative: bool,
    /// Mantissa digits (values 0..=9), most significant first, no leading zero.
    pub digits: Vec<u8>,
    /// Written exponent, at most `MAX_EXP` in magnitude.
    pub exp: i32,
    /// Number of fraction digits.
    pub frac_len: u32,
}

fn is_digit(b: u8) -> bool {
    b >= b'0' && b <= b'9'
}

/// End of the run of digits starting at `i`.
fn digits_end(s: &[u8], mut i: usize) -> usize {
    while i < s.len() && is_digit(s[i]) {
        i += 1;
    }
    i
}

/// Appends the digits `s[from..to]`, skipping leading zeros of the whole mantissa.
fn push_digits(digits: &mut Vec<u8>, s: &[u8], from: usize, to: usize) {
    let mut i = from;
    while i < to {
        let d = s[i] - b'0';
        if d != 0 || digits.len() != 0 {
            digits.push(d);
        }
        i += 1;
    }
}

/// Value of the exponent digits `s[from..to]` if at most `MAX_EXP`.
/// Once the bound is exceeded the value stays saturated at `MAX_EXP + 1`.
fn bounded_exp(s: &[u8], from: usize, to: usize) -> Option<u32> {
    let mut value: u32 = 0;
    let mut i = from;
    while i < to {
        if value <= MAX_EXP {
            value = value * 10 + (s[i] - b'0') as u32;
        }
        i += 1;
    }
    if value <= MAX_EXP {
        Some(value)
    } else {
        None
    }
}

/// End of an optional leading `-`.
fn sign_end(s: &[u8]) -> usize {
    if s.len() > 0 && s[0] == b'-' {
        1
    } else {
        0
    }
}

/// End of an optional fraction `.digits` starting at `i`; `None` if a `.`
/// is not followed by a digit.
fn fraction_end(s: &[u8], i: usize) -> Option<usize> {
    if i < s.len() && s[i] == b'.' {
        let end = digits_end(s, i + 1);
        if end == i + 1 {
            None
        } else {
            Some(end)
        }
    } else {
        Some(i)
    }
}

fn is_exp_marker(b: u8) -> bool {
    b == b'e' || b == b'E'
}

fn is_sign(b: u8) -> bool {
    b == b'-' || b == b'+'
}

/// An optional exponent sign at `i`: whether it is `-`, and where the digits start.
fn exp_sign(s: &[u8], i: usize) -> (bool, usize) {
    if i < s.len() && is_sign(s[i]) {
        (s[i] == b'-', i + 1)
    } else {
        (false, i)
    }
}

/// The signed value of the exponent digits `s[from..to]` if at most `MAX_EXP`.
fn signed_exp(s: &[u8], from: usize, to: usize, minus: bool) -> Option<i32> {
    match bounded_exp(s, from, to) {
        Some(m) => Some(if minus { -(m as i32) } else { m as i32 }),
        None => None,
    }
}

/// An optional exponent `[eE][+-]?digits` starting at `i`: its value and end.
fn exponent(s: &[u8], i: usize) -> Option<(i32, usize)> {
    if i < s.len() && is_exp_marker(s[i]) {
        let (minus, start) = exp_sign(s, i + 1);
        let end = digits_end(s, start);
        if end == start {
            return None;
        }
        match signed_exp(s, start, end, minus) {
            Some(e) => Some((e, end)),
            None => None,
        }
    } else {
        Some((0, i))
    }
}

/// A nonempty integer part without a leading zero, unless it is `0` itself.
fn integer_ok(s: &[u8], start: usize, end: usize) -> bool {
    end != start && (end - start == 1 || s[start] != b'0')
}

/// Mantissa digits of `int[.frac]` without leading zeros, and the number of
/// fraction digits.
fn mantissa(s: &[u8], int_start: usize, int_end: usize, frac_end: usize) -> (Vec<u8>, u32) {
    let mut digits = Vec::new();
    push_digits(&mut digits, s, int_start, int_end);
    if frac_end > int_end {
        push_digits(&mut digits, s, int_end + 1, frac_end);
        (digits, (frac_end - int_end - 1) as u32)
    } else {
        (digits, 0)
    }
}

pub fn parse(s: &[u8]) -> Option<Dec> {
    if s.len() > u32::MAX as usize {
        return None;
    }
    let int_start = sign_end(s);
    let int_end = digits_end(s, int_start);
    if !integer_ok(s, int_start, int_end) {
        return None;
    }
    let frac_end = match fraction_end(s, int_end) {
        Some(e) => e,
        None => return None,
    };
    let (exp, end) = match exponent(s, frac_end) {
        Some(x) => x,
        None => return None,
    };
    if end != s.len() {
        return None;
    }
    let (digits, frac_len) = mantissa(s, int_start, int_end, frac_end);
    Some(Dec {
        negative: int_start == 1,
        digits,
        exp,
        frac_len,
    })
}

/// Digit `i` of `digits` followed by zeros.
fn padded(digits: &[u8], i: u64) -> u8 {
    if i < digits.len() as u64 {
        digits[i as usize]
    } else {
        0
    }
}

/// Compares `a · 10^pa` with `b · 10^pb` for nonzero digit strings without
/// leading zeros: longer is larger, equal lengths compare digit by digit.
fn compare_magnitude(a: &[u8], pa: u64, b: &[u8], pb: u64) -> Order {
    let la = a.len() as u64 + pa;
    let lb = b.len() as u64 + pb;
    if la < lb {
        return Order::Lt;
    }
    if la > lb {
        return Order::Gt;
    }
    // The first differing digit decides; later digits are scanned but ignored.
    let mut order = Order::Eq;
    let mut i: u64 = 0;
    while i < la {
        if let Order::Eq = order {
            let da = padded(a, i);
            let db = padded(b, i);
            if da < db {
                order = Order::Lt;
            } else if da > db {
                order = Order::Gt;
            }
        }
        i += 1;
    }
    order
}

fn reverse(o: Order) -> Order {
    match o {
        Order::Lt => Order::Gt,
        Order::Eq => Order::Eq,
        Order::Gt => Order::Lt,
    }
}

/// Order of the magnitudes of two nonzero decimals: both are scaled to the
/// smaller effective exponent `exp - frac_len`.
fn magnitude(a: &Dec, b: &Dec) -> Order {
    let ea = a.exp as i64 - a.frac_len as i64;
    let eb = b.exp as i64 - b.frac_len as i64;
    let e = if ea < eb { ea } else { eb };
    compare_magnitude(&a.digits, (ea - e) as u64, &b.digits, (eb - e) as u64)
}

/// Exact order of two decimals.
pub fn compare(a: &Dec, b: &Dec) -> Order {
    let a_zero = a.digits.len() == 0;
    let b_zero = b.digits.len() == 0;
    if a_zero {
        if b_zero {
            Order::Eq
        } else if b.negative {
            Order::Gt
        } else {
            Order::Lt
        }
    } else if b_zero {
        if a.negative {
            Order::Lt
        } else {
            Order::Gt
        }
    } else if a.negative != b.negative {
        if a.negative {
            Order::Lt
        } else {
            Order::Gt
        }
    } else if a.negative {
        reverse(magnitude(a, b))
    } else {
        magnitude(a, b)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cmp(a: &str, b: &str) -> Order {
        compare(&parse(a.as_bytes()).unwrap(), &parse(b.as_bytes()).unwrap())
    }

    #[test]
    fn grammar() {
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
            assert!(parse(ok.as_bytes()).is_some(), "{ok}");
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
            assert!(parse(bad.as_bytes()).is_none(), "{bad}");
        }
    }

    #[test]
    fn exact_order() {
        assert_eq!(cmp("-0", "0"), Order::Eq);
        assert_eq!(cmp("-0.0", "0"), Order::Eq);
        assert_eq!(cmp("1e3", "1000"), Order::Eq);
        assert_eq!(cmp("0.10", "0.1"), Order::Eq);
        assert_eq!(cmp("1E-2", "0.01"), Order::Eq);
        assert_eq!(cmp("0.1", "0.10000000000000000001"), Order::Lt);
        assert_eq!(cmp("9007199254740993", "9007199254740992.0"), Order::Gt);
        assert_eq!(cmp("-2.5", "-3"), Order::Gt);
        assert_eq!(cmp("-50", "-6"), Order::Lt);
        assert_eq!(cmp("1e1000", "1e999"), Order::Gt);
        assert_eq!(cmp("1e-1000", "0"), Order::Gt);
        assert_eq!(cmp("0", "-1"), Order::Gt);
        assert_eq!(cmp("-1", "0"), Order::Lt);
    }
}
