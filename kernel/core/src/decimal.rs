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

pub fn parse(s: &[u8]) -> Option<Dec> {
    if s.len() > u32::MAX as usize {
        return None;
    }
    let mut i = 0;
    let negative = i < s.len() && s[i] == b'-';
    if negative {
        i += 1;
    }
    let int_start = i;
    let int_end = digits_end(s, i);
    if int_end == int_start || (int_end - int_start > 1 && s[int_start] == b'0') {
        return None;
    }
    let mut digits = Vec::new();
    push_digits(&mut digits, s, int_start, int_end);
    i = int_end;
    let mut frac_len: u32 = 0;
    if i < s.len() && s[i] == b'.' {
        let frac_end = digits_end(s, i + 1);
        if frac_end == i + 1 {
            return None;
        }
        push_digits(&mut digits, s, i + 1, frac_end);
        frac_len = (frac_end - (i + 1)) as u32;
        i = frac_end;
    }
    let mut exp: i32 = 0;
    if i < s.len() && (s[i] == b'e' || s[i] == b'E') {
        i += 1;
        let mut minus = false;
        if i < s.len() && (s[i] == b'-' || s[i] == b'+') {
            minus = s[i] == b'-';
            i += 1;
        }
        let exp_end = digits_end(s, i);
        if exp_end == i {
            return None;
        }
        let magnitude = match bounded_exp(s, i, exp_end) {
            Some(m) => m as i32,
            None => return None,
        };
        exp = if minus { -magnitude } else { magnitude };
        i = exp_end;
    }
    if i != s.len() {
        return None;
    }
    Some(Dec {
        negative,
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
