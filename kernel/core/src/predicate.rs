//! Predicate decisions over resolved operands; refines `TclMesh.Predicate`.
//!
//! The kernel resolves a predicate's operands against the state and request
//! and lowers it to a `Pred`; `eval` decides it. Faults that resolution or
//! lowering raised are carried as indices into the caller's fault table.

use crate::decimal;
use crate::Order;

/// A resolved operand.
#[cfg_attr(test, derive(Debug))]
pub enum Res {
    /// Resolution raised the fault with this index.
    Fault(usize),
    Str(Vec<u8>),
    /// A list value; `None` marks an element that is not a scalar.
    Arr(Vec<Option<Vec<u8>>>),
    Other,
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum CmpOp {
    Lt,
    Lte,
    Gt,
    Gte,
}

/// A predicate whose operands are resolved; `And` and `Or` are binary.
#[cfg_attr(test, derive(Debug))]
pub enum Pred {
    /// A structural fault met while lowering, by index.
    Fail(usize),
    True,
    False,
    Eq(Res, Res),
    Neq(Res, Res),
    Cmp(CmpOp, Res, Res),
    Mem(Res, Res),
    Contains(Res, Res),
    Not(Box<Pred>),
    And(Box<Pred>, Box<Pred>),
    Or(Box<Pred>, Box<Pred>),
}

#[cfg_attr(test, derive(Debug))]
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// The caller's fault with this index.
    Given(usize),
    /// An operand that must be a scalar is not.
    NotScalar,
    /// A membership haystack that is neither a scalar nor a list.
    NotList,
    NonNumeric(CmpOp),
    NonCanonicalList,
}

fn scalar(r: &Res) -> Result<&[u8], Error> {
    match r {
        Res::Fault(i) => Err(Error::Given(*i)),
        Res::Str(b) => Ok(b),
        Res::Arr(_) => Err(Error::NotScalar),
        Res::Other => Err(Error::NotScalar),
    }
}

/// Byte-wise equality of `a[from..to]` and `b`.
fn range_eq(a: &[u8], from: usize, to: usize, b: &[u8]) -> bool {
    if to - from != b.len() {
        false
    } else {
        let mut same = true;
        let mut i = 0;
        while i < b.len() {
            same &= a[from + i] == b[i];
            i += 1;
        }
        same
    }
}

fn bytes_eq(a: &[u8], b: &[u8]) -> bool {
    range_eq(a, 0, a.len(), b)
}

/// Whether `needle` occurs in `hay`.
fn is_infix(needle: &[u8], hay: &[u8]) -> bool {
    if needle.len() == 0 {
        true
    } else {
        let mut found = false;
        let mut i = 0;
        while i < hay.len() && needle.len() <= hay.len() - i {
            found |= range_eq(hay, i, i + needle.len(), needle);
            i += 1;
        }
        found
    }
}

fn is_space(b: u8) -> bool {
    b == b' ' || b == b'\t' || b == b'\n' || b == 0x0b || b == 0x0c || b == b'\r'
}

fn is_quote(b: u8) -> bool {
    b == b'\\' || b == b'"'
}

/// One byte of `plain_element`: whether the element is still plain, and its
/// brace depth (which never reaches `cap`, the element's length).
fn plain_step(ok: bool, depth: usize, b: u8, cap: usize) -> (bool, usize) {
    if is_quote(b) {
        (false, depth)
    } else if b == b'{' {
        if depth < cap {
            (ok, depth + 1)
        } else {
            (ok, depth)
        }
    } else if b == b'}' {
        if depth == 0 {
            (false, depth)
        } else {
            (ok, depth - 1)
        }
    } else {
        (ok, depth)
    }
}

/// An element Tcl renders without backslashes or quotes: none of either,
/// braces balanced.
fn plain_element(b: &[u8]) -> bool {
    let mut ok = true;
    let mut depth: usize = 0;
    let mut i = 0;
    while i < b.len() {
        let (o, d) = plain_step(ok, depth, b[i], b.len());
        ok = o;
        depth = d;
        i += 1;
    }
    ok && depth == 0
}

fn has_quote(b: &[u8]) -> bool {
    let mut found = false;
    let mut i = 0;
    while i < b.len() {
        found |= is_quote(b[i]);
        i += 1;
    }
    found
}

/// First non-space at or after `i`.
fn skip_space(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && is_space(b[i]) {
        i += 1;
    }
    i
}

/// End of the bare word starting at `i`.
fn word_end(b: &[u8], mut i: usize) -> usize {
    while i < b.len() && !is_space(b[i]) {
        i += 1;
    }
    i
}

/// One byte of a brace group at positive `depth` (which never reaches `cap`).
fn group_step(depth: usize, b: u8, cap: usize) -> usize {
    if b == b'{' {
        if depth < cap {
            depth + 1
        } else {
            depth
        }
    } else if b == b'}' {
        depth - 1
    } else {
        depth
    }
}

/// Scans a brace group whose body starts at `i`: the index just past its
/// matching close, or `b.len()` with depth left over if it never closes.
fn group_end(b: &[u8], mut i: usize) -> (usize, usize) {
    let mut depth: usize = 1;
    while depth > 0 && i < b.len() {
        depth = group_step(depth, b[i], b.len());
        i += 1;
    }
    (depth, i)
}

/// The list element starting at the non-space `text[i]`: whether it is
/// well formed, whether it equals `needle`, and where it ends.
fn list_item(text: &[u8], needle: &[u8], i: usize) -> (bool, bool, usize) {
    if text[i] == b'{' {
        let (depth, end) = group_end(text, i + 1);
        if depth != 0 {
            (false, false, end)
        } else {
            let hit = range_eq(text, i + 1, end - 1, needle);
            (end == text.len() || is_space(text[end]), hit, end)
        }
    } else {
        let end = word_end(text, i);
        (true, range_eq(text, i, end, needle), end)
    }
}

/// Membership of `needle` in the canonical list `text`; `None` if `text` is
/// not a canonical list.
fn list_member(text: &[u8], needle: &[u8]) -> Option<bool> {
    if has_quote(text) {
        None
    } else {
        let mut ok = true;
        let mut found = false;
        let mut i = skip_space(text, 0);
        while ok && i < text.len() {
            let (o, hit, end) = list_item(text, needle, i);
            ok = o;
            found |= hit;
            i = skip_space(text, end);
        }
        if ok {
            Some(found)
        } else {
            None
        }
    }
}

/// One element of a list value, given whether the needle was found so far.
fn item_member(item: &Option<Vec<u8>>, needle: &[u8], found: bool) -> Result<bool, Error> {
    match item {
        None => Err(Error::NotScalar),
        Some(b) => {
            if !plain_element(b) {
                Err(Error::NonCanonicalList)
            } else {
                Ok(found || bytes_eq(b, needle))
            }
        }
    }
}

fn item_step(
    status: Result<bool, Error>,
    item: &Option<Vec<u8>>,
    needle: &[u8],
) -> Result<bool, Error> {
    match status {
        Ok(found) => item_member(item, needle, found),
        Err(e) => Err(e),
    }
}

/// Membership in a list value: every element must be a plain scalar.
fn items_member(items: &[Option<Vec<u8>>], needle: &[u8]) -> Result<bool, Error> {
    let mut status: Result<bool, Error> = Ok(false);
    let mut i = 0;
    while i < items.len() {
        status = item_step(status, &items[i], needle);
        i += 1;
    }
    status
}

fn member(needle: &[u8], haystack: &Res) -> Result<bool, Error> {
    match haystack {
        Res::Fault(i) => Err(Error::Given(*i)),
        Res::Str(text) => match list_member(text, needle) {
            Some(found) => Ok(found),
            None => Err(Error::NonCanonicalList),
        },
        Res::Arr(items) => items_member(items, needle),
        Res::Other => Err(Error::NotList),
    }
}

fn holds(op: CmpOp, o: Order) -> bool {
    match op {
        CmpOp::Lt => o == Order::Lt,
        CmpOp::Lte => o != Order::Gt,
        CmpOp::Gt => o == Order::Gt,
        CmpOp::Gte => o != Order::Lt,
    }
}

fn compare(op: CmpOp, l: &[u8], r: &[u8]) -> Result<bool, Error> {
    match decimal::parse(l) {
        None => Err(Error::NonNumeric(op)),
        Some(x) => match decimal::parse(r) {
            None => Err(Error::NonNumeric(op)),
            Some(y) => Ok(holds(op, decimal::compare(&x, &y))),
        },
    }
}

fn leaf(p: &Pred) -> Result<bool, Error> {
    match p {
        Pred::Eq(a, b) => match scalar(a) {
            Err(e) => Err(e),
            Ok(x) => match scalar(b) {
                Err(e) => Err(e),
                Ok(y) => Ok(bytes_eq(x, y)),
            },
        },
        Pred::Neq(a, b) => match scalar(a) {
            Err(e) => Err(e),
            Ok(x) => match scalar(b) {
                Err(e) => Err(e),
                Ok(y) => Ok(!bytes_eq(x, y)),
            },
        },
        Pred::Cmp(op, a, b) => match scalar(a) {
            Err(e) => Err(e),
            Ok(l) => match scalar(b) {
                Err(e) => Err(e),
                Ok(r) => compare(*op, l, r),
            },
        },
        Pred::Mem(n, h) => match scalar(n) {
            Err(e) => Err(e),
            Ok(needle) => member(needle, h),
        },
        Pred::Contains(h, n) => match scalar(h) {
            Err(e) => Err(e),
            Ok(hay) => match scalar(n) {
                Err(e) => Err(e),
                Ok(needle) => Ok(needle.len() != 0 && is_infix(needle, hay)),
            },
        },
        Pred::Fail(i) => Err(Error::Given(*i)),
        Pred::True => Ok(true),
        _ => Ok(false),
    }
}

pub fn eval(p: &Pred) -> Result<bool, Error> {
    match p {
        Pred::Not(q) => match eval(q) {
            Err(e) => Err(e),
            Ok(b) => Ok(!b),
        },
        Pred::And(q, r) => match eval(q) {
            Err(e) => Err(e),
            Ok(true) => eval(r),
            Ok(false) => Ok(false),
        },
        Pred::Or(q, r) => match eval(q) {
            Err(e) => Err(e),
            Ok(true) => Ok(true),
            Ok(false) => eval(r),
        },
        _ => leaf(p),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn s(x: &str) -> Res {
        Res::Str(x.as_bytes().to_vec())
    }

    #[test]
    fn lists() {
        let m = |t: &str, n: &str| list_member(t.as_bytes(), n.as_bytes());
        assert_eq!(m("", "a"), Some(false));
        assert_eq!(m(" north\teast ", "east"), Some(true));
        assert_eq!(m("{a b} c {}", "a b"), Some(true));
        assert_eq!(m("{a b} c {}", ""), Some(true));
        assert_eq!(m("{a {b c}}", "a {b c}"), Some(true));
        assert_eq!(m("a{b c}", "c}"), Some(true));
        for bad in ["{a", "{a}b", "{a {b}", "\"a b\"", "a\\ b"] {
            assert_eq!(m(bad, "a"), None, "{bad}");
        }
    }

    #[test]
    fn decisions() {
        let cmp = Pred::Cmp(CmpOp::Lt, s("0.1"), s("1e-0"));
        assert_eq!(eval(&cmp), Ok(true));
        let bad = Pred::Cmp(CmpOp::Gte, s("1"), s("0x10"));
        assert_eq!(
            eval(&Pred::Not(Box::new(bad))),
            Err(Error::NonNumeric(CmpOp::Gte))
        );
        let skip = Pred::And(Box::new(Pred::False), Box::new(Pred::Fail(3)));
        assert_eq!(eval(&skip), Ok(false));
        let arr = Res::Arr(vec![Some(b"a".to_vec()), Some(b"x\\y".to_vec())]);
        assert_eq!(eval(&Pred::Mem(s("a"), arr)), Err(Error::NonCanonicalList));
        assert_eq!(eval(&Pred::Contains(s("héllo"), s("é"))), Ok(true));
        assert_eq!(eval(&Pred::Contains(s("abc"), s(""))), Ok(false));
    }
}
