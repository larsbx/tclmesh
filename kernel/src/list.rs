//! Canonical subset of Tcl list syntax.
//!
//! Accepted: whitespace-separated bare words and brace-quoted words with
//! balanced nesting. Rejected: backslashes, double quotes, unbalanced braces,
//! and anything that follows a closing brace without whitespace. The Tcl
//! reference (`_canonical_list`) applies the same rule.

const SPACE: &[u8] = b" \t\n\x0b\x0c\r";

pub fn parse(text: &str) -> Option<Vec<&str>> {
    if text.bytes().any(|b| b == b'\\' || b == b'"') {
        return None;
    }
    let b = text.as_bytes();
    let mut out = Vec::new();
    let mut i = 0;
    loop {
        while i < b.len() && SPACE.contains(&b[i]) {
            i += 1;
        }
        if i == b.len() {
            return Some(out);
        }
        if b[i] == b'{' {
            let start = i + 1;
            let mut depth = 1;
            i += 1;
            while depth > 0 {
                match b.get(i)? {
                    b'{' => depth += 1,
                    b'}' => depth -= 1,
                    _ => {}
                }
                i += 1;
            }
            out.push(&text[start..i - 1]);
            if i < b.len() && !SPACE.contains(&b[i]) {
                return None;
            }
        } else {
            let start = i;
            while i < b.len() && !SPACE.contains(&b[i]) {
                i += 1;
            }
            out.push(&text[start..i]);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::parse;

    #[test]
    fn canonical_lists() {
        assert_eq!(parse(""), Some(vec![]));
        assert_eq!(parse(" north\teast "), Some(vec!["north", "east"]));
        assert_eq!(parse("{a b} c {}"), Some(vec!["a b", "c", ""]));
        assert_eq!(parse("{a {b c}}"), Some(vec!["a {b c}"]));
        assert_eq!(parse("a{b c}"), Some(vec!["a{b", "c}"]));
    }

    #[test]
    fn declines_everything_else() {
        for bad in ["{a", "{a}b", "{a {b}", "\"a b\"", "a\\ b"] {
            assert_eq!(parse(bad), None, "{bad}");
        }
    }
}
