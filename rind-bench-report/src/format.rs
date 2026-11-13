//! Python `str` formatting, `fnmatch.fnmatchcase`, and `re.escape` as CPython 3.12 does them.

/// CPython `json.dumps` of a finite float, which matches `repr` with a signed two-digit exponent.
pub fn py_float(n: f64) -> String {
    if n.is_nan() {
        return "NaN".to_string();
    }
    if n.is_infinite() {
        return if n.is_sign_negative() {
            "-Infinity".to_string()
        } else {
            "Infinity".to_string()
        };
    }
    let mut text = format!("{n:?}");
    if let Some(index) = text.find('e') {
        let (mantissa, exponent) = text.split_at(index);
        let exponent = &exponent[1..];
        let (sign, digits) = if let Some(rest) = exponent.strip_prefix('-') {
            ("-", rest)
        } else if let Some(rest) = exponent.strip_prefix('+') {
            ("+", rest)
        } else {
            ("+", exponent)
        };
        let digits = if digits.len() < 2 {
            format!("0{digits}")
        } else {
            digits.to_string()
        };
        text = format!("{mantissa}e{sign}{digits}");
    }
    text
}
pub fn human(ns: f64) -> String {
    if ns < 1e3 {
        format!("{ns:.0} ns")
    } else if ns < 1e6 {
        format!("{:.2} µs", ns / 1e3)
    } else {
        format!("{:.2} ms", ns / 1e6)
    }
}

/// Python `float(f"{ns:.4g}")`: four significant digits, half-even, then back to `f64`.
pub fn significant(ns: f64) -> f64 {
    if !ns.is_finite() {
        return ns;
    }
    let neg = ns.is_sign_negative();
    let abs = ns.abs();
    if abs == 0.0 {
        return if neg { -0.0 } else { 0.0 };
    }
    // 17 significant digits is enough to recover an f64; rounding that decimal
    // to 4 significant digits matches CPython's `g` format on the report's data.
    let sci = format!("{abs:.16e}");
    let text = round_sci(&sci, 4);
    let value: f64 = text.parse().unwrap_or(abs);
    if neg { -value } else { value }
}

fn round_sci(sci: &str, prec: usize) -> String {
    let (mant, exp_text) = sci.split_once('e').expect("scientific format");
    let mut exp: i32 = exp_text.parse().expect("exponent");
    let digits: String = mant.chars().filter(|c| *c != '.').collect();
    let mut ds: Vec<u8> = digits.into_bytes();
    if ds.len() > prec {
        let round_up = match ds[prec] {
            b'0'..=b'4' => false,
            b'5' => {
                let rest = ds[prec + 1..].iter().any(|d| *d != b'0');
                rest || !(ds[prec - 1] - b'0').is_multiple_of(2)
            }
            _ => true,
        };
        ds.truncate(prec);
        if round_up {
            let mut i = prec as isize - 1;
            loop {
                if i < 0 {
                    ds.insert(0, b'1');
                    break;
                }
                if ds[i as usize] < b'9' {
                    ds[i as usize] += 1;
                    break;
                }
                ds[i as usize] = b'0';
                i -= 1;
            }
        }
    }
    if ds.len() > prec {
        exp += 1;
        ds.truncate(prec);
    }
    let mut out = String::new();
    out.push(ds[0] as char);
    if ds.len() > 1 {
        out.push('.');
        for byte in &ds[1..] {
            out.push(*byte as char);
        }
    }
    if exp != 0 {
        out.push('e');
        out.push_str(&exp.to_string());
    }
    out
}

/// Characters CPython 3.7+ `re.escape` escapes (ASCII).
fn re_escape_char(c: char) -> bool {
    matches!(
        c,
        '\t' | '\n'
            | '\u{0b}'
            | '\u{0c}'
            | '\r'
            | ' '
            | '#'
            | '$'
            | '&'
            | '('
            | ')'
            | '*'
            | '+'
            | '-'
            | '.'
            | '?'
            | '['
            | '\\'
            | ']'
            | '^'
            | '{'
            | '|'
            | '}'
            | '~'
    )
}

pub fn re_escape(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    for c in text.chars() {
        if re_escape_char(c) {
            out.push('\\');
        }
        out.push(c);
    }
    out
}

/// Shell pattern match using Linux CPython's case-sensitive rules.
///
/// `*` matches any string, `?` one byte, `[seq]` a class, and `[!seq]` its
/// complement. The comparison does not casefold: `SHA256` does not match
/// `sha256`.
///
/// `admin/bench-report` uses `fnmatch.fnmatchcase` for gap and proof rows, and
/// `fnmatch.filter` when a verified pattern must name an operation. On Linux
/// `fnmatch.fnmatch` (what `filter` calls) is case-sensitive, the same as
/// `fnmatchcase`. On macOS `fnmatch.fnmatch` casefolds both sides first, so a
/// pattern that differs only by case would match. This crate always uses the
/// Linux / `fnmatchcase` rule. That is what `just ci` checks, and the report's
/// operation names are lowercase.
pub fn fnmatchcase(name: &str, pat: &str) -> bool {
    fnmatch_bytes(name.as_bytes(), pat.as_bytes())
}

fn fnmatch_bytes(name: &[u8], pat: &[u8]) -> bool {
    let mut ni = 0;
    let mut pi = 0;
    let mut star_p: Option<usize> = None;
    let mut star_n = 0;
    while ni < name.len() {
        if pi < pat.len() {
            let matched = match pat[pi] {
                b'?' => {
                    ni += 1;
                    pi += 1;
                    true
                }
                b'*' => {
                    star_p = Some(pi);
                    star_n = ni;
                    pi += 1;
                    true
                }
                b'[' => match char_class(pat, pi, name[ni]) {
                    Some((end, true)) => {
                        ni += 1;
                        pi = end;
                        true
                    }
                    Some((_, false)) => false,
                    None => {
                        if name[ni] == b'[' {
                            ni += 1;
                            pi += 1;
                            true
                        } else {
                            false
                        }
                    }
                },
                c => {
                    if name[ni] == c {
                        ni += 1;
                        pi += 1;
                        true
                    } else {
                        false
                    }
                }
            };
            if matched {
                continue;
            }
        }
        if let Some(sp) = star_p {
            star_n += 1;
            if star_n > name.len() {
                return false;
            }
            pi = sp + 1;
            ni = star_n;
            continue;
        }
        return false;
    }
    while pi < pat.len() && pat[pi] == b'*' {
        pi += 1;
    }
    pi == pat.len()
}

/// Returns `(index after ']' , whether `ch` is in the class)`, or `None` when `[` is literal.
fn char_class(pat: &[u8], start: usize, ch: u8) -> Option<(usize, bool)> {
    let mut j = start + 1;
    if j >= pat.len() {
        return None;
    }
    let neg = pat[j] == b'!';
    if neg {
        j += 1;
    }
    if j < pat.len() && pat[j] == b']' {
        j += 1;
    }
    let class_start = j;
    while j < pat.len() && pat[j] != b']' {
        j += 1;
    }
    if j >= pat.len() {
        return None;
    }
    let class = &pat[class_start..j];
    let mut matched = false;
    let mut i = 0;
    while i < class.len() {
        if i + 2 < class.len() && class[i + 1] == b'-' && class[i] != b'\\' {
            if ch >= class[i] && ch <= class[i + 2] {
                matched = true;
                break;
            }
            i += 3;
        } else {
            if class[i] == ch {
                matched = true;
                break;
            }
            i += 1;
        }
    }
    Some((j + 1, if neg { !matched } else { matched }))
}

pub fn sorted_comma(mut items: Vec<String>) -> String {
    items.sort();
    items.join(", ")
}
