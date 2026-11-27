//! Just enough DER to tell the shapes of input rind refuses by design.

// Each target uses some of these.
#![allow(dead_code)]

/// The DER element starting `input`: its tag, its contents, and the bytes
/// after it.
pub fn element(input: &[u8]) -> Option<(u8, &[u8], &[u8])> {
    let (&tag, rest) = input.split_first()?;
    let (&first, rest) = rest.split_first()?;
    let (len, rest) = match first {
        0..=0x7f => (usize::from(first), rest),
        0x81..=0x84 => {
            let (len, rest) = rest.split_at_checked(usize::from(first & 0x7f))?;
            let len = len.iter().fold(0, |len, &b| len << 8 | usize::from(b));
            (len, rest)
        }
        _ => return None,
    };
    let (contents, rest) = rest.split_at_checked(len)?;
    Some((tag, contents, rest))
}

/// The tags and contents of the DER elements in `contents`, up to the first
/// that does not parse.
pub fn elements(mut contents: &[u8]) -> impl Iterator<Item = (u8, &[u8])> {
    std::iter::from_fn(move || {
        let (tag, inner, rest) = element(contents)?;
        contents = rest;
        Some((tag, inner))
    })
}

/// The contents of the sequence starting `input`.
pub fn sequence(input: &[u8]) -> Option<&[u8]> {
    element(input).and_then(|(tag, contents, _)| (tag == 0x30).then_some(contents))
}

/// Whether bytes follow the DER element starting `input`, which aws-lc-rs
/// ignores and rind refuses as malformed.
pub fn trailing(input: &[u8]) -> bool {
    element(input).is_some_and(|(_, _, rest)| !rest.is_empty())
}

/// Whether `input` is shaped like a `SubjectPublicKeyInfo`: a sequence whose
/// first element is a sequence, the algorithm identifier. aws-lc-rs takes one
/// wherever it takes a public key, and rind only an RSA key's.
pub fn spki(input: &[u8]) -> bool {
    sequence(input).is_some_and(|contents| contents.first() == Some(&0x30))
}

/// Whether `input` is a `SubjectPublicKeyInfo` whose algorithm identifier
/// holds more after its object identifier than the `NULL` parameters or
/// none. aws-lc ignores whatever follows it, and rind refuses it.
pub fn spki_parameters(input: &[u8]) -> bool {
    sequence(input)
        .and_then(sequence)
        .and_then(element)
        .is_some_and(|(_, _, parameters)| !matches!(parameters, [] | [0x05, 0x00]))
}

/// An ECDSA signature as `r || s`, each `len` bytes, from its algorithm's
/// encoding: a DER one's two integers when `der`, else a fixed-width one as
/// it is, or `None` if it is malformed. A DER signature can be `2 * len`
/// bytes too, so the length cannot tell them apart.
pub fn fixed_width(signature: &[u8], len: usize, der: bool) -> Option<Vec<u8>> {
    if !der {
        return (signature.len() == 2 * len).then(|| signature.to_vec());
    }
    let (0x30, body, []) = element(signature)? else {
        return None;
    };
    // Exactly two non-negative INTEGERs fill the body.
    let mut fixed = Vec::with_capacity(2 * len);
    let mut rest = body;
    for _ in 0..2 {
        let (0x02, int @ [first, ..], after) = element(rest)? else {
            return None;
        };
        if first & 0x80 != 0 {
            return None;
        }
        let int = &int[int.iter().take_while(|&&b| b == 0).count()..];
        if int.len() > len {
            return None;
        }
        fixed.extend(std::iter::repeat_n(0, len - int.len()));
        fixed.extend_from_slice(int);
        rest = after;
    }
    rest.is_empty().then_some(fixed)
}

/// The `subjectPublicKey` of a `SubjectPublicKeyInfo`, the BIT STRING's
/// bytes, whatever its algorithm identifier's parameters.
pub fn spki_key(input: &[u8]) -> Option<&[u8]> {
    let mut elements = elements(sequence(input)?);
    let (0x30, _) = elements.next()? else {
        return None;
    };
    let (0x03, [0, key @ ..]) = elements.next()? else {
        return None;
    };
    Some(key)
}
