//! PEM as rcgen's `pem` crate (4.0) reads and writes it, with base64ct's
//! constant-time base64 in place of `pem`'s, which indexes a table with each
//! secret character.
//!
//! Parsing accepts exactly what `pem::parse` does: text around the block, any
//! label, RFC 1421 headers, and any line wrapping or whitespace. Finding the
//! delimiters and whitespace compares secret characters with public ones,
//! which reveals only where they sit.

use base64ct::{Base64, Encoding};
use rcgen::Error;

/// Decodes the first PEM block in `pem`, as `pem::parse` does.
pub(crate) fn decode(pem: &str) -> Result<Vec<u8>, Error> {
    let malformed = || Error::PemError("malformedframing".to_string());
    let input = pem.as_bytes();
    let (input, _) = read_until(input, b"-----BEGIN ").ok_or_else(malformed)?;
    let (input, begin) = read_until(input, b"-----").ok_or_else(malformed)?;
    let input = skip_whitespace(input);
    let (input, payload) = read_until(input, b"-----END ").ok_or_else(malformed)?;
    let (headers, data) = match read_until(payload, b"\n\n") {
        Some((data, headers)) => (headers, data),
        None => match read_until(payload, b"\r\n\r\n") {
            Some((data, headers)) => (headers, data),
            None => (&[][..], payload),
        },
    };
    let (_, end) = read_until(input, b"-----").ok_or_else(malformed)?;

    // Checked in `pem`'s order, so malformed input reports the same error.
    if begin.is_empty() {
        return Err(Error::PemError("missing BEGIN tag".to_string()));
    }
    if end.is_empty() {
        return Err(Error::PemError("missing END tag".to_string()));
    }
    // Every slice starts and ends next to an ASCII delimiter, so it is UTF-8.
    let text = |bytes: &[u8]| String::from_utf8_lossy(bytes).into_owned();
    if begin != end {
        return Err(Error::PemError(format!(
            "mismatching BEGIN (\"{}\") and END (\"{}\") tags",
            text(begin),
            text(end)
        )));
    }

    // `data` lies between ASCII delimiters, so it is a slice of `pem` at
    // character boundaries; taking it as one checks only its first byte.
    let at = data.as_ptr().addr() - pem.as_ptr().addr();
    let data = pem.get(at..at + data.len()).ok_or_else(malformed)?;
    let der = Base64::decode_vec(&strip_whitespace(data))
        .map_err(|e| Error::PemError(format!("invalid data: {e}")))?;

    for line in text(headers).lines() {
        if !line.contains(':') {
            return Err(Error::PemError(format!("invalid header: {line}")));
        }
    }
    Ok(der)
}

/// Encodes `contents` as `pem::encode_config` does, with rcgen's line endings.
pub(crate) fn encode(label: &str, contents: &[u8]) -> String {
    let line_ending = if cfg!(target_family = "windows") {
        "\r\n"
    } else {
        "\n"
    };
    let base64 = Base64::encode_string(contents);
    let mut out = format!("-----BEGIN {label}-----{line_ending}");
    for line in base64.as_bytes().chunks(64) {
        // base64ct writes only ASCII, so each chunk is whole characters.
        out.push_str(core::str::from_utf8(line).unwrap_or_default());
        out.push_str(line_ending);
    }
    out.push_str(&format!("-----END {label}-----{line_ending}"));
    out
}

/// `data` without the Unicode whitespace `pem` strips. Joining the runs
/// between whitespace, rather than filtering characters, keeps the length
/// public: a branch-free filter would count each kept character from its
/// secret value.
fn strip_whitespace(data: &str) -> String {
    let mut out = String::with_capacity(data.len());
    let mut run = 0;
    for (i, c) in data.char_indices() {
        if c.is_whitespace() {
            out.push_str(&data[run..i]);
            run = i + c.len_utf8();
        }
    }
    out.push_str(&data[run..]);
    out
}

/// `pem`'s `[ \t\n\r]*`.
fn skip_whitespace(mut input: &[u8]) -> &[u8] {
    while let [b' ' | b'\t' | b'\n' | b'\r', rest @ ..] = input {
        input = rest;
    }
    input
}

/// Splits `input` at the first `marker`, returning what follows it and what
/// precedes it. Like `pem`'s, a partial match that fails restarts after the
/// failing byte rather than at it, so `------BEGIN ` holds no `-----BEGIN `.
fn read_until<'a>(input: &'a [u8], marker: &[u8]) -> Option<(&'a [u8], &'a [u8])> {
    let mut found = 0;
    for (index, &byte) in input.iter().enumerate() {
        if byte == marker[found] {
            found += 1;
        } else {
            found = 0;
        }
        if found == marker.len() {
            return Some((&input[index + 1..], &input[..index + 1 - found]));
        }
    }
    None
}

#[cfg(test)]
mod tests {
    use crabgrind::memcheck::{self, MemState};
    use crabgrind::valgrind::{self, RunningMode};

    use super::{decode, encode};
    use crate::KeyPair;

    fn mark(value: &[u8], state: MemState) {
        if let RunningMode::Valgrind = valgrind::running_mode() {
            memcheck::mark_memory(value.as_ptr().cast(), value.len(), state).unwrap();
        }
    }

    /// `admin/ctgrind` runs this under valgrind, which flags any branch or
    /// memory index on a private key's bytes while they are PEM encoded and
    /// decoded. Whatever the codec only frames is marked public.
    #[test]
    fn constant_time() {
        let mut keys = vec![include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der").to_vec()];
        for alg in [
            &rcgen::PKCS_ECDSA_P256_SHA256,
            &rcgen::PKCS_ECDSA_P384_SHA384,
            &rcgen::PKCS_ED25519,
        ] {
            keys.push(KeyPair::generate_for(alg).unwrap().serialize_der());
        }
        for der in keys {
            mark(&der, MemState::Undefined);
            let pem = encode("PRIVATE KEY", &der);
            mark(&der, MemState::Defined);

            // Find the base64 lines while the PEM is public, then mark them.
            mark(pem.as_bytes(), MemState::Defined);
            let base64: Vec<&str> = pem
                .lines()
                .filter(|line| !line.starts_with("-----"))
                .collect();
            for line in &base64 {
                mark(line.as_bytes(), MemState::Undefined);
            }
            // base64ct sizes its output by whether the last two characters
            // are `=`, so memcheck would taint every length derived from the
            // public padding. Keep the final block public; every other block
            // goes through the same transform.
            let last = base64.last().unwrap().as_bytes();
            mark(&last[last.len() - 4..], MemState::Defined);

            let decoded = decode(&pem).unwrap();
            mark(&decoded, MemState::Defined);
            mark(pem.as_bytes(), MemState::Defined);
            assert_eq!(decoded, der);
        }
    }
}
