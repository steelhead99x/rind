//! The harness the Marvin toolkit times: it decrypts each ciphertext of a
//! file in turn, in the random order the toolkit wrote them, and records each
//! call's counter ticks. See <https://github.com/tomato42/marvin-toolkit>.

use std::fs::File;
use std::hint::black_box;
use std::io::{BufReader, BufWriter, Read, Write};

use rind::rsa;

use crate::clock::{ticks, ticks_per_second};

/// Decrypts every ciphertext in `ciphertexts` with the PKCS#8 key in `key`,
/// writing each call's ticks to `out` as a little-endian u64, and prints the
/// counter's rate in MHz, for `extract.py --clock-frequency`.
pub fn run(key: &str, ciphertexts: &str, out: &str) -> Result<(), String> {
    let der = std::fs::read(key).map_err(|e| format!("{key}: {e}"))?;
    let key = rsa::DecryptingKey::from_pkcs8(&rsa::OAEP_SHA256, &der)
        .map_err(|e| format!("{key}: {e:?}"))?;
    // A ciphertext is as long as the modulus.
    let len = key
        .public_key()
        .encrypt(b"", b"")
        .map_err(|e| format!("encrypt: {e:?}"))?
        .as_ref()
        .len();

    let file = File::open(ciphertexts).map_err(|e| format!("{ciphertexts}: {e}"))?;
    let size = file
        .metadata()
        .map_err(|e| format!("{ciphertexts}: {e}"))?
        .len();
    if size % len as u64 != 0 {
        return Err(format!(
            "{ciphertexts}: not a whole number of {len}-byte ciphertexts"
        ));
    }
    let mut input = BufReader::new(file);
    let mut output = BufWriter::new(File::create(out).map_err(|e| format!("{out}: {e}"))?);
    let mut c = vec![0; len];
    for _ in 0..size / len as u64 {
        input
            .read_exact(&mut c)
            .map_err(|e| format!("{ciphertexts}: {e}"))?;
        let start = ticks();
        // Every probe the toolkit writes for OAEP is refused; only the time
        // matters.
        let _ = black_box(key.decrypt(black_box(&c), b""));
        let time = ticks().wrapping_sub(start);
        output
            .write_all(&time.to_le_bytes())
            .map_err(|e| format!("{out}: {e}"))?;
    }
    output.flush().map_err(|e| format!("{out}: {e}"))?;
    println!("{:.3}", ticks_per_second() as f64 / 1e6);
    Ok(())
}
