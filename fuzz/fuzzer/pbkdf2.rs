#![no_main]

//! PBKDF2 against aws-lc-rs and RustCrypto for any secret, salt, and output
//! length, and checking that output tampered with.

use std::num::NonZeroU32;

use aws_lc_rs::pbkdf2 as theirs;
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::pbkdf2 as ours;

mod edit;

/// RustCrypto's PBKDF2: password, salt, iterations, and output.
type Independent = fn(&[u8], &[u8], u32, &mut [u8]);

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    /// One less than the iteration count, which stays small so each input
    /// runs quickly.
    iterations: u8,
    secret: Vec<u8>,
    salt: Vec<u8>,
    /// The output length, up to a few blocks of the longest hash.
    len: u16,
    edit: edit::Edit,
}

fuzz_target!(|input: Input| {
    use ::pbkdf2::pbkdf2_hmac;
    let (ours_algorithm, theirs_algorithm, independent, hash_len): (_, _, Independent, _) =
        match input.algorithm % 4 {
            0 => (
                &ours::legacy::PBKDF2_HMAC_SHA1,
                theirs::PBKDF2_HMAC_SHA1,
                pbkdf2_hmac::<sha1::Sha1>,
                20,
            ),
            1 => (
                &ours::PBKDF2_HMAC_SHA256,
                theirs::PBKDF2_HMAC_SHA256,
                pbkdf2_hmac::<sha2::Sha256>,
                32,
            ),
            2 => (
                &ours::PBKDF2_HMAC_SHA384,
                theirs::PBKDF2_HMAC_SHA384,
                pbkdf2_hmac::<sha2::Sha384>,
                48,
            ),
            _ => (
                &ours::PBKDF2_HMAC_SHA512,
                theirs::PBKDF2_HMAC_SHA512,
                pbkdf2_hmac::<sha2::Sha512>,
                64,
            ),
        };
    let iterations = NonZeroU32::new(u32::from(input.iterations) + 1).unwrap();
    let (secret, salt) = (&input.secret, &input.salt);
    let len = usize::from(input.len) % 512;

    let ours_secret = ours::Secret::new(ours_algorithm, secret);
    let mut ours_out = vec![0; len];
    let ours_result = ours_secret.derive(iterations, salt, &mut ours_out);
    // rind refuses an empty output, which aws-lc-rs fills.
    if len == 0 {
        assert_eq!(ours_result, Err(rind::Error::WrongLength));
        return;
    }
    ours_result.unwrap();
    let mut theirs_out = vec![0; len];
    theirs::derive(theirs_algorithm, iterations, salt, secret, &mut theirs_out);
    assert_eq!(ours_out, theirs_out);
    let mut independent_out = vec![0; len];
    independent(secret, salt, iterations.get(), &mut independent_out);
    assert_eq!(ours_out, independent_out);

    // A shorter key is a prefix of a longer one, so cutting the end off
    // leaves a valid key.
    let mut stored = ours_out.clone();
    input.edit.apply(&mut stored);
    let valid = stored == ours_out[..stored.len()];
    let ours_result = ours_secret.verify(iterations, salt, &stored);
    let theirs_result = theirs::verify(theirs_algorithm, iterations, salt, secret, &stored);
    // rind refuses a stored key shorter than the hash, which is easier to
    // match by chance, and aws-lc-rs checks it.
    if stored.len() < hash_len {
        assert_eq!(ours_result, Err(rind::Error::WrongLength));
        return;
    }
    assert_eq!(
        ours_result.is_ok(),
        theirs_result.is_ok(),
        "{ours_result:?}"
    );
    assert_eq!(ours_result.is_ok(), valid);
});
