#![no_main]

//! HKDF against aws-lc-rs for any salt, secret, info, and output length, up
//! to twice the most HKDF-Expand allows, from an extracted pseudorandom key
//! or one loaded from up to 64 bytes.

use aws_lc_rs::hkdf as theirs;
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::hkdf as ours;

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    salt: Vec<u8>,
    secret: Vec<u8>,
    info: Vec<Vec<u8>>,
    len: u16,
    /// Takes `secret` as the pseudorandom key, skipping HKDF-Extract.
    loaded: bool,
}

/// An output length for aws-lc-rs.
struct Len(usize);

impl theirs::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

fuzz_target!(|input: Input| {
    let (ours_algorithm, theirs_algorithm, hash_len) = match input.algorithm % 4 {
        0 => (
            &ours::legacy::HKDF_SHA1,
            theirs::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
            20,
        ),
        1 => (&ours::HKDF_SHA256, theirs::HKDF_SHA256, 32),
        2 => (&ours::HKDF_SHA384, theirs::HKDF_SHA384, 48),
        _ => (&ours::HKDF_SHA512, theirs::HKDF_SHA512, 64),
    };
    let len = usize::from(input.len) % (2 * 255 * hash_len);
    let info: Vec<&[u8]> = input.info.iter().map(Vec::as_slice).collect();

    let (ours_prk, theirs_prk) = match input.loaded {
        // Up to the 64 bytes aws-lc-rs's `new_less_safe` holds before it panics.
        true => {
            let prk = &input.secret[..input.secret.len().min(64)];
            (
                ours::Prk::new(ours_algorithm, prk),
                theirs::Prk::new_less_safe(theirs_algorithm, prk),
            )
        }
        false => (
            ours::Salt::new(ours_algorithm, &input.salt)
                .extract(&input.secret)
                .unwrap(),
            theirs::Salt::new(theirs_algorithm, &input.salt).extract(&input.secret),
        ),
    };
    let mut ours_out = vec![0; len];
    let ours_result = ours_prk.fill(&info, &mut ours_out);
    let mut theirs_out = vec![0; len];
    let theirs_result = theirs_prk
        .expand(&info, Len(len))
        .and_then(|okm| okm.fill(&mut theirs_out));

    assert_eq!(
        ours_result.is_ok(),
        theirs_result.is_ok(),
        "{ours_result:?}"
    );
    match ours_result {
        Ok(()) => assert_eq!(ours_out, theirs_out),
        // A refused fill leaves the buffer as it was.
        Err(_) => assert!(ours_out.iter().all(|&b| b == 0)),
    }
});
