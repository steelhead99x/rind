#![no_main]

//! HKDF against aws-lc-rs for any salt, secret, info, and output length, up
//! to twice the most HKDF-Expand allows.

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
    /// The buffer's length, if it differs from the length asked for.
    out_len: Option<u16>,
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
    let limit = 2 * 255 * hash_len;
    let len = usize::from(input.len) % limit;
    let out_len = input.out_len.map_or(len, |n| usize::from(n) % limit);
    let info: Vec<&[u8]> = input.info.iter().map(Vec::as_slice).collect();

    let mut ours_out = vec![0; out_len];
    let ours_result = ours::Salt::new(ours_algorithm, &input.salt)
        .extract(&input.secret)
        .unwrap()
        .expand(&info, len)
        .and_then(|okm| okm.fill(&mut ours_out));
    let mut theirs_out = vec![0; out_len];
    let theirs_result = theirs::Salt::new(theirs_algorithm, &input.salt)
        .extract(&input.secret)
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
