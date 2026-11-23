#![no_main]

//! HKDF against aws-lc-rs and RustCrypto for any salt, secret, info, and
//! output length, up to twice the most HKDF-Expand allows, from an extracted
//! pseudorandom key or one loaded from up to 64 bytes. RustCrypto refuses to
//! load one shorter than the hash, so aws-lc-rs alone checks those.

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

/// RustCrypto's HKDF: `len` bytes expanded from the PRK extracted from
/// `secret` under `salt`, or from `secret` taken as the PRK, which it
/// refuses, as `None`, when shorter than the hash.
type Independent = fn(&[u8], &[u8], bool, &[&[u8]], usize) -> Option<Option<Vec<u8>>>;

fn rustcrypto<D: ::hmac::EagerHash>(
    salt: &[u8],
    secret: &[u8],
    loaded: bool,
    info: &[&[u8]],
    len: usize,
) -> Option<Option<Vec<u8>>>
where
    ::hmac::Hmac<D>: ::hkdf::HmacImpl,
{
    let hkdf = match loaded {
        true => ::hkdf::Hkdf::<D>::from_prk(secret).ok()?,
        false => ::hkdf::Hkdf::<D>::new(Some(salt), secret),
    };
    let mut okm = vec![0u8; len];
    Some(hkdf.expand_multi_info(info, &mut okm).ok().map(|()| okm))
}

fuzz_target!(|input: Input| {
    let (ours_algorithm, theirs_algorithm, independent, hash_len): (_, _, Independent, _) =
        match input.algorithm % 4 {
            0 => (
                &ours::legacy::HKDF_SHA1,
                theirs::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
                rustcrypto::<sha1::Sha1>,
                20,
            ),
            1 => (
                &ours::HKDF_SHA256,
                theirs::HKDF_SHA256,
                rustcrypto::<sha2::Sha256>,
                32,
            ),
            2 => (
                &ours::HKDF_SHA384,
                theirs::HKDF_SHA384,
                rustcrypto::<sha2::Sha384>,
                48,
            ),
            _ => (
                &ours::HKDF_SHA512,
                theirs::HKDF_SHA512,
                rustcrypto::<sha2::Sha512>,
                64,
            ),
        };
    let len = usize::from(input.len) % (2 * 255 * hash_len);
    let info: Vec<&[u8]> = input.info.iter().map(Vec::as_slice).collect();

    // Up to the 64 bytes aws-lc-rs's `new_less_safe` holds before it panics.
    let secret = match input.loaded {
        true => &input.secret[..input.secret.len().min(64)],
        false => &input.secret[..],
    };
    let independent = independent(&input.salt, secret, input.loaded, &info, len);
    let (ours_prk, theirs_prk) = match input.loaded {
        true => (
            ours::Prk::new(ours_algorithm, secret),
            theirs::Prk::new_less_safe(theirs_algorithm, secret),
        ),
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
    if let Some(independent) = independent {
        assert_eq!(
            ours_result.as_ref().ok().map(|_| &ours_out),
            independent.as_ref()
        );
    }
    match ours_result {
        Ok(()) => assert_eq!(ours_out, theirs_out),
        // A refused fill leaves the buffer as it was.
        Err(_) => assert!(ours_out.iter().all(|&b| b == 0)),
    }
});
