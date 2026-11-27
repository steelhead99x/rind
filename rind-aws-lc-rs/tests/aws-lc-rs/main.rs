//! aws-lc-rs 1.19.0's own tests, run against rind-aws-lc-rs renamed to
//! `aws_lc_rs`; see `README.md` for what changed.

// A lint on aws-lc-rs's code that clippy cannot fix, kept as aws-lc-rs wrote it.
#![allow(clippy::chunks_exact_to_as_chunks)]

// Shadows the `aws-lc-rs` dev-dependency, so these tests reach the adapter.
extern crate rind_aws_lc_rs as aws_lc_rs;

// Helpers that only aws-lc-rs's tests of what rind does not offer use.
#[allow(dead_code)]
mod test;

mod aead_out_of_place;
mod aead_out_of_place_tls;
mod aead_test;
mod basic_aead_test;
mod basic_quic_test;
mod basic_rsa_test;
mod cipher_test;
mod digest_test;
mod ecdsa_tests;
mod ed25519_tests;
mod hkdf_test;
mod hmac_test;
mod pbkdf2_test;
mod pqdsa_test;
mod quic_test;
mod rand_test;
mod rsa_test;

// aws-lc-rs's tests kept beside its code in `src/`, each at its path there.
mod unit {
    mod aead;
    mod agreement;
    mod cipher;
    mod digest;
    mod ec;
    mod ed25519;
    mod error;
    mod hkdf;
    mod hmac;
    #[cfg(feature = "ring-io")]
    mod io;
    mod iv;
    mod kem;
    mod key_wrap;
    mod lib;
    mod pbkdf2;
    mod pqdsa;
    mod rand;
    mod rsa;
    mod signature;

    // Stands in for the `regex` crate in the `Debug` checks that used it.
    fn is_lower_hex(s: &str) -> bool {
        !s.is_empty() && s.bytes().all(|b| matches!(b, b'0'..=b'9' | b'a'..=b'f'))
    }
}
