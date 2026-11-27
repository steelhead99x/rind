#![no_main]

//! SHA-2 and HMAC over it against aws-lc-rs's and RustCrypto's, in updates
//! of any length with clones between.

use ::hmac::{KeyInit, Mac};
use aws_lc_rs::{digest, hmac};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use sha2::Digest;

fuzz_target!(|op: Operation| {
    use rind::digest as ours;
    use rind::hmac as ours_hmac;
    match op {
        Operation::Sha256(steps) => {
            hash::<sha2::Sha256>(&digest::SHA256, &ours::SHA256, steps);
        }
        Operation::Sha384(steps) => {
            hash::<sha2::Sha384>(&digest::SHA384, &ours::SHA384, steps);
        }
        Operation::Sha512(steps) => {
            hash::<sha2::Sha512>(&digest::SHA512, &ours::SHA512, steps);
        }
        Operation::Sha512_256(steps) => {
            hash::<sha2::Sha512_256>(&digest::SHA512_256, &ours::SHA512_256, steps);
        }
        Operation::HmacSha256 { key, steps } => {
            mac::<sha2::Sha256>(hmac::HMAC_SHA256, &ours_hmac::HMAC_SHA256, &key, steps);
        }
        Operation::HmacSha384 { key, steps } => {
            mac::<sha2::Sha384>(hmac::HMAC_SHA384, &ours_hmac::HMAC_SHA384, &key, steps);
        }
        Operation::HmacSha512 { key, steps } => {
            mac::<sha2::Sha512>(hmac::HMAC_SHA512, &ours_hmac::HMAC_SHA512, &key, steps);
        }
    }
});

fn hash<D: Digest>(
    theirs: &'static digest::Algorithm,
    ours: &'static rind::digest::Algorithm,
    steps: Vec<Step>,
) {
    let mut left = digest::Context::new(theirs);
    let mut right = rind::digest::Context::new(ours);
    let mut independent = D::new();
    for s in steps {
        match s {
            Step::Clone => {
                left = left.clone();
                right = right.clone();
            }
            Step::Input(d) => {
                left.update(&d);
                right.update(&d);
                independent.update(&d);
            }
        }
    }

    let left = left.finish();
    let right = right.finish();
    assert_eq!(left.as_ref(), right.as_ref());
    assert_eq!(left.as_ref(), &independent.finalize()[..]);
}

fn mac<D: ::hmac::EagerHash>(
    theirs: hmac::Algorithm,
    ours: &'static rind::hmac::Algorithm,
    key: &[u8],
    steps: Vec<Step>,
) {
    let mut left = hmac::Context::with_key(&hmac::Key::new(theirs, key));
    let mut right = rind::hmac::Context::with_key(&rind::hmac::Key::new(ours, key));
    let mut independent = ::hmac::Hmac::<D>::new_from_slice(key).unwrap();
    for s in steps {
        match s {
            Step::Clone => {
                left = left.clone();
                right = right.clone();
            }
            Step::Input(d) => {
                left.update(&d);
                right.update(&d);
                independent.update(&d);
            }
        }
    }

    let left = left.sign();
    let right = right.sign();
    assert_eq!(left.as_ref(), right.as_ref());
    assert_eq!(left.as_ref(), &independent.finalize().into_bytes()[..]);
}

#[derive(Arbitrary, Debug)]
enum Operation {
    Sha256(Vec<Step>),
    Sha384(Vec<Step>),
    Sha512(Vec<Step>),
    HmacSha256 { key: Vec<u8>, steps: Vec<Step> },
    HmacSha384 { key: Vec<u8>, steps: Vec<Step> },
    HmacSha512 { key: Vec<u8>, steps: Vec<Step> },
    Sha512_256(Vec<Step>),
}

#[derive(Arbitrary, Debug)]
enum Step {
    Clone,
    Input(Vec<u8>),
}
