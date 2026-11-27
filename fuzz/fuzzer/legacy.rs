#![no_main]

//! The legacy hashes, MD5 and SHA-1, and HMAC-SHA1, against aws-lc's and
//! RustCrypto's. aws-lc-rs has no MD5, so that calls aws-lc directly.

use ::hmac::{KeyInit, Mac};
use aws_lc_rs::{digest, hmac};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use sha1::Digest;

fuzz_target!(|op: Operation| {
    match op {
        Operation::Md5(steps) => {
            let mut ours = rind::digest::Context::new(&rind::digest::legacy::MD5);
            let mut message = Vec::new();
            for s in steps {
                match s {
                    Step::Clone => ours = ours.clone(),
                    Step::Input(d) => {
                        ours.update(&d);
                        message.extend(d);
                    }
                }
            }

            let mut theirs = [0u8; 16];
            // SAFETY: `message` is `message.len()` readable bytes, and
            // `theirs` the 16 writable bytes of an MD5 digest.
            let ok = unsafe {
                aws_lc_sys::EVP_Digest(
                    message.as_ptr().cast(),
                    message.len(),
                    theirs.as_mut_ptr(),
                    core::ptr::null_mut(),
                    aws_lc_sys::EVP_md5(),
                    core::ptr::null_mut(),
                )
            };
            assert_eq!(ok, 1);
            assert_eq!(ours.finish().as_ref(), theirs);
            assert_eq!(md5::Md5::digest(&message)[..], theirs);
        }
        Operation::Sha1(steps) => {
            let mut left = digest::Context::new(&digest::SHA1_FOR_LEGACY_USE_ONLY);
            let mut right = rind::digest::Context::new(&rind::digest::legacy::SHA1);
            let mut independent = sha1::Sha1::new();

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
        Operation::HmacSha1 { key, steps } => {
            let mut left =
                hmac::Context::with_key(&hmac::Key::new(hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY, &key));
            let mut right = rind::hmac::Context::with_key(&rind::hmac::Key::new(
                &rind::hmac::legacy::HMAC_SHA1,
                &key,
            ));
            let mut independent = ::hmac::Hmac::<sha1::Sha1>::new_from_slice(&key).unwrap();

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
    }
});

#[derive(Arbitrary, Debug)]
enum Operation {
    Md5(Vec<Step>),
    Sha1(Vec<Step>),
    HmacSha1 { key: Vec<u8>, steps: Vec<Step> },
}

#[derive(Arbitrary, Debug)]
enum Step {
    Clone,
    Input(Vec<u8>),
}
