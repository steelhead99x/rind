#![no_main]

//! SHA-3 against aws-lc-rs's and RustCrypto's, in updates of any length with
//! clones between.

use aws_lc_rs::digest;
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use sha3::digest::DynDigest;

fuzz_target!(|op: Operation| {
    let (theirs, ours, mut independent): (_, _, Box<dyn DynDigest>) = match op.algorithm {
        Algorithm::Sha3_256 => (
            &digest::SHA3_256,
            &rind::digest::SHA3_256,
            Box::new(sha3::Sha3_256::default()),
        ),
        Algorithm::Sha3_384 => (
            &digest::SHA3_384,
            &rind::digest::SHA3_384,
            Box::new(sha3::Sha3_384::default()),
        ),
        Algorithm::Sha3_512 => (
            &digest::SHA3_512,
            &rind::digest::SHA3_512,
            Box::new(sha3::Sha3_512::default()),
        ),
    };
    let mut left = digest::Context::new(theirs);
    let mut right = rind::digest::Context::new(ours);

    for s in op.steps {
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
});

#[derive(Arbitrary, Debug)]
struct Operation {
    algorithm: Algorithm,
    steps: Vec<Step>,
}

#[derive(Arbitrary, Debug)]
enum Algorithm {
    Sha3_256,
    Sha3_384,
    Sha3_512,
}

#[derive(Arbitrary, Debug)]
enum Step {
    Clone,
    Input(Vec<u8>),
}
