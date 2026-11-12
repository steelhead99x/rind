#![no_main]

//! ML-KEM decapsulating what aws-lc-rs encapsulates, tampered with, in each
//! parameter set.
//!
//! rind's decapsulation keys are only ever generated, and never exported, so
//! aws-lc-rs cannot hold the same key: this checks rind recovers aws-lc-rs's
//! secret exactly when the ciphertext is untouched. The in-crate crosscheck
//! compares the implicit-rejection secret.

use aws_lc_rs::kem as theirs;
use libfuzzer_sys::fuzz_target;
use rind::kem as ours;

mod edit;

fuzz_target!(|input: (u8, edit::Edit)| {
    let (set, edit) = input;
    match set % 3 {
        0 => check::<ours::MlKem512>(&theirs::ML_KEM_512, &edit),
        1 => check::<ours::MlKem768>(&theirs::ML_KEM_768, &edit),
        _ => check::<ours::MlKem1024>(&theirs::ML_KEM_1024, &edit),
    }
});

/// Decapsulates `edit` of aws-lc-rs's encapsulation to a new key of set `A`.
fn check<A: ours::Algorithm>(
    algorithm: &'static theirs::Algorithm<theirs::AlgorithmId>,
    edit: &edit::Edit,
) {
    let key = ours::DecapsulationKey::<A>::generate().unwrap();
    let (ciphertext, secret) = theirs::EncapsulationKey::new(algorithm, key.public_key().as_ref())
        .unwrap()
        .encapsulate()
        .unwrap();
    let mut ciphertext = ciphertext.as_ref().to_vec();
    let len = ciphertext.len();
    let changed = edit.apply(&mut ciphertext);

    match (
        ciphertext.len() == len,
        ours::Ciphertext::<A>::new(&ciphertext),
    ) {
        (true, Ok(c)) => assert_eq!(key.decapsulate(&c).as_ref() == secret.as_ref(), !changed),
        (true, Err(e)) => panic!("refused a ciphertext of the right length: {e:?}"),
        (false, result) => assert_eq!(result.err(), Some(rind::Error::WrongLength)),
    }
}
