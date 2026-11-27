#![no_main]

//! ML-KEM decapsulating what aws-lc-rs and RustCrypto encapsulate, tampered
//! with, in each parameter set, and RustCrypto decapsulating what rind
//! encapsulates.
//!
//! rind's decapsulation keys are only ever generated, and never exported, so
//! neither can hold the same key: this checks rind recovers each one's
//! secret exactly when the ciphertext is untouched. The in-crate crosscheck
//! compares the implicit-rejection secret.

use aws_lc_rs::kem as theirs;
use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};
use libfuzzer_sys::fuzz_target;
use ml_kem::{Decapsulate, KeyExport};
use rind::kem as ours;
use sha2::Digest;

mod edit;

// The input is the parameter set and the edit alone, so corpora from before
// the independent oracle still decode alike; its message and seed are
// hashed from it, since any value exercises the same constant-time code.
fuzz_target!(|data: &[u8]| {
    let Ok((set, edit)) = <(u8, edit::Edit)>::arbitrary_take_rest(Unstructured::new(data)) else {
        return;
    };
    let m: [u8; 32] = sha2::Sha256::digest(data).into();
    let seed: [u8; 64] = sha2::Sha512::digest(data).into();
    match set % 3 {
        0 => check!(
            ours::MlKem512,
            ml_kem::MlKem512,
            theirs::ML_KEM_512,
            edit,
            m,
            seed
        ),
        1 => check!(
            ours::MlKem768,
            ml_kem::MlKem768,
            theirs::ML_KEM_768,
            edit,
            m,
            seed
        ),
        _ => check!(
            ours::MlKem1024,
            ml_kem::MlKem1024,
            theirs::ML_KEM_1024,
            edit,
            m,
            seed
        ),
    }
});

/// Decapsulates `edit` of aws-lc-rs's encapsulation to a new key of set
/// `$ours`, and of RustCrypto's from message `m`, and encapsulates to
/// RustCrypto's key of `seed`, which decapsulates rind's secret.
macro_rules! check {
    ($ours:ty, $independent:ty, $theirs:expr, $edit:expr, $m:expr, $seed:expr) => {{
        let key = ours::DecapsulationKey::<$ours>::generate().unwrap();
        let public = key.public_key();
        let (ciphertext, secret) = theirs::EncapsulationKey::new(&$theirs, public.as_ref())
            .unwrap()
            .encapsulate()
            .unwrap();
        decapsulate(&key, ciphertext.as_ref(), secret.as_ref(), &$edit);

        let independent =
            ml_kem::EncapsulationKey::<$independent>::new(public.as_ref().try_into().unwrap())
                .expect("RustCrypto refused rind's encapsulation key");
        let (ciphertext, secret) = independent.encapsulate_deterministic(&$m.into());
        decapsulate(&key, &ciphertext, &secret, &$edit);

        let independent = ml_kem::DecapsulationKey::<$independent>::from_seed($seed.into());
        let public = independent.encapsulation_key().to_bytes();
        let (ciphertext, secret) = ours::EncapsulationKey::<$ours>::new(&public)
            .unwrap()
            .encapsulate()
            .unwrap();
        let decapsulated = independent.decapsulate(ciphertext.as_ref().try_into().unwrap());
        assert_eq!(secret.as_ref(), &decapsulated[..]);
    }};
}
use check;

/// Decapsulates `edit` of `ciphertext`, which encapsulates `secret` to
/// `key`: the same secret exactly when the edit leaves it untouched, and a
/// refusal when it changes its length.
fn decapsulate<A: ours::Algorithm>(
    key: &ours::DecapsulationKey<A>,
    ciphertext: &[u8],
    secret: &[u8],
    edit: &edit::Edit,
) {
    let mut ciphertext = ciphertext.to_vec();
    let len = ciphertext.len();
    let changed = edit.apply(&mut ciphertext);

    match (
        ciphertext.len() == len,
        ours::Ciphertext::<A>::new(&ciphertext),
    ) {
        (true, Ok(c)) => assert_eq!(key.decapsulate(&c).as_ref() == secret, !changed),
        (true, Err(e)) => panic!("refused a ciphertext of the right length: {e:?}"),
        (false, result) => assert_eq!(result.err(), Some(rind::Error::WrongLength)),
    }
}
