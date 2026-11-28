//! RustCrypto's documented `ml-kem` example and its inherent API, with only
//! the crate in each path swapped for rind-kem, so code written against
//! `ml-kem` builds here unchanged; each result is checked against `ml-kem`'s.

#[test]
fn ml_kem_example() {
    use rind_kem::{
        MlKem768,
        kem::{Decapsulate, Encapsulate, Kem},
    };

    let (dk, ek) = MlKem768::generate_keypair();
    let (ct, k_send) = ek.encapsulate();
    let k_recv = dk.decapsulate(&ct);
    assert_eq!(k_send, k_recv);
}

/// `ml-kem`'s inherent methods, aliases, and per-set modules.
#[test]
fn inherent_api() {
    use rind_kem::{B32, DecapsulationKey768, EncapsulationKey768, KeyExport, Seed, SharedKey};

    let seed = Seed::from([0x42; 64]);
    let ours = DecapsulationKey768::from_seed(seed);
    let theirs = ml_kem::DecapsulationKey768::from_seed(seed);
    assert_eq!(ours.to_seed(), theirs.to_seed());
    assert_eq!(
        ours.encapsulation_key().to_bytes(),
        theirs.encapsulation_key().to_bytes()
    );
    let from: rind_kem::ml_kem_768::DecapsulationKey = seed.into();
    assert_eq!(from.to_seed(), Some(seed));

    let ek = EncapsulationKey768::new(&theirs.encapsulation_key().to_bytes()).unwrap();
    let m = B32::from([7; 32]);
    let (ct, k): (rind_kem::ml_kem_768::Ciphertext, SharedKey) = ek.encapsulate_deterministic(&m);
    assert_eq!(
        (ct, k),
        theirs.encapsulation_key().encapsulate_deterministic(&m)
    );
    let _: rind_kem::ml_kem_512::MlKem512 = rind_kem::MlKem512;
    let _: rind_kem::ml_kem_1024::MlKem1024 = rind_kem::MlKem1024;
}
