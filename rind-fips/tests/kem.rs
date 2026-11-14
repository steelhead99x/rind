// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM-768 through the module interoperates with rind's, which its own
//! tests check against Wycheproof, CCTV, and aws-lc-rs, and refuses every
//! malformed key and ciphertext with rind's error.
#![cfg(rind_fips_module)]

use rind_fips::kem::{DecapsulationKey, EncapsulationKey, ML_KEM_768};

/// Asserts that both succeeded, or failed with the same error.
#[track_caller]
fn same_result<T, U>(
    ours: &Result<T, rind_fips::Error>,
    theirs: &Result<U, rind::Error>,
    what: &str,
) {
    match (ours, theirs) {
        (Ok(_), Ok(_)) => {}
        (Err(ours), Err(theirs)) => assert_eq!(ours.to_string(), theirs.to_string(), "{what}"),
        _ => panic!(
            "{what}: the module {}, rind {}",
            ours.as_ref()
                .map_or_else(|e| e.to_string(), |_| "accepted".into()),
            theirs
                .as_ref()
                .map_or_else(|e| e.to_string(), |_| "accepted".into()),
        ),
    }
}

#[test]
fn interoperates_with_rind() {
    let theirs = &rind::kem::ML_KEM_768;
    for _ in 0..4 {
        // The module decapsulates what rind encapsulated to its key.
        let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
        let public = key.public_key();
        let peer = rind::kem::EncapsulationKey::new(theirs, public.as_ref()).unwrap();
        assert_eq!(peer.as_ref(), public.as_ref());
        let (ciphertext, secret) = peer.encapsulate().unwrap();
        assert_eq!(
            key.decapsulate(ciphertext.as_ref()).unwrap().as_ref(),
            secret.as_ref()
        );

        // rind decapsulates what the module encapsulated to its key.
        let reference = rind::kem::DecapsulationKey::generate(theirs).unwrap();
        let peer = EncapsulationKey::new(&ML_KEM_768, reference.public_key().as_ref()).unwrap();
        assert_eq!(peer.as_ref(), reference.public_key().as_ref());
        for peer in [peer.clone(), peer] {
            let (ciphertext, secret) = peer.encapsulate().unwrap();
            assert_eq!(ciphertext.as_ref().len(), 1088);
            assert_eq!(secret.as_ref().len(), 32);
            let recovered = reference.decapsulate(ciphertext.as_ref()).unwrap();
            assert_eq!(recovered.as_ref(), secret.as_ref());
        }

        // A key's own encapsulation key parses back to itself.
        let reparsed = EncapsulationKey::new(&ML_KEM_768, public.as_ref()).unwrap();
        let (ciphertext, secret) = reparsed.encapsulate().unwrap();
        assert_eq!(
            key.decapsulate(ciphertext.clone().as_ref())
                .unwrap()
                .as_ref(),
            secret.as_ref()
        );
    }
}

#[test]
fn rejects_tampered_ciphertexts_implicitly() {
    let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
    let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
    for at in [0, 1, 500, 1087] {
        let mut tampered = ciphertext.as_ref().to_vec();
        tampered[at] ^= 1;
        // FIPS 203's implicit rejection: a secret, unrelated to the real one,
        // the same each time. The module's self-test checks its value
        // against rind's on a known key.
        let rejected = key.decapsulate(&tampered).unwrap();
        assert_ne!(rejected.as_ref(), secret.as_ref());
        assert_eq!(
            key.decapsulate(&tampered).unwrap().as_ref(),
            rejected.as_ref()
        );
    }
}

#[test]
fn refuses_what_rind_refuses() {
    let theirs = &rind::kem::ML_KEM_768;
    let reference = rind::kem::DecapsulationKey::generate(theirs).unwrap();
    let public = reference.public_key().as_ref().to_vec();

    // The first coefficient set to 4095, above q, fails the modulus check.
    let mut above_q = public.clone();
    above_q[0] = 0xff;
    above_q[1] |= 0x0f;
    let keys: [(&str, Vec<u8>); 5] = [
        ("empty", vec![]),
        ("short", public[..1183].to_vec()),
        ("long", [&public[..], &[0]].concat()),
        ("above the modulus", above_q),
        ("a valid key", public),
    ];
    for (what, bytes) in &keys {
        same_result(
            &EncapsulationKey::new(&ML_KEM_768, bytes),
            &rind::kem::EncapsulationKey::new(theirs, bytes),
            &format!("encapsulation key {what}"),
        );
    }

    let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
    for len in [0, 1087, 1089] {
        same_result(
            &key.decapsulate(&vec![0; len]),
            &reference.decapsulate(&vec![0; len]),
            &format!("a ciphertext of {len} bytes"),
        );
    }
}

#[test]
fn debug_matches_rind() {
    assert_eq!(
        format!("{ML_KEM_768:?}"),
        format!("{:?}", rind::kem::ML_KEM_768)
    );
    let reference = rind::kem::DecapsulationKey::generate(&rind::kem::ML_KEM_768).unwrap();
    let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
    assert_eq!(format!("{key:?}"), format!("{reference:?}"));

    let theirs = reference.public_key();
    let ours = EncapsulationKey::new(&ML_KEM_768, theirs.as_ref()).unwrap();
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));

    // A ciphertext prints as rind's derived `Debug` does, around its bytes.
    let (ciphertext, secret) = ours.encapsulate().unwrap();
    let (their_ciphertext, their_secret) = theirs.encapsulate().unwrap();
    let bytes: [u8; 1088] = ciphertext.as_ref().try_into().unwrap();
    let their_bytes: [u8; 1088] = their_ciphertext.as_ref().try_into().unwrap();
    assert_eq!(
        format!("{ciphertext:?}"),
        format!("Ciphertext(Ciphertext({bytes:?}))")
    );
    assert_eq!(
        format!("{their_ciphertext:?}"),
        format!("Ciphertext(Ciphertext({their_bytes:?}))")
    );
    assert_eq!(format!("{secret:?}"), format!("{their_secret:?}"));
}
