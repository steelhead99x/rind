// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ML-KEM through the module interoperates with rind's, which its own tests
//! check against Wycheproof, CCTV, and aws-lc-rs, and refuses every
//! malformed key and ciphertext with rind's error, at every parameter set.
#![cfg(rind_fips_module)]

use rind_fips::kem::{Ciphertext, DecapsulationKey, EncapsulationKey};

/// A parameter set as the module and rind each type it.
trait Set {
    type Ours: rind_fips::kem::Algorithm;
    type Theirs: rind::kem::Algorithm;
    const EK_LEN: usize;
    const CT_LEN: usize;
}

macro_rules! set {
    ($name:ident, $ek:literal, $ct:literal) => {
        impl Set for rind_fips::kem::$name {
            type Ours = Self;
            type Theirs = rind::kem::$name;
            const EK_LEN: usize = $ek;
            const CT_LEN: usize = $ct;
        }
    };
}

set!(MlKem512, 800, 768);
set!(MlKem768, 1184, 1088);
set!(MlKem1024, 1568, 1568);

/// Runs the generic test `f` for every parameter set.
macro_rules! each_set {
    ($f:ident) => {
        $f::<rind_fips::kem::MlKem512>();
        $f::<rind_fips::kem::MlKem768>();
        $f::<rind_fips::kem::MlKem1024>();
    };
}

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
    fn check<S: Set>() {
        for _ in 0..4 {
            // The module decapsulates what rind encapsulated to its key.
            let key = DecapsulationKey::<S::Ours>::generate().unwrap();
            let public = key.public_key();
            let peer = rind::kem::EncapsulationKey::<S::Theirs>::new(public.as_ref()).unwrap();
            assert_eq!(peer.as_ref(), public.as_ref());
            let (ciphertext, secret) = peer.encapsulate().unwrap();
            let ciphertext = Ciphertext::new(ciphertext.as_ref()).unwrap();
            assert_eq!(key.decapsulate(&ciphertext).as_ref(), secret.as_ref());

            // rind decapsulates what the module encapsulated to its key.
            let reference = rind::kem::DecapsulationKey::<S::Theirs>::generate().unwrap();
            let peer = EncapsulationKey::<S::Ours>::new(reference.public_key().as_ref()).unwrap();
            assert_eq!(peer.as_ref(), reference.public_key().as_ref());
            for peer in [peer.clone(), peer] {
                let (ciphertext, secret) = peer.encapsulate().unwrap();
                assert_eq!(ciphertext.as_ref().len(), S::CT_LEN);
                assert_eq!(secret.as_ref().len(), 32);
                let ciphertext = rind::kem::Ciphertext::new(ciphertext.as_ref()).unwrap();
                let recovered = reference.decapsulate(&ciphertext);
                assert_eq!(recovered.as_ref(), secret.as_ref());
            }

            // A key's own encapsulation key parses back to itself.
            let reparsed = EncapsulationKey::<S::Ours>::new(public.as_ref()).unwrap();
            let (ciphertext, secret) = reparsed.encapsulate().unwrap();
            assert_eq!(
                key.decapsulate(&ciphertext.clone()).as_ref(),
                secret.as_ref()
            );
        }
    }
    each_set!(check);
}

#[test]
fn rejects_tampered_ciphertexts_implicitly() {
    fn check<S: Set>() {
        let key = DecapsulationKey::<S::Ours>::generate().unwrap();
        let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
        for at in [0, 1, 500, S::CT_LEN - 1] {
            let mut tampered = ciphertext.as_ref().to_vec();
            tampered[at] ^= 1;
            let tampered = Ciphertext::new(&tampered).unwrap();
            // FIPS 203's implicit rejection: a secret, unrelated to the real
            // one, the same each time. The module's self-test checks its
            // value against rind's on a known key.
            let rejected = key.decapsulate(&tampered);
            assert_ne!(rejected.as_ref(), secret.as_ref());
            assert_eq!(key.decapsulate(&tampered).as_ref(), rejected.as_ref());
        }
    }
    each_set!(check);
}

#[test]
fn refuses_what_rind_refuses() {
    fn check<S: Set>() {
        let reference = rind::kem::DecapsulationKey::<S::Theirs>::generate().unwrap();
        let public = reference.public_key().as_ref().to_vec();

        // The first coefficient set to 4095, above q, fails the modulus
        // check.
        let mut above_q = public.clone();
        above_q[0] = 0xff;
        above_q[1] |= 0x0f;
        let keys: [(&str, Vec<u8>); 5] = [
            ("empty", vec![]),
            ("short", public[..S::EK_LEN - 1].to_vec()),
            ("long", [&public[..], &[0]].concat()),
            ("above the modulus", above_q),
            ("a valid key", public),
        ];
        for (what, bytes) in &keys {
            same_result(
                &EncapsulationKey::<S::Ours>::new(bytes),
                &rind::kem::EncapsulationKey::<S::Theirs>::new(bytes),
                &format!("encapsulation key {what}"),
            );
        }

        for len in [0, S::CT_LEN - 1, S::CT_LEN + 1] {
            same_result(
                &Ciphertext::<S::Ours>::new(&vec![0; len]),
                &rind::kem::Ciphertext::<S::Theirs>::new(&vec![0; len]),
                &format!("a ciphertext of {len} bytes"),
            );
        }
    }
    each_set!(check);
}

#[test]
fn debug_matches_rind() {
    fn check<S: Set>() {
        let reference = rind::kem::DecapsulationKey::<S::Theirs>::generate().unwrap();
        let key = DecapsulationKey::<S::Ours>::generate().unwrap();
        assert_eq!(format!("{key:?}"), format!("{reference:?}"));

        let theirs = reference.public_key();
        let ours = EncapsulationKey::<S::Ours>::new(theirs.as_ref()).unwrap();
        assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));

        // A ciphertext prints as rind's does, around its bytes.
        let (ciphertext, secret) = ours.encapsulate().unwrap();
        let (_, their_secret) = theirs.encapsulate().unwrap();
        let same = rind::kem::Ciphertext::<S::Theirs>::new(ciphertext.as_ref()).unwrap();
        assert_eq!(format!("{ciphertext:?}"), format!("{same:?}"));
        assert_eq!(format!("{secret:?}"), format!("{their_secret:?}"));
    }
    each_set!(check);
}
