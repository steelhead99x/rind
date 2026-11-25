#![no_main]

//! ECDH against aws-lc-rs and an independent oracle for any scalar and peer
//! key: libcrux's X25519, HACL*'s, which rind runs nowhere, and the NIST
//! curves' oracle for this tier. The oracle checks only what aws-lc-rs
//! accepts.

use aws_lc_rs::agreement as theirs;
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use oracle::Nist;
use rind::agreement as ours;

mod oracle;

fuzz_target!(|op: Operation| {
    match op {
        Operation::X25519 { scalar, peer } => {
            check(&ours::X25519, &theirs::X25519, &X25519, &scalar, &peer);
        }
        Operation::P256 { scalar, peer } => {
            let oracle = oracle::p256();
            check(
                &ours::ECDH_P256,
                &theirs::ECDH_P256,
                &oracle,
                &scalar,
                &peer,
            );
        }
        Operation::P384 { scalar, peer } => {
            let oracle = oracle::p384();
            check(
                &ours::ECDH_P384,
                &theirs::ECDH_P384,
                &oracle,
                &scalar,
                &peer,
            );
        }
        Operation::P521 { scalar, peer } => {
            let oracle = oracle::p521();
            check(
                &ours::ECDH_P521,
                &theirs::ECDH_P521,
                &oracle,
                &scalar,
                &peer,
            );
        }
    }
});

/// The ECDH an independent oracle computes.
trait Independent {
    fn public_key(&self, scalar: &[u8]) -> Vec<u8>;
    fn agree(&self, scalar: &[u8], peer: &[u8]) -> Option<Vec<u8>>;
}

impl<T: Nist> Independent for T {
    fn public_key(&self, scalar: &[u8]) -> Vec<u8> {
        Nist::public_key(self, scalar)
    }

    fn agree(&self, scalar: &[u8], peer: &[u8]) -> Option<Vec<u8>> {
        Nist::agree(self, scalar, peer)
    }
}

/// libcrux's X25519.
struct X25519;

impl Independent for X25519 {
    fn public_key(&self, scalar: &[u8]) -> Vec<u8> {
        let mut public = [0u8; 32];
        libcrux_curve25519::secret_to_public(&mut public, scalar.try_into().unwrap());
        public.to_vec()
    }

    fn agree(&self, scalar: &[u8], peer: &[u8]) -> Option<Vec<u8>> {
        let mut secret = [0u8; 32];
        libcrux_curve25519::ecdh(
            &mut secret,
            peer.try_into().unwrap(),
            scalar.try_into().unwrap(),
        )
        .ok()?;
        Some(secret.to_vec())
    }
}

// Both load the fuzzed scalar, which checks our base and variable-base
// multiplication against aws-lc-rs's and the oracle's, and agree with the
// fuzzed peer key.
fn check(
    ours_algorithm: &'static ours::Algorithm,
    theirs_algorithm: &'static theirs::Algorithm,
    independent: &impl Independent,
    scalar: &[u8],
    peer: &[u8],
) {
    let ours_key = ours::PrivateKey::from_scalar(ours_algorithm, scalar);
    let theirs_key = theirs::PrivateKey::from_private_key(theirs_algorithm, scalar);
    assert_eq!(ours_key.is_ok(), theirs_key.is_ok());
    let (Ok(ours_key), Ok(theirs_key)) = (ours_key, theirs_key) else {
        return;
    };
    let ours_public = ours_key.public_key();
    let theirs_public = theirs_key.compute_public_key().unwrap();
    assert_eq!(ours_public.as_ref(), theirs_public.as_ref());
    assert_eq!(ours_public.as_ref(), independent.public_key(scalar));

    // Both accept or refuse the same peer key, and agree on the secret.
    let ours_secret = ours_key.agree(peer);
    let theirs_secret = theirs::agree(
        &theirs_key,
        theirs::UnparsedPublicKey::new(theirs_algorithm, peer),
        (),
        |secret| Ok(secret.to_vec()),
    );
    match (ours_secret, theirs_secret) {
        (Ok(ours), Ok(theirs)) => {
            assert_eq!(ours.as_ref(), &theirs[..]);
            assert_eq!(Some(theirs), independent.agree(scalar, peer));
        }
        (Err(_), Err(())) => {}
        (ours, theirs) => panic!("rind: {:?}, aws-lc-rs: {:?}", ours.err(), theirs.err()),
    }
}

#[derive(Arbitrary, Debug)]
enum Operation {
    X25519 { scalar: [u8; 32], peer: [u8; 32] },
    P256 { scalar: [u8; 32], peer: [u8; 65] },
    P384 { scalar: [u8; 48], peer: [u8; 97] },
    P521 { scalar: [u8; 66], peer: [u8; 133] },
}
