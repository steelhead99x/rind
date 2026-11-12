// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Differential tests against the Zcash Foundation's frost 3.0 crates.
//! aws-lc-rs has no FROST. Each side deals in rind, then both libraries
//! verify the other's signature over the same key.

use std::collections::BTreeMap;

use super::{
    ED25519_SHA512, P256_SHA256, RISTRETTO255_SHA512, SigningNonces, SigningPackage, Suite,
    signature_from_bytes,
};

macro_rules! cross {
    ($frost:ident, $suite:expr) => {{
        let suite: &Suite = $suite;
        let dealt = suite.deal(2, 2).unwrap();
        let message = b"differential";
        let (nonces0, commitment0) = SigningNonces::commit(&dealt.signing_shares[0]).unwrap();
        let (nonces1, commitment1) = SigningNonces::commit(&dealt.signing_shares[1]).unwrap();
        let package = SigningPackage::new(vec![commitment0, commitment1], message).unwrap();
        let share0 = nonces0
            .sign(&package, &dealt.signing_shares[0], &dealt.verifying_key)
            .unwrap();
        let share1 = nonces1
            .sign(&package, &dealt.signing_shares[1], &dealt.verifying_key)
            .unwrap();
        let signature = suite
            .aggregate(
                &package,
                &[share0, share1],
                &dealt.verifying_shares,
                &dealt.verifying_key,
            )
            .unwrap();
        signature.verify(&dealt.verifying_key, message).unwrap();

        let verifying_key =
            $frost::VerifyingKey::deserialize(dealt.verifying_key.as_bytes()).unwrap();
        let their_signature = $frost::Signature::deserialize(signature.as_bytes()).unwrap();
        verifying_key
            .verify(message, &their_signature)
            .expect("frost verifies a rind signature");

        let mut keys = Vec::new();
        let mut verifying_shares = BTreeMap::new();
        for (signing, verifying) in dealt.signing_shares.iter().zip(&dealt.verifying_shares) {
            let identifier = $frost::Identifier::deserialize(verifying.identifier()).unwrap();
            let signing_share =
                $frost::keys::SigningShare::deserialize(signing.scalar_bytes()).unwrap();
            let verifying_share =
                $frost::keys::VerifyingShare::deserialize(verifying.as_bytes()).unwrap();
            keys.push($frost::keys::KeyPackage::new(
                identifier,
                signing_share,
                verifying_share,
                verifying_key,
                2,
            ));
            verifying_shares.insert(identifier, verifying_share);
        }
        let public_keys =
            $frost::keys::PublicKeyPackage::new(verifying_shares, verifying_key, Some(2));

        let mut rng = CounterRng::default();
        let mut commitments = BTreeMap::new();
        let mut nonces = Vec::new();
        for key in &keys {
            let (nonce, commitment) = $frost::round1::commit(key.signing_share(), &mut rng);
            commitments.insert(*key.identifier(), commitment);
            nonces.push(nonce);
        }
        let their_package = $frost::SigningPackage::new(commitments, message);
        let mut their_shares = BTreeMap::new();
        for (key, nonce) in keys.iter().zip(nonces) {
            let share = $frost::round2::sign(&their_package, &nonce, key).unwrap();
            their_shares.insert(*key.identifier(), share);
        }
        let their_signature = $frost::aggregate(&their_package, &their_shares, &public_keys)
            .expect("frost signs with rind's shares");
        let imported = signature_from_bytes(suite, their_signature.serialize().unwrap()).unwrap();
        imported
            .verify(&dealt.verifying_key, message)
            .expect("rind verifies a frost signature");
    }};
}

#[test]
fn matches_frost_ed25519() {
    cross!(frost_ed25519, &ED25519_SHA512);
}

#[test]
fn matches_frost_ristretto255() {
    cross!(frost_ristretto255, &RISTRETTO255_SHA512);
}

#[test]
fn matches_frost_p256() {
    cross!(frost_p256, &P256_SHA256);
}

struct CounterRng(u64);

impl Default for CounterRng {
    fn default() -> Self {
        Self(1)
    }
}

impl frost_ed25519::rand_core::RngCore for CounterRng {
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        self.0
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        for byte in dest {
            *byte = self.next_u64() as u8;
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), frost_ed25519::rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl frost_ed25519::rand_core::CryptoRng for CounterRng {}
