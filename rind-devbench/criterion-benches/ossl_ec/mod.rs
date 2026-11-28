//! OpenSSL's ECDH and ECDSA on one curve, timing the same steps as the other
//! libraries' rows: key generation and encoding for ECDH, and parsing the
//! public key for each verification.

use std::hint::black_box;

use openssl::bn::{BigNum, BigNumContext};
use openssl::derive::Deriver;
use openssl::ec::{EcGroup, EcKey, EcPoint, PointConversionForm};
use openssl::ecdsa::EcdsaSig;
use openssl::hash::MessageDigest;
use openssl::nid::Nid;
use openssl::pkey::{PKey, Private, Public};
use openssl::sign::{Signer, Verifier};

pub struct Curve {
    group: EcGroup,
    ctx: BigNumContext,
    digest: MessageDigest,
}

impl Curve {
    /// The curve `nid`, signing over `digest`.
    pub fn new(nid: Nid, digest: MessageDigest) -> Self {
        Self {
            group: EcGroup::from_curve_name(nid).unwrap(),
            ctx: BigNumContext::new().unwrap(),
            digest,
        }
    }

    fn public_key(&mut self, encoded: &[u8]) -> PKey<Public> {
        let point = EcPoint::from_bytes(&self.group, encoded, &mut self.ctx).unwrap();
        PKey::from_ec_key(EcKey::from_public_key(&self.group, &point).unwrap()).unwrap()
    }

    pub fn generate(&self) -> PKey<Private> {
        PKey::from_ec_key(EcKey::generate(&self.group).unwrap()).unwrap()
    }

    /// An ephemeral key agreement with the uncompressed point `peer`.
    pub fn ecdh(&mut self, peer: &[u8]) {
        let key = self.generate();
        let ec_key = key.ec_key().unwrap();
        black_box(
            ec_key
                .public_key()
                .to_bytes(
                    &self.group,
                    PointConversionForm::UNCOMPRESSED,
                    &mut self.ctx,
                )
                .unwrap(),
        );

        let peer = self.public_key(peer);
        let mut deriver = Deriver::new(&key).unwrap();
        deriver.set_peer(&peer).unwrap();
        black_box(deriver.derive_to_vec().unwrap());
    }

    /// `signature`, fixed-length `r || s`, in the DER form OpenSSL takes.
    pub fn der(signature: &[u8]) -> Vec<u8> {
        let (r, s) = signature.split_at(signature.len() / 2);
        EcdsaSig::from_private_components(
            BigNum::from_slice(r).unwrap(),
            BigNum::from_slice(s).unwrap(),
        )
        .unwrap()
        .to_der()
        .unwrap()
    }

    /// Verifies the DER `signature` with the uncompressed point `public_key`.
    pub fn verify(&mut self, public_key: &[u8], message: &[u8], signature: &[u8]) {
        let key = self.public_key(public_key);
        let mut verifier = Verifier::new(self.digest, &key).unwrap();
        assert!(verifier.verify_oneshot(signature, message).unwrap());
    }

    pub fn sign(&self, key: &PKey<Private>, message: &[u8]) -> Vec<u8> {
        let mut signer = Signer::new(self.digest, key).unwrap();
        signer.sign_oneshot_to_vec(message).unwrap()
    }
}
