//! The curves' independent oracles, each sharing no code with the path rind
//! runs on this tier: on x86_64 and aarch64, RustCrypto's NIST curves; on
//! armv7 and the portable backend, where rind, aws-lc-rs, and RustCrypto's
//! `p521` run fiat-crypto's field arithmetic, libcrux's P-256 and the
//! textbook reference's P-384 and P-521. RustCrypto's `p256`, and `p384`
//! without its optional fiat backend, would share nothing there either.
//!
//! `tests/crosschecks.rs` and the fuzz targets include this file, which
//! takes the textbook reference as `super::reference` from the module that
//! includes it and picks by `rind_backend`, which the fuzz crate's build
//! script sets as rind's does.

/// ECDH and ECDSA on one NIST curve, over big-endian scalars, SEC 1
/// points, and fixed-width signatures.
pub(crate) trait Nist {
    /// The uncompressed public key of a private scalar.
    fn public_key(&self, scalar: &[u8]) -> Vec<u8>;
    /// The ECDH secret with a peer's point, uncompressed or compressed,
    /// or `None` where the oracle refuses the point.
    fn agree(&self, scalar: &[u8], peer: &[u8]) -> Option<Vec<u8>>;
    /// A signature over a digest of the curve's own hash.
    fn sign(&self, scalar: &[u8], digest: &[u8]) -> Vec<u8>;
    /// Whether a signature is over the digest.
    fn verify(&self, public_key: &[u8], digest: &[u8], signature: &[u8]) -> bool;
}

#[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
macro_rules! rustcrypto {
    ($name:ident, $curve:ident) => {
        /// RustCrypto's curve.
        pub(crate) struct $name;

        impl Nist for $name {
            fn public_key(&self, scalar: &[u8]) -> Vec<u8> {
                use $curve::elliptic_curve::sec1::ToSec1Point;
                let key = $curve::SecretKey::from_slice(scalar).unwrap();
                key.public_key().to_sec1_point(false).as_bytes().to_vec()
            }

            fn agree(&self, scalar: &[u8], peer: &[u8]) -> Option<Vec<u8>> {
                let peer = $curve::PublicKey::from_sec1_bytes(peer).ok()?;
                let key = $curve::SecretKey::from_slice(scalar).unwrap();
                let secret =
                    $curve::ecdh::diffie_hellman(key.to_nonzero_scalar(), peer.as_affine());
                Some(secret.raw_secret_bytes().to_vec())
            }

            fn sign(&self, scalar: &[u8], digest: &[u8]) -> Vec<u8> {
                use $curve::ecdsa::signature::hazmat::PrehashSigner;
                let key = $curve::ecdsa::SigningKey::from_slice(scalar).unwrap();
                let signature: $curve::ecdsa::Signature = key.sign_prehash(digest).unwrap();
                signature.to_bytes().to_vec()
            }

            fn verify(&self, public_key: &[u8], digest: &[u8], signature: &[u8]) -> bool {
                use $curve::ecdsa::signature::hazmat::PrehashVerifier;
                let (Ok(key), Ok(signature)) = (
                    $curve::ecdsa::VerifyingKey::from_sec1_bytes(public_key),
                    $curve::ecdsa::Signature::from_slice(signature),
                ) else {
                    return false;
                };
                key.verify_prehash(digest, &signature).is_ok()
            }
        }
    };
}

#[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
mod rustcrypto {
    use super::Nist;
    rustcrypto!(P256, p256);
    rustcrypto!(P384, p384);
    rustcrypto!(P521, p521);
}

#[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
pub(crate) use rustcrypto::{P256, P384, P521};

/// libcrux's P-256, HACL*'s, which rind runs nowhere.
#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
pub(crate) struct P256;

#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
impl Nist for P256 {
    fn public_key(&self, scalar: &[u8]) -> Vec<u8> {
        let mut raw = [0u8; 64];
        assert!(libcrux_p256::dh_initiator(&mut raw, scalar));
        [&[4][..], &raw].concat()
    }

    fn agree(&self, scalar: &[u8], peer: &[u8]) -> Option<Vec<u8>> {
        let mut raw = [0u8; 64];
        let parsed = match peer.len() {
            65 => libcrux_p256::uncompressed_to_raw(peer, &mut raw),
            33 => libcrux_p256::compressed_to_raw(peer, &mut raw),
            _ => false,
        };
        let mut secret = [0u8; 64];
        (parsed && libcrux_p256::dh_responder(&mut secret, &raw, scalar))
            .then(|| secret[..32].to_vec())
    }

    fn sign(&self, scalar: &[u8], digest: &[u8]) -> Vec<u8> {
        use sha2::Digest;
        let mut signature = [0u8; 64];
        for counter in 0u8.. {
            let nonce = sha2::Sha256::digest([scalar, digest, &[counter]].concat());
            if libcrux_p256::ecdsa_sign_p256_without_hash(
                &mut signature,
                32,
                digest,
                scalar,
                &nonce,
            ) {
                return signature.to_vec();
            }
        }
        unreachable!()
    }

    fn verify(&self, public_key: &[u8], digest: &[u8], signature: &[u8]) -> bool {
        let mut raw = [0u8; 64];
        signature.len() == 64
            && libcrux_p256::uncompressed_to_raw(public_key, &mut raw)
            && libcrux_p256::ecdsa_verif_without_hash(
                32,
                digest,
                &raw,
                &signature[..32],
                &signature[32..],
            )
    }
}

#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
impl Nist for super::reference::Weierstrass {
    fn public_key(&self, scalar: &[u8]) -> Vec<u8> {
        super::reference::Weierstrass::public_key(self, scalar)
    }

    fn agree(&self, scalar: &[u8], peer: &[u8]) -> Option<Vec<u8>> {
        super::reference::Weierstrass::agree(self, scalar, peer)
    }

    fn sign(&self, scalar: &[u8], digest: &[u8]) -> Vec<u8> {
        super::reference::Weierstrass::sign(self, scalar, digest)
    }

    fn verify(&self, public_key: &[u8], digest: &[u8], signature: &[u8]) -> bool {
        super::reference::Weierstrass::verify(self, public_key, digest, signature)
    }
}

pub(crate) fn p256() -> impl Nist {
    P256
}

#[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
pub(crate) fn p384() -> impl Nist {
    P384
}

#[cfg(not(any(rind_backend = "arm", rind_backend = "portable")))]
pub(crate) fn p521() -> impl Nist {
    P521
}

#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
pub(crate) fn p384() -> impl Nist {
    super::reference::p384()
}

#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
pub(crate) fn p521() -> impl Nist {
    super::reference::p521()
}
