// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ECVRF (RFC 9381): ECVRF-EDWARDS25519-SHA512-TAI and ECVRF-P256-SHA256-TAI.
//!
//! Each suite's steps are RFC 9381 section 5's, over the group code in `mid`.
//! Proving multiplies by the secret key and the nonce in constant time;
//! try-and-increment (section 5.4.1.1) loops on the public key and the input,
//! never on a secret.
//!
//! The SSWU and ELL2 suites are left out: no RFC 9381 consumer uses them, and
//! Cardano's and Algorand's VRFs follow an incompatible pre-RFC draft.

use core::fmt;

use super::ed25519::has_small_order;
use super::hash::Sha256;
use super::hmac_drbg::HmacDrbg;
use crate::error::{Error, KeyFormatError};
use crate::low::{self, Entry, ct};
use crate::mid::edwards25519;
use crate::mid::p256;
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::sha2::{Sha256Context, Sha512Context};

/// An ECVRF ciphersuite.
pub struct Algorithm {
    id: AlgorithmId,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum AlgorithmId {
    Edwards25519Sha512Tai,
    P256Sha256Tai,
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id
    }
}

impl Eq for Algorithm {}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

/// ECVRF-EDWARDS25519-SHA512-TAI: a 32-byte secret key (an RFC 8032 seed),
/// 32-byte public keys, 80-byte proofs, and 64-byte outputs.
pub static ECVRF_EDWARDS25519_SHA512_TAI: Algorithm = Algorithm {
    id: AlgorithmId::Edwards25519Sha512Tai,
};

/// ECVRF-P256-SHA256-TAI: a 32-byte big-endian secret scalar, 33-byte X9.62
/// compressed public keys, 81-byte proofs, and 32-byte outputs.
pub static ECVRF_P256_SHA256_TAI: Algorithm = Algorithm {
    id: AlgorithmId::P256Sha256Tai,
};

/// The secret key that proves outputs, wiped on drop under the `wipe` feature.
///
/// It keeps its public key, computed once when it is generated or loaded.
pub struct SecretKey {
    secret: Secret,
    public: PublicKey,
}

// `repr(u8)` puts `Edwards25519` at tag zero, and each variant is plain words,
// so all-bits-zero is a valid value and `Drop` can wipe the tag and any unused
// tail along with the key.
#[repr(u8)]
enum Secret {
    Edwards25519 {
        seed: [u8; 32],
        /// The clamped scalar, reduced: the points it multiplies are in the
        /// prime-order subgroup.
        x: edwards25519::Scalar,
        /// The second half of the seed's hash, which keys the nonce.
        prefix: [u8; 32],
    },
    P256 {
        x: p256::Scalar,
    },
}

impl low::Zeroable for Secret {}

impl low::Zeroable for SecretKey {}

impl SecretKey {
    /// Generates a secret key for `algorithm` from the system random source.
    pub fn generate(algorithm: &'static Algorithm) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let mut bytes = [0u8; 32];
        loop {
            SystemRandom.fill(&mut bytes)?;
            ct::secret_slice(&bytes);
            // Only P-256 refuses any: a scalar not from 1 to n - 1, a chance
            // of about 2^-32.
            if let Ok(key) = Self::load(algorithm, &bytes) {
                return Ok(key);
            }
        }
    }

    /// Loads a secret key for `algorithm`: Edwards25519's 32-byte RFC 8032
    /// seed, any value, or P-256's 32-byte big-endian scalar, refused unless
    /// it is from 1 to n - 1.
    pub fn from_bytes(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let bytes: &[u8; 32] = bytes.try_into().map_err(|_| KeyFormatError::WrongLength)?;
        Self::load(algorithm, &ct::into_secret(*bytes))
    }

    fn load(algorithm: &'static Algorithm, bytes: &[u8; 32]) -> Result<Self, Error> {
        match algorithm.id {
            AlgorithmId::Edwards25519Sha512Tai => {
                // RFC 8032 5.1.5: the clamped low half of the seed's hash.
                let h = sha512(&[bytes]);
                let mut wide = [0u8; 64];
                wide[..32].copy_from_slice(&h[..32]);
                wide[0] &= 248;
                wide[31] &= 127;
                wide[31] |= 64;
                let x = edwards25519::Scalar::from_uniform_bytes(&wide);
                let point = ct::into_public(edwards25519::Point::mul_base(&x));
                Ok(Self {
                    secret: Secret::Edwards25519 {
                        seed: *bytes,
                        x,
                        prefix: h[32..].try_into().unwrap(),
                    },
                    public: PublicKey(Public::Edwards25519 {
                        bytes: point.to_bytes(),
                        point,
                    }),
                })
            }
            AlgorithmId::P256Sha256Tai => {
                let x = p256::Scalar::from_bytes_checked(bytes)?;
                let point = ct::into_public(p256::Point::mul_base(&x));
                Ok(Self {
                    secret: Secret::P256 { x },
                    public: PublicKey(Public::P256 {
                        bytes: point.to_compressed(),
                        point,
                    }),
                })
            }
        }
    }

    /// Encodes the secret key as [`Self::from_bytes`] loads it.
    pub fn to_bytes(&self) -> SecretKeyBytes {
        SecretKeyBytes(match &self.secret {
            Secret::Edwards25519 { seed, .. } => *seed,
            Secret::P256 { x } => x.as_bytes(),
        })
    }

    /// Returns the public key that verifies this key's proofs.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Returns the key's algorithm.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.public.algorithm()
    }

    /// Proves the output for the input `alpha`, returning the proof to send
    /// to a verifier and the output it will recover.
    ///
    /// The time taken depends on `alpha`, as try-and-increment's loop does
    /// (RFC 9381 section 5.4.1.1), so a VRF whose input must stay secret from
    /// an observer of its timing needs another suite.
    pub fn prove(&self, alpha: &[u8]) -> (Proof, Output) {
        let _entry = Entry::new_secret();
        let mut proof = Proof {
            bytes: [0; Proof::MAX_LEN],
            len: 0,
        };
        let output = match (&self.secret, &self.public.0) {
            (Secret::Edwards25519 { x, prefix, .. }, Public::Edwards25519 { bytes, .. }) => {
                proof.len = EDWARDS25519_PROOF_LEN;
                let (h, h_string) = edwards25519_encode_to_curve(bytes, alpha)
                    .expect("each candidate decodes with a chance of about 1/2");
                let gamma_point = h.mul(x);
                let gamma = gamma_point.to_bytes();
                // RFC 9381 5.4.2.2's nonce, keyed by the seed's hash.
                let k = edwards25519::Scalar::from_uniform_bytes(&sha512(&[prefix, &h_string]));
                let u = edwards25519::Point::mul_base(&k).to_bytes();
                let v = h.mul(&k).to_bytes();
                let c = sha512(&[
                    &[EDWARDS25519_SUITE, CHALLENGE],
                    bytes,
                    &h_string,
                    &gamma,
                    &u,
                    &v,
                    &[0],
                ]);
                let c = &c[..CHALLENGE_LEN];
                let s = edwards25519_challenge(c).mul_add(x, &k);
                proof.bytes[..32].copy_from_slice(&gamma);
                proof.bytes[32..48].copy_from_slice(c);
                proof.bytes[48..80].copy_from_slice(&s.to_bytes());
                edwards25519_proof_to_hash(&gamma_point)
            }
            (Secret::P256 { x }, Public::P256 { bytes, .. }) => {
                proof.len = P256_PROOF_LEN;
                let (h, h_string) = p256_encode_to_curve(bytes, alpha)
                    .expect("each candidate decodes with a chance of about 1/2");
                let gamma = h.mul(x).to_compressed();
                let k = p256_nonce(x, &h_string);
                let u = p256::Point::mul_base(&k).to_compressed();
                let v = h.mul(&k).to_compressed();
                let c = sha256(&[
                    &[P256_SUITE, CHALLENGE],
                    bytes,
                    &h_string,
                    &gamma,
                    &u,
                    &v,
                    &[0],
                ]);
                let c = &c[..CHALLENGE_LEN];
                let s = p256::Scalar::from_bytes_reduced(c).unwrap().mul_add(x, &k);
                proof.bytes[..33].copy_from_slice(&gamma);
                proof.bytes[33..49].copy_from_slice(c);
                proof.bytes[49..81].copy_from_slice(&s.as_bytes());
                p256_proof_to_hash(&gamma)
            }
            _ => unreachable!("a key's halves share their algorithm"),
        };
        (ct::into_public(proof), ct::into_public(output))
    }
}

impl Drop for SecretKey {
    fn drop(&mut self) {
        // The public key is not secret, but a key type wipes its whole value.
        low::zeroise_value(self);
    }
}

impl fmt::Debug for SecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SecretKey")
            .field("algorithm", self.algorithm())
            .finish_non_exhaustive()
    }
}

/// An encoded secret key, wiped on drop under the `wipe` feature.
pub struct SecretKeyBytes([u8; 32]);

impl AsRef<[u8]> for SecretKeyBytes {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Drop for SecretKeyBytes {
    fn drop(&mut self) {
        low::zeroise(&mut self.0);
    }
}

impl fmt::Debug for SecretKeyBytes {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SecretKeyBytes").finish_non_exhaustive()
    }
}

/// A public key, which verifies proofs.
#[derive(Clone)]
pub struct PublicKey(Public);

// As `Secret`: all-bits-zero is a valid `Edwards25519` key.
#[derive(Clone)]
#[repr(u8)]
enum Public {
    Edwards25519 {
        bytes: [u8; 32],
        point: edwards25519::Point,
    },
    P256 {
        bytes: [u8; p256::Point::COMPRESSED_BYTES],
        point: p256::Point,
    },
}

impl low::Zeroable for Public {}

impl PublicKey {
    /// Parses an encoded public key for `algorithm`: Edwards25519's RFC 8032
    /// encoding, or P-256's X9.62 compressed point.
    ///
    /// It is validated as RFC 9381 section 5.4.5 requires: a key of small
    /// order, which would let one input have many outputs, is refused, along
    /// with a non-canonical encoding or one off the curve.
    pub fn new(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        Ok(Self(match algorithm.id {
            AlgorithmId::Edwards25519Sha512Tai => {
                let bytes: [u8; 32] = bytes.try_into().map_err(|_| KeyFormatError::WrongLength)?;
                if has_small_order(&bytes) {
                    return Err(KeyFormatError::SmallOrder.into());
                }
                let point =
                    edwards25519::Point::from_bytes(&bytes).ok_or(KeyFormatError::NotOnCurve)?;
                Public::Edwards25519 { bytes, point }
            }
            AlgorithmId::P256Sha256Tai => {
                let bytes: [u8; p256::Point::COMPRESSED_BYTES] =
                    bytes.try_into().map_err(|_| KeyFormatError::WrongLength)?;
                // No compressed point is at infinity, so this is all RFC 9381
                // 5.4.5 asks of P-256.
                let point =
                    p256::Point::from_compressed(&bytes).ok_or(KeyFormatError::NotOnCurve)?;
                Public::P256 { bytes, point }
            }
        }))
    }

    /// Returns the key's algorithm.
    pub fn algorithm(&self) -> &'static Algorithm {
        match self.0 {
            Public::Edwards25519 { .. } => &ECVRF_EDWARDS25519_SHA512_TAI,
            Public::P256 { .. } => &ECVRF_P256_SHA256_TAI,
        }
    }

    /// Verifies `proof` for the input `alpha`, returning the output the
    /// secret key proved.
    ///
    /// A proof that does not verify is refused with
    /// [`Error::BadSignature`].
    pub fn verify(&self, alpha: &[u8], proof: &[u8]) -> Result<Output, Error> {
        let _entry = Entry::new_public();
        match &self.0 {
            Public::Edwards25519 { bytes, point } => {
                let proof: &[u8; EDWARDS25519_PROOF_LEN] =
                    proof.try_into().map_err(|_| Error::BadSignature)?;
                let gamma = edwards25519::Point::from_bytes(proof[..32].try_into().unwrap())
                    .ok_or(Error::BadSignature)?;
                let c_bytes = &proof[32..48];
                let s = edwards25519::Scalar::from_canonical_bytes(proof[48..].try_into().unwrap())
                    .ok_or(Error::BadSignature)?;
                let (h, h_string) =
                    edwards25519_encode_to_curve(bytes, alpha).ok_or(Error::BadSignature)?;
                let c = edwards25519_challenge(c_bytes);
                // U = s * B - c * Y, and V = s * H - c * Gamma.
                let u = edwards25519::Point::mul_base(&s).add(&point.neg().mul(&c));
                let v = h.mul(&s).add(&gamma.neg().mul(&c));
                let want = sha512(&[
                    &[EDWARDS25519_SUITE, CHALLENGE],
                    bytes,
                    &h_string,
                    &proof[..32],
                    &u.to_bytes(),
                    &v.to_bytes(),
                    &[0],
                ]);
                match want[..CHALLENGE_LEN] == *c_bytes {
                    true => Ok(edwards25519_proof_to_hash(&gamma)),
                    false => Err(Error::BadSignature),
                }
            }
            Public::P256 { bytes, point } => {
                let proof: &[u8; P256_PROOF_LEN] =
                    proof.try_into().map_err(|_| Error::BadSignature)?;
                let gamma_string = &proof[..33];
                let gamma =
                    p256::Point::from_compressed(gamma_string).ok_or(Error::BadSignature)?;
                let c_bytes = &proof[33..49];
                let s = p256::Scalar::from_bytes_below_n(proof[49..].try_into().unwrap())
                    .ok_or(Error::BadSignature)?;
                let (h, h_string) =
                    p256_encode_to_curve(bytes, alpha).ok_or(Error::BadSignature)?;
                let minus_c = p256::Scalar::from_bytes_reduced(c_bytes)?.neg();
                // U = s * G - c * Y, and V = s * H - c * Gamma. No honest
                // proof has either at infinity, whose encoding is not ptLen
                // bytes, as the nonce is from 1 to n - 1.
                let u = point
                    .public_mul_base_add(&s, &minus_c)
                    .ok_or(Error::BadSignature)?;
                let v = p256::Point::public_mul_sum([(&h, &s), (&gamma, &minus_c)])
                    .ok_or(Error::BadSignature)?;
                let want = sha256(&[
                    &[P256_SUITE, CHALLENGE],
                    bytes,
                    &h_string,
                    gamma_string,
                    &u.to_compressed(),
                    &v.to_compressed(),
                    &[0],
                ]);
                match want[..CHALLENGE_LEN] == *c_bytes {
                    true => Ok(p256_proof_to_hash(gamma_string.try_into().unwrap())),
                    false => Err(Error::BadSignature),
                }
            }
        }
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        match &self.0 {
            Public::Edwards25519 { bytes, .. } => bytes,
            Public::P256 { bytes, .. } => bytes,
        }
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").field(&self.as_ref()).finish()
    }
}

/// A proof of an output, which [`PublicKey::verify`] checks.
#[derive(Clone)]
pub struct Proof {
    bytes: [u8; Self::MAX_LEN],
    len: usize,
}

impl Proof {
    const MAX_LEN: usize = P256_PROOF_LEN;
}

impl AsRef<[u8]> for Proof {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl fmt::Debug for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Proof").field(&self.as_ref()).finish()
    }
}

/// A VRF output: pseudorandom to anyone without the secret key, and the
/// same for every proof of one input.
#[derive(Clone)]
pub struct Output {
    bytes: [u8; Self::MAX_LEN],
    len: usize,
}

impl Output {
    const MAX_LEN: usize = Sha512Context::OUTPUT_SZ;
}

impl AsRef<[u8]> for Output {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl fmt::Debug for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Output").field(&self.as_ref()).finish()
    }
}

const EDWARDS25519_SUITE: u8 = 0x03;
const P256_SUITE: u8 = 0x01;

/// The front domain separators of RFC 9381's hashes; each ends with 0x00.
const ENCODE_TO_CURVE: u8 = 0x01;
const CHALLENGE: u8 = 0x02;
const PROOF_TO_HASH: u8 = 0x03;

/// `cLen`, for both suites.
const CHALLENGE_LEN: usize = 16;

/// `ptLen + cLen + qLen`.
const EDWARDS25519_PROOF_LEN: usize = 32 + CHALLENGE_LEN + 32;
const P256_PROOF_LEN: usize = p256::Point::COMPRESSED_BYTES + CHALLENGE_LEN + 32;

/// RFC 9381 5.4.1.1's try-and-increment, salted with the public key: `H`,
/// with its encoding, or `None` if no counter gives a point.
///
/// Each candidate decodes with a chance of about 1/2, so `None` has a chance
/// of about 2^-256: no input can be found that gives it.
fn edwards25519_encode_to_curve(
    public_key: &[u8; 32],
    alpha: &[u8],
) -> Option<(edwards25519::Point, [u8; 32])> {
    (0..=u8::MAX).find_map(|ctr| {
        let hash = sha512(&[
            &[EDWARDS25519_SUITE, ENCODE_TO_CURVE],
            public_key,
            alpha,
            &[ctr, 0],
        ]);
        let h = edwards25519::Point::from_bytes(hash[..32].try_into().unwrap())?;
        let h = h.mul_by_cofactor();
        let encoding = h.to_bytes();
        // A candidate of small order clears to the identity, which the loop
        // skips.
        (encoding != EDWARDS25519_IDENTITY).then_some((h, encoding))
    })
}

/// The identity's encoding, `y = 1`.
const EDWARDS25519_IDENTITY: [u8; 32] = {
    let mut one = [0u8; 32];
    one[0] = 1;
    one
};

/// The challenge `c`, from its `cLen` little-endian bytes.
fn edwards25519_challenge(c: &[u8]) -> edwards25519::Scalar {
    let mut bytes = [0u8; 32];
    bytes[..CHALLENGE_LEN].copy_from_slice(c);
    // Below 2^128, so below `L`.
    edwards25519::Scalar::from_canonical_bytes(&bytes).unwrap()
}

/// RFC 9381 5.2's output, from `Gamma`.
fn edwards25519_proof_to_hash(gamma: &edwards25519::Point) -> Output {
    let hash = sha512(&[
        &[EDWARDS25519_SUITE, PROOF_TO_HASH],
        &gamma.mul_by_cofactor().to_bytes(),
        &[0],
    ]);
    Output {
        bytes: hash,
        len: hash.len(),
    }
}

/// As [`edwards25519_encode_to_curve`], for P-256, whose candidates are a
/// compressed point's `x` with an even `y`.
fn p256_encode_to_curve(
    public_key: &[u8; p256::Point::COMPRESSED_BYTES],
    alpha: &[u8],
) -> Option<(p256::Point, [u8; p256::Point::COMPRESSED_BYTES])> {
    (0..=u8::MAX).find_map(|ctr| {
        let hash = sha256(&[&[P256_SUITE, ENCODE_TO_CURVE], public_key, alpha, &[ctr, 0]]);
        let mut encoding = [0x02; p256::Point::COMPRESSED_BYTES];
        encoding[1..].copy_from_slice(&hash);
        // The cofactor is 1, and no compressed point is at infinity.
        let h = p256::Point::from_compressed(&encoding)?;
        Some((h, encoding))
    })
}

/// RFC 9381 5.4.2.1's nonce: RFC 6979 section 3.2's, with `h_string` as the
/// message and no check that it suits ECDSA.
fn p256_nonce(x: &p256::Scalar, h_string: &[u8]) -> p256::Scalar {
    // `bits2octets(H(m))`: qlen and hlen are both 256 bits, so the hash is
    // only reduced.
    let h1 = p256::Scalar::from_bytes_reduced(&sha256(&[h_string]))
        .unwrap()
        .as_bytes();
    let mut drbg = HmacDrbg::<Sha256>::new(&x.as_bytes(), &h1, &[]);
    let mut candidate = [0u8; p256::Scalar::BYTES];
    loop {
        // Each draw regenerates as RFC 6979 3.2 h.3 does; HMAC-DRBG cannot
        // fail.
        drbg.fill(&mut candidate).unwrap();
        if let Ok(k) = p256::Scalar::from_bytes_checked(&candidate) {
            return k;
        }
    }
}

/// RFC 9381 5.2's output, from `Gamma`'s encoding: the cofactor is 1.
fn p256_proof_to_hash(gamma: &[u8; p256::Point::COMPRESSED_BYTES]) -> Output {
    let hash = sha256(&[&[P256_SUITE, PROOF_TO_HASH], gamma, &[0]]);
    let mut bytes = [0u8; Output::MAX_LEN];
    bytes[..hash.len()].copy_from_slice(&hash);
    Output {
        bytes,
        len: hash.len(),
    }
}

fn sha512(parts: &[&[u8]]) -> [u8; Sha512Context::OUTPUT_SZ] {
    let mut ctx = Sha512Context::new();
    for part in parts {
        ctx.update(part);
    }
    ctx.finish()
}

fn sha256(parts: &[&[u8]]) -> [u8; Sha256Context::OUTPUT_SZ] {
    let mut ctx = Sha256Context::new();
    for part in parts {
        ctx.update(part);
    }
    ctx.finish()
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    struct Vector {
        algorithm: &'static Algorithm,
        secret_key: &'static str,
        public_key: &'static str,
        alpha: &'static str,
        proof: &'static str,
        output: &'static str,
    }

    /// RFC 9381 Appendix B.1's examples 10 to 12, and B.3's 16 to 18.
    const VECTORS: [Vector; 6] = [
        Vector {
            algorithm: &ECVRF_P256_SHA256_TAI,
            secret_key: "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
            public_key: "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6",
            alpha: "73616d706c65",
            proof: "035b5c726e8c0e2c488a107c600578ee75cb702343c153cb1eb8dec77f4b5071b4a53f0a46f018bc2c56e58d383f2305e0975972c26feea0eb122fe7893c15af376b33edf7de17c6ea056d4d82de6bc02f",
            output: "a3ad7b0ef73d8fc6655053ea22f9bede8c743f08bbed3d38821f0e16474b505e",
        },
        Vector {
            algorithm: &ECVRF_P256_SHA256_TAI,
            secret_key: "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
            public_key: "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6",
            alpha: "74657374",
            proof: "034dac60aba508ba0c01aa9be80377ebd7562c4a52d74722e0abae7dc3080ddb56c19e067b15a8a8174905b13617804534214f935b94c2287f797e393eb0816969d864f37625b443f30f1a5a33f2b3c854",
            output: "a284f94ceec2ff4b3794629da7cbafa49121972671b466cab4ce170aa365f26d",
        },
        Vector {
            algorithm: &ECVRF_P256_SHA256_TAI,
            secret_key: "2ca1411a41b17b24cc8c3b089cfd033f1920202a6c0de8abb97df1498d50d2c8",
            public_key: "03596375e6ce57e0f20294fc46bdfcfd19a39f8161b58695b3ec5b3d16427c274d",
            alpha: "4578616d706c65207573696e67204543445341206b65792066726f6d20417070656e646978204c2e342e32206f6620414e53492e58392d36322d32303035",
            proof: "03d03398bf53aa23831d7d1b2937e005fb0062cbefa06796579f2a1fc7e7b8c667d091c00b0f5c3619d10ecea44363b5a599cadc5b2957e223fec62e81f7b4825fc799a771a3d7334b9186bdbee87316b1",
            output: "90871e06da5caa39a3c61578ebb844de8635e27ac0b13e829997d0d95dd98c19",
        },
        Vector {
            algorithm: &ECVRF_EDWARDS25519_SHA512_TAI,
            secret_key: "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
            public_key: "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
            alpha: "",
            proof: "8657106690b5526245a92b003bb079ccd1a92130477671f6fc01ad16f26f723f26f8a57ccaed74ee1b190bed1f479d9727d2d0f9b005a6e456a35d4fb0daab1268a1b0db10836d9826a528ca76567805",
            output: "90cf1df3b703cce59e2a35b925d411164068269d7b2d29f3301c03dd757876ff66b71dda49d2de59d03450451af026798e8f81cd2e333de5cdf4f3e140fdd8ae",
        },
        Vector {
            algorithm: &ECVRF_EDWARDS25519_SHA512_TAI,
            secret_key: "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
            public_key: "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
            alpha: "72",
            proof: "f3141cd382dc42909d19ec5110469e4feae18300e94f304590abdced48aed5933bf0864a62558b3ed7f2fea45c92a465301b3bbf5e3e54ddf2d935be3b67926da3ef39226bbc355bdc9850112c8f4b02",
            output: "eb4440665d3891d668e7e0fcaf587f1b4bd7fbfe99d0eb2211ccec90496310eb5e33821bc613efb94db5e5b54c70a848a0bef4553a41befc57663b56373a5031",
        },
        Vector {
            algorithm: &ECVRF_EDWARDS25519_SHA512_TAI,
            secret_key: "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
            public_key: "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
            alpha: "af82",
            proof: "9bc0f79119cc5604bf02d23b4caede71393cedfbb191434dd016d30177ccbf8096bb474e53895c362d8628ee9f9ea3c0e52c7a5c691b6c18c9979866568add7a2d41b00b05081ed0f58ee5e31b3a970e",
            output: "645427e5d00c62a23fb703732fa5d892940935942101e456ecca7bb217c61c452118fec1219202a0edcf038bb6373241578be7217ba85a2687f7a0310b2df19f",
        },
    ];

    fn h(hex: &str) -> Vec<u8> {
        hex::decode(hex).unwrap()
    }

    #[test]
    fn rfc9381_vectors() {
        for v in &VECTORS {
            let key = SecretKey::from_bytes(v.algorithm, &h(v.secret_key)).unwrap();
            // `to_bytes` is the secret key, still secret under ctgrind.
            assert_eq!(ct::into_public(key.to_bytes().0), &h(v.secret_key)[..]);
            assert_eq!(key.public_key().as_ref(), h(v.public_key));
            let (proof, output) = key.prove(&h(v.alpha));
            assert_eq!(proof.as_ref(), h(v.proof), "{}", v.proof);
            assert_eq!(output.as_ref(), h(v.output));

            let public_key = PublicKey::new(v.algorithm, &h(v.public_key)).unwrap();
            let verified = public_key.verify(&h(v.alpha), &h(v.proof)).unwrap();
            assert_eq!(verified.as_ref(), h(v.output));
        }
    }

    /// Every single-bit change to a proof, its input, or its key is refused.
    #[test]
    fn refuses_altered_proofs() {
        for v in &VECTORS {
            let public_key = PublicKey::new(v.algorithm, &h(v.public_key)).unwrap();
            let alpha = h(v.alpha);
            let proof = h(v.proof);
            for bit in 0..proof.len() * 8 {
                let mut altered = proof.clone();
                altered[bit / 8] ^= 1 << (bit % 8);
                assert!(public_key.verify(&alpha, &altered).is_err(), "bit {bit}");
            }
            assert!(
                public_key
                    .verify(&[&alpha[..], b"!"].concat(), &proof)
                    .is_err()
            );
            assert!(public_key.verify(&alpha, &proof[1..]).is_err());
            assert!(
                public_key
                    .verify(&alpha, &[&proof[..], &[0]].concat())
                    .is_err()
            );

            let other = SecretKey::generate(v.algorithm).unwrap();
            assert!(other.public_key().verify(&alpha, &proof).is_err());
        }
    }

    /// `s + L` is the same scalar, but a proof carrying it is refused, as
    /// RFC 9381 5.4.4 requires: no proof has a second encoding.
    #[test]
    fn refuses_unreduced_s() {
        let v = &VECTORS[3];
        let public_key = PublicKey::new(v.algorithm, &h(v.public_key)).unwrap();
        let mut proof = h(v.proof);
        let order = h("edd3f55c1a631258d69cf7a2def9de1400000000000000000000000000000010");
        let mut carry = 0u16;
        for (s, l) in proof[48..].iter_mut().zip(&order) {
            let sum = u16::from(*s) + u16::from(*l) + carry;
            *s = sum as u8;
            carry = sum >> 8;
        }
        assert_eq!(carry, 0);
        assert_eq!(
            public_key.verify(&h(v.alpha), &proof).unwrap_err(),
            Error::BadSignature
        );

        // P-256's s at n is refused too.
        let v = &VECTORS[0];
        let public_key = PublicKey::new(v.algorithm, &h(v.public_key)).unwrap();
        let mut proof = h(v.proof);
        proof[49..].copy_from_slice(&h(
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
        ));
        assert_eq!(
            public_key.verify(&h(v.alpha), &proof).unwrap_err(),
            Error::BadSignature
        );
    }

    /// RFC 9381 5.4.5's list of Edwards25519 keys `validate_key` refuses,
    /// along with keys that do not decode.
    #[test]
    fn refuses_bad_public_keys() {
        let p = "edffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f";
        let small_order = [
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0100000000000000000000000000000000000000000000000000000000000000",
            // `bad_y2` and `p - bad_y2`, of order 8.
            "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
            "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
            // `p - 1`, of order 2.
            "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        ];
        for y in small_order {
            for sign in [0, 0x80] {
                let mut key = h(y);
                key[31] |= sign;
                assert!(PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, &key).is_err());
            }
        }
        // `y = p`, non-canonical.
        assert!(PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, &h(p)).is_err());
        // `y = 2` has no point.
        let mut two = [0u8; 32];
        two[0] = 2;
        assert!(PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, &two).is_err());

        let p256 = h(VECTORS[0].public_key);
        assert!(PublicKey::new(&ECVRF_P256_SHA256_TAI, &p256[1..]).is_err());
        let mut uncompressed = [0x04; 65];
        uncompressed[1..33].copy_from_slice(&p256[1..]);
        assert!(PublicKey::new(&ECVRF_P256_SHA256_TAI, &uncompressed).is_err());
        let mut bad_tag = p256;
        bad_tag[0] = 0x04;
        assert!(PublicKey::new(&ECVRF_P256_SHA256_TAI, &bad_tag).is_err());
        // `x = p` is refused rather than reduced.
        let mut x_is_p = h("02ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
        assert!(PublicKey::new(&ECVRF_P256_SHA256_TAI, &x_is_p).is_err());
        x_is_p[0] = 0x03;
        assert!(PublicKey::new(&ECVRF_P256_SHA256_TAI, &x_is_p).is_err());
    }

    #[test]
    fn refuses_bad_secret_keys() {
        for algorithm in [&ECVRF_EDWARDS25519_SHA512_TAI, &ECVRF_P256_SHA256_TAI] {
            assert!(SecretKey::from_bytes(algorithm, &[1; 31]).is_err());
            assert!(SecretKey::from_bytes(algorithm, &[1; 33]).is_err());
        }
        // P-256 refuses 0 and n.
        assert!(SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &[0; 32]).is_err());
        let n = h("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
        assert!(SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &n).is_err());
    }

    #[test]
    fn generated_keys_round_trip() {
        for algorithm in [&ECVRF_EDWARDS25519_SHA512_TAI, &ECVRF_P256_SHA256_TAI] {
            let key = SecretKey::generate(algorithm).unwrap();
            assert_eq!(key.algorithm(), algorithm);
            let loaded = SecretKey::from_bytes(algorithm, key.to_bytes().as_ref()).unwrap();
            assert_eq!(loaded.public_key().as_ref(), key.public_key().as_ref());
            let public_key = PublicKey::new(algorithm, key.public_key().as_ref()).unwrap();
            assert_eq!(public_key.algorithm(), algorithm);
            let (proof, output) = key.prove(b"input");
            let verified = public_key.verify(b"input", proof.as_ref()).unwrap();
            assert_eq!(verified.as_ref(), output.as_ref());
        }
    }

    /// Under `admin/ctgrind`, memcheck fails this if loading a key or
    /// proving branches on or indexes by the secret key or the nonce.
    #[test]
    fn stays_secret() {
        for v in &VECTORS {
            let secret = h(v.secret_key);
            ct::secret_slice(&secret);
            let key = SecretKey::from_bytes(v.algorithm, &secret).unwrap();
            let (proof, output) = key.prove(&h(v.alpha));
            assert_eq!(proof.as_ref(), h(v.proof));
            assert_eq!(output.as_ref(), h(v.output));
        }
    }
}
