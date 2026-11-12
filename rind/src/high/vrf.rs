// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ECVRF-EDWARDS25519-SHA512-TAI and ECVRF-P256-SHA256-TAI (RFC 9381).
//!
//! The group operations are rind's. On x86_64 and aarch64 the Edwards
//! products are [`crate::mid::edwards25519`]'s, over s2n-bignum's field and
//! point routines. On armv7 and the portable backend they are
//! curve25519-dalek's, as Ed25519's are. P-256 uses the same arithmetic as
//! ECDH. Try-and-increment, which hashes the input onto the curve, is the
//! one step whose running time depends on that input.

use core::fmt;

use crate::error::{Error, KeyFormatError};
use crate::high::hash::Sha256;
use crate::high::hmac::HmacKey;
use crate::low::{Entry, Zeroable, ZeroableRef, ct, zeroise_value};
use crate::mid::edwards25519::{Point as EdPoint, Scalar as EdScalar};
use crate::mid::p256::group::{self, Point as P256Point};
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::sha2::{Sha256Context, Sha512Context};

const ED_SUITE: u8 = 0x03;
const P256_SUITE: u8 = 0x01;
const ED_PROOF_LEN: usize = 80;
const P256_PROOF_LEN: usize = 81;
const ED_OUTPUT_LEN: usize = 64;
const P256_OUTPUT_LEN: usize = 32;
const ED_PUBLIC_LEN: usize = 32;
const P256_PUBLIC_LEN: usize = 33;
const SECRET_LEN: usize = 32;
const CHALLENGE_LEN: usize = 16;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Suite {
    Edwards,
    P256,
}

/// An ECVRF ciphersuite from RFC 9381.
///
/// [`ECVRF_EDWARDS25519_SHA512_TAI`] and [`ECVRF_P256_SHA256_TAI`] are the two
/// suites key transparency uses. The ELL2 and SSWU suites are a different
/// hash to curve, and rind does not implement them.
pub struct Algorithm {
    suite: Suite,
}

impl PartialEq for Algorithm {
    fn eq(&self, other: &Self) -> bool {
        self.suite == other.suite
    }
}

impl Eq for Algorithm {}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl Algorithm {
    const fn name(&self) -> &'static str {
        match self.suite {
            Suite::Edwards => "ECVRF-EDWARDS25519-SHA512-TAI",
            Suite::P256 => "ECVRF-P256-SHA256-TAI",
        }
    }

    /// The length of a secret key, 32 bytes for either suite.
    pub const fn secret_key_len(&self) -> usize {
        SECRET_LEN
    }

    /// The length of a compressed public key.
    pub const fn public_key_len(&self) -> usize {
        match self.suite {
            Suite::Edwards => ED_PUBLIC_LEN,
            Suite::P256 => P256_PUBLIC_LEN,
        }
    }

    /// The length of a proof.
    pub const fn proof_len(&self) -> usize {
        match self.suite {
            Suite::Edwards => ED_PROOF_LEN,
            Suite::P256 => P256_PROOF_LEN,
        }
    }

    /// The length of a VRF output.
    pub const fn output_len(&self) -> usize {
        match self.suite {
            Suite::Edwards => ED_OUTPUT_LEN,
            Suite::P256 => P256_OUTPUT_LEN,
        }
    }
}

/// ECVRF-EDWARDS25519-SHA512-TAI (RFC 9381).
///
/// Secret keys are 32-byte seeds, expanded as Ed25519 expands them. Public
/// keys and proof points are 32-byte Edwards encodings. The output is 64
/// bytes.
pub static ECVRF_EDWARDS25519_SHA512_TAI: Algorithm = Algorithm {
    suite: Suite::Edwards,
};

/// ECVRF-P256-SHA256-TAI (RFC 9381).
///
/// A secret key is the scalar itself, an integer in `[1, n)`. Public keys
/// and proof points are 33-byte SEC1 compressed points. The output is 32
/// bytes.
pub static ECVRF_P256_SHA256_TAI: Algorithm = Algorithm { suite: Suite::P256 };

/// An ECVRF proof.
///
/// [`PublicKey::verify`] is the only way to recover the output a proof
/// claims. A proof from another suite does not verify under this one.
#[derive(Clone, Copy)]
pub struct Proof {
    algorithm: &'static Algorithm,
    bytes: [u8; P256_PROOF_LEN],
    len: u8,
}

impl Proof {
    /// Copies `bytes` when they are this suite's [`Algorithm::proof_len`].
    ///
    /// The point and the scalar are checked by [`PublicKey::verify`]. A
    /// different length fails with [`Error::BadSignature`].
    pub fn from_bytes(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        Self::from_bytes_inner(algorithm, bytes)
    }

    fn from_bytes_inner(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != algorithm.proof_len() {
            return Err(Error::BadSignature);
        }
        let mut stored = [0u8; P256_PROOF_LEN];
        stored[..bytes.len()].copy_from_slice(bytes);
        Ok(Self {
            algorithm,
            bytes: stored,
            len: bytes.len() as u8,
        })
    }

    fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }
}

impl AsRef<[u8]> for Proof {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl PartialEq for Proof {
    fn eq(&self, other: &Self) -> bool {
        self.algorithm == other.algorithm && self.as_ref() == other.as_ref()
    }
}

impl Eq for Proof {}

impl fmt::Debug for Proof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Proof")
            .field("algorithm", &self.algorithm)
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// The VRF output.
///
/// Proving returns it next to the proof. Verifying returns it only after the
/// proof checks, so a caller cannot treat an output it did not check as real.
#[derive(Clone, Copy)]
pub struct Output {
    algorithm: &'static Algorithm,
    bytes: [u8; ED_OUTPUT_LEN],
    len: u8,
}

impl Output {
    fn new(algorithm: &'static Algorithm, bytes: &[u8]) -> Self {
        let mut stored = [0u8; ED_OUTPUT_LEN];
        stored[..bytes.len()].copy_from_slice(bytes);
        Self {
            algorithm,
            bytes: stored,
            len: bytes.len() as u8,
        }
    }
}

impl AsRef<[u8]> for Output {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl PartialEq for Output {
    fn eq(&self, other: &Self) -> bool {
        self.algorithm == other.algorithm && self.as_ref() == other.as_ref()
    }
}

impl Eq for Output {}

impl fmt::Debug for Output {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Output")
            .field("algorithm", &self.algorithm)
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// An ECVRF public key, validated as RFC 9381 section 5.4.5 requires.
///
/// An Edwards key is a curve point whose order does not divide 8. A P-256
/// key is a compressed point on the curve, which is enough: the cofactor is
/// 1, so the check is that the point is not the identity, and the compressed
/// encoding has no identity.
#[derive(Clone, Copy)]
pub struct PublicKey {
    algorithm: &'static Algorithm,
    bytes: [u8; P256_PUBLIC_LEN],
    len: u8,
}

impl PublicKey {
    /// Parses `bytes` as this suite's public key.
    ///
    /// Fails with [`Error::KeyRejected`] when the length is wrong, the
    /// encoding is not a point, or the point fails section 5.4.5.
    pub fn from_bytes(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        Self::from_bytes_inner(algorithm, bytes)
    }

    fn from_bytes_inner(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        Entry::assert_held();
        if bytes.len() != algorithm.public_key_len() {
            return Err(KeyFormatError::WrongLength.into());
        }
        match algorithm.suite {
            Suite::Edwards => {
                let encoded: [u8; 32] = bytes.try_into().unwrap();
                let point = EdPoint::from_bytes(&encoded).ok_or(KeyFormatError::NotOnCurve)?;
                if point.mul_cofactor().is_identity() {
                    return Err(KeyFormatError::SmallOrder.into());
                }
            }
            Suite::P256 => {
                // Decoding rejects off-curve points and the identity, which
                // is the whole of section 5.4.5 when the cofactor is 1.
                P256Point::from_compressed(bytes)?;
            }
        }
        let mut stored = [0u8; P256_PUBLIC_LEN];
        stored[..bytes.len()].copy_from_slice(bytes);
        Ok(Self {
            algorithm,
            bytes: stored,
            len: bytes.len() as u8,
        })
    }

    /// The suite this key verifies.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// Checks `proof` of `alpha` and returns the output.
    ///
    /// Fails with [`Error::BadSignature`] when the proof is the wrong length
    /// or does not check, and with [`Error::Unsupported`] when it was built
    /// for another suite. `alpha` is public here, as it is in a proof: see
    /// [`SecretKey::prove`].
    pub fn verify(&self, alpha: &[u8], proof: &Proof) -> Result<Output, Error> {
        let _entry = Entry::new_public();
        if proof.algorithm() != self.algorithm {
            return Err(Error::Unsupported);
        }
        let pi = proof.as_ref();
        if pi.len() != self.algorithm.proof_len() {
            return Err(Error::BadSignature);
        }
        match self.algorithm.suite {
            Suite::Edwards => Ok(Output::new(
                self.algorithm,
                &verify_edwards(self.as_ref(), alpha, pi)?,
            )),
            Suite::P256 => Ok(Output::new(
                self.algorithm,
                &verify_p256(self.as_ref(), alpha, pi)?,
            )),
        }
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("algorithm", &self.algorithm)
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// An ECVRF secret key, wiped on drop under the `wipe` feature.
///
/// The whole value is the 32-byte seed. Edwards expands it like Ed25519.
/// P-256 uses it as the scalar.
#[repr(C)]
pub struct SecretKey {
    algorithm: ZeroableRef<Algorithm>,
    seed: [u8; SECRET_LEN],
}

impl SecretKey {
    /// Generates a key with the system RNG.
    ///
    /// An Edwards seed is 32 uniform bytes. A P-256 scalar is rejected and
    /// drawn again until it lies in `[1, n)`, at most 64 times.
    pub fn generate(algorithm: &'static Algorithm) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let mut rng = SystemRandom;
        for _ in 0..64 {
            let mut seed = [0u8; SECRET_LEN];
            rng.fill(&mut seed)?;
            ct::secret_slice(&seed);
            if let Ok(key) = Self::from_seed(algorithm, &seed) {
                return Ok(key);
            }
        }
        Err(Error::RngFailed)
    }

    /// Loads a 32-byte key.
    ///
    /// Every Edwards seed is a key. A P-256 seed fails with
    /// [`Error::KeyRejected`] unless it is an integer in `[1, n)`. Any other
    /// length fails the same way.
    pub fn from_bytes(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        let seed: [u8; SECRET_LEN] = bytes.try_into().map_err(|_| KeyFormatError::WrongLength)?;
        ct::secret_slice(&seed);
        Self::from_seed(algorithm, &seed)
    }

    fn from_seed(algorithm: &'static Algorithm, seed: &[u8; SECRET_LEN]) -> Result<Self, Error> {
        if algorithm.suite == Suite::P256 {
            // The in-range bit is public. The scalar stays secret.
            group::scalar_checked(seed)?;
        }
        Ok(Self {
            algorithm: ZeroableRef::new(algorithm),
            seed: *seed,
        })
    }

    /// The suite this key proves with.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm.get()
    }

    /// The 32-byte seed. It is still secret.
    pub fn to_bytes(&self) -> [u8; SECRET_LEN] {
        let _entry = Entry::new_secret();
        self.seed
    }

    /// The public key, validated by construction.
    pub fn public_key(&self) -> PublicKey {
        let _entry = Entry::new_secret();
        let bytes = match self.algorithm().suite {
            Suite::Edwards => {
                let scalar = edwards_scalar(&self.seed);
                let mut bytes = [0u8; P256_PUBLIC_LEN];
                bytes[..ED_PUBLIC_LEN].copy_from_slice(&EdPoint::mul_base(&scalar).to_bytes());
                bytes
            }
            Suite::P256 => {
                let scalar = group::scalar_checked(&self.seed).expect("checked at load");
                let point = P256Point::mul_base(&scalar);
                point
                    .to_compressed()
                    .expect("a scalar in range has a point")
            }
        };
        // The encoding is the public key a peer is given.
        let len = self.algorithm().public_key_len();
        ct::public_slice(&bytes[..len]);
        PublicKey::from_bytes_inner(self.algorithm(), &bytes[..len])
            .expect("a generated public key validates")
    }

    /// Proves `alpha`, returning the proof and its output.
    ///
    /// The running time depends on `alpha`. Try-and-increment hashes `alpha`
    /// onto the curve by testing candidates until one lands on the curve, so
    /// a secret `alpha` leaks through how long proving takes. RFC 9381
    /// section 5.4.1.1 says not to use this hash when the input must stay
    /// secret, and section 7.6 says a proof hides nothing about its input
    /// anyway. The secret key does not affect the number of candidates or any
    /// other branch.
    ///
    /// Fails with [`Error::Fault`] only when no candidate in the 256 the
    /// counter can name is a point, which is not a key or an input a caller
    /// can fix.
    pub fn prove(&self, alpha: &[u8]) -> Result<(Proof, Output), Error> {
        let _entry = Entry::new_secret();
        match self.algorithm().suite {
            Suite::Edwards => {
                let (proof, output) = prove_edwards(&self.seed, alpha)?;
                ct::public_slice(&proof);
                ct::public_slice(&output);
                Ok((
                    Proof::from_bytes_inner(self.algorithm(), &proof)?,
                    Output::new(self.algorithm(), &output),
                ))
            }
            Suite::P256 => {
                let (proof, output) = prove_p256(&self.seed, alpha)?;
                ct::public_slice(&proof);
                ct::public_slice(&output);
                Ok((
                    Proof::from_bytes_inner(self.algorithm(), &proof)?,
                    Output::new(self.algorithm(), &output),
                ))
            }
        }
    }
}

impl Clone for SecretKey {
    fn clone(&self) -> Self {
        Self {
            algorithm: self.algorithm,
            seed: self.seed,
        }
    }
}

impl Drop for SecretKey {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for SecretKey {}

impl fmt::Debug for SecretKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SecretKey")
            .field("algorithm", &self.algorithm())
            .finish_non_exhaustive()
    }
}

fn prove_edwards(
    seed: &[u8; 32],
    alpha: &[u8],
) -> Result<([u8; ED_PROOF_LEN], [u8; ED_OUTPUT_LEN]), Error> {
    let (scalar, prefix) = edwards_expanded(seed);
    let public = EdPoint::mul_base(&scalar).to_bytes();
    ct::public_slice(&public);
    let hashed = hash_to_curve_edwards(&public, alpha)?;
    let h_bytes = hashed.to_bytes();
    ct::public_slice(&h_bytes);
    let gamma = hashed.mul(&scalar);
    let nonce = edwards_nonce(&prefix, &h_bytes);
    let u = EdPoint::mul_base(&nonce);
    let v = hashed.mul(&nonce);
    let y = EdPoint::from_bytes(&public).ok_or(Error::Fault)?;
    let challenge = challenge_edwards(&[y, hashed, gamma, u, v]);
    let c_scalar = ed_scalar_short(&challenge)?;
    let s = nonce.add(&c_scalar.mul(&scalar));
    let mut proof = [0u8; ED_PROOF_LEN];
    proof[..32].copy_from_slice(&gamma.to_bytes());
    proof[32..48].copy_from_slice(&challenge);
    proof[48..].copy_from_slice(&s.to_bytes());
    Ok((proof, output_edwards(&gamma)))
}

fn verify_edwards(public: &[u8], alpha: &[u8], proof: &[u8]) -> Result<[u8; ED_OUTPUT_LEN], Error> {
    let pk: [u8; 32] = public.try_into().unwrap();
    let y = EdPoint::from_bytes(&pk).ok_or(Error::BadSignature)?;
    let gamma_bytes: [u8; 32] = proof[..32].try_into().unwrap();
    let gamma = EdPoint::from_bytes(&gamma_bytes).ok_or(Error::BadSignature)?;
    let challenge: [u8; 16] = proof[32..48].try_into().unwrap();
    let s_bytes: [u8; 32] = proof[48..].try_into().unwrap();
    let s = EdScalar::from_canonical_bytes(&s_bytes).ok_or(Error::BadSignature)?;
    let c_scalar = ed_scalar_short(&challenge)?;
    // Exhausting the counter is a bad proof, not an internal fault.
    let hashed = hash_to_curve_edwards(&pk, alpha).map_err(|_| Error::BadSignature)?;
    // The identity encodes, so a nonce of zero still has a challenge point.
    let u = EdPoint::mul_base(&s).add(&y.mul(&c_scalar).negate());
    let v = hashed.mul(&s).add(&gamma.mul(&c_scalar).negate());
    let challenge_prime = challenge_edwards(&[y, hashed, gamma, u, v]);
    if challenge_prime != challenge {
        return Err(Error::BadSignature);
    }
    Ok(output_edwards(&gamma))
}

fn prove_p256(
    seed: &[u8; 32],
    alpha: &[u8],
) -> Result<([u8; P256_PROOF_LEN], [u8; P256_OUTPUT_LEN]), Error> {
    let scalar = group::scalar_checked(seed).expect("checked at load");
    let public = P256Point::mul_base(&scalar)
        .to_compressed()
        .ok_or(Error::Fault)?;
    ct::public_slice(&public);
    let hashed = hash_to_curve_p256(&public, alpha)?;
    let h_bytes = hashed.to_compressed().ok_or(Error::Fault)?;
    ct::public_slice(&h_bytes);
    let gamma = hashed.mul(&scalar);
    let gamma_bytes = gamma.to_compressed().ok_or(Error::Fault)?;
    let nonce = p256_nonce(&group::scalar_bytes(&scalar), &h_bytes)?;
    let u = P256Point::mul_base(&nonce);
    let v = hashed.mul(&nonce);
    let u_bytes = u.to_compressed().ok_or(Error::Fault)?;
    let v_bytes = v.to_compressed().ok_or(Error::Fault)?;
    let challenge = challenge_p256(&[&public, &h_bytes, &gamma_bytes, &u_bytes, &v_bytes]);
    let c_scalar = group::scalar_reduced(&challenge)?;
    let s = group::scalar_add(&nonce, &group::scalar_mul(&c_scalar, &scalar));
    let mut proof = [0u8; P256_PROOF_LEN];
    proof[..33].copy_from_slice(&gamma_bytes);
    proof[33..49].copy_from_slice(&challenge);
    proof[49..].copy_from_slice(&group::scalar_bytes(&s));
    Ok((proof, output_p256(&gamma_bytes)))
}

fn verify_p256(public: &[u8], alpha: &[u8], proof: &[u8]) -> Result<[u8; P256_OUTPUT_LEN], Error> {
    let y = P256Point::from_compressed(public).map_err(|_| Error::BadSignature)?;
    let gamma = P256Point::from_compressed(&proof[..33]).map_err(|_| Error::BadSignature)?;
    let gamma_bytes: [u8; 33] = proof[..33].try_into().unwrap();
    let challenge: [u8; 16] = proof[33..49].try_into().unwrap();
    // `s` may be zero. A value at or above `n` is not canonical.
    let s = group::scalar_canonical(&proof[49..])?;
    let c_scalar = group::scalar_reduced(&challenge)?;
    let hashed = hash_to_curve_p256(public, alpha).map_err(|_| Error::BadSignature)?;
    let u = P256Point::mul_base_public(&s).add_public(y.mul_public(&c_scalar).negate());
    let v = hashed
        .mul_public(&s)
        .add_public(gamma.mul_public(&c_scalar).negate());
    let (Some(u_bytes), Some(v_bytes)) = (u.to_compressed(), v.to_compressed()) else {
        return Err(Error::BadSignature);
    };
    let h_bytes = hashed.to_compressed().ok_or(Error::BadSignature)?;
    let challenge_prime = challenge_p256(&[public, &h_bytes, &gamma_bytes, &u_bytes, &v_bytes]);
    if challenge_prime != challenge {
        return Err(Error::BadSignature);
    }
    Ok(output_p256(&gamma_bytes))
}

fn edwards_expanded(seed: &[u8; 32]) -> (EdScalar, [u8; 32]) {
    let hash = sha512(&[seed]);
    let mut prefix = [0u8; 32];
    prefix.copy_from_slice(&hash[32..]);
    let mut clamped = [0u8; 32];
    clamped.copy_from_slice(&hash[..32]);
    clamped[0] &= 0xf8;
    clamped[31] &= 0x7f;
    clamped[31] |= 0x40;
    let mut wide = [0u8; 64];
    wide[..32].copy_from_slice(&clamped);
    (EdScalar::from_uniform_bytes(&wide), prefix)
}

fn edwards_scalar(seed: &[u8; 32]) -> EdScalar {
    edwards_expanded(seed).0
}

fn edwards_nonce(prefix: &[u8; 32], h_bytes: &[u8]) -> EdScalar {
    let wide = sha512(&[prefix, h_bytes]);
    EdScalar::from_uniform_bytes(&wide)
}

fn ed_scalar_short(bytes: &[u8]) -> Result<EdScalar, Error> {
    let mut wide = [0u8; 32];
    wide[..bytes.len()].copy_from_slice(bytes);
    EdScalar::from_canonical_bytes(&wide).ok_or(Error::Fault)
}

fn hash_to_curve_edwards(public: &[u8], alpha: &[u8]) -> Result<EdPoint, Error> {
    // The prefix is the same for every counter. Verify hashes a public input
    // that may be long, so each try clones that prefix instead of hashing it
    // again. Proving uses the same function; the prefix holds no secret.
    let mut prefix = Sha512Context::new();
    prefix.update(&[ED_SUITE, 0x01]);
    prefix.update(public);
    prefix.update(alpha);
    for ctr in 0..=255u8 {
        let mut ctx = prefix.clone();
        ctx.update(&[ctr, 0x00]);
        let hash = ctx.finish();
        let mut candidate = [0u8; 32];
        candidate.copy_from_slice(&hash[..32]);
        if let Some(point) = EdPoint::from_bytes(&candidate) {
            let cleared = point.mul_cofactor();
            if !cleared.is_identity() {
                return Ok(cleared);
            }
        }
    }
    Err(Error::Fault)
}

fn challenge_edwards(points: &[EdPoint; 5]) -> [u8; CHALLENGE_LEN] {
    let mut ctx = Sha512Context::new();
    ctx.update(&[ED_SUITE, 0x02]);
    for point in points {
        ctx.update(&point.to_bytes());
    }
    ctx.update(&[0x00]);
    let hash = ctx.finish();
    let mut challenge = [0u8; CHALLENGE_LEN];
    challenge.copy_from_slice(&hash[..CHALLENGE_LEN]);
    challenge
}

fn output_edwards(gamma: &EdPoint) -> [u8; ED_OUTPUT_LEN] {
    let cleared = gamma.mul_cofactor().to_bytes();
    sha512(&[&[ED_SUITE, 0x03], &cleared, &[0x00]])
}

fn hash_to_curve_p256(public: &[u8], alpha: &[u8]) -> Result<P256Point, Error> {
    for ctr in 0..=255u8 {
        let hash = sha256(&[&[P256_SUITE, 0x01], public, alpha, &[ctr, 0x00]]);
        let mut encoded = [0u8; 33];
        encoded[0] = 0x02;
        encoded[1..].copy_from_slice(&hash);
        if let Ok(point) = P256Point::from_compressed(&encoded) {
            return Ok(point);
        }
    }
    Err(Error::Fault)
}

fn challenge_p256(points: &[&[u8]; 5]) -> [u8; CHALLENGE_LEN] {
    let mut ctx = Sha256Context::new();
    ctx.update(&[P256_SUITE, 0x02]);
    for point in points {
        ctx.update(point);
    }
    ctx.update(&[0x00]);
    let hash = ctx.finish();
    let mut challenge = [0u8; CHALLENGE_LEN];
    challenge.copy_from_slice(&hash[..CHALLENGE_LEN]);
    challenge
}

fn output_p256(gamma: &[u8]) -> [u8; P256_OUTPUT_LEN] {
    sha256(&[&[P256_SUITE, 0x03], gamma, &[0x00]])
}

/// RFC 6979's nonce, without the ECDSA check that `k * G` has a nonzero `x`.
///
/// A candidate outside `[1, n)` is refused and the generator steps. Whether
/// it was in range is public, as a rejected ECDSA nonce's is, and says
/// nothing about the candidate that is kept. The loop is capped: past 64
/// refusals is a fault, not a key a caller can fix.
fn p256_nonce(x: &[u8; 32], h_string: &[u8]) -> Result<group::Scalar, Error> {
    let h1 = sha256(&[h_string]);
    let h1_octets = group::scalar_bytes(&group::scalar_reduced(&h1)?);
    let mut v = [0x01u8; 32];
    let mut k = [0x00u8; 32];
    k = hmac_sha256(&k, &[&v, &[0x00], x, &h1_octets]);
    v = hmac_sha256(&k, &[&v]);
    k = hmac_sha256(&k, &[&v, &[0x01], x, &h1_octets]);
    v = hmac_sha256(&k, &[&v]);
    for _ in 0..64 {
        v = hmac_sha256(&k, &[&v]);
        if let Ok(nonce) = group::scalar_checked(&v) {
            return Ok(nonce);
        }
        k = hmac_sha256(&k, &[&v, &[0x00]]);
        v = hmac_sha256(&k, &[&v]);
    }
    Err(Error::Fault)
}

fn hmac_sha256(key: &[u8], parts: &[&[u8]]) -> [u8; 32] {
    let mut ctx = HmacKey::<Sha256>::new(key).start();
    for part in parts {
        ctx.update(part);
    }
    let tag = ctx.finish();
    let mut out = [0u8; 32];
    out.copy_from_slice(tag.as_ref());
    out
}

fn sha512(parts: &[&[u8]]) -> [u8; 64] {
    let mut ctx = Sha512Context::new();
    for part in parts {
        ctx.update(part);
    }
    ctx.finish()
}

fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut ctx = Sha256Context::new();
    for part in parts {
        ctx.update(part);
    }
    ctx.finish()
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::*;

    fn decode(hex_text: &str) -> Vec<u8> {
        hex::decode(hex_text).unwrap()
    }

    struct Vector {
        algorithm: &'static Algorithm,
        seed: &'static str,
        public: &'static str,
        alpha: &'static [u8],
        proof: &'static str,
        output: &'static str,
    }

    fn rfc9381(vector: &Vector) {
        let seed = decode(vector.seed);
        let key = SecretKey::from_bytes(vector.algorithm, &seed).unwrap();
        assert_eq!(hex::encode(key.public_key().as_ref()), vector.public);
        let (proof, output) = key.prove(vector.alpha).unwrap();
        assert_eq!(hex::encode(proof.as_ref()), vector.proof);
        assert_eq!(hex::encode(output.as_ref()), vector.output);
        let parsed = PublicKey::from_bytes(vector.algorithm, &decode(vector.public)).unwrap();
        let checked = parsed
            .verify(
                vector.alpha,
                &Proof::from_bytes(vector.algorithm, &decode(vector.proof)).unwrap(),
            )
            .unwrap();
        assert_eq!(checked.as_ref(), output.as_ref());
    }

    #[test]
    fn rfc9381_edwards() {
        let vectors = [
            Vector {
                algorithm: &ECVRF_EDWARDS25519_SHA512_TAI,
                seed: "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
                public: "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
                alpha: b"",
                proof: "8657106690b5526245a92b003bb079ccd1a92130477671f6fc01ad16f26f723f26f8a57ccaed74ee1b190bed1f479d9727d2d0f9b005a6e456a35d4fb0daab1268a1b0db10836d9826a528ca76567805",
                output: "90cf1df3b703cce59e2a35b925d411164068269d7b2d29f3301c03dd757876ff66b71dda49d2de59d03450451af026798e8f81cd2e333de5cdf4f3e140fdd8ae",
            },
            Vector {
                algorithm: &ECVRF_EDWARDS25519_SHA512_TAI,
                seed: "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
                public: "3d4017c3e843895a92b70aa74d1b7ebc9c982ccf2ec4968cc0cd55f12af4660c",
                alpha: b"\x72",
                proof: "f3141cd382dc42909d19ec5110469e4feae18300e94f304590abdced48aed5933bf0864a62558b3ed7f2fea45c92a465301b3bbf5e3e54ddf2d935be3b67926da3ef39226bbc355bdc9850112c8f4b02",
                output: "eb4440665d3891d668e7e0fcaf587f1b4bd7fbfe99d0eb2211ccec90496310eb5e33821bc613efb94db5e5b54c70a848a0bef4553a41befc57663b56373a5031",
            },
            Vector {
                algorithm: &ECVRF_EDWARDS25519_SHA512_TAI,
                seed: "c5aa8df43f9f837bedb7442f31dcb7b166d38535076f094b85ce3a2e0b4458f7",
                public: "fc51cd8e6218a1a38da47ed00230f0580816ed13ba3303ac5deb911548908025",
                alpha: b"\xaf\x82",
                proof: "9bc0f79119cc5604bf02d23b4caede71393cedfbb191434dd016d30177ccbf8096bb474e53895c362d8628ee9f9ea3c0e52c7a5c691b6c18c9979866568add7a2d41b00b05081ed0f58ee5e31b3a970e",
                output: "645427e5d00c62a23fb703732fa5d892940935942101e456ecca7bb217c61c452118fec1219202a0edcf038bb6373241578be7217ba85a2687f7a0310b2df19f",
            },
        ];
        for vector in vectors {
            rfc9381(&vector);
        }
    }

    #[test]
    fn rfc9381_p256() {
        let long = b"Example using ECDSA key from Appendix L.4.2 of ANSI.X9-62-2005";
        let vectors = [
            Vector {
                algorithm: &ECVRF_P256_SHA256_TAI,
                seed: "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
                public: "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6",
                alpha: b"sample",
                proof: "035b5c726e8c0e2c488a107c600578ee75cb702343c153cb1eb8dec77f4b5071b4a53f0a46f018bc2c56e58d383f2305e0975972c26feea0eb122fe7893c15af376b33edf7de17c6ea056d4d82de6bc02f",
                output: "a3ad7b0ef73d8fc6655053ea22f9bede8c743f08bbed3d38821f0e16474b505e",
            },
            Vector {
                algorithm: &ECVRF_P256_SHA256_TAI,
                seed: "c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721",
                public: "0360fed4ba255a9d31c961eb74c6356d68c049b8923b61fa6ce669622e60f29fb6",
                alpha: b"test",
                proof: "034dac60aba508ba0c01aa9be80377ebd7562c4a52d74722e0abae7dc3080ddb56c19e067b15a8a8174905b13617804534214f935b94c2287f797e393eb0816969d864f37625b443f30f1a5a33f2b3c854",
                output: "a284f94ceec2ff4b3794629da7cbafa49121972671b466cab4ce170aa365f26d",
            },
            Vector {
                algorithm: &ECVRF_P256_SHA256_TAI,
                seed: "2ca1411a41b17b24cc8c3b089cfd033f1920202a6c0de8abb97df1498d50d2c8",
                public: "03596375e6ce57e0f20294fc46bdfcfd19a39f8161b58695b3ec5b3d16427c274d",
                alpha: long,
                proof: "03d03398bf53aa23831d7d1b2937e005fb0062cbefa06796579f2a1fc7e7b8c667d091c00b0f5c3619d10ecea44363b5a599cadc5b2957e223fec62e81f7b4825fc799a771a3d7334b9186bdbee87316b1",
                output: "90871e06da5caa39a3c61578ebb844de8635e27ac0b13e829997d0d95dd98c19",
            },
        ];
        for vector in vectors {
            rfc9381(&vector);
        }
    }

    fn rejected_because(err: Error, reason: &str) {
        let Error::KeyRejected(rejected) = err else {
            panic!("expected a rejected key, got {err:?}");
        };
        assert!(rejected.to_string().contains(reason), "{rejected}");
    }

    fn not_on_curve(err: Error) {
        rejected_because(err, "not on the curve");
    }

    fn small_order(err: Error) {
        rejected_because(err, "small-order");
    }

    /// Canonical encodings of the eight points whose order divides 8.
    fn edwards_torsion() -> [[u8; 32]; 8] {
        [
            "0100000000000000000000000000000000000000000000000000000000000000",
            "0000000000000000000000000000000000000000000000000000000000000000",
            "0000000000000000000000000000000000000000000000000000000000000080",
            "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc05",
            "26e8958fc2b227b045c3f489f2ef98f0d5dfac05d3c63339b13802886d53fc85",
            "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac037a",
            "c7176a703d4dd84fba3c0b760d10670f2a2053fa2c39ccc64ec7fd7792ac03fa",
            "ecffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7f",
        ]
        .map(|hex_text| decode(hex_text).try_into().unwrap())
    }

    /// `y + p` as a 255-bit little-endian Edwards coordinate, sign bit clear.
    /// `y` is at most 18, so the sum does not carry out of the low byte.
    fn edwards_y_plus_p(y: u8) -> [u8; 32] {
        let mut bytes = [0xffu8; 32];
        bytes[0] = 0xed + y;
        bytes[31] = 0x7f;
        bytes
    }

    /// `L`, little-endian, and `L - 1`.
    fn edwards_order() -> ([u8; 32], [u8; 32]) {
        let order = [
            0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9,
            0xde, 0x14, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0x10,
        ];
        let mut below = order;
        below[0] = 0xec;
        (order, below)
    }

    /// P-256's field prime and its order, big-endian.
    fn p256_prime_and_order() -> ([u8; 32], [u8; 32]) {
        let prime = decode("ffffffff00000001000000000000000000000000ffffffffffffffffffffffff");
        let order = decode("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
        (prime.try_into().unwrap(), order.try_into().unwrap())
    }

    fn bad_signature(result: Result<Output, Error>) {
        assert!(
            matches!(result, Err(Error::BadSignature)),
            "expected BadSignature, got {result:?}"
        );
    }

    #[test]
    fn refuses_bad_keys_and_proofs() {
        let ed = &ECVRF_EDWARDS25519_SHA512_TAI;
        let p256 = &ECVRF_P256_SHA256_TAI;
        assert!(SecretKey::from_bytes(ed, &[0; 31]).is_err());
        assert!(SecretKey::from_bytes(p256, &[0; 32]).is_err());
        assert!(SecretKey::from_bytes(p256, &[0xff; 32]).is_err());

        // Identity, both order-4 points, the four order-8 points, and the
        // order-2 point. Section 5.4.5 refuses every point of order dividing 8.
        let torsion = edwards_torsion();
        for point in torsion {
            small_order(PublicKey::from_bytes(ed, &point).unwrap_err());
        }
        let order_two = torsion[7];
        assert!(PublicKey::from_bytes(ed, &[0; 31]).is_err());

        // RFC 8032 rejects `y >= p` and a set sign bit on `x = 0`. dalek's
        // decompress accepts both; the portable backend must not.
        let mut negative_zero = [0u8; 32];
        negative_zero[0] = 1;
        negative_zero[31] = 0x80;
        not_on_curve(PublicKey::from_bytes(ed, &negative_zero).unwrap_err());
        for y in [0, 1, 3, 4, 5, 6, 9, 10, 14, 15, 16, 18] {
            not_on_curve(PublicKey::from_bytes(ed, &edwards_y_plus_p(y)).unwrap_err());
        }

        let key = SecretKey::from_bytes(ed, &[0x11; 32]).unwrap();
        let (proof, output) = key.prove(b"alpha").unwrap();
        ct::public_slice(output.as_ref());
        let checked = key.public_key().verify(b"alpha", &proof).unwrap();
        ct::public_slice(checked.as_ref());
        assert_eq!(checked.as_ref(), output.as_ref());
        assert!(key.public_key().verify(b"other", &proof).is_err());
        let mut tampered = proof.as_ref().to_vec();
        tampered[0] ^= 0x01;
        let tampered = Proof::from_bytes(ed, &tampered).unwrap();
        bad_signature(key.public_key().verify(b"alpha", &tampered));

        // `s = 0` is in range and fails the equation. `s = L` and above are
        // not canonical.
        let (order, order_minus) = edwards_order();
        for scalar in [[0; 32], order, order_minus, [0xff; 32]] {
            let mut proof_bytes = proof.as_ref().to_vec();
            proof_bytes[48..].copy_from_slice(&scalar);
            let proof = Proof::from_bytes(ed, &proof_bytes).unwrap();
            bad_signature(key.public_key().verify(b"alpha", &proof));
        }
        for gamma in [negative_zero, order_two, edwards_y_plus_p(3)] {
            let mut proof_bytes = proof.as_ref().to_vec();
            proof_bytes[..32].copy_from_slice(&gamma);
            let proof = Proof::from_bytes(ed, &proof_bytes).unwrap();
            bad_signature(key.public_key().verify(b"alpha", &proof));
        }
        for y in [0, 1, 3, 4, 5, 6, 9, 10, 14, 15, 16, 18] {
            let mut proof_bytes = proof.as_ref().to_vec();
            proof_bytes[..32].copy_from_slice(&edwards_y_plus_p(y));
            let proof = Proof::from_bytes(ed, &proof_bytes).unwrap();
            bad_signature(key.public_key().verify(b"alpha", &proof));
        }

        assert!(Proof::from_bytes(ed, &[0; 79]).is_err());
        let other = Proof::from_bytes(p256, &[0x02; 81]).unwrap();
        assert!(matches!(
            key.public_key().verify(b"alpha", &other),
            Err(Error::Unsupported)
        ));

        let p256_key = SecretKey::from_bytes(
            p256,
            &decode("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721"),
        )
        .unwrap();
        let (proof, _) = p256_key.prove(b"alpha").unwrap();
        let proof_bytes = proof.as_ref().to_vec();
        let (prime, order) = p256_prime_and_order();
        let mut order_minus = order;
        order_minus[31] -= 1;
        for scalar in [order, order_minus, [0xff; 32], [0; 32]] {
            let mut edited = proof_bytes.clone();
            edited[49..].copy_from_slice(&scalar);
            let proof = Proof::from_bytes(p256, &edited).unwrap();
            bad_signature(p256_key.public_key().verify(b"alpha", &proof));
        }

        let refuse_gamma = |bytes: &[u8]| {
            let mut edited = proof_bytes.clone();
            edited[..33].copy_from_slice(bytes);
            let proof = Proof::from_bytes(p256, &edited).unwrap();
            bad_signature(p256_key.public_key().verify(b"alpha", &proof));
        };
        let mut tagged = [0x04u8; 33];
        let rejected = PublicKey::from_bytes(p256, &tagged).unwrap_err();
        let Error::KeyRejected(rejected) = rejected else {
            panic!("expected a rejected key, got {rejected:?}");
        };
        assert!(
            rejected
                .to_string()
                .contains("neither compressed nor uncompressed"),
            "{rejected}"
        );
        refuse_gamma(&tagged);
        tagged[0] = 0x02;
        tagged[1..].copy_from_slice(&prime);
        not_on_curve(PublicKey::from_bytes(p256, &tagged).unwrap_err());
        refuse_gamma(&tagged);
        let mut below_prime = prime;
        below_prime[31] -= 1;
        tagged[1..].copy_from_slice(&below_prime);
        not_on_curve(PublicKey::from_bytes(p256, &tagged).unwrap_err());
        refuse_gamma(&tagged);

        // The other parity is the negation, still a curve point, so it is a
        // public key. As Gamma it is not this proof's point.
        let mut flipped = p256_key.public_key().as_ref().to_vec();
        flipped[0] ^= 1;
        PublicKey::from_bytes(p256, &flipped).unwrap();
        let mut gamma = proof_bytes[..33].to_vec();
        gamma[0] ^= 1;
        let mut edited = proof_bytes.clone();
        edited[..33].copy_from_slice(&gamma);
        let proof = Proof::from_bytes(p256, &edited).unwrap();
        bad_signature(p256_key.public_key().verify(b"alpha", &proof));

        // `c = 0` takes `add_public`'s identity arm. `s = c*x` adds a point to
        // its negation, `s = -c*x` doubles, and `Gamma = t*H` with `s = c*t`
        // does the same for `V`.
        let mut zero_c = proof_bytes.clone();
        zero_c[33..49].fill(0);
        bad_signature(
            p256_key
                .public_key()
                .verify(b"alpha", &Proof::from_bytes(p256, &zero_c).unwrap()),
        );

        // `from_bytes` marked this seed secret. The cases below splice a
        // public `s` into a proof, and verify branches on the point sum and
        // the challenge, so the seed and those `s` bytes are public.
        let seed = p256_key.to_bytes();
        ct::public_slice(&seed[..]);
        let x = group::scalar_checked(&seed).unwrap();
        let c = group::scalar_reduced(&proof_bytes[33..49]).unwrap();
        let cx = group::scalar_mul(&c, &x);
        let cx_bytes = group::scalar_bytes(&cx);
        ct::public_slice(&cx_bytes[..]);
        let mut opposite = proof_bytes.clone();
        opposite[49..].copy_from_slice(&cx_bytes);
        bad_signature(
            p256_key
                .public_key()
                .verify(b"alpha", &Proof::from_bytes(p256, &opposite).unwrap()),
        );
        assert!(
            !ct::into_public(cx.is_zero()),
            "this proof's challenge is zero, so s = -c*x does not double"
        );
        let mut neg = order;
        let mut borrow = 0u16;
        for i in (0..32).rev() {
            let diff = u16::from(neg[i])
                .wrapping_sub(u16::from(cx_bytes[i]))
                .wrapping_sub(borrow);
            neg[i] = diff as u8;
            borrow = (diff >> 8) & 1;
        }
        let neg_scalar = group::scalar_canonical(&neg).unwrap();
        assert!(ct::into_public(
            group::scalar_add(&cx, &neg_scalar).is_zero()
        ));
        ct::public_slice(&neg[..]);
        let mut doubled = proof_bytes.clone();
        doubled[49..].copy_from_slice(&neg);
        bad_signature(
            p256_key
                .public_key()
                .verify(b"alpha", &Proof::from_bytes(p256, &doubled).unwrap()),
        );
        let hashed = hash_to_curve_p256(p256_key.public_key().as_ref(), b"alpha").unwrap();
        let t = group::scalar_reduced(&[2]).unwrap();
        let gamma_t = hashed.mul_public(&t).to_compressed().unwrap();
        let s_ct = group::scalar_mul(&c, &t);
        let mut vee = proof_bytes.clone();
        vee[..33].copy_from_slice(&gamma_t);
        vee[49..].copy_from_slice(&group::scalar_bytes(&s_ct));
        bad_signature(
            p256_key
                .public_key()
                .verify(b"alpha", &Proof::from_bytes(p256, &vee).unwrap()),
        );
    }

    fn declassified_eq(left: &[u8], right: &[u8]) {
        ct::public_slice(left);
        ct::public_slice(right);
        assert_eq!(left, right);
    }

    #[test]
    fn secrets_stay_secret() {
        let seed = [0x11u8; 32];
        ct::secret_slice(&seed[..]);
        let key = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &seed).unwrap();
        let encoded = key.to_bytes();
        core::hint::black_box(&encoded[..]);
        let public = key.public_key();
        let (proof, output) = key.prove(b"alpha").unwrap();
        let checked = public.verify(b"alpha", &proof).unwrap();
        declassified_eq(checked.as_ref(), output.as_ref());

        let seed = decode("c9afa9d845ba75166b5c215767b1d6934e50c3db36e89b127b8a622b120f6721");
        ct::secret_slice(&seed[..]);
        let key = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &seed).unwrap();
        let encoded = key.to_bytes();
        core::hint::black_box(&encoded[..]);
        let public = key.public_key();
        let (proof, output) = key.prove(b"sample").unwrap();
        let checked = public.verify(b"sample", &proof).unwrap();
        declassified_eq(checked.as_ref(), output.as_ref());

        for algorithm in [&ECVRF_EDWARDS25519_SHA512_TAI, &ECVRF_P256_SHA256_TAI] {
            let generated = SecretKey::generate(algorithm).unwrap();
            let (proof, output) = generated.prove(b"generated").unwrap();
            let checked = generated.public_key().verify(b"generated", &proof).unwrap();
            declassified_eq(checked.as_ref(), output.as_ref());
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 32, ..ProptestConfig::default() })]

        #[test]
        fn edwards_round_trip(seed: [u8; 32], alpha in proptest::collection::vec(any::<u8>(), 0..40)) {
            let key = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &seed).unwrap();
            let (proof, output) = key.prove(&alpha).unwrap();
            let got = key.public_key().verify(&alpha, &proof).unwrap();
            prop_assert_eq!(got.as_ref(), output.as_ref());
            let mut tampered = proof.as_ref().to_vec();
            tampered[10] ^= 0x01;
            let tampered = Proof::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &tampered).unwrap();
            prop_assert!(key.public_key().verify(&alpha, &tampered).is_err());
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig { cases: 16, ..ProptestConfig::default() })]

        #[test]
        fn p256_round_trip(seed: [u8; 32], alpha in proptest::collection::vec(any::<u8>(), 0..=64)) {
            let Ok(key) = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &seed) else {
                return Ok(());
            };
            let (proof, output) = key.prove(&alpha).unwrap();
            let got = key.public_key().verify(&alpha, &proof).unwrap();
            ct::public_slice(got.as_ref());
            ct::public_slice(output.as_ref());
            prop_assert_eq!(got.as_ref(), output.as_ref());
        }
    }

    #[cfg(not(any(miri, target_family = "wasm")))]
    proptest! {
        #![proptest_config(ProptestConfig { cases: 16, ..ProptestConfig::default() })]

        #[test]
        fn matches_akd_core(seed: [u8; 32], alpha in proptest::collection::vec(any::<u8>(), 0..=64)) {
            use akd_core::ecvrf::{Proof as AkdProof, VRFPrivateKey, VRFPublicKey};

            let key = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &seed).unwrap();
            let (proof, output) = key.prove(&alpha).unwrap();
            let akd = VRFPrivateKey::try_from(seed.as_slice()).unwrap();
            let akd_proof = akd.prove(&alpha);
            let akd_bytes = akd_proof.to_bytes();
            ct::public_slice(&akd_bytes[..]);
            ct::public_slice(proof.as_ref());
            ct::public_slice(output.as_ref());
            prop_assert_eq!(&akd_bytes[..], proof.as_ref());

            let akd_public = VRFPublicKey::try_from(key.public_key().as_ref()).unwrap();
            akd_public.verify(&akd_proof, &alpha).unwrap();
            let parsed = Proof::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &akd_bytes[..]).unwrap();
            let checked = key.public_key().verify(&alpha, &parsed).unwrap();
            ct::public_slice(checked.as_ref());
            prop_assert_eq!(checked.as_ref(), output.as_ref());

            let mut order_two = [0xffu8; 32];
            order_two[0] = 0xec;
            order_two[31] = 0x7f;
            let mut negative_zero = [0u8; 32];
            negative_zero[0] = 1;
            negative_zero[31] = 0x80;
            let (order, _) = edwards_order();
            let mut order_plus = order;
            order_plus[0] = order_plus[0].wrapping_add(1);
            let mut mutations = Vec::new();
            for index in [0usize, 16, 31, 32, 40, 47, 48, 64, 79] {
                let mut edited = akd_bytes;
                edited[index] ^= 0x01;
                mutations.push(edited);
            }
            for scalar in [order, order_plus, [0xff; 32]] {
                let mut edited = akd_bytes;
                edited[48..].copy_from_slice(&scalar);
                mutations.push(edited);
            }
            for gamma in [order_two, negative_zero, edwards_y_plus_p(0), edwards_y_plus_p(3)] {
                let mut edited = akd_bytes;
                edited[..32].copy_from_slice(&gamma);
                mutations.push(edited);
            }
            for edited in mutations {
                let rind_ok = Proof::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &edited[..])
                    .and_then(|parsed| key.public_key().verify(&alpha, &parsed))
                    .is_ok();
                let akd_ok = AkdProof::try_from(edited.as_slice())
                    .is_ok_and(|parsed| akd_public.verify(&parsed, &alpha).is_ok());
                if rind_ok != akd_ok {
                    let bytes = edited
                        .iter()
                        .map(|byte| format!("{byte:02x}"))
                        .collect::<String>();
                    return Err(TestCaseError::fail(format!(
                        "rind {rind_ok}, akd_core {akd_ok}, proof {bytes}"
                    )));
                }
            }
        }

        #[test]
        fn matches_vrf_rfc9381(
            seed: [u8; 32],
            alpha in proptest::collection::vec(any::<u8>(), 0..=64),
        ) {
            use vrf_rfc9381::ec::p256::tai::{EcVrfP256Tai, EcVrfP256TaiSecretKey};
            use vrf_rfc9381::{Prover, VRF};

            let Ok(key) = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &seed) else {
                return Ok(());
            };
            let suite = EcVrfP256Tai;
            let Ok(theirs) = EcVrfP256TaiSecretKey::from_slice(&seed[..]) else {
                return Err(TestCaseError::fail(
                    "vrf-rfc9381 refused a canonical P-256 scalar",
                ));
            };
            let (proof, output) = key.prove(&alpha).unwrap();
            let their_bytes = suite.prove(&theirs, &alpha).unwrap();
            ct::public_slice(&their_bytes[..]);
            ct::public_slice(proof.as_ref());
            ct::public_slice(output.as_ref());
            prop_assert_eq!(&their_bytes[..], proof.as_ref());
            let their_output = suite
                .verify(&theirs.verifier(), &alpha, &their_bytes)
                .unwrap();
            ct::public_slice(their_output.as_slice());
            prop_assert_eq!(their_output.as_slice(), output.as_ref());
        }
    }
}
