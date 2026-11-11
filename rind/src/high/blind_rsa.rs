// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RSA blind signatures, RSABSSA-SHA384 (RFC 9474).

use core::fmt;

use super::digest;
use super::hash;
use super::pkcs1;
use super::rsa::{SigningKey, VerifyingKey};
use crate::error::Error;
use crate::low::{Entry, Zeroable, ct, zeroise_value};
use crate::mid::rng::{RandomSource, SystemRandom};
use crate::mid::rsa_pub;

const PREFIX_LEN: usize = 32;
const SHA384_LEN: u16 = 48;
const MAX_MODULUS: usize = rsa_pub::MAX_PUBLIC_MODULUS_BYTES;
const SPKI_MAX: usize = MAX_MODULUS + 256;

/// One RSABSSA-SHA384 variant. Only this module's constants build one.
///
/// A new variant is a new [`Kind`], and every match on it has to name it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Algorithm {
    kind: Kind,
}

/// The four variants. `#[repr(u8)]` makes the zero bit pattern the first one,
/// which a wiped [`Blinding`] may hold.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
enum Kind {
    Randomized,
    ZeroRandomized,
    Deterministic,
    ZeroDeterministic,
}

impl Kind {
    fn salt_len(self) -> usize {
        match self {
            Self::Randomized | Self::Deterministic => usize::from(SHA384_LEN),
            Self::ZeroRandomized | Self::ZeroDeterministic => 0,
        }
    }

    fn randomized(self) -> bool {
        match self {
            Self::Randomized | Self::ZeroRandomized => true,
            Self::Deterministic | Self::ZeroDeterministic => false,
        }
    }

    fn algorithm(self) -> &'static Algorithm {
        match self {
            Self::Randomized => &RSABSSA_SHA384_PSS_RANDOMIZED,
            Self::ZeroRandomized => &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
            Self::Deterministic => &RSABSSA_SHA384_PSS_DETERMINISTIC,
            Self::ZeroDeterministic => &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
        }
    }
}

impl Algorithm {
    fn salt_len(self) -> usize {
        self.kind.salt_len()
    }

    fn randomized(self) -> bool {
        self.kind.randomized()
    }
}

/// RSABSSA-SHA384-PSS-Randomized. The signed message is 32 random bytes
/// followed by the caller's message, and the PSS salt is 48 bytes.
pub static RSABSSA_SHA384_PSS_RANDOMIZED: Algorithm = Algorithm {
    kind: Kind::Randomized,
};

/// RSABSSA-SHA384-PSSZERO-Randomized. Same preparation, with an empty PSS salt.
pub static RSABSSA_SHA384_PSSZERO_RANDOMIZED: Algorithm = Algorithm {
    kind: Kind::ZeroRandomized,
};

/// RSABSSA-SHA384-PSS-Deterministic. The message is signed as given, with a
/// 48-byte PSS salt. Privacy Pass tokens (RFC 9578 type `0x0002`) use this
/// with a 2048-bit key.
pub static RSABSSA_SHA384_PSS_DETERMINISTIC: Algorithm = Algorithm {
    kind: Kind::Deterministic,
};

/// RSABSSA-SHA384-PSSZERO-Deterministic. The message is signed as given, with
/// an empty PSS salt.
pub static RSABSSA_SHA384_PSSZERO_DETERMINISTIC: Algorithm = Algorithm {
    kind: Kind::ZeroDeterministic,
};

/// A message prepared for a randomized variant: 32 random bytes, then the
/// message, reduced to the SHA-384 digest that PSS signs. Verification takes
/// this type, so the unprepared message is not a signature input.
pub struct PreparedMessage {
    prefix: [u8; PREFIX_LEN],
    digest: [u8; 48],
    kind: Kind,
}

impl PreparedMessage {
    /// The 32-byte prefix.
    ///
    /// This is the value the client sends with the signature, so it is
    /// public from here on. `prepare` marks the fresh bytes secret only
    /// while they are being copied in.
    pub fn prefix(&self) -> &[u8; PREFIX_LEN] {
        ct::public_slice(&self.prefix);
        &self.prefix
    }

    /// SHA-384 of the prefix and the caller's message.
    fn digest(&self) -> &[u8] {
        &self.digest
    }
}

impl fmt::Debug for PreparedMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PreparedMessage").finish_non_exhaustive()
    }
}

struct PreparedBytes<'a> {
    prefix: &'a [u8],
    message: &'a [u8],
}

impl PreparedBytes<'_> {
    fn hash(&self) -> digest::Digest {
        let mut ctx = digest::Context::new(&digest::SHA384);
        ctx.update(self.prefix);
        ctx.update(self.message);
        ctx.finish()
    }
}

/// The client's RSA public key.
///
/// `salt` is the `id-RSASSA-PSS` salt length when the key was loaded from
/// that algorithm. `None` is `rsaEncryption` or raw components, which name
/// no PSS parameters and accept every variant.
#[derive(Clone)]
pub struct PublicKey {
    key: VerifyingKey,
    salt: Option<u8>,
}

impl PublicKey {
    /// Decodes an RSA public key from `SubjectPublicKeyInfo` DER.
    ///
    /// An `id-RSASSA-PSS` key must name SHA-384, MGF1 with SHA-384, and
    /// `algorithm`'s salt length. `rsaEncryption` carries no PSS parameters.
    /// Any other algorithm, or a parameter that does not match, is refused.
    pub fn from_spki(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        let (key, salt) = spki_key(algorithm, bytes)?;
        Ok(Self { key, salt })
    }

    /// Loads an RSA public key from its big-endian modulus and exponent.
    pub fn from_components(n: &[u8], e: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        Ok(Self {
            key: VerifyingKey::from_components(n, e)?,
            salt: None,
        })
    }

    fn require(&self, algorithm: &Algorithm) -> Result<(), Error> {
        match self.salt {
            Some(salt) if usize::from(salt) == algorithm.salt_len() => Ok(()),
            Some(_) => Err(Error::Unsupported),
            None => Ok(()),
        }
    }

    /// `n` and `e`, big-endian, with no leading zero.
    pub fn components(&self) -> Result<Components, Error> {
        let _entry = Entry::new_public();
        let mut wide = [0u8; MAX_MODULUS];
        let raw = self.key.modulus_be(&mut wide)?;
        let mut n = [0u8; MAX_MODULUS];
        n[..raw.len()].copy_from_slice(raw);
        let n_len = raw.len() as u16;
        let be = self.key.exponent().to_be_bytes();
        let start = be.iter().position(|byte| *byte != 0).unwrap_or(0);
        let mut e = [0u8; 8];
        e[..be.len() - start].copy_from_slice(&be[start..]);
        Ok(Components {
            n,
            n_len,
            e,
            e_len: (be.len() - start) as u8,
        })
    }

    /// `SubjectPublicKeyInfo` for `id-RSASSA-PSS`, with `algorithm`'s hash
    /// and salt. A key loaded with a different salt is [`Error::Unsupported`].
    pub fn to_spki(&self, algorithm: &'static Algorithm) -> Result<SubjectPublicKeyInfo, Error> {
        let _entry = Entry::new_public();
        self.require(algorithm)?;
        let mut bytes = [0u8; SPKI_MAX];
        let len = encode_pss_spki(&self.key, algorithm, &mut bytes)?;
        Ok(SubjectPublicKeyInfo {
            bytes,
            len: len as u16,
        })
    }

    /// Prepares `message` for a randomized variant.
    ///
    /// Fails with [`Error::Unsupported`] for a deterministic variant.
    /// `message` has no length cap: only its digest is kept.
    pub fn prepare(
        &self,
        algorithm: &'static Algorithm,
        message: &[u8],
    ) -> Result<PreparedMessage, Error> {
        let _entry = Entry::new_public();
        if !algorithm.randomized() {
            return Err(Error::Unsupported);
        }
        let mut prefix = [0u8; PREFIX_LEN];
        SystemRandom.fill(&mut prefix)?;
        ct::secret_slice(&prefix);
        Self::prepared(algorithm, &prefix, message)
    }

    /// A randomized prepared message with a caller-supplied prefix.
    ///
    /// The prefix is the 32 bytes that were prepended. Fails with
    /// [`Error::Unsupported`] for a deterministic variant, and with
    /// [`Error::WrongLength`] when `prefix` is not 32 bytes.
    pub fn prepared(
        algorithm: &'static Algorithm,
        prefix: &[u8],
        message: &[u8],
    ) -> Result<PreparedMessage, Error> {
        let _entry = Entry::new_public();
        if !algorithm.randomized() || prefix.len() != PREFIX_LEN {
            return Err(if prefix.len() == PREFIX_LEN {
                Error::Unsupported
            } else {
                Error::WrongLength
            });
        }
        let mut prefix_bytes = [0u8; PREFIX_LEN];
        prefix_bytes.copy_from_slice(prefix);
        let digest = PreparedBytes {
            prefix: &prefix_bytes,
            message,
        }
        .hash();
        let mut stored = [0u8; 48];
        stored.copy_from_slice(digest.as_ref());
        Ok(PreparedMessage {
            prefix: prefix_bytes,
            digest: stored,
            kind: algorithm.kind,
        })
    }

    /// Blinds a deterministic variant's message.
    ///
    /// Fails with [`Error::Unsupported`] for a randomized variant, or when
    /// the PSS encoding shares a factor with the modulus. The key's PSS
    /// salt, when the key names one, has to be this variant's.
    pub fn blind(
        &self,
        algorithm: &'static Algorithm,
        message: &[u8],
    ) -> Result<(BlindedMessage, Blinding), Error> {
        let _entry = Entry::new_secret();
        self.require(algorithm)?;
        if algorithm.randomized() {
            return Err(Error::Unsupported);
        }
        let digest = PreparedBytes {
            prefix: &[],
            message,
        }
        .hash();
        blind_message(&self.key, algorithm, digest.as_ref(), None, None)
    }

    /// Blinds a [`PreparedMessage`].
    pub fn blind_prepared(
        &self,
        message: &PreparedMessage,
    ) -> Result<(BlindedMessage, Blinding), Error> {
        let _entry = Entry::new_secret();
        self.require(message.kind.algorithm())?;
        blind_message(
            &self.key,
            message.kind.algorithm(),
            message.digest(),
            None,
            None,
        )
    }

    /// Verifies `signature` on `message` under a deterministic variant.
    ///
    /// A randomized variant is [`Error::Unsupported`]: pass the
    /// [`PreparedMessage`] to [`Self::verify_prepared`].
    pub fn verify(
        &self,
        algorithm: &'static Algorithm,
        message: &[u8],
        signature: &Signature,
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        self.require(algorithm)?;
        if algorithm.randomized() {
            return Err(Error::Unsupported);
        }
        verify_message(&self.key, algorithm, &[], message, signature.as_ref())
    }

    /// Verifies `signature` on a randomized prepared message.
    pub fn verify_prepared(
        &self,
        message: &PreparedMessage,
        signature: &Signature,
    ) -> Result<(), Error> {
        let _entry = Entry::new_public();
        self.require(message.kind.algorithm())?;
        finish_verify(
            &self.key,
            *message.kind.algorithm(),
            &message.digest,
            signature.as_ref(),
        )
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("modulus_len", &self.key.modulus_len_bytes())
            .finish_non_exhaustive()
    }
}

/// The integer the client sends to be signed, modulus-length and big-endian.
pub struct BlindedMessage {
    bytes: [u8; MAX_MODULUS],
    len: u16,
}

impl BlindedMessage {
    /// Copies `bytes` when they fit a modulus this library accepts.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        fixed(bytes).map(|fixed| Self {
            bytes: fixed.0,
            len: fixed.1,
        })
    }
}

impl AsRef<[u8]> for BlindedMessage {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl fmt::Debug for BlindedMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BlindedMessage")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

/// The server's signature of a [`BlindedMessage`].
pub struct BlindSignature {
    bytes: [u8; MAX_MODULUS],
    len: u16,
}

impl BlindSignature {
    /// Copies `bytes` when they fit a modulus this library accepts.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        fixed(bytes).map(|fixed| Self {
            bytes: fixed.0,
            len: fixed.1,
        })
    }
}

impl AsRef<[u8]> for BlindSignature {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl fmt::Debug for BlindSignature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BlindSignature")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

/// An RSASSA-PSS signature, modulus-length and big-endian.
pub struct Signature {
    bytes: [u8; MAX_MODULUS],
    len: u16,
}

impl Signature {
    /// Copies `bytes` when they fit a modulus this library accepts.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_public();
        fixed(bytes).map(|fixed| Self {
            bytes: fixed.0,
            len: fixed.1,
        })
    }
}

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Signature")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

fn fixed(bytes: &[u8]) -> Result<([u8; MAX_MODULUS], u16), Error> {
    if bytes.is_empty() || bytes.len() > MAX_MODULUS {
        return Err(Error::WrongLength);
    }
    let mut stored = [0u8; MAX_MODULUS];
    stored[..bytes.len()].copy_from_slice(bytes);
    Ok((stored, bytes.len() as u16))
}

/// The client's secret blinding factor and the digest it covers.
///
/// [`Self::finalize`] consumes it and checks the signature before returning
/// one. Drop wipes it under `wipe`.
pub struct Blinding {
    key: VerifyingKey,
    inverse: [u8; MAX_MODULUS],
    digest: [u8; 48],
    kind: Kind,
}

impl Blinding {
    /// Turns `blind_signature` into a verified RSASSA-PSS signature.
    ///
    /// Fails with [`Error::BadSignature`] when the signature does not
    /// unblind to this message, including when the integer is not below the
    /// modulus. [`Error::WrongLength`] is a signature that is not the
    /// modulus length.
    pub fn finalize(self, blind_signature: &BlindSignature) -> Result<Signature, Error> {
        let _entry = Entry::new_secret();
        let k = self.key.modulus_len_bytes();
        if blind_signature.as_ref().len() != k {
            return Err(Error::WrongLength);
        }
        let mut signature = [0u8; MAX_MODULUS];
        if self
            .key
            .mul_mod_be(blind_signature.as_ref(), &self.inverse[..k], &mut signature)
            .is_err()
        {
            return Err(Error::BadSignature);
        }
        ct::secret_slice(&signature[..k]);
        let algorithm = *self.kind.algorithm();
        let verdict = verify_secret(&self.key, algorithm, &self.digest, &signature[..k])?;
        if !ct::into_public(verdict) {
            return Err(Error::BadSignature);
        }
        ct::public_slice(&signature[..k]);
        Ok(Signature {
            bytes: signature,
            len: k as u16,
        })
    }
}

impl fmt::Debug for Blinding {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Blinding").finish_non_exhaustive()
    }
}

impl Drop for Blinding {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for Blinding {}

/// An RSA signing key. Drop wipes the whole value under `wipe`.
pub struct KeyPair {
    key: SigningKey,
}

impl KeyPair {
    /// Generates a two-prime RSA key of `size`.
    pub fn generate(size: crate::mid::rsa_key_size::RsaKeySize) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        Ok(Self {
            key: SigningKey::generate(size)?,
        })
    }

    /// Decodes a two-prime RSA key from PKCS#8 DER.
    pub fn from_pkcs8(bytes: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        Ok(Self {
            key: SigningKey::from_pkcs8_der(bytes)?,
        })
    }

    /// Signs `blinded`. The signature is an ordinary RSA private operation,
    /// checked against the public key.
    pub fn blind_sign(&self, blinded: &BlindedMessage) -> Result<BlindSignature, Error> {
        let _entry = Entry::new_secret();
        let mut out = [0u8; MAX_MODULUS];
        let signed = self.key.blind_sign(blinded.as_ref(), &mut out)?;
        let len = signed.len();
        Ok(BlindSignature {
            bytes: out,
            len: len as u16,
        })
    }

    /// The public key. It names no PSS parameters, so every variant accepts it.
    pub fn public_key(&self) -> PublicKey {
        PublicKey {
            key: self.key.public_key(),
            salt: None,
        }
    }

    /// `n` and `e`, big-endian, with no leading zero.
    pub fn components(&self) -> Result<Components, Error> {
        self.public_key().components()
    }

    /// `SubjectPublicKeyInfo` for `id-RSASSA-PSS`, with `algorithm`'s salt.
    pub fn to_spki(&self, algorithm: &'static Algorithm) -> Result<SubjectPublicKeyInfo, Error> {
        self.public_key().to_spki(algorithm)
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair").finish_non_exhaustive()
    }
}

impl Drop for KeyPair {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for KeyPair {}

struct SaltBytes<'a>(&'a [u8]);

impl RandomSource for SaltBytes<'_> {
    fn fill(&mut self, out: &mut [u8]) -> Result<(), Error> {
        if out.len() != self.0.len() {
            return Err(Error::WrongLength);
        }
        out.copy_from_slice(self.0);
        Ok(())
    }
}

fn blind_message(
    key: &VerifyingKey,
    algorithm: &'static Algorithm,
    digest: &[u8],
    salt: Option<&[u8]>,
    inverse: Option<&[u8]>,
) -> Result<(BlindedMessage, Blinding), Error> {
    let _entry = Entry::new_secret();
    let k = key.modulus_len_bytes();
    let em_bits = key.modulus_len_bits() - 1;
    let em_len = em_bits.div_ceil(8);
    let mut em = [0u8; MAX_MODULUS];
    let attempts = if salt.is_some() || algorithm.salt_len() == 0 {
        1
    } else {
        4
    };
    let mut stored_digest = [0u8; 48];
    stored_digest[..digest.len()].copy_from_slice(digest);
    ct::secret_slice(&stored_digest);
    for _ in 0..attempts {
        match salt {
            Some(salt) => {
                pkcs1::encode_pss_sig::<hash::Sha384>(
                    &mut em[..em_len],
                    em_bits,
                    &mut SaltBytes(salt),
                    digest,
                    algorithm.salt_len(),
                )?;
            }
            None => {
                pkcs1::encode_pss_sig::<hash::Sha384>(
                    &mut em[..em_len],
                    em_bits,
                    &mut SystemRandom,
                    digest,
                    algorithm.salt_len(),
                )?;
            }
        }
        ct::secret_slice(&em[..em_len]);
        let mut encoded = [0u8; MAX_MODULUS];
        encoded[k - em_len..k].copy_from_slice(&em[..em_len]);
        if !key.is_coprime_be(&encoded[..k])? {
            continue;
        }

        let mut factor = [0u8; MAX_MODULUS];
        let mut inv = [0u8; MAX_MODULUS];
        match inverse {
            Some(given) => {
                if given.len() != k {
                    return Err(Error::WrongLength);
                }
                key.invert_be(given, &mut factor)?;
                inv[..k].copy_from_slice(given);
                ct::secret_slice(&inv[..k]);
            }
            None => {
                key.random_factor_be(&mut SystemRandom, &mut factor)?;
                key.invert_coprime_be(&factor[..k], &mut inv)?;
            }
        }
        ct::secret_slice(&factor[..k]);
        let mut powered = [0u8; MAX_MODULUS];
        key.public_op_be(&factor[..k], &mut powered)?;
        ct::secret_slice(&powered[..k]);
        let mut blinded = [0u8; MAX_MODULUS];
        key.mul_mod_be(&encoded[..k], &powered[..k], &mut blinded)?;
        ct::public_slice(&blinded[..k]);

        return Ok((
            BlindedMessage {
                bytes: blinded,
                len: k as u16,
            },
            Blinding {
                key: key.clone(),
                inverse: inv,
                digest: stored_digest,
                kind: algorithm.kind,
            },
        ));
    }
    Err(Error::Unsupported)
}

fn verify_message(
    key: &VerifyingKey,
    algorithm: &'static Algorithm,
    prefix: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<(), Error> {
    let _entry = Entry::new_public();
    let hash = PreparedBytes { prefix, message }.hash();
    finish_verify(key, *algorithm, hash.as_ref(), signature)
}

fn finish_verify(
    key: &VerifyingKey,
    algorithm: Algorithm,
    hash: &[u8],
    signature: &[u8],
) -> Result<(), Error> {
    if signature.len() != key.modulus_len_bytes() {
        return Err(Error::BadSignature);
    }
    match verify_secret(key, algorithm, hash, signature) {
        Ok(verdict) if ct::into_public(verdict) => Ok(()),
        Ok(_) => Err(Error::BadSignature),
        Err(Error::WrongLength) => Err(Error::BadSignature),
        Err(error) => Err(error),
    }
}

fn verify_secret(
    key: &VerifyingKey,
    algorithm: Algorithm,
    hash: &[u8],
    signature: &[u8],
) -> Result<bool, Error> {
    let em_bits = key.modulus_len_bits() - 1;
    let mut em = [0u8; MAX_MODULUS];
    let opened = key.public_op_be(signature, &mut em)?;
    let em_len = em_bits.div_ceil(8);
    if opened.len() < em_len {
        return Ok(false);
    }
    let start = opened.len() - em_len;
    let mut encoded = [0u8; MAX_MODULUS];
    encoded[..em_len].copy_from_slice(&opened[start..]);
    ct::secret_slice(&encoded[..em_len]);
    // RFC 8017 I2OSP to emLen: a modulus whose bit length is 1 mod 8 is one
    // byte longer than EM. That byte is part of the representative, so a
    // nonzero value fails together with the PSS checks.
    ct::secret_slice(&opened[..start]);
    let zeroes = [0u8; MAX_MODULUS];
    let fits = crate::low::ct_equal(&opened[..start], &zeroes[..start]);
    Ok(fits
        & pkcs1::verify_pss_sig_secret::<hash::Sha384>(
            &mut encoded[..em_len],
            em_bits,
            hash,
            algorithm.salt_len(),
        ))
}

fn spki_key(algorithm: &Algorithm, bytes: &[u8]) -> Result<(VerifyingKey, Option<u8>), Error> {
    use crate::high::asn1::pkix::PssSubjectPublicKeyInfo;
    use crate::high::asn1::{Type, oid};

    match PssSubjectPublicKeyInfo::from_bytes(bytes) {
        Ok(spki) if spki.algorithm.algorithm == oid::id_RSASSA_PSS => {
            let salt = pss_salt(algorithm, &spki.algorithm.parameters)?;
            let key = VerifyingKey::from_pkcs1_der(spki.subjectPublicKey.as_octets())?;
            Ok((key, Some(salt)))
        }
        _ => Ok((VerifyingKey::from_spki_der(bytes)?, None)),
    }
}

/// The salt length bound into an `id-RSASSA-PSS` key.
///
/// `high::asn1` reads the parameters in order and rejects a non-canonical
/// length, a high tag, and trailing data, so a field out of order fails as
/// trailing data. A present field whose value is the RFC 4055 default is
/// rejected too: DER omits those.
fn pss_salt(
    algorithm: &Algorithm,
    params: &crate::high::asn1::pkix::RsaSsaPssParameters<'_>,
) -> Result<u8, Error> {
    use crate::high::asn1::pkix::AlgorithmIdentifier;
    use crate::high::asn1::{Any, oid};

    fn hash_ok(id: &AlgorithmIdentifier<'_>) -> Result<bool, Error> {
        let null_or_absent = match &id.parameters {
            None | Some(Any::Null(_)) => true,
            Some(_) => false,
        };
        if id.algorithm == oid::id_sha1 {
            return Err(asn1_error(crate::high::asn1::Error::NonCanonicalEncoding));
        }
        Ok(null_or_absent && id.algorithm == oid::id_sha384)
    }

    let Some(hash) = params.hashAlgorithm.inner().as_ref() else {
        return Err(mismatched());
    };
    if !hash_ok(hash)? {
        return Err(mismatched());
    }

    let Some(mgf) = params.maskGenAlgorithm.inner().as_ref() else {
        return Err(mismatched());
    };
    if mgf.algorithm != oid::id_mgf1 || !hash_ok(&mgf.hash)? {
        return Err(mismatched());
    }

    let Some(salt) = params.saltLength.inner().as_ref() else {
        return Err(mismatched());
    };
    let salt = salt.as_usize().map_err(asn1_error)?;
    if salt == 20 {
        return Err(asn1_error(crate::high::asn1::Error::NonCanonicalEncoding));
    }
    if salt != algorithm.salt_len() {
        return Err(mismatched());
    }

    if let Some(trailer) = params.trailerField.inner().as_ref() {
        let trailer = trailer.as_usize().map_err(asn1_error)?;
        if trailer == 1 {
            return Err(asn1_error(crate::high::asn1::Error::NonCanonicalEncoding));
        }
        return Err(mismatched());
    }
    u8::try_from(salt).map_err(|_| mismatched())
}

fn encode_pss_spki(
    key: &VerifyingKey,
    algorithm: &Algorithm,
    out: &mut [u8],
) -> Result<usize, Error> {
    use crate::high::asn1::pkix::{
        AlgorithmIdentifier, Mgf1Algorithm, PssAlgorithmIdentifier, PssSubjectPublicKeyInfo,
        RsaSsaPssParameters,
    };
    use crate::high::asn1::{Any, BitString, Encoder, Integer, Null, Type, oid};

    let mut pkcs1 = [0u8; crate::high::rsa::MAX_PUBLIC_KEY_LEN];
    let pkcs1 = key.to_pkcs1_der(&mut pkcs1)?;
    let hash = AlgorithmIdentifier {
        algorithm: oid::id_sha384.clone(),
        parameters: Some(Any::Null(Null)),
    };
    let salt = [u8::try_from(algorithm.salt_len()).map_err(|_| Error::Unsupported)?];
    let spki = PssSubjectPublicKeyInfo {
        algorithm: PssAlgorithmIdentifier {
            algorithm: oid::id_RSASSA_PSS.clone(),
            parameters: RsaSsaPssParameters {
                hashAlgorithm: hash.clone().into(),
                maskGenAlgorithm: Mgf1Algorithm {
                    algorithm: oid::id_mgf1.clone(),
                    hash,
                }
                .into(),
                saltLength: Integer::new(&salt).into(),
                trailerField: crate::high::asn1::Context::absent(),
            },
        },
        subjectPublicKey: BitString::new(pkcs1),
    };
    spki.encode(&mut Encoder::new(out))
        .map_err(|_| Error::WrongLength)
}

/// `n` and `e` of an RSA public key.
pub struct Components {
    n: [u8; MAX_MODULUS],
    n_len: u16,
    e: [u8; 8],
    e_len: u8,
}

impl Components {
    /// The modulus.
    pub fn modulus(&self) -> &[u8] {
        &self.n[..usize::from(self.n_len)]
    }

    /// The public exponent.
    pub fn exponent(&self) -> &[u8] {
        &self.e[..usize::from(self.e_len)]
    }
}

impl fmt::Debug for Components {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Components")
            .field("n_len", &self.n_len)
            .finish_non_exhaustive()
    }
}

/// An `id-RSASSA-PSS` `SubjectPublicKeyInfo`.
pub struct SubjectPublicKeyInfo {
    bytes: [u8; SPKI_MAX],
    len: u16,
}

impl AsRef<[u8]> for SubjectPublicKeyInfo {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..usize::from(self.len)]
    }
}

impl fmt::Debug for SubjectPublicKeyInfo {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SubjectPublicKeyInfo")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

fn mismatched() -> Error {
    crate::error::KeyFormatError::MismatchedSpkiAlgorithm.into()
}

fn asn1_error(error: crate::high::asn1::Error) -> Error {
    crate::error::KeyFormatError::Asn1(error).into()
}

/// Blinds with a fixed PSS salt and blinding inverse. RFC 9474's vectors
/// publish both.
#[cfg(test)]
pub(crate) fn blind_fixed(
    key: &PublicKey,
    algorithm: &'static Algorithm,
    prefix: &[u8],
    message: &[u8],
    salt: &[u8],
    inverse: &[u8],
) -> Result<(BlindedMessage, Blinding), Error> {
    let hash = PreparedBytes { prefix, message }.hash();
    blind_message(
        &key.key,
        algorithm,
        hash.as_ref(),
        Some(salt),
        Some(inverse),
    )
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    /// OpenSSL `RSA-PSS` SPKIs. Parameters must match the chosen variant.
    #[test]
    fn accepts_openssl_rsassa_pss_spki() {
        fn der(hex_spki: &str) -> Vec<u8> {
            hex::decode(hex_spki).unwrap()
        }
        // sha384, MGF1-sha384, salt 48.
        let pss = openssl_pss_spki();
        let key = PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, &pss).unwrap();
        assert_eq!(key.key.modulus_len_bits(), 2048);
        PublicKey::from_spki(&RSABSSA_SHA384_PSS_RANDOMIZED, &pss).unwrap();
        assert!(PublicKey::from_spki(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, &pss).is_err());
        assert!(PublicKey::from_spki(&RSABSSA_SHA384_PSSZERO_RANDOMIZED, &pss).is_err());

        // The same hash and MGF, salt 0.
        let zero = der(
            "30820156304106092a864886f70d01010a3034a00f300d06096086480165030402020500a11c301a06092a864886f70d010108300d06096086480165030402020500a2030201000382010f003082010a0282010100dc0bd86e1a7d48ff4d7d45e74373fd8f4377434c37662951be00981b3beed446c4bd8b05bd78b46aa3e612c3fff6adbffc6758ec521b0bc57ba2560a92b90f3b355a57866344330aeaf2906691a0e8f95a3151dbd981a9452f7ea4ec3c230688ed79360575f72a0521e0811371cba6efb2476ed5bda7938be1560a6062e0dc52a0775ad679a5775f484062661e6adf39a452865546b585148ca7ef5875274fdef93cc52aa33952a5cb777e36eb636dddfa01fb5576d8b046f2fba778aa0a6ba93d32630f0413a0a98f019b9b50a3fb26c825d0e6f5de9056a2867cc9274245f45170cf4b68e8acd4a789642b092303b362fb32ca3f051b983f3e7e459428ef470203010001",
        );
        PublicKey::from_spki(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, &zero).unwrap();
        PublicKey::from_spki(&RSABSSA_SHA384_PSSZERO_RANDOMIZED, &zero).unwrap();
        assert!(PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, &zero).is_err());

        // Salt 32, SHA-256, and MGF1-SHA-512 do not match a SHA-384 salt-48 variant.
        let salt32 = der(
            "30820156304106092a864886f70d01010a3034a00f300d06096086480165030402020500a11c301a06092a864886f70d010108300d06096086480165030402020500a2030201200382010f003082010a028201010098a82428a4d968925a7c153b6277e6616327797b43f3f191a0d05961478fe6d3c0a40ba63e7a25ce06cd3da407f4cda9b7c614d41a1998501f1b5d0e5d9e8ed44e383de67e05d6e847dfa871adafb55d74fada77147b35c8c4b605fcc30de4cc3f00144906f1227781e624745891aad280fc5885e6300ab4197acc277307bc394bddb5972cfdb78f265f4ac27dd238c58dc76be6efa5e15705699e8309dcb5670cae2607aca7743d057b09ff696abfca871dbcbc1c25e7cd131276008379a6e555797691b24ac75891d8f1c7c9af644a0bbb0d11a0b9097fb58bb2e76f27b0851d01493f274cadd1dafc89f9b106ef86e699389466ff6cb6a12fb7cd143711190203010001",
        );
        let sha256 = der(
            "30820156304106092a864886f70d01010a3034a00f300d06096086480165030402010500a11c301a06092a864886f70d010108300d06096086480165030402010500a2030201300382010f003082010a0282010100db065e83dd316d9791578ca73ba82415de348b62fa4e70ea00823167c96be4537aac2adb58a7c4f3a072a31d008725821ccbbd371efb26c47dfa4f965470d3c0c0bca4fbbccf646f70cd03e8df2eed40cd2098ae96149dbfb73889f691ac82b11062cc2dc86308845aa0254e6d3a3fe4edd4be57f5773b234edbd26271130a0758033d1ea5189f64bcbe6226e99fd06d880e9ea9f30ae9b2eaeed48acf975ed82f405bf07ad8b32d7e8c7a952457b15fc375928390fe37fd4f51f5308bf97031cd638cdbaca7dc13f5f39f22e7fcef9a43262a131b2f805097da2832472fd1750c97f1f7d7e75ebf85ebd953fe0730ab197f3249909385b1b5531dc06864533d0203010001",
        );
        let mgf512 = der(
            "30820156304106092a864886f70d01010a3034a00f300d06096086480165030402020500a11c301a06092a864886f70d010108300d06096086480165030402030500a2030201300382010f003082010a0282010100d11d4ba5c30cd11f12e99def01deb04361cc7469360e28fa802e96c72e4f22e64b2bd78f8ce990667b1d47a59ec1cf0a4a4950d2ddf8a84ac6c37f7b51cdd432ef08ccab57698bd52a360d5f019d9cf435af0af31c815ba75ad5dbe14ce7b5f53b19fc314c90b5de41475ca49ff3e27de0df96845a752006cfbe54fe35936d09c8008ca136f05dbe7c09ec1ede27f1588bfb36874c22b57d2131b2b99852f231ff836db769b3275fda3ad37d49184f0832d574d55ac2c8c28ced1c9e25c28375b059ca784ce6b741274177218a38538ce1b4e004305179d7a4103bb9e4ea5f93f510c2bc774e54e78c7b05541a91b972a1e528a9c4bf62211cb8b7cdd2f7b72d0203010001",
        );
        for spki in [&salt32, &sha256, &mgf512] {
            assert!(PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, spki).is_err());
        }

        let dummy = Signature::from_bytes(&vec![1u8; key.key.modulus_len_bytes()]).unwrap();
        assert_eq!(
            key.blind(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, b"m").err(),
            Some(Error::Unsupported)
        );
        assert_eq!(
            key.verify(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, b"m", &dummy)
                .err(),
            Some(Error::Unsupported)
        );
        let zero_key = PublicKey::from_spki(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, &zero).unwrap();
        let dummy0 = Signature::from_bytes(&vec![1u8; zero_key.key.modulus_len_bytes()]).unwrap();
        assert_eq!(
            zero_key
                .blind(&RSABSSA_SHA384_PSS_DETERMINISTIC, b"m")
                .err(),
            Some(Error::Unsupported)
        );
        assert_eq!(
            zero_key
                .verify(&RSABSSA_SHA384_PSS_DETERMINISTIC, b"m", &dummy0)
                .err(),
            Some(Error::Unsupported)
        );
        assert_eq!(
            key.blind(&RSABSSA_SHA384_PSS_RANDOMIZED, b"m").err(),
            Some(Error::Unsupported)
        );
        key.blind(&RSABSSA_SHA384_PSS_DETERMINISTIC, &[0x5a; 2048])
            .unwrap();

        let exported = key.to_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC).unwrap();
        let loaded =
            PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, exported.as_ref()).unwrap();
        assert_eq!(
            loaded.components().unwrap().modulus(),
            key.components().unwrap().modulus()
        );
        assert_eq!(
            loaded.components().unwrap().exponent(),
            key.components().unwrap().exponent()
        );
        assert!(
            loaded
                .to_spki(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC)
                .is_err()
        );
        assert!(
            PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, &nested_spki(&pss)).is_err()
        );
        reject_malformed_pss(&pss);
    }

    /// OpenSSL `RSA-PSS` SPKI, SHA-384, MGF1-SHA-384, salt 48.
    fn openssl_pss_spki() -> Vec<u8> {
        hex::decode("30820156304106092a864886f70d01010a3034a00f300d06096086480165030402020500a11c301a06092a864886f70d010108300d06096086480165030402020500a2030201300382010f003082010a02820101009e289eb2008fd6f7c68fa7653e27a63ed0c8f79d69185aaa48f7498f8257718237a8cb65eaa2ae401747d9197e82ce98212e9992104a2309de21ec1725727d03f9dcb03440f5c7c1b31dbbd3fe78fe427fef216d034766d85c1483faa946630eb62199e7125532fce10405a3bdd5cf4708cbe8d73045e64e3de5d80c2af25850039718799b02f5af27772307523b2b436f080f6bbc89b42160f658df733baa51a3e543d8a15e638d80f38032e2232ebb3dd920bd2dbec61bf04c9a740c24e9c443e700729a06df3644250e0dc367cd76696753d22406849c7ff9a2c1a67f4f38a89a014fbfa8e287a56e98148907359d4f70bd08b1589b5d0721e03f2f0325690203010001").unwrap()
    }

    /// `from_spki` takes `SubjectPublicKeyInfo`. A PKCS#1 `RSAPublicKey` is not one.
    #[test]
    fn rejects_a_bare_pkcs1_key() {
        let key =
            PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, &openssl_pss_spki()).unwrap();
        let mut pkcs1_buf = [0u8; crate::high::rsa::MAX_PUBLIC_KEY_LEN];
        let pkcs1 = key.key.to_pkcs1_der(&mut pkcs1_buf).unwrap();
        assert!(PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, pkcs1).is_err());

        // An RSA SPKI is the PKCS#1 key plus its algorithm identifier.
        let mut spki_buf = [0u8; crate::high::rsa::MAX_PUBLIC_KEY_LEN + 32];
        let spki = key.key.to_spki_der(&mut spki_buf).unwrap();
        let loaded = PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, spki).unwrap();
        assert!(loaded.salt.is_none());
    }

    /// The BIT STRING of a valid SPKI, replaced by that SPKI. PKCS#1 decoding
    /// refuses the nested `SubjectPublicKeyInfo`.
    fn nested_spki(spki: &[u8]) -> Vec<u8> {
        assert_eq!(&spki[..4], &[0x30, 0x82, 0x01, 0x56]);
        let alg = &spki[4..4 + 67];
        assert_eq!(alg[0], 0x30);
        let mut bits = Vec::new();
        bits.push(0x03);
        let body = spki.len() + 1;
        bits.push(0x82);
        bits.push((body >> 8) as u8);
        bits.push(body as u8);
        bits.push(0x00);
        bits.extend(spki);
        let total = alg.len() + bits.len();
        let mut out = vec![0x30, 0x82, (total >> 8) as u8, total as u8];
        out.extend(alg);
        out.extend(bits);
        out
    }

    fn reject_malformed_pss(spki: &[u8]) {
        let algorithm = &RSABSSA_SHA384_PSS_DETERMINISTIC;
        assert!(PublicKey::from_spki(algorithm, &spki[..spki.len() - 8]).is_err());
        let mut indefinite = spki.to_vec();
        // The hash context's short length becomes the indefinite-length octet.
        let hash = indefinite
            .windows(2)
            .position(|w| w == [0xa0, 0x0f])
            .unwrap();
        indefinite[hash + 1] = 0x80;
        assert!(PublicKey::from_spki(algorithm, &indefinite).is_err());

        let mut long_form = spki.to_vec();
        long_form[hash + 1] = 0x81;
        long_form.insert(hash + 2, 0x0f);
        assert!(PublicKey::from_spki(algorithm, &long_form).is_err());

        let mut high_tag = spki.to_vec();
        high_tag[hash] = 0xbf;
        assert!(PublicKey::from_spki(algorithm, &high_tag).is_err());

        let mut duplicate = spki.to_vec();
        let field = &spki[hash..hash + 2 + 0x0f];
        duplicate.splice(hash..hash, field.iter().copied());
        assert!(PublicKey::from_spki(algorithm, &duplicate).is_err());

        let mut unknown = spki.to_vec();
        unknown[hash] = 0xa4;
        assert!(PublicKey::from_spki(algorithm, &unknown).is_err());

        // salt INTEGER 48, `02 01 30`, written with a leading zero.
        let salt = spki
            .windows(4)
            .position(|w| w == [0x02, 0x01, 0x30, 0x03])
            .unwrap();
        let mut overlong = spki.to_vec();
        overlong.splice(salt..salt + 3, [0x02, 0x02, 0x00, 0x30]);
        assert!(PublicKey::from_spki(algorithm, &overlong).is_err());

        // Trailer DEFAULT 1, encoded explicitly after the salt.
        let mut trailer = spki.to_vec();
        let after_salt = salt + 3;
        trailer.splice(after_salt..after_salt, [0xa3, 0x03, 0x02, 0x01, 0x01]);
        assert!(PublicKey::from_spki(algorithm, &trailer).is_err());

        // Salt, then the hash: same length, so only the order changed.
        let hash_end = hash + 2 + 0x0f;
        let salt_start = salt - 2;
        let salt_end = salt + 3;
        assert_eq!(&spki[salt_start..salt_start + 2], &[0xa2, 0x03]);
        let hash_tlv = spki[hash..hash_end].to_vec();
        let middle = spki[hash_end..salt_start].to_vec();
        let salt_tlv = spki[salt_start..salt_end].to_vec();
        let mut ordered = spki.to_vec();
        ordered.splice(
            hash..salt_end,
            salt_tlv.iter().chain(&middle).chain(&hash_tlv).copied(),
        );
        assert_eq!(ordered.len(), spki.len());
        assert!(PublicKey::from_spki(algorithm, &ordered).is_err());

        // No parameters: the algorithm is the OID and a NULL.
        let mut absent = spki.to_vec();
        let params_at = absent.windows(2).position(|w| w == [0x30, 0x34]).unwrap();
        absent.splice(params_at..params_at + 2 + 0x34, [0x05, 0x00]);
        assert!(PublicKey::from_spki(algorithm, &absent).is_err());

        let mut trailing = spki.to_vec();
        trailing.push(0x00);
        assert!(PublicKey::from_spki(algorithm, &trailing).is_err());
    }

    #[test]
    #[cfg(not(miri))]
    fn blind_sign_and_finalize_reject_bad_integers() {
        let first = KeyPair::generate(crate::rsa::KeySize::Rsa2048).unwrap();
        let second = KeyPair::generate(crate::rsa::KeySize::Rsa2048).unwrap();
        let public = first.public_key();
        let k = public.key.modulus_len_bytes();
        let blinded = |bytes: &[u8]| BlindedMessage::from_bytes(bytes).unwrap();
        assert!(BlindedMessage::from_bytes(&[]).is_err());
        assert_eq!(
            first.blind_sign(&blinded(&[0u8; 1])).err(),
            Some(Error::WrongLength)
        );
        assert_eq!(
            first.blind_sign(&blinded(&vec![0u8; k + 1])).err(),
            Some(Error::WrongLength)
        );
        assert!(first.blind_sign(&blinded(&vec![0u8; k])).is_ok());

        let parts = public.components().unwrap();
        let modulus = parts.modulus();
        let mut n = vec![0u8; k];
        n[k - modulus.len()..].copy_from_slice(modulus);
        assert_eq!(
            first.blind_sign(&blinded(&n)).err(),
            Some(Error::WrongLength)
        );
        let mut bigger = n.clone();
        bigger[0] = bigger[0].saturating_add(1);
        assert_eq!(
            first.blind_sign(&blinded(&bigger)).err(),
            Some(Error::WrongLength)
        );

        let algorithm = &RSABSSA_SHA384_PSS_DETERMINISTIC;
        let (message, blinding) = public.blind(algorithm, b"token").unwrap();
        let foreign = second.blind_sign(&message).unwrap();
        assert_eq!(blinding.finalize(&foreign).err(), Some(Error::BadSignature));
        let (_, blinding) = public.blind(algorithm, b"token").unwrap();
        assert_eq!(
            blinding
                .finalize(&BlindSignature::from_bytes(&n).unwrap())
                .err(),
            Some(Error::BadSignature)
        );
    }

    /// A 2049-bit modulus drops one octet when the encoded message is
    /// written at `emLen`. RFC 8017's I2OSP refuses that octet unless it is
    /// zero. `e = 3`, so `0x01 || EM` is a signature of a valid encoding.
    #[test]
    fn rejects_nonzero_octet_above_em_len() {
        let n = hex::decode("01d543aff201e1b06b8b7654bcbe732431a08c76b17e57713356339f2864538fa57e91c489d8289d50aaf76419fe44df8013b3f520aaf7b5af6349dbf7efa722b0c38a7ef90cc658015712c8f67cbbd9a3770d06e9cf9eec8939af8c9ee88d8d00928b3297f49d57a2ec4b2b07e715793baeee41e5f95f831db2ae1a4635a744ed5d5bf8bff72a1c058e9350ae00dbb8b432da6abbb421bd2773818a0f5f7b93637d2b472a2dd4bf7298277f818bcbc8f0d6c458afa644161e96931c6b797bd9a7344c8c24d22062cb688dbd5a01ec9fbc37f50349a10112c5e4fd8da8a5b4a1c82bb488bfc61ca756fa6bcb72bae2996d848b882036c16cef00ea1920f13c5ab7").unwrap();
        let signing = SigningKey::from_components(
            &hex::decode("01d92300d6c7d773fcad94c7f69041aa28475d2d5197926dcd0bf4ed28a42c3e6e425d4f00a804d3a9a5cfd904e3781ed704e6bdfc7a804a02ce70658d55836604a7a1f191dee966cafb5958fbbe05876dfb5e2de7f11f0fec05014b5a9a1baf22d6a988cf0eaa7088f89c4f5881b091281280d2166a6414eca297356081fdf8b9").unwrap(),
            &hex::decode("00fde7a0fc32a43bc513cabf82eb570f7f361027fdfb28bca6fb66dc19a8759b3b40d6255e4e10c51a08727eb79f85315621cb902eb022ebde759bde6a85a47cd06642a66ceea9020417d0c5ab3fa8393fee0094660dfb05b375d13cf1c6a46b908b6a38d9010fd87095989acb179863f3a80df74a814b6a684edad9a020ab56ef").unwrap(),
            &hex::decode("0138d7caa15696759d07a4387dd44cc2cbc05da476543a4b778ecd14c59837b518ff0bd85be57068e071fa42bbfed895000d22a36b1ca523ca42313d4ff51a1720825c54a608843aab8f61db4efdd29117a4b359f135149db0d11fb3149b0908ab0c5ccc654dbe3a6c9d87720544b8fb7d1f498143fb950213cc74118423c4d89c598b8f48a874482d3377db7858d754b3239e0e48164461ccf2c3d5de0c91267bfbfa8c877a7f6f1f4698c52e05defb2d200c0702fd15ead38c59e5a2698d4f36c4454d6eadb3fbfd8e4269ccad7f3f5edf0ed5fd1699fe199c1cae3d834daf633115da0fceec3ee8f2cf40df6bbbc2e1315329d4dcb69e66b4fab16adf0cb20b").unwrap(),
            &n,
            3,
        )
        .unwrap();
        let public = PublicKey {
            key: signing.public_key(),
            salt: None,
        };
        assert_eq!(public.key.modulus_len_bits() % 8, 1);
        let algorithm = &RSABSSA_SHA384_PSS_DETERMINISTIC;
        let message = b"2049-bit modulus";
        let hash = PreparedBytes {
            prefix: &[],
            message,
        }
        .hash();
        let em_bits = public.key.modulus_len_bits() - 1;
        let em_len = em_bits.div_ceil(8);
        let k = public.key.modulus_len_bytes();
        assert_eq!(k, em_len + 1);
        let low = &n[k - em_len..];

        let mut witnessed = false;
        for salt_byte in 0..=255 {
            let salt = [salt_byte; 48];
            let mut em = [0u8; MAX_MODULUS];
            pkcs1::encode_pss_sig::<hash::Sha384>(
                &mut em[..em_len],
                em_bits,
                &mut SaltBytes(&salt),
                hash.as_ref(),
                algorithm.salt_len(),
            )
            .unwrap();
            if &em[..em_len] >= low {
                continue;
            }
            let mut encoded = vec![0u8; k];
            encoded[k - em_len..].copy_from_slice(&em[..em_len]);
            let mut lifted = encoded.clone();
            lifted[0] = 0x01;

            let mut out = [0u8; MAX_MODULUS];
            let good_bytes = signing.blind_sign(&encoded, &mut out).unwrap().to_vec();
            let mut out = [0u8; MAX_MODULUS];
            let bad_bytes = signing.blind_sign(&lifted, &mut out).unwrap().to_vec();
            let good = Signature::from_bytes(&good_bytes).unwrap();
            let bad = Signature::from_bytes(&bad_bytes).unwrap();
            public.verify(algorithm, message, &good).unwrap();
            assert!(
                public.verify(algorithm, message, &bad).is_err(),
                "public verification accepted 0x01 || EM"
            );

            let mut inverse = [0u8; MAX_MODULUS];
            inverse[k - 1] = 1;
            let mut digest = [0u8; 48];
            digest.copy_from_slice(hash.as_ref());
            let blinding = || Blinding {
                key: public.key.clone(),
                inverse,
                digest,
                kind: algorithm.kind,
            };
            assert!(
                blinding()
                    .finalize(&BlindSignature::from_bytes(&bad_bytes).unwrap())
                    .is_err(),
                "finalize accepted 0x01 || EM"
            );
            blinding()
                .finalize(&BlindSignature::from_bytes(&good_bytes).unwrap())
                .unwrap();
            witnessed = true;
            break;
        }
        assert!(witnessed, "no encoded message sat under the spare octet");
    }

    #[test]
    fn rejects_the_wrong_variant_and_a_long_message() {
        assert_eq!(
            PublicKey::prepared(&RSABSSA_SHA384_PSS_DETERMINISTIC, &[0; 32], b"m").err(),
            Some(Error::Unsupported)
        );
        assert_eq!(
            PublicKey::prepared(&RSABSSA_SHA384_PSS_RANDOMIZED, &[0; 16], b"m").err(),
            Some(Error::WrongLength)
        );
        assert!(PublicKey::prepared(&RSABSSA_SHA384_PSS_RANDOMIZED, &[0; 32], &[0; 4096]).is_ok());
    }

    #[test]
    #[cfg(not(miri))]
    fn rfc9474() {
        let vectors: Vec<serde_json::Value> =
            serde_json::from_str(include_str!("../../tests/rfc9474.json")).unwrap();
        assert_eq!(vectors.len(), 4);
        for vector in vectors {
            let algorithm = match vector["name"].as_str().unwrap() {
                "RSABSSA-SHA384-PSS-Randomized" => &RSABSSA_SHA384_PSS_RANDOMIZED,
                "RSABSSA-SHA384-PSSZERO-Randomized" => &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
                "RSABSSA-SHA384-PSS-Deterministic" => &RSABSSA_SHA384_PSS_DETERMINISTIC,
                "RSABSSA-SHA384-PSSZERO-Deterministic" => &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
                other => panic!("unexpected variant {other}"),
            };
            let number = |name: &str| {
                let text = vector[name].as_str().unwrap();
                let text = text.strip_prefix("0x").unwrap_or(text);
                hex::decode(text).unwrap()
            };
            let signing = SigningKey::from_components(
                &number("p"),
                &number("q"),
                &number("d"),
                &number("n"),
                u64::from_be_bytes([0, 0, 0, 0, 0, 0x01, 0x00, 0x01]),
            )
            .unwrap();
            let mut pkcs8 = [0u8; crate::high::rsa::MAX_PKCS8_LEN];
            let pkcs8 = signing.to_pkcs8_der(&mut pkcs8).unwrap();
            let pair = KeyPair::from_pkcs8(pkcs8).unwrap();
            let public = pair.public_key();
            let msg = number("msg");
            let prefix = number("msg_prefix");
            let salt = number("salt");
            let inverse = number("inv");
            let (blinded, blinding) =
                blind_fixed(&public, algorithm, &prefix, &msg, &salt, &inverse).unwrap();
            if let Some(encoded) = vector["encoded_msg"].as_str() {
                let encoded = hex::decode(encoded).unwrap();
                let mut em = [0u8; MAX_MODULUS];
                let em_bits = public.key.modulus_len_bits() - 1;
                let em_len = em_bits.div_ceil(8);
                let hash = PreparedBytes {
                    prefix: &prefix,
                    message: &msg,
                }
                .hash();
                pkcs1::encode_pss_sig::<hash::Sha384>(
                    &mut em[..em_len],
                    em_bits,
                    &mut SaltBytes(&salt),
                    hash.as_ref(),
                    algorithm.salt_len(),
                )
                .unwrap();
                assert_eq!(&em[..em_len], encoded.as_slice(), "{:?}", algorithm.kind);
            }
            assert_eq!(blinded.as_ref(), number("blinded_msg").as_slice());
            let blind_sig = pair.blind_sign(&blinded).unwrap();
            assert_eq!(blind_sig.as_ref(), number("blind_sig").as_slice());
            let signature = blinding.finalize(&blind_sig).unwrap();
            assert_eq!(signature.as_ref(), number("sig").as_slice());
            if algorithm.randomized() {
                let prepared = PublicKey::prepared(algorithm, &prefix, &msg).unwrap();
                public.verify_prepared(&prepared, &signature).unwrap();
                assert_eq!(
                    public.verify(algorithm, &msg, &signature).err(),
                    Some(Error::Unsupported)
                );
            } else {
                public.verify(algorithm, &msg, &signature).unwrap();
            }
        }
    }

    #[test]
    #[cfg(not(miri))]
    fn wycheproof_pss_sha384() {
        #[derive(serde::Deserialize)]
        struct File {
            #[serde(rename = "testGroups")]
            groups: Vec<Group>,
        }
        #[derive(serde::Deserialize)]
        struct Group {
            #[serde(rename = "publicKeyDer", with = "hex::serde")]
            public_key_der: Vec<u8>,
            sha: String,
            #[serde(rename = "mgfSha")]
            mgf_sha: String,
            #[serde(rename = "sLen")]
            salt_len: usize,
            tests: Vec<Case>,
        }
        #[derive(serde::Deserialize)]
        struct Case {
            #[serde(with = "hex::serde")]
            msg: Vec<u8>,
            #[serde(with = "hex::serde")]
            sig: Vec<u8>,
            result: String,
        }

        for file in [
            include_str!(
                "../../../thirdparty/wycheproof/testvectors_v1/rsa_pss_2048_sha384_mgf1_48_test.json"
            ),
            include_str!(
                "../../../thirdparty/wycheproof/testvectors_v1/rsa_pss_4096_sha384_mgf1_48_test.json"
            ),
        ] {
            let file: File = serde_json::from_str(file).unwrap();
            assert!(!file.groups.is_empty());
            for group in file.groups {
                assert_eq!(group.sha, "SHA-384");
                assert_eq!(group.mgf_sha, "SHA-384");
                assert_eq!(group.salt_len, 48);
                let key =
                    PublicKey::from_spki(&RSABSSA_SHA384_PSS_DETERMINISTIC, &group.public_key_der)
                        .unwrap();
                for case in group.tests {
                    let signature = match Signature::from_bytes(&case.sig) {
                        Ok(signature) => signature,
                        Err(Error::WrongLength) => {
                            assert_ne!(case.result, "valid");
                            continue;
                        }
                        Err(error) => panic!("{error:?}"),
                    };
                    let result =
                        key.verify(&RSABSSA_SHA384_PSS_DETERMINISTIC, &case.msg, &signature);
                    match case.result.as_str() {
                        "valid" => result.unwrap(),
                        "invalid" | "acceptable" => {
                            assert_eq!(result.err(), Some(Error::BadSignature));
                        }
                        other => panic!("unexpected result {other}"),
                    }
                }
            }
        }
    }

    #[test]
    #[cfg(not(miri))]
    fn matches_blind_rsa_signatures() {
        use blind_rsa_signatures::{
            DefaultRng, Deterministic, KeyPair as TheirKey, MessageRandomizer, PSS, PSSZero,
            Randomized, SecretKey as TheirSecret, Sha384,
        };

        let mut rng = DefaultRng;
        let generated = TheirKey::<Sha384, PSS, Deterministic>::generate(&mut rng, 2048).unwrap();
        let pkcs8 = generated.sk.to_der().unwrap();
        let ours = KeyPair::from_pkcs8(&pkcs8).unwrap();
        let public = ours.public_key();
        let message = b"blind rsa differential";

        // Deterministic PSS.
        {
            let sk = TheirSecret::<Sha384, PSS, Deterministic>::from_der(&pkcs8).unwrap();
            let pk = sk.public_key().unwrap();
            let (blinded, blinding) = public
                .blind(&RSABSSA_SHA384_PSS_DETERMINISTIC, message)
                .unwrap();
            let their_sig = sk
                .blind_sign(blind_rsa_signatures::BlindMessage(
                    blinded.as_ref().to_vec(),
                ))
                .unwrap();
            let signature = blinding
                .finalize(&BlindSignature::from_bytes(their_sig.as_ref()).unwrap())
                .unwrap();
            pk.verify(
                &blind_rsa_signatures::Signature(signature.as_ref().to_vec()),
                None,
                message.as_slice(),
            )
            .unwrap();

            let mut rng = DefaultRng;
            let theirs = pk.blind(&mut rng, message.as_slice()).unwrap();
            let blind_sig = ours
                .blind_sign(&BlindedMessage::from_bytes(theirs.blind_message.as_ref()).unwrap())
                .unwrap();
            let their_final = pk
                .finalize(
                    &blind_rsa_signatures::BlindSignature(blind_sig.as_ref().to_vec()),
                    &theirs,
                    message.as_slice(),
                )
                .unwrap();
            public
                .verify(
                    &RSABSSA_SHA384_PSS_DETERMINISTIC,
                    message,
                    &Signature::from_bytes(their_final.as_ref()).unwrap(),
                )
                .unwrap();
        }

        // Deterministic PSSZERO.
        {
            let sk = TheirSecret::<Sha384, PSSZero, Deterministic>::from_der(&pkcs8).unwrap();
            let pk = sk.public_key().unwrap();
            let (blinded, blinding) = public
                .blind(&RSABSSA_SHA384_PSSZERO_DETERMINISTIC, message)
                .unwrap();
            let their_sig = sk
                .blind_sign(blind_rsa_signatures::BlindMessage(
                    blinded.as_ref().to_vec(),
                ))
                .unwrap();
            let signature = blinding
                .finalize(&BlindSignature::from_bytes(their_sig.as_ref()).unwrap())
                .unwrap();
            pk.verify(
                &blind_rsa_signatures::Signature(signature.as_ref().to_vec()),
                None,
                message.as_slice(),
            )
            .unwrap();
        }

        // Randomized PSS. The prefix travels with the prepared message.
        {
            let sk = TheirSecret::<Sha384, PSS, Randomized>::from_der(&pkcs8).unwrap();
            let pk = sk.public_key().unwrap();
            let prepared = public
                .prepare(&RSABSSA_SHA384_PSS_RANDOMIZED, message)
                .unwrap();
            let (blinded, blinding) = public.blind_prepared(&prepared).unwrap();
            let their_sig = sk
                .blind_sign(blind_rsa_signatures::BlindMessage(
                    blinded.as_ref().to_vec(),
                ))
                .unwrap();
            let signature = blinding
                .finalize(&BlindSignature::from_bytes(their_sig.as_ref()).unwrap())
                .unwrap();
            pk.verify(
                &blind_rsa_signatures::Signature(signature.as_ref().to_vec()),
                Some(MessageRandomizer(*prepared.prefix())),
                message.as_slice(),
            )
            .unwrap();
            public.verify_prepared(&prepared, &signature).unwrap();
        }

        // Randomized PSSZERO, their blinding, our signature.
        {
            let sk = TheirSecret::<Sha384, PSSZero, Randomized>::from_der(&pkcs8).unwrap();
            let pk = sk.public_key().unwrap();
            let mut rng = DefaultRng;
            let theirs = pk.blind(&mut rng, message.as_slice()).unwrap();
            let blind_sig = ours
                .blind_sign(&BlindedMessage::from_bytes(theirs.blind_message.as_ref()).unwrap())
                .unwrap();
            let their_final = pk
                .finalize(
                    &blind_rsa_signatures::BlindSignature(blind_sig.as_ref().to_vec()),
                    &theirs,
                    message.as_slice(),
                )
                .unwrap();
            let prepared = PublicKey::prepared(
                &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
                &theirs.msg_randomizer.unwrap().0,
                message,
            )
            .unwrap();
            // The signature is PSSZERO. The salt-48 variant must reject it.
            verify_message(
                &public.key,
                &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
                prepared.prefix(),
                message,
                their_final.as_ref(),
            )
            .unwrap();
            assert!(
                verify_message(
                    &public.key,
                    &RSABSSA_SHA384_PSS_RANDOMIZED,
                    prepared.prefix(),
                    message,
                    their_final.as_ref(),
                )
                .is_err()
            );
        }
    }

    #[test]
    fn secrets_stay_secret() {
        // A 2048-bit exchange. The message, the blinding factor, and the
        // private key are secret until the signature is declassified.
        let mut rng = SystemRandom;
        let signing = SigningKey::generate(crate::mid::rsa_key_size::RsaKeySize::Rsa2048).unwrap();
        let mut pkcs8 = [0u8; crate::high::rsa::MAX_PKCS8_LEN];
        let pkcs8 = signing.to_pkcs8_der(&mut pkcs8).unwrap();
        // The private scalars are marked when the key is loaded. The DER's
        // lengths and algorithm identifier stay public.
        let pair = KeyPair::from_pkcs8(pkcs8).unwrap();
        let public = pair.public_key();
        let mut message = [0u8; 48];
        rng.fill(&mut message).unwrap();
        ct::secret_slice(&message);
        let prepared = public
            .prepare(&RSABSSA_SHA384_PSS_DETERMINISTIC, &message)
            .unwrap_err();
        assert_eq!(prepared, Error::Unsupported);
        let (blinded, blinding) = public
            .blind(&RSABSSA_SHA384_PSS_DETERMINISTIC, &message)
            .unwrap();
        ct::public_slice(blinded.as_ref());
        let blind_sig = pair.blind_sign(&blinded).unwrap();
        ct::public_slice(blind_sig.as_ref());
        let signature = blinding.finalize(&blind_sig).unwrap();
        ct::public_slice(signature.as_ref());
        public
            .verify(&RSABSSA_SHA384_PSS_DETERMINISTIC, &message, &signature)
            .unwrap();

        let prepared = public
            .prepare(&RSABSSA_SHA384_PSS_RANDOMIZED, &message)
            .unwrap();
        // The prefix is public once `prefix` returns it: a verifier may
        // branch on those bytes. Leaving them secret makes that a ctgrind
        // false positive.
        let mut branched = 0u8;
        for byte in prepared.prefix() {
            if core::hint::black_box(*byte) == 0 {
                branched = core::hint::black_box(branched.wrapping_add(1));
            }
        }
        core::hint::black_box(branched);
        let (blinded, blinding) = public.blind_prepared(&prepared).unwrap();
        ct::public_slice(blinded.as_ref());
        let blind_sig = pair.blind_sign(&blinded).unwrap();
        let signature = blinding.finalize(&blind_sig).unwrap();
        ct::public_slice(signature.as_ref());
        public.verify_prepared(&prepared, &signature).unwrap();
    }
}
