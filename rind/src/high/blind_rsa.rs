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

/// The longest message [`PublicKey::blind`] or [`PublicKey::prepare`] takes.
pub const MAX_MESSAGE: usize = 1024;

const PREFIX_LEN: usize = 32;
const SHA384_LEN: u16 = 48;
const MAX_MODULUS: usize = rsa_pub::MAX_PUBLIC_MODULUS_BYTES;

/// One RSABSSA-SHA384 variant. Only this module's constants build one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Algorithm {
    salt_len: u16,
    randomized: bool,
}

impl Algorithm {
    fn salt_len(self) -> usize {
        usize::from(self.salt_len)
    }

    fn kind(self) -> u8 {
        match (self.randomized, self.salt_len) {
            (true, SHA384_LEN) => 0,
            (true, 0) => 1,
            (false, SHA384_LEN) => 2,
            (false, 0) => 3,
            // The constants are the only constructors.
            _ => 0,
        }
    }

    fn from_kind(kind: u8) -> Self {
        match kind {
            1 => RSABSSA_SHA384_PSSZERO_RANDOMIZED,
            2 => RSABSSA_SHA384_PSS_DETERMINISTIC,
            3 => RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
            _ => RSABSSA_SHA384_PSS_RANDOMIZED,
        }
    }
}

/// RSABSSA-SHA384-PSS-Randomized. The signed message is 32 random bytes
/// followed by the caller's message, and the PSS salt is 48 bytes.
pub static RSABSSA_SHA384_PSS_RANDOMIZED: Algorithm = Algorithm {
    salt_len: SHA384_LEN,
    randomized: true,
};

/// RSABSSA-SHA384-PSSZERO-Randomized. Same preparation, with an empty PSS salt.
pub static RSABSSA_SHA384_PSSZERO_RANDOMIZED: Algorithm = Algorithm {
    salt_len: 0,
    randomized: true,
};

/// RSABSSA-SHA384-PSS-Deterministic. The message is signed as given, with a
/// 48-byte PSS salt. Privacy Pass tokens (RFC 9578 type `0x0002`) use this
/// with a 2048-bit key.
pub static RSABSSA_SHA384_PSS_DETERMINISTIC: Algorithm = Algorithm {
    salt_len: SHA384_LEN,
    randomized: false,
};

/// RSABSSA-SHA384-PSSZERO-Deterministic. The message is signed as given, with
/// an empty PSS salt.
pub static RSABSSA_SHA384_PSSZERO_DETERMINISTIC: Algorithm = Algorithm {
    salt_len: 0,
    randomized: false,
};

/// A message prepared for a randomized variant: 32 random bytes, then the
/// message. Verification takes this type, so the unprepared message is not
/// a signature input.
pub struct PreparedMessage {
    prefix: [u8; PREFIX_LEN],
    message: [u8; MAX_MESSAGE],
    message_len: u16,
    kind: u8,
}

impl PreparedMessage {
    /// The 32-byte prefix.
    pub fn prefix(&self) -> &[u8; PREFIX_LEN] {
        &self.prefix
    }

    /// The caller's message.
    pub fn message(&self) -> &[u8] {
        &self.message[..usize::from(self.message_len)]
    }
}

impl fmt::Debug for PreparedMessage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PreparedMessage")
            .field("message_len", &self.message_len)
            .finish_non_exhaustive()
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
#[derive(Clone)]
pub struct PublicKey {
    key: VerifyingKey,
}

impl PublicKey {
    /// Decodes an RSA public key from `SubjectPublicKeyInfo` DER.
    pub fn from_spki(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: VerifyingKey::from_der(bytes)?,
        })
    }

    /// Loads an RSA public key from its big-endian modulus and exponent.
    pub fn from_components(n: &[u8], e: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: VerifyingKey::from_components(n, e)?,
        })
    }

    /// Prepares `message` for a randomized variant.
    ///
    /// Fails with [`Error::Unsupported`] for a deterministic variant, and
    /// with [`Error::WrongLength`] when `message` is longer than
    /// [`MAX_MESSAGE`].
    pub fn prepare(
        &self,
        algorithm: &'static Algorithm,
        message: &[u8],
    ) -> Result<PreparedMessage, Error> {
        let _entry = Entry::new_public();
        if !algorithm.randomized {
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
    /// [`Error::WrongLength`] when `prefix` is not 32 bytes or `message`
    /// is longer than [`MAX_MESSAGE`].
    pub fn prepared(
        algorithm: &'static Algorithm,
        prefix: &[u8],
        message: &[u8],
    ) -> Result<PreparedMessage, Error> {
        if !algorithm.randomized || prefix.len() != PREFIX_LEN {
            return Err(if prefix.len() == PREFIX_LEN {
                Error::Unsupported
            } else {
                Error::WrongLength
            });
        }
        if message.len() > MAX_MESSAGE {
            return Err(Error::WrongLength);
        }
        let mut stored = [0u8; MAX_MESSAGE];
        stored[..message.len()].copy_from_slice(message);
        let mut prefix_bytes = [0u8; PREFIX_LEN];
        prefix_bytes.copy_from_slice(prefix);
        Ok(PreparedMessage {
            prefix: prefix_bytes,
            message: stored,
            message_len: message.len() as u16,
            kind: algorithm.kind(),
        })
    }

    /// Blinds a deterministic variant's message.
    ///
    /// Fails with [`Error::Unsupported`] for a randomized variant, or when
    /// the PSS encoding shares a factor with the modulus. A message longer
    /// than [`MAX_MESSAGE`] is [`Error::WrongLength`].
    pub fn blind(
        &self,
        algorithm: &'static Algorithm,
        message: &[u8],
    ) -> Result<(BlindedMessage, Blinding), Error> {
        if algorithm.randomized {
            return Err(Error::Unsupported);
        }
        if message.len() > MAX_MESSAGE {
            return Err(Error::WrongLength);
        }
        blind_message(&self.key, algorithm, &[], message, None, None)
    }

    /// Blinds a [`PreparedMessage`].
    pub fn blind_prepared(
        &self,
        message: &PreparedMessage,
    ) -> Result<(BlindedMessage, Blinding), Error> {
        let algorithm = Algorithm::from_kind(message.kind);
        blind_message(
            &self.key,
            algorithm_static(algorithm),
            message.prefix(),
            message.message(),
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
        if algorithm.randomized {
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
        verify_message(
            &self.key,
            algorithm_static(Algorithm::from_kind(message.kind)),
            message.prefix(),
            message.message(),
            signature.as_ref(),
        )
    }
}

fn algorithm_static(algorithm: Algorithm) -> &'static Algorithm {
    match algorithm.kind() {
        1 => &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
        2 => &RSABSSA_SHA384_PSS_DETERMINISTIC,
        3 => &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
        _ => &RSABSSA_SHA384_PSS_RANDOMIZED,
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

/// The client's secret blinding factor and the message it covers.
///
/// [`Self::finalize`] consumes it and checks the signature before returning
/// one. Drop wipes it under `wipe`.
pub struct Blinding {
    key: VerifyingKey,
    inverse: [u8; MAX_MODULUS],
    inverse_len: u16,
    prefix: [u8; PREFIX_LEN],
    prefix_len: u8,
    message: [u8; MAX_MESSAGE],
    message_len: u16,
    kind: u8,
}

impl Blinding {
    /// Turns `blind_signature` into a verified RSASSA-PSS signature.
    ///
    /// Fails with [`Error::BadSignature`] when the signature does not
    /// unblind to this message, and with [`Error::WrongLength`] when it is
    /// not the modulus length.
    pub fn finalize(self, blind_signature: &BlindSignature) -> Result<Signature, Error> {
        let _entry = Entry::new_secret();
        let k = self.key.modulus_len_bytes();
        if blind_signature.as_ref().len() != k || usize::from(self.inverse_len) != k {
            return Err(Error::WrongLength);
        }
        let mut signature = [0u8; MAX_MODULUS];
        self.key
            .mul_mod_be(blind_signature.as_ref(), &self.inverse[..k], &mut signature)?;
        ct::secret_slice(&signature[..k]);
        let algorithm = Algorithm::from_kind(self.kind);
        let verdict = verify_secret(
            &self.key,
            algorithm,
            &self.prefix[..usize::from(self.prefix_len)],
            &self.message[..usize::from(self.message_len)],
            &signature[..k],
        )?;
        if !ct::into_public(verdict) {
            return Err(Error::BadSignature);
        }
        ct::public_slice(&signature[..k]);
        Ok(Signature {
            bytes: signature,
            len: self.inverse_len,
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
        Ok(Self {
            key: SigningKey::generate(size)?,
        })
    }

    /// Decodes a two-prime RSA key from PKCS#8 DER.
    pub fn from_pkcs8(bytes: &[u8]) -> Result<Self, Error> {
        Ok(Self {
            key: SigningKey::from_pkcs8_der(bytes)?,
        })
    }

    /// Signs `blinded`. The signature is an ordinary RSA private operation,
    /// checked against the public key.
    pub fn blind_sign(&self, blinded: &BlindedMessage) -> Result<BlindSignature, Error> {
        let mut out = [0u8; MAX_MODULUS];
        let signed = self.key.blind_sign(blinded.as_ref(), &mut out)?;
        let len = signed.len();
        Ok(BlindSignature {
            bytes: out,
            len: len as u16,
        })
    }

    /// The public key.
    pub fn public_key(&self) -> PublicKey {
        PublicKey {
            key: self.key.public_key(),
        }
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
    prefix: &[u8],
    message: &[u8],
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
    for _ in 0..attempts {
        let hash = PreparedBytes { prefix, message }.hash();
        match salt {
            Some(salt) => {
                pkcs1::encode_pss_sig::<hash::Sha384>(
                    &mut em[..em_len],
                    em_bits,
                    &mut SaltBytes(salt),
                    hash.as_ref(),
                    algorithm.salt_len(),
                )?;
            }
            None => {
                pkcs1::encode_pss_sig::<hash::Sha384>(
                    &mut em[..em_len],
                    em_bits,
                    &mut SystemRandom,
                    hash.as_ref(),
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
                key.invert_be(&factor[..k], &mut inv)?;
            }
        }
        ct::secret_slice(&factor[..k]);
        let mut powered = [0u8; MAX_MODULUS];
        key.public_op_be(&factor[..k], &mut powered)?;
        ct::secret_slice(&powered[..k]);
        let mut blinded = [0u8; MAX_MODULUS];
        key.mul_mod_be(&encoded[..k], &powered[..k], &mut blinded)?;
        ct::public_slice(&blinded[..k]);

        let mut stored_prefix = [0u8; PREFIX_LEN];
        stored_prefix[..prefix.len()].copy_from_slice(prefix);
        let mut stored_message = [0u8; MAX_MESSAGE];
        stored_message[..message.len()].copy_from_slice(message);
        return Ok((
            BlindedMessage {
                bytes: blinded,
                len: k as u16,
            },
            Blinding {
                key: key.clone(),
                inverse: inv,
                inverse_len: k as u16,
                prefix: stored_prefix,
                prefix_len: prefix.len() as u8,
                message: stored_message,
                message_len: message.len() as u16,
                kind: algorithm.kind(),
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
    if signature.len() != key.modulus_len_bytes() {
        return Err(Error::BadSignature);
    }
    let hash = PreparedBytes { prefix, message }.hash();
    let em_bits = key.modulus_len_bits() - 1;
    let mut em = [0u8; MAX_MODULUS];
    let em_len = em_bits.div_ceil(8);
    let opened = match key.public_op_be(signature, &mut em) {
        Ok(opened) => opened,
        Err(Error::WrongLength) => return Err(Error::BadSignature),
        Err(error) => return Err(error),
    };
    if opened.len() < em_len {
        return Err(Error::BadSignature);
    }
    let start = opened.len() - em_len;
    let mut encoded = [0u8; MAX_MODULUS];
    encoded[..em_len].copy_from_slice(&opened[start..start + em_len]);
    match pkcs1::verify_pss_sig_secret::<hash::Sha384>(
        &mut encoded[..em_len],
        em_bits,
        hash.as_ref(),
        algorithm.salt_len(),
    ) {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

fn verify_secret(
    key: &VerifyingKey,
    algorithm: Algorithm,
    prefix: &[u8],
    message: &[u8],
    signature: &[u8],
) -> Result<bool, Error> {
    let hash = PreparedBytes { prefix, message }.hash();
    let em_bits = key.modulus_len_bits() - 1;
    let mut em = [0u8; MAX_MODULUS];
    let opened = key.public_op_be(signature, &mut em)?;
    let em_len = em_bits.div_ceil(8);
    if opened.len() < em_len {
        return Ok(false);
    }
    let start = opened.len() - em_len;
    let mut encoded = [0u8; MAX_MODULUS];
    encoded[..em_len].copy_from_slice(&opened[start..start + em_len]);
    ct::secret_slice(&encoded[..em_len]);
    Ok(pkcs1::verify_pss_sig_secret::<hash::Sha384>(
        &mut encoded[..em_len],
        em_bits,
        hash.as_ref(),
        algorithm.salt_len(),
    ))
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
    blind_message(
        &key.key,
        algorithm,
        prefix,
        message,
        Some(salt),
        Some(inverse),
    )
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

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
        assert_eq!(
            PublicKey::prepared(
                &RSABSSA_SHA384_PSS_RANDOMIZED,
                &[0; 32],
                &[0; MAX_MESSAGE + 1]
            )
            .err(),
            Some(Error::WrongLength)
        );
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
                assert_eq!(&em[..em_len], encoded.as_slice(), "{}", algorithm.kind());
            }
            assert_eq!(blinded.as_ref(), number("blinded_msg").as_slice());
            let blind_sig = pair.blind_sign(&blinded).unwrap();
            assert_eq!(blind_sig.as_ref(), number("blind_sig").as_slice());
            let signature = blinding.finalize(&blind_sig).unwrap();
            assert_eq!(signature.as_ref(), number("sig").as_slice());
            if algorithm.randomized {
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

        let file: File = serde_json::from_str(include_str!(
            "../../../thirdparty/wycheproof/testvectors_v1/rsa_pss_2048_sha384_mgf1_48_test.json"
        ))
        .unwrap();
        assert!(!file.groups.is_empty());
        for group in file.groups {
            assert_eq!(group.sha, "SHA-384");
            assert_eq!(group.mgf_sha, "SHA-384");
            assert_eq!(group.salt_len, 48);
            let key = PublicKey::from_spki(&group.public_key_der).unwrap();
            for case in group.tests {
                let signature = match Signature::from_bytes(&case.sig) {
                    Ok(signature) => signature,
                    Err(Error::WrongLength) => {
                        assert_ne!(case.result, "valid");
                        continue;
                    }
                    Err(error) => panic!("{error:?}"),
                };
                let result = key.verify(&RSABSSA_SHA384_PSS_DETERMINISTIC, &case.msg, &signature);
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
            // Their signature used PSSZERO. Our verifier tries PSS first.
            // Check the salt-zero variant by blinding's kind: verify the
            // signature bytes with a fresh PSSZERO finalize path, which is
            // `verify_message` through a signature we know is PSSZERO.
            verify_message(
                &public.key,
                &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
                prepared.prefix(),
                prepared.message(),
                their_final.as_ref(),
            )
            .unwrap();
            assert!(
                verify_message(
                    &public.key,
                    &RSABSSA_SHA384_PSS_RANDOMIZED,
                    prepared.prefix(),
                    prepared.message(),
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
        let (blinded, blinding) = public.blind_prepared(&prepared).unwrap();
        ct::public_slice(blinded.as_ref());
        let blind_sig = pair.blind_sign(&blinded).unwrap();
        let signature = blinding.finalize(&blind_sig).unwrap();
        ct::public_slice(signature.as_ref());
        public.verify_prepared(&prepared, &signature).unwrap();
    }
}
