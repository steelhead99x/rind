// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Operations the unpublished `rind-acvp` binary needs.
//!
//! Not a supported API. The `__acvp` feature exists so that binary can answer
//! NIST's seeded tests. rind's callers generate keys from the system RNG and
//! sign with fresh randomness. Cargo features are public and additive, so the
//! `__` prefix, matching `__ctgrind`, is what marks this one internal.

use crate::error::{Error, KeyFormatError};
use crate::high::hash::{LegacySha1, Sha256, Sha384, Sha512};
use crate::high::hmac_drbg::HmacDrbg;
use crate::low::{PosInt, SecretPosInt};
use crate::low::{Zeroable, zeroise, zeroise_value};
use crate::mid::mlkem768::{Ciphertext, DecapKey, EncapKey, Message};

const RSA_WORDS: usize = 8192 / 64;
const MLKEM_DK: usize = 2400;
/// `dk_pke`, the start of an ML-KEM-768 decapsulation key.
const MLKEM_DK_PKE: usize = 1152;
const MLKEM_EK: usize = 1184;
const MLKEM_C: usize = 1088;

/// An ML-DSA-87 expanded private key, the largest secret this module returns.
const SECRET_LEN: usize = 4896;

/// A secret byte string wiped on drop under the `wipe` feature.
///
/// The bytes live in the value, not a `Vec`, so `rind/tests/zeroing.rs` can
/// see every byte after `Drop` and before the allocation is freed. A `Vec`
/// frees its buffer inside `Drop`, so that test would only see the header.
#[doc(hidden)]
pub struct SecretBuf {
    bytes: [u8; SECRET_LEN],
    len: usize,
}

impl SecretBuf {
    /// Copies `bytes` and marks the copy secret.
    ///
    /// # Panics
    ///
    /// Panics if `bytes` is longer than an ML-DSA-87 expanded private key.
    /// Every secret this module returns is that long or shorter.
    pub fn from_slice(bytes: &[u8]) -> Self {
        assert!(
            bytes.len() <= SECRET_LEN,
            "secret of {} bytes exceeds {SECRET_LEN}",
            bytes.len()
        );
        let mut secret = Self {
            bytes: [0; SECRET_LEN],
            len: bytes.len(),
        };
        secret.bytes[..bytes.len()].copy_from_slice(bytes);
        crate::low::ct::secret_slice(secret.as_slice());
        secret
    }

    /// The secret bytes.
    pub fn as_slice(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

impl AsRef<[u8]> for SecretBuf {
    fn as_ref(&self) -> &[u8] {
        self.as_slice()
    }
}

impl core::fmt::Debug for SecretBuf {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("SecretBuf")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl Drop for SecretBuf {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for SecretBuf {}

/// ML-KEM-768 key generation from FIPS 203's 64-byte seed `d || z`.
///
/// Returns `(ek, dk)`. `dk` is wiped on drop.
pub fn mlkem768_keygen(seed: &[u8]) -> Result<(Vec<u8>, SecretBuf), Error> {
    let _entry = crate::low::Entry::new_secret();
    let seed: &[u8; 64] = seed.try_into().map_err(|_| Error::WrongLength)?;
    let key = DecapKey::keygen_internal(seed);
    let ek = key.encapsulation_key().as_bytes().to_vec();
    let dk = SecretBuf::from_slice(&key.as_bytes());
    Ok((ek, dk))
}

/// ML-KEM-768 encapsulation of a given 32-byte message.
///
/// Returns `(ciphertext, shared secret)`. The shared secret is wiped on drop.
pub fn mlkem768_encaps(ek: &[u8], m: &[u8]) -> Result<(Vec<u8>, SecretBuf), Error> {
    let _entry = crate::low::Entry::new_secret();
    let ek: &[u8; MLKEM_EK] = ek.try_into().map_err(|_| Error::WrongLength)?;
    let m: [u8; 32] = m.try_into().map_err(|_| Error::WrongLength)?;
    let key = EncapKey::from_bytes(ek)?;
    let (secret, ciphertext) = key.encaps_internal(Message(m));
    Ok((
        ciphertext.as_ref().to_vec(),
        SecretBuf::from_slice(secret.as_ref()),
    ))
}

/// ML-KEM-768 decapsulation of an expanded decapsulation key.
///
/// A `dk` whose length is not 2400 bytes is [`Error::WrongLength`]: the
/// caller handed over a buffer of the wrong size. A 2400-byte `dk` that the
/// decapsulation-key check refuses is [`Error::KeyRejected`], the modulus
/// check. That refusal is the embedded encapsulation key failing FIPS 203's
/// modulus check, or `H(ek)` not matching that key. Neither is a length
/// error, and the modulus check is the error rind already uses for an
/// encapsulation key that fails it.
///
/// The shared secret is wiped on drop.
pub fn mlkem768_decaps(dk: &[u8], ciphertext: &[u8]) -> Result<SecretBuf, Error> {
    let _entry = crate::low::Entry::new_secret();
    let dk: [u8; MLKEM_DK] = dk.try_into().map_err(|_| Error::WrongLength)?;
    let ciphertext: [u8; MLKEM_C] = ciphertext.try_into().map_err(|_| Error::WrongLength)?;
    // `dk` is `dk_pke || ek || H(ek) || z`. Mark the two secret parts, as
    // rind marks the keys it parses, so `admin/ctgrind` checks decapsulation
    // with this key. `ek` and `H(ek)` stay public: the key check branches on
    // them. The stack copy itself stays: `DecapKey` wipes its own value on
    // drop, and a copy inside the call is not wiped.
    crate::low::ct::secret_slice(&dk[..MLKEM_DK_PKE]);
    crate::low::ct::secret_slice(&dk[MLKEM_DK - 32..]);
    let key = DecapKey::from_bytes(&dk).ok_or(KeyFormatError::MlKemModulus)?;
    let shared = key.decaps(&Ciphertext::from(ciphertext));
    Ok(SecretBuf::from_slice(shared.as_ref()))
}

/// Whether `ek` passes FIPS 203's encapsulation-key check.
pub fn mlkem768_ek_ok(ek: &[u8]) -> bool {
    let Ok(ek) = ek.try_into() else {
        return false;
    };
    EncapKey::from_bytes(ek).is_ok()
}

/// Whether `dk` passes FIPS 203's decapsulation-key check.
pub fn mlkem768_dk_ok(dk: &[u8]) -> bool {
    let Ok(dk) = dk.try_into() else {
        return false;
    };
    DecapKey::from_bytes(dk).is_some()
}

/// `base` ^ `exp` mod `modulus`, at `modulus`'s byte length, or `None`.
///
/// `None` covers a `base` that is not below the modulus, a modulus that is
/// even or zero, or a value that does not fit. Montgomery reduction requires
/// an odd modulus, so an even or zero modulus is refused before that
/// reduction runs.
///
/// The result is secret. ACVP uses this for the RSA signature primitive and
/// for decryption, and `m^d mod n` is then as good as `d`. It is returned in
/// a [`SecretBuf`] and is not marked public.
///
/// The exponentiation's trace follows the exponent's width. A shorter
/// exponent is widened to the modulus, so that trace follows the public
/// modulus length rather than how many leading zeros the exponent's encoding
/// had. An exponent wider than the modulus is left as it is: widening it
/// would drop its high words, and its trace stays that wider length.
pub fn rsa_modexp(base: &[u8], exp: &[u8], modulus: &[u8]) -> Option<SecretBuf> {
    let _entry = crate::low::Entry::new_secret();
    let base = PosInt::<RSA_WORDS>::from_bytes(base).ok()?;
    // Parsing trims the exponent's leading zero bytes, so its encoded length
    // is public, as an RSA key's DER length is. Its words are then secret,
    // as rind's RSA keys are, and wiped on drop.
    let mut exp = SecretPosInt::from(PosInt::<RSA_WORDS>::from_bytes(exp).ok()?);
    let modulus_n = PosInt::<RSA_WORDS>::from_bytes(modulus).ok()?;
    if modulus_n.is_even() || !base.less_than(&modulus_n) {
        return None;
    }
    exp.widen_to(&modulus_n);
    let mont = modulus_n.montifier();
    let n0 = modulus_n.mont_neg_inverse();
    let out = base.mod_exp(&*exp, &modulus_n, &mont, n0);
    let mut bytes = vec![0u8; modulus.len()];
    out.to_bytes(&mut bytes).ok()?;
    let secret = SecretBuf::from_slice(&bytes);
    zeroise(&mut bytes);
    Some(secret)
}

/// rind's SP 800-90A HMAC_DRBG, for the unpublished `rind-acvp` binary.
///
/// Not a supported API. The state is wiped on drop under `wipe`.
#[doc(hidden)]
pub struct AcvpDrbg(DrbgKind);

enum DrbgKind {
    Sha1(HmacDrbg<LegacySha1>),
    Sha256(HmacDrbg<Sha256>),
    Sha384(HmacDrbg<Sha384>),
    Sha512(HmacDrbg<Sha512>),
}

impl AcvpDrbg {
    /// Instantiates from `entropy`, `nonce`, and `personalization`.
    ///
    /// `hash` is `SHA-1`, `SHA2-256`, `SHA2-384`, or `SHA2-512`.
    pub fn new(hash: &str, entropy: &[u8], nonce: &[u8], personalization: &[u8]) -> Option<Self> {
        let _entry = crate::low::Entry::new_secret();
        let kind = match hash {
            "SHA-1" => DrbgKind::Sha1(HmacDrbg::new(entropy, nonce, personalization)),
            "SHA2-256" => DrbgKind::Sha256(HmacDrbg::new(entropy, nonce, personalization)),
            "SHA2-384" => DrbgKind::Sha384(HmacDrbg::new(entropy, nonce, personalization)),
            "SHA2-512" => DrbgKind::Sha512(HmacDrbg::new(entropy, nonce, personalization)),
            _ => return None,
        };
        Some(Self(kind))
    }

    /// SP 800-90A's reseed.
    pub fn reseed(&mut self, entropy: &[u8], additional: &[u8]) {
        let _entry = crate::low::Entry::new_secret();
        match &mut self.0 {
            DrbgKind::Sha1(drbg) => drbg.reseed(entropy, additional),
            DrbgKind::Sha256(drbg) => drbg.reseed(entropy, additional),
            DrbgKind::Sha384(drbg) => drbg.reseed(entropy, additional),
            DrbgKind::Sha512(drbg) => drbg.reseed(entropy, additional),
        }
    }

    /// SP 800-90A's generate, with `additional` empty when there is none.
    pub fn generate(&mut self, out: &mut [u8], additional: &[u8]) {
        let _entry = crate::low::Entry::new_secret();
        match &mut self.0 {
            DrbgKind::Sha1(drbg) => drbg.generate(out, additional),
            DrbgKind::Sha256(drbg) => drbg.generate(out, additional),
            DrbgKind::Sha384(drbg) => drbg.generate(out, additional),
            DrbgKind::Sha512(drbg) => drbg.generate(out, additional),
        }
    }
}

impl Drop for AcvpDrbg {
    fn drop(&mut self) {
        match &mut self.0 {
            DrbgKind::Sha1(drbg) => drbg.zeroise(),
            DrbgKind::Sha256(drbg) => drbg.zeroise(),
            DrbgKind::Sha384(drbg) => drbg.zeroise(),
            DrbgKind::Sha512(drbg) => drbg.zeroise(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{AcvpDrbg, SecretBuf};
    use crate::low::ct::{into_public, public_slice, secret_slice};

    /// Under `admin/ctgrind`, copying into a [`SecretBuf`] does not branch
    /// on the secret.
    #[test]
    fn secret_buf_copy_does_not_branch() {
        let bytes = [0xa5u8; 32];
        let wanted = copy32(&SecretBuf::from_slice(&bytes));
        // `from_slice` marks its copy secret, so the bytes `copy32` wrote are
        // secret until this names them public. Comparing them otherwise is a
        // branch on a secret.
        public_slice(&wanted);
        secret_slice(&bytes);
        let got = copy32(&SecretBuf::from_slice(&bytes));
        assert_eq!(into_public(got), wanted);
    }

    fn copy32(buf: &SecretBuf) -> [u8; 32] {
        let mut out = [0u8; 32];
        out.copy_from_slice(buf.as_slice());
        out
    }

    /// A [`SecretBuf`]'s bytes, marked public so the test may compare them.
    fn reveal(buf: &SecretBuf) -> Vec<u8> {
        let out = buf.as_slice().to_vec();
        public_slice(&out);
        out
    }

    /// Under `admin/ctgrind`, nothing may branch on or index by the entropy
    /// or the K and V derived from it, for any hash ACVP names, through
    /// instantiate, reseed, and a generate with a partial last block, both
    /// with and without additional input.
    #[test]
    fn drbg_secret_entropy_every_hash() {
        fn draw(hash: &str, entropy: &[u8], reseed: &[u8]) -> [u8; 100] {
            let mut drbg = AcvpDrbg::new(hash, entropy, &[0xa5; 16], b"personal").unwrap();
            drbg.reseed(reseed, b"reseed");
            let mut out = [0u8; 100];
            drbg.generate(&mut out, b"additional");
            drbg.generate(&mut out, b"");
            out
        }

        for hash in ["SHA-1", "SHA2-256", "SHA2-384", "SHA2-512"] {
            let entropy = [0x5a; 32];
            let reseed = [0x3c; 32];
            let wanted = draw(hash, &entropy, &reseed);
            secret_slice(&entropy);
            secret_slice(&reseed);
            assert_eq!(into_public(draw(hash, &entropy, &reseed)), wanted, "{hash}");
        }
        assert!(AcvpDrbg::new("SHA3-256", &[0; 32], &[0; 16], b"").is_none());
    }

    /// Under `admin/ctgrind`, seeded key generation, encapsulation of a given
    /// message, and decapsulation of a parsed key, for a ciphertext it
    /// accepts and one it rejects, do not branch on the seed, the message,
    /// or the key's `dk_pke` and `z`, which these functions mark.
    #[test]
    fn mlkem768_secret_seed_message_and_key() {
        let (ek, dk) = super::mlkem768_keygen(&[0x5a; 64]).unwrap();
        public_slice(&ek);
        let dk = reveal(&dk);
        let (mut ciphertext, sent) = super::mlkem768_encaps(&ek, &[0xa5; 32]).unwrap();
        public_slice(&ciphertext);
        let opened = super::mlkem768_decaps(&dk, &ciphertext).unwrap();
        assert_eq!(reveal(&opened), reveal(&sent));

        ciphertext[0] ^= 1;
        let rejected = super::mlkem768_decaps(&dk, &ciphertext).unwrap();
        assert_ne!(reveal(&rejected), reveal(&sent));
    }

    /// Under `admin/ctgrind`, the RSA primitive does not branch on or index
    /// by the exponent, which it marks once parsed, at the modulus's width
    /// or widened up to it.
    #[test]
    fn rsa_modexp_secret_exponent() {
        let mut modulus = [0xc3u8; 256];
        modulus[255] = 0xc5;
        let base = [0x11u8; 256];
        let wide = super::rsa_modexp(&base, &[0x5a; 256], &modulus).unwrap();
        assert_eq!(wide.as_slice().len(), 256);
        let short = super::rsa_modexp(&base, &[0x5a; 3], &modulus).unwrap();
        let mut exp = [0u8; 256];
        exp[253..].fill(0x5a);
        let padded = super::rsa_modexp(&base, &exp, &modulus).unwrap();
        assert_eq!(reveal(&short), reveal(&padded));
        assert_ne!(reveal(&short), reveal(&wide));
    }

    /// Under `admin/ctgrind`, ACVP's ML-DSA signing does not branch on the
    /// key or on `rnd`, for a key from a seed and one loaded from its
    /// expanded form, with a computed `mu` and a supplied one.
    #[test]
    fn mldsa_sign_acvp_secret_key_and_rnd() {
        use crate::high::signature::{MlDsaKeyPair, mldsa_verify_acvp};
        use crate::mid::mldsa::MlDsa44;

        let seeded = MlDsaKeyPair::<MlDsa44>::from_seed(&[0x5a; 32]).unwrap();
        let expanded = reveal(&seeded.expanded_secret());
        let loaded = MlDsaKeyPair::<MlDsa44>::from_expanded(&expanded).unwrap();
        let public_key = seeded.public_key();
        let rnd = [0xa5; 32];
        for (mu, internal) in [(None, false), (None, true), (Some(&[0x3c; 64][..]), true)] {
            let a = seeded
                .sign_acvp(b"context", b"message", mu, internal, &rnd)
                .unwrap();
            let b = loaded
                .sign_acvp(b"context", b"message", mu, internal, &rnd)
                .unwrap();
            assert_eq!(a.as_ref(), b.as_ref());
            mldsa_verify_acvp::<MlDsa44>(
                public_key.as_ref(),
                b"message",
                b"context",
                mu,
                internal,
                a.as_ref(),
            )
            .unwrap();
        }
    }
}
