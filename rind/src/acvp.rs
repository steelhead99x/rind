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
use crate::low::{Zeroable, zeroise_value};
use crate::mid::mlkem768::{Ciphertext, DecapKey, EncapKey, Message};

const RSA_WORDS: usize = 8192 / 64;
const MLKEM_DK: usize = 2400;
/// `dk_pke`, the start of an ML-KEM-768 decapsulation key.
const MLKEM_DK_PKE: usize = 1152;
const MLKEM_EK: usize = 1184;
const MLKEM_C: usize = 1088;

/// The longest HKDF output, 255 SHA-512 blocks.
const SECRET_LEN: usize = 255 * 64;

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
    /// A zeroed secret of `len` bytes, bounded by the longest HKDF output.
    pub fn zeroed(len: usize) -> Result<Self, Error> {
        if len > SECRET_LEN {
            return Err(Error::WrongLength);
        }
        Ok(Self {
            bytes: [0; SECRET_LEN],
            len,
        })
    }

    /// Copies `bytes` and marks the copy secret.
    ///
    /// # Panics
    ///
    /// Panics if `bytes` is longer than 255 SHA-512 output blocks.
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

    /// The secret bytes for a primitive to fill in place.
    pub fn as_mut_slice(&mut self) -> &mut [u8] {
        &mut self.bytes[..self.len]
    }

    /// Shrinks the visible bytes, keeping the backing value for drop to wipe.
    pub fn truncate(&mut self, len: usize) -> Result<(), Error> {
        if len > self.len {
            return Err(Error::WrongLength);
        }
        self.len = len;
        Ok(())
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

/// A big-endian integer as exactly `len` bytes.
///
/// The lengths are public. A longer `bytes` is accepted when every byte of
/// its prefix is zero. That check reads the whole prefix, and the accept or
/// reject is public: it is the error.
#[cfg(feature = "__acvp")]
pub fn field_bytes(bytes: &[u8], len: usize) -> Option<Vec<u8>> {
    let body = if bytes.len() > len {
        let extra = bytes.len() - len;
        let mut acc = 0u8;
        for &byte in &bytes[..extra] {
            acc |= byte;
        }
        if crate::low::ct::into_public(acc) != 0 {
            return None;
        }
        &bytes[extra..]
    } else {
        bytes
    };
    let mut out = vec![0u8; len - body.len()];
    out.extend_from_slice(body);
    Some(out)
}

/// `base` ^ `exp` mod `modulus`, at `modulus`'s byte length, or `None`.
///
/// `None` covers a `base` that is not below the modulus, a modulus that is
/// even or zero, or a value that does not fit. The modulus encoding is at
/// most 1024 bytes, including any leading zeros. Montgomery reduction
/// requires an odd modulus, so an even or zero modulus is refused before
/// that reduction runs.
///
/// The result is secret. ACVP uses this for the RSA signature primitive and
/// for decryption, and `m^d mod n` is then as good as `d`. It is returned in
/// a [`SecretBuf`] and is not marked public.
///
/// The exponentiation's trace follows public lengths. `exp.len()` fixes the
/// exponent's limb count, and a shorter exponent is widened to the modulus,
/// whose length is public too. Leading zero bytes stay in the value: they are
/// not a separate length. An exponent whose public length is already wider
/// than the modulus keeps that width, so its high words are not dropped.
pub fn rsa_modexp(base: &[u8], exp: &[u8], modulus: &[u8]) -> Option<SecretBuf> {
    let _entry = crate::low::Entry::new_secret();
    if modulus.len() > RSA_WORDS * 8 {
        return None;
    }
    let base = PosInt::<RSA_WORDS>::from_bytes(base).ok()?;
    let modulus_n = PosInt::<RSA_WORDS>::from_bytes(modulus).ok()?;
    if modulus_n.is_even() || !base.less_than(&modulus_n) {
        return None;
    }
    // Mark the exponent before it is loaded. Its byte length is public; the
    // bytes, including leading zeros, are secret. The words are wiped on drop.
    crate::low::ct::secret_slice(exp);
    let exp = SecretPosInt::from(PosInt::<RSA_WORDS>::from_public_width(exp, &modulus_n).ok()?);
    let mont = modulus_n.montifier();
    let n0 = modulus_n.mont_neg_inverse();
    let out = base.mod_exp(&*exp, &modulus_n, &mont, n0);
    rsa_bytes(&out, modulus.len())
}

/// RSA's non-CRT private operation with key validation and a public fault check.
pub fn rsa_private(base: &[u8], d: &[u8], n: &[u8], e: &[u8]) -> Option<SecretBuf> {
    let _entry = crate::low::Entry::new_secret();
    let public = rsa_public(n, e)?;
    let base = PosInt::from_bytes(base).ok()?;
    if !base.less_than(&public.n) {
        return None;
    }
    crate::low::ct::secret_slice(d);
    let d = SecretPosInt::from(PosInt::from_public_width(d, &public.n).ok()?);
    let valid = !d.equals(&PosInt::zero()) & d.less_than(&public.n);
    if !crate::low::ct::into_public(valid) {
        return None;
    }
    let mont = public.n.montifier();
    let n0 = public.n.mont_neg_inverse();
    let out = base.mod_exp(&d, &public.n, &mont, n0);
    let checked = public.public_op(out.clone()).ok()?;
    if !crate::low::ct::into_public(checked.equals(&base)) {
        return None;
    }
    rsa_bytes(&out, n.len())
}

/// An ACVP public key, at most 8192 bits with a u64 exponent below its modulus.
fn rsa_public(n: &[u8], e: &[u8]) -> Option<crate::mid::rsa_pub::RsaPublicKey> {
    if n.len() > RSA_WORDS * 8 || e.len() > 8 {
        return None;
    }
    let n = PosInt::from_bytes(n).ok()?;
    let e = e.iter().fold(0u64, |e, byte| (e << 8) | u64::from(*byte));
    crate::mid::rsa_pub::RsaPublicKey::new_acvp(n, e).ok()
}

/// The big-endian components of a two-prime RSA private key.
pub struct RsaCrtComponents<'a> {
    /// The public modulus.
    pub n: &'a [u8],
    /// The public exponent.
    pub e: &'a [u8],
    /// The private exponent.
    pub d: &'a [u8],
    /// The first prime.
    pub p: &'a [u8],
    /// The second prime.
    pub q: &'a [u8],
    /// The private exponent modulo `p - 1`.
    pub dp: &'a [u8],
    /// The private exponent modulo `q - 1`.
    pub dq: &'a [u8],
    /// The inverse of `q` modulo `p`.
    pub iqmp: &'a [u8],
}

/// rind's validated RSA CRT operation, or `None` for a bad key or input.
pub fn rsa_crt(base: &[u8], key: &RsaCrtComponents<'_>) -> Option<SecretBuf> {
    use crate::mid::rsa_priv::RsaPrivateKey;

    let _entry = crate::low::Entry::new_secret();
    let public = rsa_public(key.n, key.e)?;
    for secret in [key.d, key.p, key.q, key.dp, key.dq, key.iqmp] {
        crate::low::ct::secret_slice(secret);
    }
    let prime_width = PosInt::<{ RSA_WORDS / 2 }>::zero();
    let p = PosInt::from_public_width(key.p, &prime_width).ok()?;
    let q = PosInt::from_public_width(key.q, &prime_width).ok()?;
    let d = PosInt::from_public_width(key.d, &public.n).ok()?;
    let dp = PosInt::from_public_width(key.dp, &p).ok()?;
    let dq = PosInt::from_public_width(key.dq, &q).ok()?;
    let iqmp = PosInt::from_public_width(key.iqmp, &p).ok()?;
    let private = RsaPrivateKey::from_components(p, q, d, dp, dq, iqmp, public).ok()?;
    let base = PosInt::from_bytes(base).ok()?;
    let out = private.private_op(&base).ok()?;
    rsa_bytes(&out, key.n.len())
}

/// Serializes a private result at the public modulus encoding width.
fn rsa_bytes(out: &PosInt<RSA_WORDS>, len: usize) -> Option<SecretBuf> {
    // PosInt encodes whole limbs. Right-align those limbs before taking
    // the modulus's byte width, which need not be a whole number of limbs.
    // The result is below the modulus, so any discarded high bytes are zero.
    let mut bytes = [0u8; RSA_WORDS * 8];
    let start = bytes.len() - out.as_words().len() * 8;
    out.to_bytes(&mut bytes[start..]).ok()?;
    Some(SecretBuf::from_slice(&bytes[bytes.len() - len..]))
}

/// Expands a raw HKDF pseudorandom key, checking the length before allocating.
pub fn hkdf_expand(
    algorithm: &'static crate::hkdf::Algorithm,
    prk: &[u8],
    info: &[u8],
    len: usize,
) -> Result<SecretBuf, Error> {
    let _entry = crate::low::Entry::new_secret();
    crate::low::ct::secret_slice(prk);
    let prk = crate::high::hkdf::Prk::new(algorithm, prk);
    let info = [info];
    let okm = prk.expand(&info, len)?;
    let mut out = SecretBuf::zeroed(len)?;
    okm.fill(out.as_mut_slice())?;
    Ok(out)
}

/// rind's SP 800-90A HMAC_DRBG, for the unpublished `rind-acvp` binary.
///
/// Not a supported API. The state is wiped on drop under `wipe`.
#[doc(hidden)]
pub struct AcvpDrbg(DrbgKind);

// An explicit zero discriminant leaves no live Digest references when Drop
// wipes the whole value, including the hash choice and the reseed counter.
#[repr(u8)]
enum DrbgKind {
    Wiped,
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
            DrbgKind::Wiped => unreachable!("wiped only on drop"),
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
            DrbgKind::Wiped => unreachable!("wiped only on drop"),
            DrbgKind::Sha1(drbg) => drbg.generate(out, additional),
            DrbgKind::Sha256(drbg) => drbg.generate(out, additional),
            DrbgKind::Sha384(drbg) => drbg.generate(out, additional),
            DrbgKind::Sha512(drbg) => drbg.generate(out, additional),
        }
    }
}

impl Drop for AcvpDrbg {
    fn drop(&mut self) {
        if cfg!(feature = "wipe") {
            self.0 = DrbgKind::Wiped;
            zeroise_value(self);
        }
    }
}

impl Zeroable for AcvpDrbg {}

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

    #[test]
    fn field_bytes_secret_padding() {
        let value = [0, 0, 1, 2, 3];
        secret_slice(&value);
        for len in [3, 5, 8] {
            let out = super::field_bytes(&value, len).unwrap();
            let mut expected = vec![0; len];
            expected[len - 3..].copy_from_slice(&[1, 2, 3]);
            public_slice(&out);
            assert_eq!(out, expected);
        }
        assert!(super::field_bytes(&value, 2).is_none());
        assert!(super::field_bytes(&[], 0).unwrap().is_empty());
    }

    #[test]
    fn secret_buf_zeroed_is_bounded() {
        assert!(SecretBuf::zeroed(0).unwrap().as_slice().is_empty());
        let mut full = SecretBuf::zeroed(super::SECRET_LEN).unwrap();
        assert_eq!(full.as_slice(), &[0; super::SECRET_LEN]);
        full.as_mut_slice().fill(0xa5);
        assert_eq!(full.as_slice(), &[0xa5; super::SECRET_LEN]);
        full.truncate(32).unwrap();
        assert_eq!(full.as_slice(), &[0xa5; 32]);
        assert_eq!(full.truncate(33), Err(crate::Error::WrongLength));
        assert_eq!(full.as_slice().len(), 32);
        full.truncate(0).unwrap();
        assert!(full.as_slice().is_empty());
        assert_eq!(
            SecretBuf::zeroed(super::SECRET_LEN + 1).unwrap_err(),
            crate::Error::WrongLength
        );
        assert_eq!(
            SecretBuf::zeroed(usize::MAX).unwrap_err(),
            crate::Error::WrongLength
        );
    }

    /// Raw PRKs, including keys longer than an HMAC block, stay secret
    /// through every hash and a partial final output block.
    #[test]
    fn hkdf_expand_secret_prk() {
        use crate::hkdf::{HKDF_SHA256, HKDF_SHA384, HKDF_SHA512, legacy::HKDF_SHA1};

        for algorithm in [&HKDF_SHA1, &HKDF_SHA256, &HKDF_SHA384, &HKDF_SHA512] {
            for prk in [&[0x5a; 32][..], &[0xa5; 145][..]] {
                let expected = reveal(&super::hkdf_expand(algorithm, prk, b"info", 100).unwrap());
                secret_slice(prk);
                let out = super::hkdf_expand(algorithm, prk, b"info", 100).unwrap();
                assert_eq!(reveal(&out), expected);
            }
            let max = 255 * algorithm.hash_len();
            assert_eq!(
                super::hkdf_expand(algorithm, &[0; 64], b"info", max + 1).unwrap_err(),
                crate::Error::WrongLength
            );
            assert_eq!(
                super::hkdf_expand(algorithm, &[0; 64], b"info", usize::MAX).unwrap_err(),
                crate::Error::WrongLength
            );
            assert!(
                super::hkdf_expand(algorithm, &[0; 64], b"", 0)
                    .unwrap()
                    .as_slice()
                    .is_empty()
            );
        }
    }

    #[cfg(not(any(miri, target_family = "wasm")))]
    #[test]
    fn hkdf_expand_matches_aws_lc_at_block_boundaries() {
        use aws_lc_rs::hkdf as theirs;

        use crate::hkdf::{HKDF_SHA256, HKDF_SHA384, HKDF_SHA512, legacy::HKDF_SHA1};

        struct Len(usize);

        impl theirs::KeyType for Len {
            fn len(&self) -> usize {
                self.0
            }
        }

        for (algorithm, reference) in [
            (&HKDF_SHA1, theirs::HKDF_SHA1_FOR_LEGACY_USE_ONLY),
            (&HKDF_SHA256, theirs::HKDF_SHA256),
            (&HKDF_SHA384, theirs::HKDF_SHA384),
            (&HKDF_SHA512, theirs::HKDF_SHA512),
        ] {
            let hash_len = algorithm.hash_len();
            let prk = [0xa5; 64];
            let info = [b"info".as_slice()];
            let reference = theirs::Prk::new_less_safe(reference, &prk);
            for len in [
                1,
                hash_len - 1,
                hash_len,
                hash_len + 1,
                255 * hash_len - 1,
                255 * hash_len,
            ] {
                let mut expected = vec![0; len];
                reference
                    .expand(&info, Len(len))
                    .unwrap()
                    .fill(&mut expected)
                    .unwrap();
                let out = super::hkdf_expand(algorithm, &prk, info[0], len).unwrap();
                assert_eq!(reveal(&out), expected);
            }
        }
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
    /// by the exponent, including its leading zero bytes. The raw buffer is
    /// marked. A short exponent, one the modulus's width, and one of that
    /// width whose first bytes are zero all run.
    #[test]
    fn rsa_modexp_secret_exponent() {
        let mut modulus = [0xc3u8; 256];
        modulus[255] = 0xc5;
        let base = [0x11u8; 256];
        let wide_exp = [0x5a; 256];
        let short_exp = [0x5a; 3];
        let mut leading = [0u8; 256];
        leading[253..].fill(0x5a);
        let wanted_wide = super::rsa_modexp(&base, &wide_exp, &modulus).unwrap();
        let wanted_short = super::rsa_modexp(&base, &short_exp, &modulus).unwrap();
        let wanted_leading = super::rsa_modexp(&base, &leading, &modulus).unwrap();
        assert_eq!(wanted_wide.as_slice().len(), 256);
        assert_eq!(reveal(&wanted_short), reveal(&wanted_leading));
        assert_ne!(reveal(&wanted_short), reveal(&wanted_wide));

        secret_slice(&wide_exp);
        secret_slice(&short_exp);
        secret_slice(&leading);
        let wide = super::rsa_modexp(&base, &wide_exp, &modulus).unwrap();
        let short = super::rsa_modexp(&base, &short_exp, &modulus).unwrap();
        let padded = super::rsa_modexp(&base, &leading, &modulus).unwrap();
        assert_eq!(reveal(&wide), reveal(&wanted_wide));
        assert_eq!(reveal(&short), reveal(&wanted_short));
        assert_eq!(reveal(&padded), reveal(&wanted_leading));
    }

    #[test]
    fn rsa_private_secret_exponent_and_validation() {
        let d = vec![5];
        let e = vec![5];
        let base = vec![2];
        for len in [1, 7, 8, 9, 16, 17, 1024] {
            let mut n = vec![0; len];
            n[len - 1] = 13;
            let result = super::rsa_private(&base, &d, &n, &e).unwrap();
            let mut expected = vec![0; len];
            expected[len - 1] = 6;
            assert_eq!(reveal(&result), expected);
        }
        let n = vec![13];
        let padded = vec![0, 0, 5];
        assert_eq!(
            reveal(&super::rsa_private(&base, &padded, &n, &e).unwrap()),
            [6]
        );
        for e in [0, 1, 2, 13, 15] {
            let invalid = Vec::from([e]);
            assert!(super::rsa_private(&base, &d, &n, &invalid).is_none());
        }
        for d in [0, 3, 13] {
            let invalid = Vec::from([d]);
            assert!(super::rsa_private(&base, &invalid, &n, &e).is_none());
        }
        assert!(super::rsa_private(&base, &d, &n, &[0; 9]).is_none());
        assert!(super::rsa_private(&base, &[0; 1025], &n, &e).is_none());
        assert!(super::rsa_private(&base, &d, &[0; 1025], &e).is_none());
    }

    #[test]
    fn rsa_private_acvp_vectors() {
        use crate::test::{Acvp, acvp};

        for (set, input, output) in [
            ("RSA-DecryptionPrimitive-Sp800-56Br2", "ct", "pt"),
            ("RSA-SignaturePrimitive-2.0", "message", "signature"),
        ] {
            for group in acvp(set) {
                if group.str("keyMode") != "standard" {
                    continue;
                }
                for test in group.tests() {
                    let (n, e, d) = (test.hex("n"), test.hex("e"), test.hex("d"));
                    let base = test.hex(input);
                    let result = super::rsa_private(&base, &d, &n, &e);
                    if test.flag("testPassed") {
                        assert_eq!(
                            reveal(&result.unwrap()),
                            test.hex(output),
                            "tcId {}",
                            test.int("tcId")
                        );
                    } else {
                        let expected = super::rsa_modexp(&base, &d, &n);
                        assert_eq!(
                            result.as_ref().map(reveal),
                            expected.as_ref().map(reveal),
                            "tcId {}",
                            test.int("tcId")
                        );
                    }
                }
            }
        }
    }

    /// Every supplied CRT component is secret before it is loaded, through
    /// validation, the private operation, and its public fault check.
    #[test]
    fn rsa_crt_secret_components() {
        use crate::high::asn1::{Type, pkix};

        let der = pkix::RSAPrivateKey::from_bytes(include_bytes!("high/rsa/rsa2048.der")).unwrap();
        fn unsigned(bytes: &[u8]) -> &[u8] {
            bytes.strip_prefix(&[0]).unwrap_or(bytes)
        }
        let key = super::RsaCrtComponents {
            n: unsigned(der.modulus.as_ref()),
            e: unsigned(der.publicExponent.as_ref()),
            d: unsigned(der.privateExponent.as_ref()),
            p: unsigned(der.prime1.as_ref()),
            q: unsigned(der.prime2.as_ref()),
            dp: unsigned(der.exponent1.as_ref()),
            dq: unsigned(der.exponent2.as_ref()),
            iqmp: unsigned(der.coefficient.as_ref()),
        };
        let result = super::rsa_crt(&[2], &key).unwrap();
        let reference = super::rsa_modexp(&[2], key.d, key.n).unwrap();
        assert_eq!(reveal(&result), reveal(&reference));

        for component in 0..8 {
            // Separate allocations keep a marked secret zero from aliasing
            // the public zero used by a later malformed-component case.
            let zero = vec![0];
            let mut invalid = super::RsaCrtComponents { ..key };
            match component {
                0 => invalid.d = &zero,
                1 => invalid.p = &zero,
                2 => invalid.q = &zero,
                3 => invalid.dp = &zero,
                4 => invalid.dq = &zero,
                5 => invalid.iqmp = &zero,
                6 => invalid.e = &zero,
                7 => invalid.n = &zero,
                _ => unreachable!(),
            }
            assert!(
                super::rsa_crt(&[2], &invalid).is_none(),
                "component {component}"
            );
        }
        for component in 0..8 {
            let mut invalid = super::RsaCrtComponents { ..key };
            match component {
                0 => invalid.d = &[0; 1025],
                1 => invalid.p = &[0; 513],
                2 => invalid.q = &[0; 513],
                3 => invalid.dp = &[0; 513],
                4 => invalid.dq = &[0; 513],
                5 => invalid.iqmp = &[0; 513],
                6 => invalid.e = &[0; 9],
                7 => invalid.n = &[0; 1025],
                _ => unreachable!(),
            }
            assert!(
                super::rsa_crt(&[2], &invalid).is_none(),
                "component {component}"
            );
        }
    }

    #[test]
    fn rsa_crt_acvp_vectors() {
        use crate::test::{Acvp, acvp};

        for group in acvp("RSA-DecryptionPrimitive-Sp800-56Br2") {
            if group.str("keyMode") != "crt" {
                continue;
            }
            for test in group.tests() {
                let (n, e, d) = (test.hex("n"), test.hex("e"), test.hex("d"));
                let (p, q) = (test.hex("p"), test.hex("q"));
                let (dp, dq, iqmp) = (test.hex("dmp1"), test.hex("dmq1"), test.hex("iqmp"));
                let key = super::RsaCrtComponents {
                    n: &n,
                    e: &e,
                    d: &d,
                    p: &p,
                    q: &q,
                    dp: &dp,
                    dq: &dq,
                    iqmp: &iqmp,
                };
                let ct = test.hex("ct");
                let result = super::rsa_crt(&ct, &key);
                if test.flag("testPassed") {
                    assert_eq!(
                        reveal(&result.unwrap()),
                        test.hex("pt"),
                        "tcId {}",
                        test.int("tcId")
                    );
                } else {
                    // The wrapper rejects SP 800-56B's trivial ciphertexts
                    // before this raw operation. Its core still computes
                    // the same value as the non-CRT exponentiation.
                    let expected = super::rsa_modexp(&ct, &d, &n);
                    assert_eq!(
                        result.as_ref().map(reveal),
                        expected.as_ref().map(reveal),
                        "tcId {}",
                        test.int("tcId")
                    );
                }
            }
        }
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
