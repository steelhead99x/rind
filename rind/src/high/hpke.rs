// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Hybrid public key encryption: [RFC 9180]'s base mode and secret export.
//!
//! [RFC 9180]: https://www.rfc-editor.org/rfc/rfc9180.html

use core::fmt;

use super::agreement;
use super::digest::Digest;
use super::hkdf::{self, Prk};
use super::hmac;
use crate::error::{Error, KeyFormatError};
use crate::{aead, low};

/// A KEM: a Diffie-Hellman group and the KDF that makes its shared secret
/// (RFC 9180 section 4.1).
pub struct Kem {
    id: u16,
    name: &'static str,
    agreement: &'static agreement::Algorithm,
    kdf: &'static hkdf::Algorithm,
    /// Npk and Nenc: an uncompressed point, or X25519's 32 bytes.
    public_len: usize,
    /// Nsk: a serialized private key.
    scalar_len: usize,
    /// How `DeriveKeyPair` makes a key from its pseudorandom key: X25519
    /// takes any bytes, and a NIST curve rejection-samples candidates with
    /// their first byte masked by this.
    candidate_mask: Option<u8>,
}

impl fmt::Debug for Kem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

/// DHKEM(X25519, HKDF-SHA256).
pub static DHKEM_X25519_HKDF_SHA256: Kem = Kem {
    id: 0x0020,
    name: "DHKEM(X25519, HKDF-SHA256)",
    agreement: &agreement::X25519,
    kdf: &hkdf::HKDF_SHA256,
    public_len: 32,
    scalar_len: 32,
    candidate_mask: None,
};

/// DHKEM(P-256, HKDF-SHA256).
pub static DHKEM_P256_HKDF_SHA256: Kem = Kem {
    id: 0x0010,
    name: "DHKEM(P-256, HKDF-SHA256)",
    agreement: &agreement::ECDH_P256,
    kdf: &hkdf::HKDF_SHA256,
    public_len: 65,
    scalar_len: 32,
    candidate_mask: Some(0xff),
};

/// DHKEM(P-384, HKDF-SHA384).
pub static DHKEM_P384_HKDF_SHA384: Kem = Kem {
    id: 0x0011,
    name: "DHKEM(P-384, HKDF-SHA384)",
    agreement: &agreement::ECDH_P384,
    kdf: &hkdf::HKDF_SHA384,
    public_len: 97,
    scalar_len: 48,
    candidate_mask: Some(0xff),
};

/// DHKEM(P-521, HKDF-SHA512).
pub static DHKEM_P521_HKDF_SHA512: Kem = Kem {
    id: 0x0012,
    name: "DHKEM(P-521, HKDF-SHA512)",
    agreement: &agreement::ECDH_P521,
    kdf: &hkdf::HKDF_SHA512,
    public_len: 133,
    scalar_len: 66,
    candidate_mask: Some(0x01),
};

/// The KDF of a suite's key schedule (RFC 9180 section 7.2).
pub struct Kdf {
    id: u16,
    hkdf: &'static hkdf::Algorithm,
}

impl fmt::Debug for Kdf {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.hkdf.fmt(f)
    }
}

/// HKDF-SHA256.
pub static HKDF_SHA256: Kdf = Kdf {
    id: 0x0001,
    hkdf: &hkdf::HKDF_SHA256,
};

/// HKDF-SHA384.
pub static HKDF_SHA384: Kdf = Kdf {
    id: 0x0002,
    hkdf: &hkdf::HKDF_SHA384,
};

/// HKDF-SHA512.
pub static HKDF_SHA512: Kdf = Kdf {
    id: 0x0003,
    hkdf: &hkdf::HKDF_SHA512,
};

/// The AEAD a suite seals with (RFC 9180 section 7.3).
pub struct Aead {
    id: u16,
    algorithm: &'static aead::Algorithm,
}

impl fmt::Debug for Aead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.algorithm.fmt(f)
    }
}

/// AES-128-GCM.
pub static AES_128_GCM: Aead = Aead {
    id: 0x0001,
    algorithm: &aead::AES_128_GCM,
};

/// AES-256-GCM.
pub static AES_256_GCM: Aead = Aead {
    id: 0x0002,
    algorithm: &aead::AES_256_GCM,
};

/// ChaCha20-Poly1305.
pub static CHACHA20_POLY1305: Aead = Aead {
    id: 0x0003,
    algorithm: &aead::CHACHA20_POLY1305,
};

/// The export-only AEAD identifier, which an [`Exporter`]'s key schedule
/// names in place of an AEAD's.
const EXPORT_ONLY: u16 = 0xffff;

/// The KDF and AEAD a [`Sender`] and [`Recipient`] derive their keys with.
///
/// The KEM, the suite's third part, is the key's: every combination is
/// valid. An [`Exporter`] takes a [`Kdf`] alone.
#[derive(Clone, Copy, Debug)]
pub struct Suite {
    /// The key schedule's KDF.
    pub kdf: &'static Kdf,
    /// The AEAD that seals and opens messages.
    pub aead: &'static Aead,
}

/// A recipient's private key, wiped on drop under the `wipe` feature.
pub struct PrivateKey {
    kem: low::ZeroableRef<Kem>,
    key: agreement::PrivateKey,
}

impl PrivateKey {
    /// Generates a key for `kem` from the system random source.
    pub fn generate(kem: &'static Kem) -> Result<Self, Error> {
        Ok(Self::new(
            kem,
            agreement::PrivateKey::generate(kem.agreement)?,
        ))
    }

    /// Derives a key for `kem` from `ikm`, as RFC 9180's `DeriveKeyPair`
    /// does (section 7.1.3).
    ///
    /// RFC 9180 asks for at least the KEM's private key length of `ikm`, all
    /// of it entropy, but takes any length, as MLS's P-521 suite, which
    /// derives keys from 64 bytes, needs.
    pub fn derive(kem: &'static Kem, ikm: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        let labels = Labels::kem(kem);
        let dkp_prk = labels.extract_prk(b"", b"dkp_prk", ikm);
        let mut bytes = [0u8; MAX_SCALAR_LEN];
        let bytes = &mut bytes[..kem.scalar_len];
        let Some(mask) = kem.candidate_mask else {
            labels.expand(&dkp_prk, b"sk", &[], bytes)?;
            return Self::from_scalar(kem, bytes);
        };

        // Whether a candidate is below the group order is public, as for an
        // ECDSA nonce: a rejected one says nothing of the one kept.
        let mut result: Result<Self, Error> = Err(KeyFormatError::ScalarOutOfRange.into());
        for counter in 0..=255u8 {
            labels.expand(&dkp_prk, b"candidate", &[&[counter]], bytes)?;
            bytes[0] &= mask;
            result = Self::from_scalar(kem, bytes);
            if result.is_ok() {
                break;
            }
        }
        result
    }

    /// Loads a key for `kem` from its serialization (RFC 9180 section
    /// 7.1.2): X25519's 32 bytes, any value, or a NIST curve's big-endian
    /// scalar, exactly the curve's length and refused unless it is from 1 to
    /// n - 1.
    pub fn from_scalar(kem: &'static Kem, scalar: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(
            kem,
            agreement::PrivateKey::from_scalar(kem.agreement, scalar)?,
        ))
    }

    /// Serializes the key as [`Self::from_scalar`] loads it.
    ///
    /// An X25519 key's bytes are those it was loaded or derived from,
    /// unclamped, as RFC 9180's test vectors, its erratum 7121, and its
    /// revision serialize them.
    pub fn to_scalar(&self) -> agreement::Scalar {
        self.key.to_scalar()
    }

    /// Returns the public key to send to senders.
    pub fn public_key(&self) -> PublicKey {
        PublicKey {
            kem: self.kem(),
            key: self.key.public_key().clone(),
        }
    }

    /// Returns the key's KEM.
    pub fn kem(&self) -> &'static Kem {
        self.kem.get()
    }

    fn new(kem: &'static Kem, key: agreement::PrivateKey) -> Self {
        Self {
            kem: low::ZeroableRef::new(kem),
            key,
        }
    }

    /// `Decap` (RFC 9180 section 4.1): the shared secret `enc` encapsulates.
    fn decapsulate(&self, enc: &[u8]) -> Result<SharedSecret, Error> {
        let kem = self.kem();
        // RFC 9180 serializes a point uncompressed, but a compressed one is
        // taken too, as aws-lc-rs takes it; `kem_context` hashes `enc` as
        // sent.
        let peer = agreement::PublicKey::new(kem.agreement, enc)?;
        let dh = self.key.agree(peer.as_ref())?;
        Ok(SharedSecret::new(
            kem,
            dh.as_ref(),
            enc,
            self.key.public_key().as_ref(),
        ))
    }
}

// A NIST curve's key is a valid agreement key; the KEM reference is a
// `ZeroableRef`.
impl low::Zeroable for PrivateKey {}

impl Drop for PrivateKey {
    fn drop(&mut self) {
        // The KEM is not secret, but a key type wipes its whole value.
        low::zeroise_value(self);
    }
}

impl fmt::Debug for PrivateKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PrivateKey")
            .field("kem", self.kem())
            .finish_non_exhaustive()
    }
}

/// A recipient's public key.
#[derive(Clone)]
pub struct PublicKey {
    kem: &'static Kem,
    key: agreement::PublicKey,
}

impl PublicKey {
    /// Parses a public key for `kem` from its serialization (RFC 9180
    /// section 7.1.1): X25519's 32 bytes, any value, or a NIST curve's
    /// uncompressed point, refused off the curve.
    pub fn new(kem: &'static Kem, bytes: &[u8]) -> Result<Self, Error> {
        if bytes.len() != kem.public_len {
            return Err(KeyFormatError::WrongLength.into());
        }
        Ok(Self {
            kem,
            key: agreement::PublicKey::new(kem.agreement, bytes)?,
        })
    }

    /// Returns the key's KEM.
    pub fn kem(&self) -> &'static Kem {
        self.kem
    }

    /// `Encap` (RFC 9180 section 4.1): a fresh shared secret and its
    /// encapsulation, under `ephemeral`.
    fn encapsulate(
        &self,
        ephemeral: &agreement::PrivateKey,
    ) -> Result<(EncapsulatedKey, SharedSecret), Error> {
        let dh = ephemeral.agree(self.key.as_ref())?;
        let enc = ephemeral.public_key();
        let secret = SharedSecret::new(self.kem, dh.as_ref(), enc.as_ref(), self.key.as_ref());
        Ok((EncapsulatedKey(enc.clone()), secret))
    }

    fn encapsulate_random(&self) -> Result<(EncapsulatedKey, SharedSecret), Error> {
        self.encapsulate(&agreement::PrivateKey::generate(self.kem.agreement)?)
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.key.as_ref()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PublicKey")
            .field("kem", self.kem)
            .field("key", &self.as_ref())
            .finish()
    }
}

/// The encapsulated key a sender sends with its messages, `enc` in RFC 9180.
#[derive(Clone)]
pub struct EncapsulatedKey(agreement::PublicKey);

impl AsRef<[u8]> for EncapsulatedKey {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for EncapsulatedKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EncapsulatedKey")
            .field(&self.as_ref())
            .finish()
    }
}

/// A sender's context, which seals messages in order and exports secrets;
/// wiped on drop under the `wipe` feature.
pub struct Sender {
    sealing: Sealing,
    exporter: Exporter,
}

impl Sender {
    /// Encapsulates a fresh secret to `public_key` and derives a context
    /// from it for `suite` and `info`, as RFC 9180's `SetupBaseS` does.
    ///
    /// Returns the encapsulated key the recipient needs. Fails with
    /// [`Error::KeyRejected`] when X25519 agreement with `public_key` gives
    /// all zeroes, as it does for a small-order point.
    pub fn new(
        suite: Suite,
        public_key: &PublicKey,
        info: &[u8],
    ) -> Result<(EncapsulatedKey, Self), Error> {
        let _entry = low::Entry::new_secret();
        let (enc, secret) = public_key.encapsulate_random()?;
        Ok((enc, Self::schedule(suite, &secret, info)))
    }

    fn schedule(suite: Suite, secret: &SharedSecret, info: &[u8]) -> Self {
        let (sealing, exporter) = schedule(suite, secret, info);
        Self { sealing, exporter }
    }

    /// Encrypts `in_out` in place under the next sequence number and appends
    /// the tag.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged and the
    /// sequence number where it was, past the AEAD's limits (see
    /// [`aead::Key::seal_in_place_separate_tag`]), and with
    /// [`Error::MessageLimitReached`] after 2^64 - 1 messages.
    pub fn seal_in_place_append_tag<InOut>(
        &mut self,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let _entry = low::Entry::new_secret();
        // Only the sequence number's step runs between encrypting and
        // advancing it, so a panic in `in_out`'s `extend` cannot leave a used
        // nonce to seal under again.
        let tag = self
            .sealing
            .step(|key, nonce| key.seal_in_place_separate_tag(nonce, aad, in_out.as_mut()))?;
        in_out.extend(tag.as_ref());
        Ok(())
    }

    /// Fills `out` with the secret RFC 9180's `Export` derives for
    /// `exporter_context` (section 5.3).
    ///
    /// Fails as [`Exporter::export`] does.
    pub fn export(&self, exporter_context: &[u8], out: &mut [u8]) -> Result<(), Error> {
        self.exporter.export(exporter_context, out)
    }
}

// All-zero is a valid AEAD key, as `aead::Key`'s drop requires, a valid
// HMAC key in the exporter's `Prk`, and plain bytes and integers otherwise.
impl low::Zeroable for Sender {}

impl Drop for Sender {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl fmt::Debug for Sender {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Sender").finish_non_exhaustive()
    }
}

/// A recipient's context, which opens messages in the order they were sealed
/// and exports secrets; wiped on drop under the `wipe` feature.
pub struct Recipient {
    sealing: Sealing,
    exporter: Exporter,
}

impl Recipient {
    /// Decapsulates `enc` with `private_key` and derives the sender's context
    /// from it for `suite` and `info`, as RFC 9180's `SetupBaseR` does.
    ///
    /// Fails with [`Error::KeyRejected`] when `enc` is not a public key of
    /// the key's KEM, or X25519 agreement with it gives all zeroes. Beside
    /// what [`PublicKey::new`] parses, `enc` may be a compressed NIST point,
    /// as aws-lc-rs takes one, which the key schedule hashes as sent.
    pub fn new(
        suite: Suite,
        private_key: &PrivateKey,
        enc: &[u8],
        info: &[u8],
    ) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        let secret = private_key.decapsulate(enc)?;
        let (sealing, exporter) = schedule(suite, &secret, info);
        Ok(Self { sealing, exporter })
    }

    /// Decrypts and verifies `in_out`, the next message's ciphertext followed
    /// by its tag, and returns the plaintext at its front.
    ///
    /// A message that fails leaves the sequence number where it was, so the
    /// next one still opens. Fails as [`aead::Key::open_in_place`] does, and
    /// with [`Error::MessageLimitReached`] after 2^64 - 1 messages.
    pub fn open_in_place<'a>(
        &mut self,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let _entry = low::Entry::new_secret();
        self.sealing
            .step(|key, nonce| key.open_in_place(nonce, aad, in_out))
    }

    /// Fills `out` with the secret RFC 9180's `Export` derives for
    /// `exporter_context` (section 5.3).
    ///
    /// Fails as [`Exporter::export`] does.
    pub fn export(&self, exporter_context: &[u8], out: &mut [u8]) -> Result<(), Error> {
        self.exporter.export(exporter_context, out)
    }
}

// As `Sender`.
impl low::Zeroable for Recipient {}

impl Drop for Recipient {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl fmt::Debug for Recipient {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Recipient").finish_non_exhaustive()
    }
}

/// An export-only context (RFC 9180 section 5.3), which derives secrets but
/// seals and opens nothing; wiped on drop under the `wipe` feature.
pub struct Exporter {
    secret: Prk,
    /// The key schedule's `suite_id`, which `Export` labels with.
    suite_id: [u8; 10],
}

impl Exporter {
    /// Encapsulates a fresh secret to `public_key` and derives an
    /// export-only context from it with `kdf` and `info`.
    ///
    /// Returns the encapsulated key the recipient needs, and fails as
    /// [`Sender::new`] does.
    pub fn sender(
        kdf: &'static Kdf,
        public_key: &PublicKey,
        info: &[u8],
    ) -> Result<(EncapsulatedKey, Self), Error> {
        let _entry = low::Entry::new_secret();
        let (enc, secret) = public_key.encapsulate_random()?;
        Ok((enc, Self::schedule(kdf, &secret, info)))
    }

    /// Decapsulates `enc` with `private_key` and derives the sender's
    /// export-only context from it with `kdf` and `info`.
    ///
    /// Fails as [`Recipient::new`] does.
    pub fn recipient(
        kdf: &'static Kdf,
        private_key: &PrivateKey,
        enc: &[u8],
        info: &[u8],
    ) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        let secret = private_key.decapsulate(enc)?;
        Ok(Self::schedule(kdf, &secret, info))
    }

    fn schedule(kdf: &'static Kdf, secret: &SharedSecret, info: &[u8]) -> Self {
        let labels = Labels::hpke(secret.kem, kdf, EXPORT_ONLY);
        KeySchedule::new(&labels, secret, info).exporter(&labels)
    }

    /// Fills `out` with the secret RFC 9180's `Export` derives for
    /// `exporter_context` (section 5.3).
    ///
    /// Fails with [`Error::WrongLength`], leaving `out` unchanged, if `out`
    /// is longer than 255 of the KDF's hash outputs.
    pub fn export(&self, exporter_context: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let _entry = low::Entry::new_secret();
        labeled_expand(
            &self.suite_id,
            &self.secret,
            b"sec",
            &[exporter_context],
            out,
        )
    }
}

// All-zero is a valid HMAC key in the `Prk`, as its drop requires.
impl low::Zeroable for Exporter {}

impl Drop for Exporter {
    fn drop(&mut self) {
        low::zeroise_value(self);
    }
}

impl fmt::Debug for Exporter {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Exporter").finish_non_exhaustive()
    }
}

/// A context's AEAD key and nonce state.
struct Sealing {
    key: aead::Key,
    base_nonce: [u8; NONCE_LEN],
    seq: u64,
}

impl Sealing {
    /// Runs `f` with the next sequence number's nonce, advancing it only when
    /// `f` succeeds.
    fn step<T>(
        &mut self,
        f: impl FnOnce(&aead::Key, aead::Nonce) -> Result<T, Error>,
    ) -> Result<T, Error> {
        // RFC 9180 allows 2^96 - 1 messages; a u64 counter stops at its own
        // limit, which no context reaches.
        let next = self.seq.checked_add(1).ok_or(Error::MessageLimitReached)?;
        let mut nonce = self.base_nonce;
        for (n, s) in nonce[NONCE_LEN - 8..]
            .iter_mut()
            .zip(self.seq.to_be_bytes())
        {
            *n ^= s;
        }
        let result = f(&self.key, aead::Nonce::assume_unique_for_key(nonce))?;
        self.seq = next;
        Ok(result)
    }
}

const NONCE_LEN: usize = 12;

/// The longest serialized private key, P-521's.
const MAX_SCALAR_LEN: usize = 66;

/// The longest KDF output, SHA-512's.
const MAX_HASH_LEN: usize = 64;

/// A KEM's shared secret, `Nsecret` bytes.
struct SharedSecret {
    kem: &'static Kem,
    bytes: [u8; MAX_HASH_LEN],
}

impl SharedSecret {
    /// `ExtractAndExpand` (RFC 9180 section 4.1), whose `kem_context` is
    /// `enc || pk_rm`.
    fn new(kem: &'static Kem, dh: &[u8], enc: &[u8], pk_rm: &[u8]) -> Self {
        let labels = Labels::kem(kem);
        let eae_prk = labels.extract_prk(b"", b"eae_prk", dh);
        let mut bytes = [0u8; MAX_HASH_LEN];
        labels
            .expand(
                &eae_prk,
                b"shared_secret",
                &[enc, pk_rm],
                &mut bytes[..kem.kdf.hash_len()],
            )
            .expect("Nsecret is one hash output");
        Self { kem, bytes }
    }

    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.kem.kdf.hash_len()]
    }
}

/// The key schedule's `secret` and `key_schedule_context` (RFC 9180 section
/// 5.1), in base mode.
struct KeySchedule {
    secret: Prk,
    /// `mode || psk_id_hash || info_hash`.
    context: [u8; 1 + 2 * MAX_HASH_LEN],
    context_len: usize,
}

impl KeySchedule {
    fn new(labels: &Labels, shared_secret: &SharedSecret, info: &[u8]) -> Self {
        const MODE_BASE: u8 = 0x00;
        let psk_id_hash = labels.extract(b"", b"psk_id_hash", b"");
        let info_hash = labels.extract(b"", b"info_hash", info);
        let mut context = [0u8; 1 + 2 * MAX_HASH_LEN];
        let mut context_len = 0;
        for part in [&[MODE_BASE][..], psk_id_hash.as_ref(), info_hash.as_ref()] {
            context[context_len..context_len + part.len()].copy_from_slice(part);
            context_len += part.len();
        }
        Self {
            secret: labels.extract_prk(shared_secret.as_ref(), b"secret", b""),
            context,
            context_len,
        }
    }

    fn context(&self) -> &[u8] {
        &self.context[..self.context_len]
    }

    fn exporter(&self, labels: &Labels) -> Exporter {
        let mut secret = [0u8; MAX_HASH_LEN];
        let secret = &mut secret[..labels.kdf.hash_len()];
        labels
            .expand(&self.secret, b"exp", &[self.context()], secret)
            .expect("Nh is one hash output");
        Exporter {
            secret: Prk::new(labels.kdf, secret),
            suite_id: labels.suite_id,
        }
    }
}

/// The key schedule for `suite` after a KEM's shared secret.
fn schedule(suite: Suite, secret: &SharedSecret, info: &[u8]) -> (Sealing, Exporter) {
    let labels = Labels::hpke(secret.kem, suite.kdf, suite.aead.id);
    let schedule = KeySchedule::new(&labels, secret, info);
    let algorithm = suite.aead.algorithm;
    let mut key = [0u8; 32];
    let key = &mut key[..algorithm.key_len()];
    let mut base_nonce = [0u8; NONCE_LEN];
    labels
        .expand(&schedule.secret, b"key", &[schedule.context()], key)
        .and_then(|()| {
            labels.expand(
                &schedule.secret,
                b"base_nonce",
                &[schedule.context()],
                &mut base_nonce,
            )
        })
        .expect("a key and nonce are shorter than one hash output");
    let sealing = Sealing {
        key: aead::Key::new(algorithm, key).expect("the AEAD's key length"),
        base_nonce,
        seq: 0,
    };
    (sealing, schedule.exporter(&labels))
}

/// RFC 9180's `LabeledExtract` and `LabeledExpand` (section 4) under one
/// `suite_id`: a KEM's within it, a whole suite's in the key schedule.
struct Labels {
    kdf: &'static hkdf::Algorithm,
    suite_id: [u8; 10],
    suite_id_len: usize,
}

impl Labels {
    /// `"KEM" || I2OSP(kem_id, 2)`, with the KEM's own KDF.
    fn kem(kem: &Kem) -> Self {
        let mut suite_id = [0u8; 10];
        suite_id[..3].copy_from_slice(b"KEM");
        suite_id[3..5].copy_from_slice(&kem.id.to_be_bytes());
        Self {
            kdf: kem.kdf,
            suite_id,
            suite_id_len: 5,
        }
    }

    /// `"HPKE" || I2OSP(kem_id, 2) || I2OSP(kdf_id, 2) || I2OSP(aead_id, 2)`.
    fn hpke(kem: &Kem, kdf: &'static Kdf, aead_id: u16) -> Self {
        let mut suite_id = [0u8; 10];
        suite_id[..4].copy_from_slice(b"HPKE");
        suite_id[4..6].copy_from_slice(&kem.id.to_be_bytes());
        suite_id[6..8].copy_from_slice(&kdf.id.to_be_bytes());
        suite_id[8..].copy_from_slice(&aead_id.to_be_bytes());
        Self {
            kdf: kdf.hkdf,
            suite_id,
            suite_id_len: 10,
        }
    }

    fn suite_id(&self) -> &[u8] {
        &self.suite_id[..self.suite_id_len]
    }

    /// `LabeledExtract(salt, label, ikm)`.
    // The streaming state is a copy inside the call, so it goes unwiped, as
    // HKDF's does; callers have entered.
    fn extract(&self, salt: &[u8], label: &[u8], ikm: &[u8]) -> Digest {
        let key = hmac::Key::new(self.kdf.hmac(), salt);
        let mut ctx = key.start();
        for part in [VERSION, self.suite_id(), label, ikm] {
            ctx.update(part);
        }
        ctx.finish()
    }

    /// `LabeledExtract(salt, label, ikm)`, as a key to expand.
    fn extract_prk(&self, salt: &[u8], label: &[u8], ikm: &[u8]) -> Prk {
        Prk::new(self.kdf, self.extract(salt, label, ikm).as_ref())
    }

    /// `LabeledExpand(prk, label, info, len(out))`, as [`labeled_expand`].
    fn expand(&self, prk: &Prk, label: &[u8], info: &[&[u8]], out: &mut [u8]) -> Result<(), Error> {
        labeled_expand(self.suite_id(), prk, label, info, out)
    }
}

/// `LabeledExpand(prk, label, info, len(out))` into `out`, `info` given as
/// the parts it concatenates, at most two.
///
/// Fails with [`Error::WrongLength`], leaving `out` unchanged, past 255 hash
/// outputs.
fn labeled_expand(
    suite_id: &[u8],
    prk: &Prk,
    label: &[u8],
    info: &[&[u8]],
    out: &mut [u8],
) -> Result<(), Error> {
    let len = u16::try_from(out.len())
        .map_err(|_| Error::WrongLength)?
        .to_be_bytes();
    let mut parts: [&[u8]; 6] = [&len, VERSION, suite_id, label, &[], &[]];
    parts[4..4 + info.len()].copy_from_slice(info);
    prk.expand(&parts[..4 + info.len()], out.len()).fill(out)
}

const VERSION: &[u8] = b"HPKE-v1";

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use std::fs::File;
    use std::io::BufReader;

    use serde::Deserialize;

    use super::*;
    use crate::test::Expected;

    const KEMS: [&Kem; 4] = [
        &DHKEM_X25519_HKDF_SHA256,
        &DHKEM_P256_HKDF_SHA256,
        &DHKEM_P384_HKDF_SHA384,
        &DHKEM_P521_HKDF_SHA512,
    ];
    const KDFS: [&Kdf; 3] = [&HKDF_SHA256, &HKDF_SHA384, &HKDF_SHA512];
    const AEADS: [&Aead; 3] = [&AES_128_GCM, &AES_256_GCM, &CHACHA20_POLY1305];

    fn kem(id: u16) -> Option<&'static Kem> {
        KEMS.into_iter().find(|kem| kem.id == id)
    }

    fn kdf(id: u16) -> &'static Kdf {
        KDFS.into_iter().find(|kdf| kdf.id == id).unwrap()
    }

    fn aead(id: u16) -> Option<&'static Aead> {
        AEADS.into_iter().find(|aead| aead.id == id)
    }

    fn suites() -> impl Iterator<Item = Suite> {
        KDFS.into_iter()
            .flat_map(|kdf| AEADS.into_iter().map(move |aead| Suite { kdf, aead }))
    }

    /// Bytes derived from a secret, released for comparing.
    fn public(bytes: &[u8]) -> Vec<u8> {
        let bytes = bytes.to_vec();
        low::ct::public_slice(&bytes);
        bytes
    }

    fn exported(export: impl FnOnce(&mut [u8]) -> Result<(), Error>, len: usize) -> Vec<u8> {
        let mut out = vec![0u8; len];
        export(&mut out).unwrap();
        public(&out)
    }

    fn opened(recipient: &mut Recipient, aad: &[u8], ct: &[u8]) -> Result<Vec<u8>, Error> {
        let mut in_out = ct.to_vec();
        recipient
            .open_in_place(aad, &mut in_out)
            .map(|pt| public(pt))
    }

    /// `SetupBaseS` with the ephemeral key `DeriveKeyPair(ikm_e)` gives.
    fn sender_with(
        suite: Suite,
        public_key: &PublicKey,
        ikm_e: &[u8],
        info: &[u8],
    ) -> Result<(EncapsulatedKey, Sender), Error> {
        let ephemeral = PrivateKey::derive(public_key.kem, ikm_e)?;
        let (enc, secret) = public_key.encapsulate(&ephemeral.key)?;
        Ok((enc, Sender::schedule(suite, &secret, info)))
    }

    /// A context's `Export`, as `(exporter_context, out)`.
    type Export<'a> = &'a dyn Fn(&[u8], &mut [u8]) -> Result<(), Error>;

    #[derive(Deserialize)]
    struct Rfc9180 {
        kem_id: u16,
        kdf_id: u16,
        aead_id: u16,
        #[serde(with = "hex::serde")]
        info: Vec<u8>,
        #[serde(rename = "ikmR", with = "hex::serde")]
        ikm_r: Vec<u8>,
        #[serde(rename = "ikmE", with = "hex::serde")]
        ikm_e: Vec<u8>,
        #[serde(rename = "skRm", with = "hex::serde")]
        sk_rm: Vec<u8>,
        #[serde(rename = "pkRm", with = "hex::serde")]
        pk_rm: Vec<u8>,
        #[serde(rename = "pkEm", with = "hex::serde")]
        pk_em: Vec<u8>,
        #[serde(with = "hex::serde")]
        enc: Vec<u8>,
        encryptions: Vec<Rfc9180Encryption>,
        exports: Vec<Rfc9180Export>,
    }

    #[derive(Deserialize)]
    struct Rfc9180Encryption {
        #[serde(with = "hex::serde")]
        aad: Vec<u8>,
        #[serde(with = "hex::serde")]
        ct: Vec<u8>,
        #[serde(with = "hex::serde")]
        pt: Vec<u8>,
    }

    #[derive(Deserialize)]
    struct Rfc9180Export {
        #[serde(with = "hex::serde")]
        exporter_context: Vec<u8>,
        #[serde(rename = "L")]
        len: usize,
        #[serde(with = "hex::serde")]
        exported_value: Vec<u8>,
    }

    #[test]
    fn rfc9180() {
        let path = format!(
            "{}/../thirdparty/vectors/rfc9180/test-vectors.json",
            env!("CARGO_MANIFEST_DIR")
        );
        let file = BufReader::new(File::open(&path).unwrap());
        let mut count = 0;
        for vector in serde_json::Deserializer::from_reader(file).into_iter::<Rfc9180>() {
            let v = vector.unwrap();
            let kem = kem(v.kem_id).unwrap();
            let kdf = kdf(v.kdf_id);
            count += 1;

            let private_key = PrivateKey::derive(kem, &v.ikm_r).unwrap();
            assert_eq!(public(private_key.to_scalar().as_ref()), v.sk_rm);
            assert_eq!(private_key.public_key().as_ref(), v.pk_rm);
            let loaded = PrivateKey::from_scalar(kem, &v.sk_rm).unwrap();
            assert_eq!(loaded.public_key().as_ref(), v.pk_rm);
            let ephemeral = PrivateKey::derive(kem, &v.ikm_e).unwrap();
            assert_eq!(ephemeral.public_key().as_ref(), v.pk_em);

            let public_key = PublicKey::new(kem, &v.pk_rm).unwrap();
            let exports = |export: Export<'_>| {
                for e in &v.exports {
                    let value = exported(|out| export(&e.exporter_context, out), e.len);
                    assert_eq!(value, e.exported_value);
                }
            };

            let Some(aead) = aead(v.aead_id) else {
                assert_eq!(v.aead_id, EXPORT_ONLY);
                let ephemeral = PrivateKey::derive(kem, &v.ikm_e).unwrap();
                let (enc, secret) = public_key.encapsulate(&ephemeral.key).unwrap();
                assert_eq!(enc.as_ref(), v.enc);
                exports(&|c, out| Exporter::schedule(kdf, &secret, &v.info).export(c, out));
                let recipient = Exporter::recipient(kdf, &loaded, &v.enc, &v.info).unwrap();
                exports(&|c, out| recipient.export(c, out));
                continue;
            };

            let suite = Suite { kdf, aead };
            let (enc, mut sender) = sender_with(suite, &public_key, &v.ikm_e, &v.info).unwrap();
            assert_eq!(enc.as_ref(), v.enc);
            let mut recipient = Recipient::new(suite, &loaded, &v.enc, &v.info).unwrap();
            for e in &v.encryptions {
                let mut ct = e.pt.clone();
                sender.seal_in_place_append_tag(&e.aad, &mut ct).unwrap();
                assert_eq!(ct, e.ct);
                assert_eq!(opened(&mut recipient, &e.aad, &e.ct).unwrap(), e.pt);
            }
            exports(&|c, out| sender.export(c, out));
            exports(&|c, out| recipient.export(c, out));
        }
        // X25519, P-256, and P-521, each with SHA-256 and SHA-512 and four
        // AEADs.
        assert_eq!(count, 24);
    }

    #[derive(Deserialize, Debug)]
    struct WycheproofTest {
        #[serde(rename = "tcId")]
        id: usize,
        #[serde(rename = "skRm", default, with = "hex::serde")]
        sk_rm: Vec<u8>,
        #[serde(rename = "pkRm", with = "hex::serde")]
        pk_rm: Vec<u8>,
        #[serde(rename = "ikmE", default, with = "hex::serde")]
        ikm_e: Vec<u8>,
        #[serde(with = "hex::serde")]
        info: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        aad: Vec<u8>,
        #[serde(with = "hex::serde")]
        enc: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        ct: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        pt: Vec<u8>,
        #[serde(default)]
        decryptions: Vec<WycheproofDecryption>,
        result: Expected,
    }

    #[derive(Deserialize, Debug)]
    struct WycheproofDecryption {
        #[serde(rename = "sequenceNumber")]
        seq: u64,
        #[serde(with = "hex::serde")]
        aad: Vec<u8>,
        #[serde(with = "hex::serde")]
        ct: Vec<u8>,
        #[serde(with = "hex::serde")]
        pt: Vec<u8>,
        result: Expected,
    }

    #[derive(Deserialize)]
    struct WycheproofGroup {
        #[serde(rename = "kdfId")]
        kdf: u16,
        #[serde(rename = "aeadId")]
        aead: u16,
        tests: Vec<WycheproofTest>,
    }

    /// Each test of a Wycheproof HPKE file with its group's suite.
    fn wycheproof_hpke(name: &str) -> Vec<(Suite, WycheproofTest)> {
        // `crate::test::wycheproof` reads tests alone; these need their
        // group's suite.
        let path = format!(
            "{}/../thirdparty/wycheproof/testvectors_v1/{name}",
            env!("CARGO_MANIFEST_DIR")
        );
        #[derive(Deserialize)]
        struct TestFile {
            #[serde(rename = "testGroups")]
            groups: Vec<WycheproofGroup>,
        }
        let file: TestFile =
            serde_json::from_reader(BufReader::new(File::open(&path).unwrap())).unwrap();
        let tests: Vec<_> = file
            .groups
            .into_iter()
            .flat_map(|group| {
                let suite = Suite {
                    kdf: kdf(group.kdf),
                    aead: aead(group.aead).unwrap(),
                };
                group.tests.into_iter().map(move |test| (suite, test))
            })
            .collect();
        assert!(!tests.is_empty());
        tests
    }

    const X25519: &Kem = &DHKEM_X25519_HKDF_SHA256;

    #[test]
    fn wycheproof_encap() {
        for (suite, test) in wycheproof_hpke("hpke_x25519_encap_test.json") {
            let result = PublicKey::new(X25519, &test.pk_rm)
                .and_then(|public_key| sender_with(suite, &public_key, &test.ikm_e, &test.info));
            match (test.result, result) {
                (Expected::Valid | Expected::Acceptable, Ok((enc, mut sender))) => {
                    assert_eq!(enc.as_ref(), test.enc, "{}", test.id);
                    let mut ct = test.pt.clone();
                    sender.seal_in_place_append_tag(&test.aad, &mut ct).unwrap();
                    assert_eq!(ct, test.ct, "{}", test.id);
                    if !test.sk_rm.is_empty() {
                        let private_key = PrivateKey::from_scalar(X25519, &test.sk_rm).unwrap();
                        let mut recipient =
                            Recipient::new(suite, &private_key, enc.as_ref(), &test.info).unwrap();
                        assert_eq!(opened(&mut recipient, &test.aad, &ct).unwrap(), test.pt);
                    }
                }
                (Expected::Invalid, Err(Error::KeyRejected(_))) => {}
                (expected, result) => panic!(
                    "{}: expected {expected:?}, got {:?}",
                    test.id,
                    result.map(|_| ())
                ),
            }
        }
    }

    #[test]
    fn wycheproof_decrypt() {
        for (suite, test) in wycheproof_hpke("hpke_x25519_decrypt_test.json") {
            let private_key = PrivateKey::from_scalar(X25519, &test.sk_rm).unwrap();
            assert_eq!(private_key.public_key().as_ref(), test.pk_rm, "{}", test.id);
            let result = Recipient::new(suite, &private_key, &test.enc, &test.info)
                .and_then(|mut recipient| opened(&mut recipient, &test.aad, &test.ct));
            match (test.result, result) {
                (Expected::Valid | Expected::Acceptable, Ok(pt)) => {
                    assert_eq!(pt, test.pt, "{}", test.id)
                }
                (Expected::Invalid | Expected::Acceptable, Err(_)) => {}
                (expected, result) => {
                    panic!("{}: expected {expected:?}, got {result:?}", test.id)
                }
            }

            // An honest sender's message seals the same way here.
            if !test.ikm_e.is_empty() {
                let public_key = PublicKey::new(X25519, &test.pk_rm).unwrap();
                let (enc, mut sender) =
                    sender_with(suite, &public_key, &test.ikm_e, &test.info).unwrap();
                assert_eq!(enc.as_ref(), test.enc, "{}", test.id);
                let mut ct = test.pt.clone();
                sender.seal_in_place_append_tag(&test.aad, &mut ct).unwrap();
                assert_eq!(ct, test.ct, "{}", test.id);
            }
        }
    }

    #[test]
    fn wycheproof_sequence() {
        for (suite, test) in wycheproof_hpke("hpke_x25519_sequence_test.json") {
            assert_eq!(test.result, Expected::Valid, "{}", test.id);
            let private_key = PrivateKey::from_scalar(X25519, &test.sk_rm).unwrap();
            let mut recipient = Recipient::new(suite, &private_key, &test.enc, &test.info).unwrap();
            for d in &test.decryptions {
                assert_eq!(recipient.sealing.seq, d.seq, "{}", test.id);
                match (d.result, opened(&mut recipient, &d.aad, &d.ct)) {
                    (Expected::Valid, Ok(pt)) => assert_eq!(pt, d.pt, "{}", test.id),
                    (Expected::Invalid, Err(Error::DecryptFailed)) => {}
                    (expected, result) => {
                        panic!("{}: expected {expected:?}, got {result:?}", test.id)
                    }
                }
            }

            if !test.ikm_e.is_empty() {
                let public_key = PublicKey::new(X25519, &test.pk_rm).unwrap();
                let (_, mut sender) =
                    sender_with(suite, &public_key, &test.ikm_e, &test.info).unwrap();
                for d in &test.decryptions {
                    let mut ct = d.pt.clone();
                    sender.seal_in_place_append_tag(&d.aad, &mut ct).unwrap();
                    assert_eq!(ct, d.ct, "{}", test.id);
                }
            }
        }
    }

    #[test]
    fn every_suite_round_trips() {
        for kem in KEMS {
            let private_key = PrivateKey::generate(kem).unwrap();
            let public_key = private_key.public_key();
            assert_eq!(public_key.as_ref().len(), kem.public_len);
            assert_eq!(
                public(private_key.to_scalar().as_ref()).len(),
                kem.scalar_len
            );
            for suite in suites() {
                let (enc, mut sender) = Sender::new(suite, &public_key, b"info").unwrap();
                let mut recipient =
                    Recipient::new(suite, &private_key, enc.as_ref(), b"info").unwrap();
                for message in [&b""[..], b"one", &[7; 1000]] {
                    let mut in_out = message.to_vec();
                    sender
                        .seal_in_place_append_tag(b"aad", &mut in_out)
                        .unwrap();
                    assert_eq!(in_out.len(), message.len() + 16);
                    assert_eq!(opened(&mut recipient, b"aad", &in_out).unwrap(), message);
                }
                let len = 255 * suite.kdf.hkdf.hash_len();
                assert_eq!(
                    exported(|out| sender.export(b"ctx", out), len),
                    exported(|out| recipient.export(b"ctx", out), len),
                );
                assert_eq!(
                    sender.export(b"ctx", &mut vec![0; len + 1]),
                    Err(Error::WrongLength)
                );

                let (enc, exporter) = Exporter::sender(suite.kdf, &public_key, b"info").unwrap();
                let other =
                    Exporter::recipient(suite.kdf, &private_key, enc.as_ref(), b"info").unwrap();
                assert_eq!(
                    exported(|out| exporter.export(b"", out), 0),
                    exported(|out| other.export(b"", out), 0),
                );
                assert_eq!(
                    exported(|out| exporter.export(b"ctx", out), 42),
                    exported(|out| other.export(b"ctx", out), 42),
                );
            }
        }
    }

    #[test]
    fn suite_and_info_bind() {
        let private_key = PrivateKey::generate(&DHKEM_P256_HKDF_SHA256).unwrap();
        let suite = Suite {
            kdf: &HKDF_SHA256,
            aead: &AES_128_GCM,
        };
        let (enc, mut sender) = Sender::new(suite, &private_key.public_key(), b"info").unwrap();
        let mut sealed = b"hello".to_vec();
        sender.seal_in_place_append_tag(b"", &mut sealed).unwrap();

        let other_kdf = Suite {
            kdf: &HKDF_SHA384,
            ..suite
        };
        for (suite, info) in [(other_kdf, &b"info"[..]), (suite, b"other")] {
            let mut recipient = Recipient::new(suite, &private_key, enc.as_ref(), info).unwrap();
            assert_eq!(
                opened(&mut recipient, b"", &sealed),
                Err(Error::DecryptFailed)
            );
        }
    }

    /// `point`, an uncompressed NIST point, compressed.
    fn compressed(point: &[u8]) -> Vec<u8> {
        let mut compressed = vec![2 | (point[point.len() - 1] & 1)];
        compressed.extend(&point[1..1 + point.len() / 2]);
        compressed
    }

    // aws-lc-rs takes a compressed `enc`, hashing it as sent, so a sender
    // that sends one hashes it so too.
    #[test]
    fn opens_compressed_enc() {
        let suite = Suite {
            kdf: &HKDF_SHA256,
            aead: &AES_128_GCM,
        };
        for kem in KEMS.iter().filter(|kem| kem.candidate_mask.is_some()) {
            let private_key = PrivateKey::generate(kem).unwrap();
            let pk_rm = private_key.public_key();
            let ephemeral = PrivateKey::generate(kem).unwrap();
            let enc = compressed(ephemeral.public_key().as_ref());
            let dh = ephemeral.key.agree(pk_rm.as_ref()).unwrap();
            let secret = SharedSecret::new(kem, dh.as_ref(), &enc, pk_rm.as_ref());
            let mut sender = Sender::schedule(suite, &secret, b"info");
            let mut sealed = b"message".to_vec();
            sender.seal_in_place_append_tag(b"", &mut sealed).unwrap();

            let mut recipient = Recipient::new(suite, &private_key, &enc, b"info").unwrap();
            assert_eq!(opened(&mut recipient, b"", &sealed).unwrap(), b"message");
            // Its uncompressed form is another `enc`.
            let enc = ephemeral.public_key();
            let mut recipient = Recipient::new(suite, &private_key, enc.as_ref(), b"info").unwrap();
            assert_eq!(
                opened(&mut recipient, b"", &sealed),
                Err(Error::DecryptFailed)
            );
        }
    }

    #[test]
    fn refuses_malformed_keys() {
        for kem in KEMS {
            let private_key = PrivateKey::generate(kem).unwrap();
            let public_key = private_key.public_key();
            let suite = Suite {
                kdf: &HKDF_SHA256,
                aead: &AES_128_GCM,
            };
            let rejected = |result: Result<(), Error>| {
                assert!(matches!(result, Err(Error::KeyRejected(_))), "{kem:?}")
            };

            let bytes = public_key.as_ref();
            let mut long = bytes.to_vec();
            long.push(0);
            for bad in [&bytes[..bytes.len() - 1], &long, &[]] {
                rejected(PublicKey::new(kem, bad).map(|_| ()));
                rejected(Recipient::new(suite, &private_key, bad, b"").map(|_| ()));
                rejected(Exporter::recipient(&HKDF_SHA256, &private_key, bad, b"").map(|_| ()));
            }
            if kem.candidate_mask.is_some() {
                // RFC 9180 serializes a point uncompressed, and no
                // recipient opens what is sealed to a compressed one (see
                // `opens_compressed_enc`).
                rejected(PublicKey::new(kem, &compressed(bytes)).map(|_| ()));

                let mut off_curve = bytes.to_vec();
                off_curve[kem.public_len - 1] ^= 1;
                rejected(PublicKey::new(kem, &off_curve).map(|_| ()));
                rejected(Recipient::new(suite, &private_key, &off_curve, b"").map(|_| ()));

                rejected(PrivateKey::from_scalar(kem, &vec![0; kem.scalar_len]).map(|_| ()));
                rejected(PrivateKey::from_scalar(kem, &vec![0xff; kem.scalar_len]).map(|_| ()));
            } else {
                // A small-order point gives an all-zero shared secret.
                let small_order = [0u8; 32];
                let public_key = PublicKey::new(kem, &small_order).unwrap();
                rejected(Sender::new(suite, &public_key, b"").map(|_| ()));
                rejected(Exporter::sender(&HKDF_SHA256, &public_key, b"").map(|_| ()));
                rejected(Recipient::new(suite, &private_key, &small_order, b"").map(|_| ()));
            }
            rejected(PrivateKey::from_scalar(kem, &vec![1; kem.scalar_len + 1]).map(|_| ()));
        }
    }

    #[test]
    fn failed_open_keeps_sequence() {
        let private_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256).unwrap();
        let suite = Suite {
            kdf: &HKDF_SHA256,
            aead: &CHACHA20_POLY1305,
        };
        let (enc, mut sender) = Sender::new(suite, &private_key.public_key(), b"").unwrap();
        let mut recipient = Recipient::new(suite, &private_key, enc.as_ref(), b"").unwrap();
        let mut first = b"first".to_vec();
        sender.seal_in_place_append_tag(b"", &mut first).unwrap();
        let mut second = b"second".to_vec();
        sender.seal_in_place_append_tag(b"", &mut second).unwrap();

        assert_eq!(
            opened(&mut recipient, b"", &second),
            Err(Error::DecryptFailed)
        );
        assert_eq!(
            opened(&mut recipient, b"", &[0; 15]),
            Err(Error::DecryptFailed)
        );
        assert_eq!(opened(&mut recipient, b"", &first).unwrap(), b"first");
        assert_eq!(
            opened(&mut recipient, b"", &first),
            Err(Error::DecryptFailed)
        );
        assert_eq!(opened(&mut recipient, b"", &second).unwrap(), b"second");
    }

    /// A buffer with no room for a tag, whose `extend` panics.
    /// wasm32-wasip2 aborts on panic, so the test that catches it cannot run there.
    #[cfg(not(target_family = "wasm"))]
    struct NoRoom(Vec<u8>);

    #[cfg(not(target_family = "wasm"))]
    impl AsMut<[u8]> for NoRoom {
        fn as_mut(&mut self) -> &mut [u8] {
            &mut self.0
        }
    }

    #[cfg(not(target_family = "wasm"))]
    impl<'a> Extend<&'a u8> for NoRoom {
        fn extend<I: IntoIterator<Item = &'a u8>>(&mut self, _: I) {
            panic!("no room for the tag");
        }
    }

    #[test]
    #[cfg(not(target_family = "wasm"))]
    fn panicking_append_spends_nonce() {
        let private_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256).unwrap();
        let suite = Suite {
            kdf: &HKDF_SHA256,
            aead: &AES_128_GCM,
        };
        let (_, mut sender) = Sender::new(suite, &private_key.public_key(), b"").unwrap();
        let mut lost = NoRoom(vec![0; 16]);
        let sealed = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            sender.seal_in_place_append_tag(b"", &mut lost)
        }));
        assert!(sealed.is_err());

        // Both stream ciphers: the next message's keystream would repeat
        // the encrypted one's under the same nonce.
        let mut next = vec![0; 16];
        sender.seal_in_place_append_tag(b"", &mut next).unwrap();
        assert_ne!(lost.0, next[..16]);
    }

    #[test]
    fn message_limit() {
        let private_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256).unwrap();
        let suite = Suite {
            kdf: &HKDF_SHA256,
            aead: &AES_256_GCM,
        };
        let (enc, mut sender) = Sender::new(suite, &private_key.public_key(), b"").unwrap();
        let mut recipient = Recipient::new(suite, &private_key, enc.as_ref(), b"").unwrap();
        sender.sealing.seq = u64::MAX - 1;
        recipient.sealing.seq = u64::MAX - 1;

        let mut last = b"last".to_vec();
        sender.seal_in_place_append_tag(b"", &mut last).unwrap();
        assert_eq!(opened(&mut recipient, b"", &last).unwrap(), b"last");

        let mut refused = b"refused".to_vec();
        assert_eq!(
            sender.seal_in_place_append_tag(b"", &mut refused),
            Err(Error::MessageLimitReached)
        );
        assert_eq!(refused, b"refused");
        assert_eq!(
            opened(&mut recipient, b"", &last),
            Err(Error::MessageLimitReached)
        );
    }

    #[test]
    fn derives_from_any_length() {
        for kem in KEMS {
            // MLS's P-521 suite derives keys from 64 bytes.
            for len in [0, 1, kem.scalar_len - 2, kem.scalar_len, 200] {
                let ikm = vec![0x42; len];
                let key = PrivateKey::derive(kem, &ikm).unwrap();
                let again = PrivateKey::derive(kem, &ikm).unwrap();
                assert_eq!(key.public_key().as_ref(), again.public_key().as_ref());
            }
        }
    }

    #[test]
    fn secret_decapsulation() {
        // Under `admin/ctgrind`, nothing may branch on or index by the
        // private key, the shared secret, or the keys and nonces derived from
        // it, opening a message included. `from_scalar` marks the key.
        let info = b"info";
        for kem in KEMS {
            let private_key = PrivateKey::generate(kem).unwrap();
            let scalar = public(private_key.to_scalar().as_ref());
            for suite in [
                Suite {
                    kdf: &HKDF_SHA256,
                    aead: &AES_128_GCM,
                },
                Suite {
                    kdf: &HKDF_SHA512,
                    aead: &CHACHA20_POLY1305,
                },
            ] {
                let (enc, mut sender) =
                    Sender::new(suite, &private_key.public_key(), info).unwrap();
                let mut sealed = b"message".to_vec();
                sender
                    .seal_in_place_append_tag(b"aad", &mut sealed)
                    .unwrap();

                let loaded = PrivateKey::from_scalar(kem, &scalar).unwrap();
                let mut recipient = Recipient::new(suite, &loaded, enc.as_ref(), info).unwrap();
                assert_eq!(opened(&mut recipient, b"aad", &sealed).unwrap(), b"message");
                assert_eq!(
                    exported(|out| recipient.export(b"ctx", out), 32),
                    exported(|out| sender.export(b"ctx", out), 32),
                );
                let exporter = Exporter::recipient(suite.kdf, &loaded, enc.as_ref(), info).unwrap();
                exported(|out| exporter.export(b"ctx", out), 32);
            }
        }
    }

    #[test]
    fn secret_key_derivation() {
        // Under `admin/ctgrind`, nothing may branch on or index by `ikm` but
        // whether a NIST curve's candidate is in range, which is public.
        for kem in KEMS {
            let ikm = [0x5a; 66];
            let wanted = PrivateKey::derive(kem, &ikm).unwrap().public_key();

            low::ct::secret_slice(&ikm);
            let key = PrivateKey::derive(kem, &ikm).unwrap();
            let scalar = public(key.to_scalar().as_ref());
            assert_eq!(key.public_key().as_ref(), wanted.as_ref());
            assert_eq!(
                PrivateKey::from_scalar(kem, &scalar)
                    .unwrap()
                    .public_key()
                    .as_ref(),
                wanted.as_ref()
            );
        }
    }

    #[test]
    fn debug_shows_no_secret() {
        let key = PrivateKey::derive(&DHKEM_P384_HKDF_SHA384, b"ikm").unwrap();
        assert_eq!(
            format!("{key:?}"),
            "PrivateKey { kem: DHKEM(P-384, HKDF-SHA384), .. }"
        );
        let suite = Suite {
            kdf: &HKDF_SHA384,
            aead: &AES_256_GCM,
        };
        let (_, sender) = Sender::new(suite, &key.public_key(), b"").unwrap();
        assert_eq!(format!("{sender:?}"), "Sender { .. }");
    }
}
