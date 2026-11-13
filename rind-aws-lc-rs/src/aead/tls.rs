//! AES-GCM keys for TLS records, which refuse a nonce whose sequence number
//! does not increase, as AWS-LC's TLS AEADs do.

use core::fmt;
use core::ops::RangeFrom;

use super::{Aad, Algorithm, LessSafeKey, NONCE_LEN, Nonce, Tag, UnboundKey};
use crate::error::Unspecified;

/// The TLS version whose nonce construction a key checks.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum TlsProtocolId {
    /// TLS 1.2 (RFC 5288), whose explicit nonce must increase.
    TLS12,
    /// TLS 1.3 (RFC 8446), whose sequence number, the nonce XOR the first
    /// nonce, must increase.
    TLS13,
}

/// A TLS record sealing key, for AES-128-GCM or AES-256-GCM.
pub struct TlsRecordSealingKey {
    key: LessSafeKey,
    protocol: TlsProtocolId,
    min_next: u64,
    // TLS 1.3's first nonce is the IV itself, whose last 8 bytes mask every
    // later sequence number.
    mask: Option<u64>,
}

impl TlsRecordSealingKey {
    /// Expands `key_bytes` for `algorithm`, which must be [`super::AES_128_GCM`] or [`super::AES_256_GCM`].
    pub fn new(
        algorithm: &'static Algorithm,
        protocol: TlsProtocolId,
        key_bytes: &[u8],
    ) -> Result<Self, Unspecified> {
        Ok(Self {
            key: tls_key(algorithm, key_bytes)?,
            protocol,
            min_next: 0,
            mask: None,
        })
    }

    // Takes `nonce`'s sequence number, refused unless it is above the last.
    // A seal it refuses zeroes its output, as AWS-LC's does, so a caller that
    // ignores the error sends no plaintext.
    fn check(&mut self, nonce: &Nonce) -> Result<(), Unspecified> {
        let given = u64::from_be_bytes(nonce.0[NONCE_LEN - 8..].try_into()?);
        let given = match self.protocol {
            TlsProtocolId::TLS12 => given,
            TlsProtocolId::TLS13 => given ^ *self.mask.get_or_insert(given),
        };
        if given == u64::MAX || given < self.min_next {
            return Err(Unspecified);
        }
        self.min_next = given + 1;
        Ok(())
    }

    /// Seals `in_out` in place and appends the tag to it.
    pub fn seal_in_place_append_tag<A, InOut>(
        &mut self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut InOut,
    ) -> Result<(), Unspecified>
    where
        A: AsRef<[u8]>,
        InOut: AsMut<[u8]> + for<'in_out> Extend<&'in_out u8>,
    {
        if let Err(refused) = self.check(&nonce) {
            // aws-lc-rs appends room for the tag before AWS-LC refuses.
            in_out.extend(&[0; super::TAG_LEN]);
            in_out.as_mut().fill(0);
            return Err(refused);
        }
        self.key.seal_in_place_append_tag(nonce, aad, in_out)
    }

    /// Seals `in_out` in place and returns the tag.
    pub fn seal_in_place_separate_tag<A>(
        &mut self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &mut [u8],
    ) -> Result<Tag, Unspecified>
    where
        A: AsRef<[u8]>,
    {
        if let Err(refused) = self.check(&nonce) {
            in_out.fill(0);
            return Err(refused);
        }
        self.key.seal_in_place_separate_tag(nonce, aad, in_out)
    }

    /// As [`LessSafeKey::seal_out_of_place_scatter`].
    pub fn seal_out_of_place_scatter<A>(
        &mut self,
        nonce: Nonce,
        aad: Aad<A>,
        in_plaintext: &[u8],
        out_ciphertext: &mut [u8],
        extra_in: &[u8],
        extra_out_and_tag: &mut [u8],
    ) -> Result<(), Unspecified>
    where
        A: AsRef<[u8]>,
    {
        // Bad buffers leave the nonce unused, as in aws-lc-rs.
        super::check_scatter(in_plaintext, out_ciphertext, extra_in, extra_out_and_tag)?;
        if let Err(refused) = self.check(&nonce) {
            out_ciphertext.fill(0);
            extra_out_and_tag.fill(0);
            return Err(refused);
        }
        self.key.seal_out_of_place_scatter(
            nonce,
            aad,
            in_plaintext,
            out_ciphertext,
            extra_in,
            extra_out_and_tag,
        )
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.key.algorithm
    }

    /// The TLS version this key checks nonces for.
    pub fn tls_protocol_id(&self) -> TlsProtocolId {
        self.protocol
    }
}

impl fmt::Debug for TlsRecordSealingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsRecordSealingKey")
            .field("key", &self.key)
            .field("protocol", &self.protocol)
            .finish()
    }
}

/// A TLS record opening key, for AES-128-GCM or AES-256-GCM.
pub struct TlsRecordOpeningKey {
    key: LessSafeKey,
    protocol: TlsProtocolId,
}

impl TlsRecordOpeningKey {
    /// Expands `key_bytes` for `algorithm`, which must be [`super::AES_128_GCM`] or [`super::AES_256_GCM`].
    pub fn new(
        algorithm: &'static Algorithm,
        protocol: TlsProtocolId,
        key_bytes: &[u8],
    ) -> Result<Self, Unspecified> {
        Ok(Self {
            key: tls_key(algorithm, key_bytes)?,
            protocol,
        })
    }

    /// Opens `in_out`, the ciphertext followed by its tag, and returns the plaintext.
    pub fn open_in_place<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
    ) -> Result<&'in_out mut [u8], Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.key.open_in_place(nonce, aad, in_out)
    }

    /// Opens `in_out[ciphertext_and_tag]`, and returns the plaintext, moved to the front of `in_out`.
    pub fn open_within<'in_out, A>(
        &self,
        nonce: Nonce,
        aad: Aad<A>,
        in_out: &'in_out mut [u8],
        ciphertext_and_tag: RangeFrom<usize>,
    ) -> Result<&'in_out mut [u8], Unspecified>
    where
        A: AsRef<[u8]>,
    {
        self.key.open_within(nonce, aad, in_out, ciphertext_and_tag)
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.key.algorithm
    }

    /// The TLS version this key is for.
    pub fn tls_protocol_id(&self) -> TlsProtocolId {
        self.protocol
    }
}

impl fmt::Debug for TlsRecordOpeningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsRecordOpeningKey")
            .field("key", &self.key)
            .field("protocol", &self.protocol)
            .finish()
    }
}

fn tls_key(algorithm: &'static Algorithm, key_bytes: &[u8]) -> Result<LessSafeKey, Unspecified> {
    if !algorithm.is_aes_gcm_128_or_256() {
        return Err(Unspecified);
    }
    Ok(LessSafeKey::new(UnboundKey::new(algorithm, key_bytes)?))
}
