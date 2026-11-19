//! The `fips` build's TLS record keys, held in rind-fips's module: sealing
//! through its TLS 1.3 IV construction, opening through its AES-GCM key.
//!
//! The module seals only TLS 1.3 records, so a TLS 1.2 sealing key is
//! refused here rather than run outside the module. It opens any AES-GCM
//! message, so an opening key takes either version.

use core::fmt;
use core::ops::RangeFrom;

use rind_fips::aead as module;
use zeroize::Zeroize;

use super::{
    Aad, Algorithm, AlgorithmId, NONCE_LEN, Nonce, TAG_LEN, Tag, TlsProtocolId, append_tag_room,
    check_scatter,
};
use crate::error::Unspecified;

/// The module's algorithm for `algorithm`, which must be AES-128-GCM or AES-256-GCM.
fn module_algorithm(algorithm: &Algorithm) -> Result<&'static module::Algorithm, Unspecified> {
    match algorithm.id {
        AlgorithmId::AES_128_GCM => Ok(&module::AES_128_GCM),
        AlgorithmId::AES_256_GCM => Ok(&module::AES_256_GCM),
        _ => Err(Unspecified),
    }
}

fn module_nonce(nonce: Nonce) -> module::Nonce {
    module::Nonce::assume_unique_for_key(nonce.0)
}

fn aws_tag(tag: module::Tag) -> Tag {
    let mut bytes = [0u8; TAG_LEN];
    bytes.copy_from_slice(tag.as_ref());
    Tag(bytes)
}

/// A TLS record sealing key, for AES-128-GCM or AES-256-GCM, held in the module.
pub struct TlsRecordSealingKey {
    key: module::TlsRecordSealingKey,
    algorithm: &'static Algorithm,
}

impl TlsRecordSealingKey {
    /// Expands `key_bytes` for `algorithm`, which must be [`super::AES_128_GCM`] or
    /// [`super::AES_256_GCM`], in the module. Fails for [`TlsProtocolId::TLS12`], which
    /// the module does not seal.
    pub fn new(
        algorithm: &'static Algorithm,
        protocol: TlsProtocolId,
        key_bytes: &[u8],
    ) -> Result<Self, Unspecified> {
        if protocol != TlsProtocolId::TLS13 {
            return Err(Unspecified);
        }
        let key = module::TlsRecordSealingKey::new(
            module_algorithm(algorithm)?,
            module::TlsProtocolId::TLS13,
            key_bytes,
        )
        .map_err(|_| Unspecified)?;
        Ok(Self { key, algorithm })
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
        // Bad buffers leave the nonce unused, as in aws-lc-rs.
        let (plaintext, tag_out) = append_tag_room(in_out)?;
        let tag = self
            .key
            .seal_in_place_separate_tag(module_nonce(nonce), aad.as_ref(), plaintext)
            .map_err(|_| Unspecified)?;
        tag_out.copy_from_slice(tag.as_ref());
        Ok(())
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
        self.key
            .seal_in_place_separate_tag(module_nonce(nonce), aad.as_ref(), in_out)
            .map(aws_tag)
            .map_err(|_| Unspecified)
    }

    /// Seals `in_plaintext` into `out_ciphertext`, and `extra_in` into the front of
    /// `extra_out_and_tag`, whose last 16 bytes are the tag.
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
        check_scatter(in_plaintext, out_ciphertext, extra_in, extra_out_and_tag)?;
        // The module seals one buffer: the plaintext, then the extra bytes.
        let split = in_plaintext.len();
        let mut message = alloc::vec::Vec::with_capacity(split + extra_in.len());
        message.extend_from_slice(in_plaintext);
        message.extend_from_slice(extra_in);
        let sealed =
            self.key
                .seal_in_place_separate_tag(module_nonce(nonce), aad.as_ref(), &mut message);
        let result = match sealed {
            Ok(tag) => {
                out_ciphertext.copy_from_slice(&message[..split]);
                let (extra_out, tag_out) = extra_out_and_tag.split_at_mut(extra_in.len());
                extra_out.copy_from_slice(&message[split..]);
                tag_out.copy_from_slice(tag.as_ref());
                Ok(())
            }
            Err(_) => {
                out_ciphertext.fill(0);
                extra_out_and_tag.fill(0);
                Err(Unspecified)
            }
        };
        message.zeroize();
        result
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// The TLS version this key checks nonces for: always TLS 1.3.
    pub fn tls_protocol_id(&self) -> TlsProtocolId {
        TlsProtocolId::TLS13
    }
}

impl fmt::Debug for TlsRecordSealingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsRecordSealingKey")
            .field("algorithm", &self.algorithm)
            .field("protocol", &TlsProtocolId::TLS13)
            .finish_non_exhaustive()
    }
}

/// A TLS record opening key, for AES-128-GCM or AES-256-GCM, held in the module.
pub struct TlsRecordOpeningKey {
    key: module::Key,
    algorithm: &'static Algorithm,
    protocol: TlsProtocolId,
}

impl TlsRecordOpeningKey {
    /// Expands `key_bytes` for `algorithm`, which must be [`super::AES_128_GCM`] or
    /// [`super::AES_256_GCM`], in the module.
    pub fn new(
        algorithm: &'static Algorithm,
        protocol: TlsProtocolId,
        key_bytes: &[u8],
    ) -> Result<Self, Unspecified> {
        let key =
            module::Key::new(module_algorithm(algorithm)?, key_bytes).map_err(|_| Unspecified)?;
        Ok(Self {
            key,
            algorithm,
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
        self.key
            .open_in_place(module_nonce(nonce), aad.as_ref(), in_out)
            .map_err(|_| Unspecified)
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
        let start = ciphertext_and_tag.start;
        if start > in_out.len() {
            return Err(Unspecified);
        }
        let plaintext_len = self
            .key
            .open_in_place(module_nonce(nonce), aad.as_ref(), &mut in_out[start..])
            .map_err(|_| Unspecified)?
            .len();
        in_out.copy_within(start..start + plaintext_len, 0);
        Ok(&mut in_out[..plaintext_len])
    }

    /// The algorithm this key was made for.
    pub fn algorithm(&self) -> &'static Algorithm {
        self.algorithm
    }

    /// The TLS version this key is for.
    pub fn tls_protocol_id(&self) -> TlsProtocolId {
        self.protocol
    }
}

impl fmt::Debug for TlsRecordOpeningKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("TlsRecordOpeningKey")
            .field("algorithm", &self.algorithm)
            .field("protocol", &self.protocol)
            .finish_non_exhaustive()
    }
}

// Nonces are this long in both crates.
const _: () = assert!(NONCE_LEN == 12);
