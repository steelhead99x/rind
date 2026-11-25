// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! PBKDF2 on pyca/verified-garbage's routine, where this CPU runs it and it
//! measured faster than rind's loop: see `low::pbkdf2_vg`.
//!
//! VG's routine keys HMAC itself on every call, so a [`Key`] holds HMAC's
//! key rather than its keyed states: the secret, or its hash where it is
//! longer than a block, which HMAC pads to the same block.

use core::num::NonZeroU32;

use super::sha1::Sha1Context;
use super::sha2::{Sha256Context, Sha384Context, Sha512Context};
use crate::Error;
use crate::low::pbkdf2_vg::Pbkdf2;
use crate::low::{Entry, Zeroable, ZeroableRef, ct, ct_equal, zeroise};

/// One hash's PBKDF2 on VG's routine.
#[derive(Clone, Copy)]
pub(crate) enum Algorithm {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
}

impl Algorithm {
    // VG's routine for this hash, if this CPU runs it.
    fn routine(self) -> Option<&'static Pbkdf2> {
        match self {
            Self::Sha1 => Pbkdf2::sha1(),
            Self::Sha256 => Pbkdf2::sha256(),
            Self::Sha384 => Pbkdf2::sha384(),
            Self::Sha512 => Pbkdf2::sha512(),
        }
    }

    // The hash's output length, which is HMAC's tag length.
    fn tag_len(self) -> usize {
        match self {
            Self::Sha1 => Sha1Context::OUTPUT_SZ,
            Self::Sha256 => Sha256Context::OUTPUT_SZ,
            Self::Sha384 => Sha384Context::OUTPUT_SZ,
            Self::Sha512 => Sha512Context::OUTPUT_SZ,
        }
    }

    // Writes HMAC's key for `secret` to the start of `key`, returning its
    // length: the secret, or its hash where it is longer than a block.
    fn hmac_key(self, secret: &[u8], key: &mut [u8; 128]) -> usize {
        let block = match self {
            Self::Sha1 => Sha1Context::BLOCK_SZ,
            Self::Sha256 => Sha256Context::BLOCK_SZ,
            Self::Sha384 | Self::Sha512 => Sha512Context::BLOCK_SZ,
        };
        if secret.len() <= block {
            key[..secret.len()].copy_from_slice(secret);
            return secret.len();
        }
        macro_rules! hash {
            ($context:ident) => {{
                let mut ctx = $context::new();
                ctx.update(secret);
                let digest = ctx.finish();
                key[..digest.len()].copy_from_slice(&digest);
                digest.len()
            }};
        }
        match self {
            Self::Sha1 => hash!(Sha1Context),
            Self::Sha256 => hash!(Sha256Context),
            Self::Sha384 => hash!(Sha384Context),
            Self::Sha512 => hash!(Sha512Context),
        }
    }
}

/// A secret keyed for VG's routine. The caller wipes it with the value that
/// holds it: all-zero is a valid value.
pub(crate) struct Key {
    routine: ZeroableRef<Pbkdf2>,
    tag_len: usize,
    key: [u8; 128],
    len: usize,
}

impl Zeroable for Key {}

impl Key {
    /// Keys `algorithm` with `secret`, if this CPU runs its VG routine.
    pub(crate) fn new(algorithm: Algorithm, secret: &[u8]) -> Option<Self> {
        let routine = algorithm.routine()?;
        let _entry = Entry::new_secret();
        let mut key = [0u8; 128];
        let len = algorithm.hmac_key(secret, &mut key);
        Some(Self {
            routine: ZeroableRef::new(routine),
            tag_len: algorithm.tag_len(),
            key,
            len,
        })
    }

    /// `pbkdf2::Secret::derive`.
    pub(crate) fn derive(
        &self,
        iterations: NonZeroU32,
        salt: &[u8],
        out: &mut [u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        self.check_len(out.len())?;
        self.routine
            .get()
            .derive(&self.key[..self.len], salt, iterations, out);
        Ok(())
    }

    /// `pbkdf2::Secret::verify`, over the whole derived key, since VG's
    /// routine derives no block alone. That key is heap scratch derived from
    /// the secret, so it is wiped.
    pub(crate) fn verify(
        &self,
        iterations: NonZeroU32,
        salt: &[u8],
        previously_derived: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        if previously_derived.len() < self.tag_len {
            return Err(Error::WrongLength);
        }
        self.check_len(previously_derived.len())?;
        let mut derived = alloc::vec![0u8; previously_derived.len()];
        self.routine
            .get()
            .derive(&self.key[..self.len], salt, iterations, &mut derived);
        let equal = ct_equal(&derived, previously_derived);
        zeroise(&mut derived);
        match ct::into_public(equal) {
            true => Ok(()),
            false => Err(Error::BadSignature),
        }
    }

    // RFC 8018 numbers blocks with a 32-bit counter starting at 1. By
    // multiplying, not dividing, so `admin/ct-vartime` finds no division.
    pub(crate) fn check_len(&self, len: usize) -> Result<(), Error> {
        let too_long = self
            .tag_len
            .checked_mul(u32::MAX as usize)
            .is_some_and(|most| len > most);
        if len == 0 || too_long {
            Err(Error::WrongLength)
        } else {
            Ok(())
        }
    }
}
