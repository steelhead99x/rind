// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2id, standardized in [RFC 9106](https://datatracker.ietf.org/doc/html/rfc9106).

use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

use crate::Error;
use crate::low::{Entry, Zeroable, ct, ct_equal, zeroise, zeroise_value};
use crate::mid::argon2::{Cost, argon2id};

/// How much memory and time Argon2id spends: RFC 9106's `m`, `t`, and `p`.
///
/// Derive and verify take these from the caller, never from the value they
/// check, so only the caller sets what a call costs: about `memory_kib`
/// KiB, held for the call, and `passes` times that much hashing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Params {
    memory_kib: u32,
    passes: u32,
    lanes: u32,
}

impl Params {
    /// RFC 9106's first recommendation: 2 GiB, one pass, and four lanes.
    pub const FIRST_RECOMMENDED: Self = Self {
        memory_kib: 1 << 21,
        passes: 1,
        lanes: 4,
    };

    /// RFC 9106's second recommendation, for when 2 GiB is too much: 64 MiB,
    /// three passes, and four lanes.
    pub const SECOND_RECOMMENDED: Self = Self {
        memory_kib: 1 << 16,
        passes: 3,
        lanes: 4,
    };

    /// Takes `memory_kib` KiB of memory, `passes` passes over it, and `lanes` lanes.
    ///
    /// Fails with [`Error::Unsupported`] below RFC 9106's minimums: one pass,
    /// one lane, and 8 KiB per lane, or with 2^24 lanes or more. The memory
    /// is used in whole multiples of 4 KiB per lane, rounding down.
    pub const fn new(memory_kib: u32, passes: u32, lanes: u32) -> Result<Self, Error> {
        if passes == 0 || lanes == 0 || lanes >= 1 << 24 || (memory_kib as u64) < 8 * lanes as u64 {
            return Err(Error::Unsupported);
        }
        Ok(Self {
            memory_kib,
            passes,
            lanes,
        })
    }

    fn cost(self) -> Cost {
        Cost {
            memory_kib: self.memory_kib,
            passes: self.passes,
            lanes: self.lanes,
        }
    }
}

/// A password, kept for every salt and cost it derives with; wiped on drop.
pub struct Secret(
    /// A copy of the password, `None` only once wiped.
    Option<Box<[u8]>>,
);

impl fmt::Debug for Secret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Secret").finish_non_exhaustive()
    }
}

impl Secret {
    /// Keeps a copy of `password`, which may be any length below 2^32 bytes.
    pub fn new(password: &[u8]) -> Self {
        Self(Some(password.into()))
    }

    fn password(&self) -> &[u8] {
        self.0.as_deref().unwrap_or_default()
    }

    /// Fills `out` with the key Argon2id derives from the password and
    /// `salt` at the cost `params` sets.
    ///
    /// Give each password its own `salt`, such as 16 random bytes stored with
    /// the key, so an attacker's guesses at one cannot be reused on another.
    /// The lanes are filled one after another, on the calling thread.
    ///
    /// Fails with [`Error::WrongLength`] if `out` is shorter than the 4 bytes
    /// RFC 9106 allows, `salt` is shorter than 8 bytes, or `out`, the
    /// password, or `salt` is 2^32 bytes or longer, and with
    /// [`Error::OutOfMemory`] if the memory `params` asks for cannot be
    /// allocated. `out` is unchanged on failure.
    pub fn derive(&self, params: Params, salt: &[u8], out: &mut [u8]) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        self.check_lengths(salt, out.len())?;
        // Argon2id fails only allocating its memory, before it writes `out`.
        argon2id(params.cost(), self.password(), salt, &[], &[], out)
    }

    /// Checks in constant time that `previously_derived` is what
    /// [`Secret::derive`] makes for `params` and `salt`.
    ///
    /// The key derived is as long as `previously_derived`. Fails with
    /// [`Error::BadSignature`] if the keys differ, and otherwise as
    /// [`Secret::derive`] does.
    pub fn verify(
        &self,
        params: Params,
        salt: &[u8],
        previously_derived: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        self.check_lengths(salt, previously_derived.len())?;
        // On the heap, since the key may be far larger than a thread's stack.
        let mut key = Vec::new();
        key.try_reserve_exact(previously_derived.len())
            .map_err(|_| Error::OutOfMemory)?;
        key.resize(previously_derived.len(), 0);
        let result = argon2id(params.cost(), self.password(), salt, &[], &[], &mut key)
            .map(|()| ct::into_public(ct_equal(&key, previously_derived)));
        // Heap scratch as good as a key derived from the password.
        zeroise(&mut key);
        match result? {
            true => Ok(()),
            false => Err(Error::BadSignature),
        }
    }

    // RFC 9106 encodes each length in 32 bits, and allows tags of 4 bytes or
    // more; its reference refuses salts shorter than 8 bytes.
    fn check_lengths(&self, salt: &[u8], out_len: usize) -> Result<(), Error> {
        let fits = |len: usize| u32::try_from(len).is_ok();
        match fits(self.password().len())
            && fits(salt.len())
            && fits(out_len)
            && salt.len() >= 8
            && out_len >= 4
        {
            true => Ok(()),
            false => Err(Error::WrongLength),
        }
    }
}

impl Drop for Secret {
    fn drop(&mut self) {
        if let Some(mut password) = self.0.take() {
            zeroise(&mut password);
        }
        zeroise_value(self);
    }
}

// `None` once wiped.
impl Zeroable for Secret {}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // The least memory each lane may have, to keep the tests fast.
    const SMALL: Params = match Params::new(16, 2, 2) {
        Ok(params) => params,
        Err(_) => panic!(),
    };

    #[test]
    fn params() {
        assert_eq!(
            Params::new(8, 1, 1),
            Ok(Params {
                memory_kib: 8,
                passes: 1,
                lanes: 1
            })
        );
        assert_eq!(Params::new(7, 1, 1), Err(Error::Unsupported));
        assert_eq!(Params::new(8, 0, 1), Err(Error::Unsupported));
        assert_eq!(Params::new(8, 1, 0), Err(Error::Unsupported));
        assert_eq!(Params::new(8 * 3, 1, 3).map(|p| p.lanes), Ok(3));
        assert_eq!(Params::new(8 * 3 - 1, 1, 3), Err(Error::Unsupported));
        assert_eq!(
            Params::new(u32::MAX, 1, (1 << 24) - 1).map(|p| p.lanes),
            Ok((1 << 24) - 1)
        );
        assert_eq!(Params::new(u32::MAX, 1, 1 << 24), Err(Error::Unsupported));
        for recommended in [Params::FIRST_RECOMMENDED, Params::SECOND_RECOMMENDED] {
            let Params {
                memory_kib,
                passes,
                lanes,
            } = recommended;
            assert_eq!(Params::new(memory_kib, passes, lanes), Ok(recommended));
        }
    }

    #[test]
    fn lengths() {
        let secret = Secret::new(b"password");
        let mut out = [0u8; 4];
        assert_eq!(
            secret.derive(SMALL, &[0; 7], &mut out),
            Err(Error::WrongLength)
        );
        assert_eq!(secret.verify(SMALL, &[0; 7], &out), Err(Error::WrongLength));
        assert_eq!(out, [0; 4]);
        // RFC 9106's shortest tag is 4 bytes.
        let mut short = [0u8; 3];
        assert_eq!(
            secret.derive(SMALL, &[0; 8], &mut short),
            Err(Error::WrongLength)
        );
        assert_eq!(
            secret.verify(SMALL, &[0; 8], &short),
            Err(Error::WrongLength)
        );
        let empty = Secret::new(b"");
        empty.derive(SMALL, &[0; 8], &mut out).unwrap();
        assert_eq!(empty.verify(SMALL, &[0; 8], &out), Ok(()));
    }

    // Only a 32-bit address space is too small for Argon2's largest memory,
    // 4 TiB; a 64-bit host may overcommit it and fail only once it is
    // touched.
    #[cfg(target_pointer_width = "32")]
    #[test]
    fn unallocatable() {
        let mut out = [0u8; 4];
        let huge = Params::new(u32::MAX, 1, 1).unwrap();
        assert_eq!(
            Secret::new(b"password").derive(huge, &[0; 8], &mut out),
            Err(Error::OutOfMemory)
        );
        assert_eq!(out, [0; 4]);
    }

    #[test]
    fn verify_checks_every_byte() {
        let salt = b"saltsalt";
        let secret = Secret::new(b"password");
        let mut key = [0u8; 20];
        secret.derive(SMALL, salt, &mut key).unwrap();
        assert_eq!(secret.verify(SMALL, salt, &key), Ok(()));
        for i in 0..key.len() {
            let mut wrong = key;
            wrong[i] ^= 1;
            assert_eq!(secret.verify(SMALL, salt, &wrong), Err(Error::BadSignature));
        }
        assert_eq!(
            Secret::new(b"passwore").verify(SMALL, salt, &key),
            Err(Error::BadSignature)
        );
        assert_eq!(
            secret.verify(SMALL, b"saltsalu", &key),
            Err(Error::BadSignature)
        );
        let more = Params::new(16, 3, 2).unwrap();
        assert_eq!(secret.verify(more, salt, &key), Err(Error::BadSignature));
        // The tag length is hashed in, so a prefix of a longer key differs.
        let mut longer = [0u8; 21];
        secret.derive(SMALL, salt, &mut longer).unwrap();
        assert_ne!(longer[..20], key);
    }

    #[test]
    fn secret_password() {
        // Under `admin/ctgrind`, nothing may branch on or index by the
        // password or anything derived from it, until the derived key or
        // verify's answer is declassified, except the data-dependent
        // references, which `mid::argon2` declassifies one by one. Two
        // passes and two lanes reach every kind of reference: the first
        // pass's data-independent half and data-dependent half, the later
        // passes', and other lanes'.
        let password = [0x5a; 40];
        let salt = b"saltsalt";
        let mut wanted = [0u8; 32];
        Secret::new(&password)
            .derive(SMALL, salt, &mut wanted)
            .unwrap();

        ct::secret_slice(&password);
        let secret = Secret::new(&password);
        let mut got = [0u8; 32];
        secret.derive(SMALL, salt, &mut got).unwrap();
        ct::public_slice(&got);
        assert_eq!(got, wanted);
        assert_eq!(secret.verify(SMALL, salt, &wanted), Ok(()));
    }
}
