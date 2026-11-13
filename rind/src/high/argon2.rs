// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2id (RFC 9106).
//!
//! The first half of the first pass reads memory at indexes that do not depend
//! on the password. The rest of the fill does: that is the memory hardness
//! RFC 9106 specifies, and the only secret-dependent addresses in this module.
//! [`Secret::verify`] compares the derived key in constant time.

use core::fmt;

use crate::Error;
use crate::low::argon2::OwnedSecret;
use crate::low::{Entry, ct, ct_equal, zeroise};
use crate::mid::argon2;

/// How much memory, and how many passes and lanes, Argon2id uses.
///
/// Constructed with [`Params::new`], or one of the two sets RFC 9106 section 4
/// recommends. Fields stay private so a value cannot name fewer than the
/// minimum: a set below it is refused, not raised to the minimum.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Params {
    memory_kib: u32,
    passes: u32,
    lanes: u32,
}

/// One pass, four lanes, and 2 GiB of memory: RFC 9106's first recommended set.
pub const RECOMMENDED: Params = Params {
    memory_kib: 1 << 21,
    passes: 1,
    lanes: 4,
};

/// Three passes, four lanes, and 64 MiB of memory: RFC 9106's second
/// recommended set, for when 2 GiB is not available.
pub const RECOMMENDED_LOW_MEMORY: Params = Params {
    memory_kib: 1 << 16,
    passes: 3,
    lanes: 4,
};

impl Params {
    /// `memory_kib` is the memory in kibibytes, `passes` the iteration count,
    /// and `lanes` the degree of parallelism.
    ///
    /// Fails with [`Error::OutOfRange`] when `lanes` is 0 or above 2^24 - 1,
    /// `passes` is 0, or `memory_kib` is below `8 * lanes`. RFC 9106 rounds a
    /// valid memory size down to a multiple of `4 * lanes` kibibytes; that
    /// rounding is the algorithm, and a size below the minimum is not rounded up.
    pub const fn new(memory_kib: u32, passes: u32, lanes: u32) -> Result<Self, Error> {
        if lanes == 0 || lanes > 0x00FF_FFFF || passes == 0 || memory_kib < lanes * 8 {
            return Err(Error::OutOfRange);
        }
        Ok(Self {
            memory_kib,
            passes,
            lanes,
        })
    }

    /// Memory, in kibibytes, before RFC 9106 rounds it down.
    #[must_use]
    pub const fn memory_kib(&self) -> u32 {
        self.memory_kib
    }

    /// Iteration count.
    #[must_use]
    pub const fn passes(&self) -> u32 {
        self.passes
    }

    /// Degree of parallelism.
    #[must_use]
    pub const fn lanes(&self) -> u32 {
        self.lanes
    }
}

/// A password, copied and wiped on drop under the `wipe` feature.
///
/// The copy is what every later [`Secret::derive`] and [`Secret::verify`] hashes.
#[repr(transparent)]
pub struct Secret(OwnedSecret);

impl fmt::Debug for Secret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Secret").finish_non_exhaustive()
    }
}

impl Secret {
    /// Copies `password`, which may be empty and must be at most 2^32 - 1 bytes.
    ///
    /// Fails with [`Error::WrongLength`] when `password` is longer than that,
    /// and with [`Error::OutOfRange`] when the copy cannot be allocated.
    pub fn new(password: &[u8]) -> Result<Self, Error> {
        let _entry = Entry::new_secret();
        if u32::try_from(password.len()).is_err() {
            return Err(Error::WrongLength);
        }
        Ok(Self(OwnedSecret::new(password)?))
    }

    /// Fills `out` with the key derived from `salt`.
    ///
    /// `secret` is RFC 9106's K and `ad` its associated data. Pass an empty
    /// slice for either one this call does not use. `salt` is at least 8 bytes
    /// and `out` at least 4, and none of `salt`, `secret`, `ad`, or `out` is
    /// longer than 2^32 - 1 bytes.
    ///
    /// Fails with [`Error::WrongLength`] when a length is outside that range,
    /// leaving `out` unchanged, and with [`Error::OutOfRange`] when the
    /// allocator refuses the matrix. The matrix is one allocation. A platform
    /// that overcommits does not refuse the reservation, and can kill the
    /// process when the matrix is first written; that kill is not an error
    /// this function returns.
    pub fn derive(
        &self,
        params: Params,
        salt: &[u8],
        secret: &[u8],
        ad: &[u8],
        out: &mut [u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_input(salt, secret, ad, out.len())?;
        argon2::derive(
            self.0.as_slice(),
            params.memory_kib,
            params.passes,
            params.lanes,
            salt,
            secret,
            ad,
            out,
        )
    }

    /// Checks in constant time that `previously_derived` is what [`Secret::derive`]
    /// makes for the same inputs.
    ///
    /// Fails with [`Error::WrongLength`] under the same conditions as
    /// [`Secret::derive`], with [`Error::OutOfRange`] when the derived tag
    /// cannot be allocated, and with [`Error::BadSignature`] when the keys differ.
    /// A stored key shorter than 4 bytes is refused because it is easier to match.
    /// Overcommit is the same limit as [`Secret::derive`]: the allocator can
    /// accept the tag and the process can still be killed when it is written.
    pub fn verify(
        &self,
        params: Params,
        salt: &[u8],
        secret: &[u8],
        ad: &[u8],
        previously_derived: &[u8],
    ) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        check_input(salt, secret, ad, previously_derived.len())?;
        let mut got = Vec::new();
        if got.try_reserve_exact(previously_derived.len()).is_err() {
            return Err(Error::OutOfRange);
        }
        got.resize(previously_derived.len(), 0);
        argon2::derive(
            self.0.as_slice(),
            params.memory_kib,
            params.passes,
            params.lanes,
            salt,
            secret,
            ad,
            &mut got,
        )?;
        let equal = ct_equal(&got, previously_derived);
        zeroise(&mut got);
        match ct::into_public(equal) {
            true => Ok(()),
            false => Err(Error::BadSignature),
        }
    }
}

fn check_input(salt: &[u8], secret: &[u8], ad: &[u8], out_len: usize) -> Result<(), Error> {
    if !(8..).contains(&salt.len()) || u32::try_from(salt.len()).is_err() {
        return Err(Error::WrongLength);
    }
    if u32::try_from(secret.len()).is_err() || u32::try_from(ad.len()).is_err() {
        return Err(Error::WrongLength);
    }
    if out_len < 4 || u32::try_from(out_len).is_err() {
        return Err(Error::WrongLength);
    }
    Ok(())
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn params(memory_kib: u32, passes: u32, lanes: u32) -> Params {
        Params::new(memory_kib, passes, lanes).unwrap()
    }

    fn derive(
        password: &[u8],
        memory_kib: u32,
        passes: u32,
        lanes: u32,
        salt: &[u8],
        secret: &[u8],
        ad: &[u8],
        out_len: usize,
    ) -> Vec<u8> {
        let mut out = vec![0u8; out_len];
        Secret::new(password)
            .unwrap()
            .derive(
                params(memory_kib, passes, lanes),
                salt,
                secret,
                ad,
                &mut out,
            )
            .unwrap();
        out
    }

    /// RFC 9106 appendix A, the Argon2id vector: 32 KiB, 3 passes, 4 lanes.
    #[test]
    fn rfc9106() {
        let got = derive(
            &[0x01; 32],
            32,
            3,
            4,
            &[0x02; 16],
            &[0x03; 8],
            &[0x04; 12],
            32,
        );
        assert_eq!(
            hex::encode(got),
            "0d640df58d78766c08c037a34a8b53c9d01ef0452d75b65eb52520e96b01e659"
        );
    }

    /// The reference implementation's known answers, from its `kats/argon2id`
    /// tag (the RFC vector) and its `hashtest` Argon2id cases at 256 KiB.
    #[test]
    fn reference_kat() {
        rfc9106();
        assert_eq!(
            hex::encode(derive(b"password", 256, 2, 1, b"somesalt", b"", b"", 32)),
            "9dfeb910e80bad0311fee20f9c0e2b12c17987b4cac90c2ef54d5b3021c68bfe"
        );
        assert_eq!(
            hex::encode(derive(b"password", 256, 2, 2, b"somesalt", b"", b"", 32)),
            "6d093c501fd5999645e0ea3bf620d7b8be7fd2db59c20d9fff9539da2bf57037"
        );
    }

    #[test]
    fn refuses_out_of_range() {
        assert_eq!(Params::new(0, 1, 1), Err(Error::OutOfRange));
        assert_eq!(Params::new(8, 0, 1), Err(Error::OutOfRange));
        assert_eq!(Params::new(8, 1, 0), Err(Error::OutOfRange));
        assert_eq!(Params::new(8, 1, 2), Err(Error::OutOfRange));
        assert_eq!(Params::new(31, 3, 4), Err(Error::OutOfRange));
        assert_eq!(
            Params::new(u32::MAX, 1, 0x0100_0000),
            Err(Error::OutOfRange)
        );
        assert_eq!(Params::new(32, 3, 4).unwrap(), params(32, 3, 4));
        assert_eq!(RECOMMENDED.memory_kib(), 1 << 21);
        assert_eq!(RECOMMENDED.passes(), 1);
        assert_eq!(RECOMMENDED.lanes(), 4);
        assert_eq!(RECOMMENDED_LOW_MEMORY.memory_kib(), 1 << 16);
        assert_eq!(RECOMMENDED_LOW_MEMORY.passes(), 3);
        assert_eq!(RECOMMENDED_LOW_MEMORY.lanes(), 4);
        // The constants are in range, so `new` accepts them.
        assert_eq!(
            Params::new(
                RECOMMENDED.memory_kib(),
                RECOMMENDED.passes(),
                RECOMMENDED.lanes()
            ),
            Ok(RECOMMENDED)
        );

        let secret = Secret::new(b"password").unwrap();
        let p = params(32, 1, 1);
        let mut out = [0u8; 4];
        assert_eq!(
            secret.derive(p, b"short", b"", b"", &mut out),
            Err(Error::WrongLength)
        );
        assert_eq!(
            secret.derive(p, b"saltsalt", b"", b"", &mut []),
            Err(Error::WrongLength)
        );
        assert_eq!(
            secret.derive(p, b"saltsalt", b"", b"", &mut [0; 3]),
            Err(Error::WrongLength)
        );
        assert_eq!(
            secret.verify(p, b"short", b"", b"", &[0; 32]),
            Err(Error::WrongLength)
        );
        assert_eq!(
            secret.verify(p, b"saltsalt", b"", b"", &[0; 3]),
            Err(Error::WrongLength)
        );
        assert!(Secret::new(b"").is_ok());

        // 2 GiB does not fit in a 32-bit address space.
        if usize::BITS == 32 {
            let mut out = [0u8; 32];
            assert_eq!(
                secret.derive(RECOMMENDED, b"saltsalt", b"", b"", &mut out),
                Err(Error::OutOfRange)
            );
        }
    }

    #[test]
    fn verify_checks_every_byte() {
        let p = params(32, 2, 1);
        let secret = Secret::new(b"password").unwrap();
        let mut key = [0u8; 32];
        secret
            .derive(p, b"saltsalt", b"pepper", b"context", &mut key)
            .unwrap();
        assert_eq!(
            secret.verify(p, b"saltsalt", b"pepper", b"context", &key),
            Ok(())
        );
        for i in 0..key.len() {
            let mut wrong = key;
            wrong[i] ^= 1;
            assert_eq!(
                secret.verify(p, b"saltsalt", b"pepper", b"context", &wrong),
                Err(Error::BadSignature)
            );
        }
        assert_eq!(
            secret.verify(params(32, 3, 1), b"saltsalt", b"pepper", b"context", &key),
            Err(Error::BadSignature)
        );
        assert_eq!(
            secret.verify(p, b"othersalt", b"pepper", b"context", &key),
            Err(Error::BadSignature)
        );
        assert_eq!(
            Secret::new(b"other")
                .unwrap()
                .verify(p, b"saltsalt", b"pepper", b"context", &key),
            Err(Error::BadSignature)
        );
        // An empty password, secret, and associated data are defined inputs.
        let mut bare = [0u8; 16];
        Secret::new(b"")
            .unwrap()
            .derive(p, b"saltsalt", b"", b"", &mut bare)
            .unwrap();
        assert_ne!(bare, key[..16]);
        // A tag of 4 bytes, the shortest RFC 9106 allows, and one past 64, so
        // the variable-length hash takes both of its shapes.
        let mut short = [0u8; 4];
        let mut long = [0u8; 65];
        secret.derive(p, b"saltsalt", b"", b"", &mut short).unwrap();
        secret.derive(p, b"saltsalt", b"", b"", &mut long).unwrap();
        assert_eq!(secret.verify(p, b"saltsalt", b"", b"", &short), Ok(()));
        assert_eq!(secret.verify(p, b"saltsalt", b"", b"", &long), Ok(()));
        // Memory that is not a multiple of 4 * lanes is accepted. The original
        // size is part of the hash, so it does not match the rounded size's tag.
        // The block count itself is `mid::argon2`'s layout test.
        let mut a = [0u8; 32];
        let mut b = [0u8; 32];
        secret
            .derive(params(33, 1, 1), b"saltsalt", b"", b"", &mut a)
            .unwrap();
        secret
            .derive(params(32, 1, 1), b"saltsalt", b"", b"", &mut b)
            .unwrap();
        assert_ne!(a, b);
    }

    #[test]
    fn secret_password() {
        // Under `admin/ctgrind`, nothing may branch on or index by the
        // password, the secret key, or anything derived from them, except the
        // data-dependent half's memory index, until the derived key or
        // verify's answer is declassified. 32 KiB and 3 passes run the
        // data-independent first half and the data-dependent rest.
        let p = params(32, 3, 1);
        for (password, pepper) in [
            (b"password".as_slice(), b"".as_slice()),
            (&[0x5a; 32], b"pepper"),
        ] {
            let mut wanted = [0u8; 32];
            Secret::new(password)
                .unwrap()
                .derive(p, b"saltsalt", pepper, b"ad", &mut wanted)
                .unwrap();

            // Mark copies: the literals are shared, read-only data, and
            // marking them would taint every other test that uses
            // `b"password"`, whichever runs after this one.
            let (password, pepper) = (password.to_vec(), pepper.to_vec());
            let (password, pepper) = (password.as_slice(), pepper.as_slice());
            ct::secret_slice(password);
            ct::secret_slice(pepper);
            let secret = Secret::new(password).unwrap();
            let mut got = [0u8; 32];
            secret
                .derive(p, b"saltsalt", pepper, b"ad", &mut got)
                .unwrap();
            ct::public_slice(&got);
            assert_eq!(got, wanted);
            assert_eq!(
                secret.verify(p, b"saltsalt", pepper, b"ad", &wanted),
                Ok(())
            );
        }
    }
}
