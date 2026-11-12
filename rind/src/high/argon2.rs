// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2id, standardized in [RFC 9106](https://datatracker.ietf.org/doc/html/rfc9106).

use crate::Error;
use crate::low::{Entry, ct, ct_equal, zeroise};
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

/// Fills `out` with the key Argon2id derives from `password` and `salt`.
///
/// Give each password its own `salt`, such as 16 random bytes stored with
/// the key, so an attacker's guesses at one cannot be reused on another.
///
/// `out` must be at least the 4 bytes RFC 9106 allows, or this fails to
/// compile. The lanes are filled one after another, on the calling thread.
///
/// Fails with [`Error::WrongLength`] if `salt` is shorter than 8 bytes, or
/// `password` or `salt` is 2^32 bytes or longer, and with
/// [`Error::OutOfMemory`] if the memory `params` asks for cannot be
/// allocated. `out` is unchanged on failure.
pub fn derive<const N: usize>(
    params: Params,
    password: &[u8],
    salt: &[u8],
    out: &mut [u8; N],
) -> Result<(), Error> {
    const { assert!(N >= 4 && N as u64 <= u32::MAX as u64) };
    let _entry = Entry::new_secret();
    check_lengths(password, salt)?;
    // Argon2id fails only allocating its memory, before it writes `out`.
    argon2id(params.cost(), password, salt, &[], &[], out)
}

/// Checks in constant time that `previously_derived` is what [`derive`](fn@derive) makes from `password` and `salt`.
///
/// Fails with [`Error::BadSignature`] if the keys differ, and otherwise as
/// [`derive`](fn@derive) does.
pub fn verify<const N: usize>(
    params: Params,
    password: &[u8],
    salt: &[u8],
    previously_derived: &[u8; N],
) -> Result<(), Error> {
    const { assert!(N >= 4 && N as u64 <= u32::MAX as u64) };
    let _entry = Entry::new_secret();
    check_lengths(password, salt)?;
    // On the heap, since `N` may be far larger than a thread's stack.
    let mut key = Vec::new();
    key.try_reserve_exact(N).map_err(|_| Error::OutOfMemory)?;
    key.resize(N, 0);
    let result = argon2id(params.cost(), password, salt, &[], &[], &mut key)
        .map(|()| ct::into_public(ct_equal(&key, previously_derived)));
    // Heap scratch as good as a key derived from the password.
    zeroise(&mut key);
    match result? {
        true => Ok(()),
        false => Err(Error::BadSignature),
    }
}

// RFC 9106 encodes each length in 32 bits, and its reference refuses salts
// shorter than 8 bytes.
fn check_lengths(password: &[u8], salt: &[u8]) -> Result<(), Error> {
    let fits = |input: &[u8]| u32::try_from(input.len()).is_ok();
    match fits(password) && fits(salt) && salt.len() >= 8 {
        true => Ok(()),
        false => Err(Error::WrongLength),
    }
}

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
        let mut out = [0u8; 4];
        assert_eq!(
            derive(SMALL, b"password", &[0; 7], &mut out),
            Err(Error::WrongLength)
        );
        assert_eq!(
            verify(SMALL, b"password", &[0; 7], &out),
            Err(Error::WrongLength)
        );
        assert_eq!(out, [0; 4]);
        derive(SMALL, b"", &[0; 8], &mut out).unwrap();
        assert_eq!(verify(SMALL, b"", &[0; 8], &out), Ok(()));
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
            derive(huge, b"password", &[0; 8], &mut out),
            Err(Error::OutOfMemory)
        );
        assert_eq!(out, [0; 4]);
    }

    #[test]
    fn verify_checks_every_byte() {
        let salt = b"saltsalt";
        let mut key = [0u8; 20];
        derive(SMALL, b"password", salt, &mut key).unwrap();
        assert_eq!(verify(SMALL, b"password", salt, &key), Ok(()));
        for i in 0..key.len() {
            let mut wrong = key;
            wrong[i] ^= 1;
            assert_eq!(
                verify(SMALL, b"password", salt, &wrong),
                Err(Error::BadSignature)
            );
        }
        assert_eq!(
            verify(SMALL, b"passwore", salt, &key),
            Err(Error::BadSignature)
        );
        assert_eq!(
            verify(SMALL, b"password", b"saltsalu", &key),
            Err(Error::BadSignature)
        );
        let more = Params::new(16, 3, 2).unwrap();
        assert_eq!(
            verify(more, b"password", salt, &key),
            Err(Error::BadSignature)
        );
        // The tag length is hashed in, so a prefix of a longer key differs.
        let mut longer = [0u8; 21];
        derive(SMALL, b"password", salt, &mut longer).unwrap();
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
        derive(SMALL, &password, salt, &mut wanted).unwrap();

        ct::secret_slice(&password);
        let mut got = [0u8; 32];
        derive(SMALL, &password, salt, &mut got).unwrap();
        ct::public_slice(&got);
        assert_eq!(got, wanted);
        assert_eq!(verify(SMALL, &password, salt, &wanted), Ok(()));
    }
}
