// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SP 800-90A HMAC_DRBG over SHA-512, for the FIPS module.
//!
//! rind's own key generation does not use this. It draws from [`crate::rand`].
//! The `rind-fips` crate is the wrapper that seeds a thread-local generator
//! from the operating system.

use core::fmt;

use super::hmac_drbg::{self, MAX_GENERATE_BYTES};
use crate::Error;
use crate::low::{Entry, Zeroable, zeroise_value};

/// An SP 800-90A HMAC_DRBG over SHA-512, with no derivation function.
///
/// SHA-512 gives the 256-bit strength the FIPS module asks for. `new` is the
/// standard's instantiate. [`Self::reseed`] mixes in new entropy. A
/// prediction-resistance generate, as ACVP's hmacDRBG samples draw, is a
/// reseed with that step's entropy and additional input followed by
/// [`Self::generate`] with `additional` of `None`.
///
/// `additional` of `None` is the standard's Null. An empty slice is provided
/// data, and the update that follows is not the Null update.
///
/// The value wipes itself on drop under the `wipe` feature, key and counter
/// included. Copies the implementation makes while computing stay unwiped.
#[repr(C)]
pub struct HmacDrbg {
    k: [u8; 64],
    v: [u8; 64],
    reseed_counter: u64,
}

impl HmacDrbg {
    /// Instantiates from `entropy`, `nonce`, and `personalization`.
    ///
    /// `personalization` may be empty. The FIPS module passes 64 bytes of
    /// entropy and 32 bytes of nonce, which covers a 256-bit strength when no
    /// derivation function is used.
    #[must_use]
    pub fn new(entropy: &[u8], nonce: &[u8], personalization: &[u8]) -> Self {
        let _entry = Entry::new_secret();
        let engine =
            hmac_drbg::HmacDrbg::<super::hash::Sha512>::new(entropy, nonce, personalization);
        Self::from_engine(&engine)
    }

    /// Mixes `entropy` into the state and starts the generate count over.
    ///
    /// `additional` of `None` is Null.
    pub fn reseed(&mut self, entropy: &[u8], additional: Option<&[u8]>) {
        let _entry = Entry::new_secret();
        self.with_engine(|engine| engine.reseed(entropy, additional));
    }

    /// Writes one generate into `out`.
    ///
    /// `out` longer than 65,536 bytes (2^19 bits, SP 800-90A's maximum for one
    /// generate) is [`Error::WrongLength`], and the state is unchanged. After
    /// more than 2^48 generates since the last seed or reseed, this returns
    /// [`Error::RngFailed`] and leaves the state unchanged so the caller can
    /// reseed. `additional` of `None` is Null.
    pub fn generate(&mut self, out: &mut [u8], additional: Option<&[u8]>) -> Result<(), Error> {
        let _entry = Entry::new_secret();
        if out.len() > MAX_GENERATE_BYTES {
            return Err(Error::WrongLength);
        }
        self.with_engine(|engine| engine.generate(out, additional))
    }

    fn from_engine(engine: &hmac_drbg::HmacDrbg<super::hash::Sha512>) -> Self {
        let (k, v, reseed_counter) = engine.to_parts();
        Self {
            k,
            v,
            reseed_counter,
        }
    }

    fn with_engine<R>(
        &mut self,
        f: impl FnOnce(&mut hmac_drbg::HmacDrbg<super::hash::Sha512>) -> R,
    ) -> R {
        let mut engine = hmac_drbg::HmacDrbg::from_parts(&self.k, &self.v, self.reseed_counter);
        let result = f(&mut engine);
        *self = Self::from_engine(&engine);
        result
    }
}

impl Drop for HmacDrbg {
    fn drop(&mut self) {
        zeroise_value(self);
    }
}

impl Zeroable for HmacDrbg {}

impl fmt::Debug for HmacDrbg {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("HmacDrbg")
            .field("algorithm", &"HMAC-SHA-512")
            .finish_non_exhaustive()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn engine_bytes(entropy: &[u8], nonce: &[u8], additional: Option<&[u8]>) -> [u8; 32] {
        let mut out = [0u8; 32];
        let mut drbg = HmacDrbg::new(entropy, nonce, &[]);
        drbg.generate(&mut out, additional).unwrap();
        out
    }

    fn second_generate(entropy: &[u8], nonce: &[u8]) -> [u8; 32] {
        let mut first = [0u8; 32];
        let mut second = [0u8; 32];
        let mut drbg = HmacDrbg::new(entropy, nonce, &[]);
        drbg.generate(&mut first, None).unwrap();
        drbg.generate(&mut second, None).unwrap();
        second
    }

    /// SP 800-90A HMAC_DRBG over SHA-512, checked against Python's `hmac`.
    /// Entropy is 32 bytes of `0x11`, the nonce 16 bytes of `0x22`.
    #[test]
    fn spec_steps() {
        let entropy = [0x11u8; 32];
        let nonce = [0x22u8; 16];
        assert_eq!(
            engine_bytes(&entropy, &nonce, None),
            [
                0xf5, 0x97, 0xde, 0x88, 0x79, 0x15, 0xd4, 0x0f, 0xd9, 0x2f, 0x5f, 0x9a, 0xb9, 0x27,
                0xeb, 0xdb, 0xd2, 0x05, 0x4c, 0xf0, 0x0d, 0xe4, 0x42, 0xe9, 0xe4, 0x24, 0xbc, 0x19,
                0xf1, 0x10, 0x86, 0x74,
            ]
        );
        // The second generate checks the state saved after the first. Drop
        // wipes the previous value while that state is stored back.
        assert_eq!(
            second_generate(&entropy, &nonce),
            [
                0x9a, 0x6f, 0x7c, 0x2d, 0xb5, 0x2b, 0xd8, 0x91, 0xf1, 0x78, 0x04, 0xc8, 0xb1, 0x66,
                0xcd, 0xe7, 0xdc, 0x2d, 0x0e, 0xcf, 0x72, 0x4b, 0xdc, 0x4c, 0xf2, 0x87, 0x48, 0x7c,
                0xaf, 0x5e, 0xa5, 0x43,
            ]
        );
        // An empty slice is provided data, not Null.
        assert_eq!(
            engine_bytes(&entropy, &nonce, Some(&[])),
            [
                0xf3, 0xf3, 0x26, 0x71, 0xc1, 0x0d, 0xe5, 0x8e, 0x6c, 0x69, 0xfb, 0xdc, 0x71, 0x3a,
                0xa8, 0xa3, 0x5e, 0x95, 0xe9, 0x45, 0x9f, 0x3a, 0x74, 0x70, 0x0a, 0x78, 0x0e, 0xfd,
                0xd3, 0x65, 0xe2, 0x38,
            ]
        );
        assert_eq!(
            engine_bytes(&entropy, &nonce, Some(&[0x33, 0x44, 0x55, 0x66])),
            [
                0x35, 0xb6, 0x0b, 0x12, 0xf4, 0x2b, 0xa2, 0x1d, 0xe3, 0xc1, 0x10, 0xdb, 0xbe, 0x45,
                0x59, 0x8c, 0x75, 0x01, 0x16, 0x98, 0x24, 0x40, 0x39, 0x80, 0x00, 0x68, 0xf9, 0xfb,
                0xf2, 0x0a, 0x5d, 0xe5,
            ]
        );
    }

    #[test]
    fn generate_refuses_an_overlong_request() {
        let mut drbg = HmacDrbg::new(&[1, 2, 3, 4], &[5, 6], &[]);
        let mut out = vec![0u8; MAX_GENERATE_BYTES + 1];
        assert_eq!(drbg.generate(&mut out, None), Err(Error::WrongLength));
        assert!(out.iter().all(|&byte| byte == 0));
    }

    fn reseed_then_generate(entropy: &[u8], nonce: &[u8], additional: &[u8]) -> [u8; 32] {
        let mut out = [0u8; 32];
        let mut drbg = HmacDrbg::new(entropy, nonce, &[]);
        drbg.reseed(entropy, Some(additional));
        drbg.generate(&mut out, Some(additional)).unwrap();
        out
    }

    #[test]
    fn secret_generate() {
        let entropy = [0x11u8; 32];
        let nonce = [0x22u8; 16];
        let additional = [0x33, 0x44, 0x55, 0x66];
        let wanted = reseed_then_generate(&entropy, &nonce, &additional);

        crate::low::ct::secret_slice(&entropy);
        crate::low::ct::secret_slice(&nonce);
        crate::low::ct::secret_slice(&additional);
        let out = reseed_then_generate(&entropy, &nonce, &additional);
        crate::low::ct::public_slice(&out);
        assert_eq!(out, wanted);
    }

    #[test]
    fn debug_hides_the_state() {
        let drbg = HmacDrbg::new(&[0xab; 32], &[0xcd; 16], b"personalization");
        let shown = format!("{drbg:?}");
        assert!(shown.contains("HmacDrbg"));
        assert!(!shown.contains("personalization"));
        assert!(!shown.contains("abab"));
    }
}
