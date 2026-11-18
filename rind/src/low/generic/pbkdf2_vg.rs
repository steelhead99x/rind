// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Where pyca/verified-garbage's PBKDF2 does not run, or was slower than
//! rind's: no routine, so callers keep rind's loop.

use core::num::NonZeroU32;

/// A VG routine this CPU runs, which here is none.
pub(crate) enum Pbkdf2 {}

impl Pbkdf2 {
    pub(crate) fn sha1() -> Option<&'static Self> {
        None
    }

    pub(crate) fn sha256() -> Option<&'static Self> {
        None
    }

    pub(crate) fn sha384() -> Option<&'static Self> {
        None
    }

    pub(crate) fn sha512() -> Option<&'static Self> {
        None
    }

    pub(crate) fn derive(&self, _: &[u8], _: &[u8], _: NonZeroU32, _: &mut [u8]) {
        match *self {}
    }
}
