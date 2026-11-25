// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Where pyca/verified-garbage's P-384 does not run: proof no CPU can give,
//! so callers keep rind's arithmetic.

/// Proof that VG's `d·G` runs here, which it never does.
#[derive(Clone, Copy, Debug)]
pub(crate) enum MulBase {}

impl MulBase {
    pub(crate) fn check() -> Option<Self> {
        None
    }

    pub(crate) fn public_key(self, _: &[u8; 48]) -> Option<[u8; 97]> {
        match self {}
    }
}

/// Proof that VG's ECDSA verification runs here, which it never does.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Verify {}

impl Verify {
    pub(crate) fn check() -> Option<Self> {
        None
    }

    pub(crate) fn ecdsa_verify(self, _: &[u8; 97], _: &[u8; 48], _: &[u8; 96]) -> bool {
        match self {}
    }
}
