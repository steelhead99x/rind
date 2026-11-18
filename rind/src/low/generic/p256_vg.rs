// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Where pyca/verified-garbage's P-256 does not run: proof no CPU can give,
//! so callers keep rind's arithmetic.

/// Proof that VG's P-256 runs here, which it never does.
#[derive(Clone, Copy, Debug)]
pub(crate) enum P256 {}

impl P256 {
    pub(crate) fn check() -> Option<Self> {
        None
    }

    pub(crate) fn check_public_key() -> Option<Self> {
        None
    }

    pub(crate) fn public_key(self, _: &[u8; 32]) -> Option<[u8; 65]> {
        match self {}
    }

    pub(crate) fn ecdh(self, _: &[u8; 32], _: &[u8; 65]) -> Option<[u8; 32]> {
        match self {}
    }

    pub(crate) fn verify(self, _: &[u8; 65], _: &[u8; 32], _: &[u8; 64]) -> bool {
        match self {}
    }
}
