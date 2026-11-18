// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Where pyca/verified-garbage's ML-KEM-768 does not run, or was slower than
//! rind's: proofs no CPU can give, so callers keep rind's arithmetic.

/// Proof that VG's encapsulation runs here, which it never does.
#[cfg(not(rind_backend = "aarch64"))]
#[derive(Clone, Copy, Debug)]
pub(crate) enum Encaps {}

#[cfg(not(rind_backend = "aarch64"))]
impl Encaps {
    pub(crate) fn check() -> Option<Self> {
        None
    }

    pub(crate) fn check_ek(self, _: &[u8; 1184]) -> bool {
        match self {}
    }

    pub(crate) fn encaps(
        self,
        _: &[u8; 1184],
        _: Option<&[u8; 32]>,
        _: &[u8; 32],
    ) -> Option<([u8; 32], [u8; 1088])> {
        match self {}
    }
}

/// Proof that VG's key generation and decapsulation run here, which they
/// never do.
#[derive(Clone, Copy, Debug)]
pub(crate) enum KeyPair {}

impl KeyPair {
    pub(crate) fn check() -> Option<Self> {
        None
    }

    pub(crate) fn keygen(self, _: &[u8; 64]) -> Option<[u8; 2400]> {
        match self {}
    }

    pub(crate) fn decaps(self, _: &[u8; 2400], _: &[u8; 1088]) -> Option<[u8; 32]> {
        match self {}
    }
}
