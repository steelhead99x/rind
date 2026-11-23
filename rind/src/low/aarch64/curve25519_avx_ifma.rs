// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! x86_64's X25519 and Ed25519 verification on AVX-IFMA, which no aarch64 CPU
//! runs: `mid::ed25519` names it on both targets, so their code and proofs
//! match.

/// Never constructed: no aarch64 CPU runs these.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Curve25519AvxIfma {}

impl Curve25519AvxIfma {
    pub(crate) fn check() -> Option<Self> {
        None
    }

    pub(crate) fn ed25519_verify(self, _public: &[u8; 32], _msg: &[u8], _sig: &[u8; 64]) -> bool {
        match self {}
    }
}
