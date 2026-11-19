// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! x86_64's X25519 and Ed25519 on AVX-512 IFMA, which no aarch64 CPU runs:
//! `mid::ed25519` names it on both targets, so their code and proofs match.

/// Never constructed: no aarch64 CPU runs these.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Curve25519Ifma {}

impl Curve25519Ifma {
    pub(crate) fn check() -> Option<Self> {
        None
    }

    pub(crate) fn ed25519_key_pair(self, _seed: &[u8; 32]) -> ([u8; 64], [u8; 32]) {
        match self {}
    }

    pub(crate) fn ed25519_sign(
        self,
        _expanded: &[u8; 64],
        _public: &[u8; 32],
        _msg: &[u8],
    ) -> [u8; 64] {
        match self {}
    }

    pub(crate) fn ed25519_verify(self, _public: &[u8; 32], _msg: &[u8], _sig: &[u8; 64]) -> bool {
        match self {}
    }
}
