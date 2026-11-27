// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Where pyca/verified-garbage's RSA `R² mod n` does not run: proof no CPU
//! can give, so callers keep `PosInt::pub_montifier`.

/// Proof that VG's routine runs for a modulus here, which it never does.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Precompute {}

impl Precompute {
    pub(crate) fn check(_: &[u64]) -> Option<Self> {
        None
    }

    pub(crate) fn precompute(self, _: &mut [u64], _: &[u8]) -> bool {
        match self {}
    }
}
