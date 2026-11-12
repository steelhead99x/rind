// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::cpu::HaveAvx2;

/// Compute Keccak-f1600 on the first `N` states in `a`.
///
/// With AVX2, permuting all four states costs less than two one at a time.
// Indexed rather than iterated, which `proofs/` reasons about more simply.
#[allow(clippy::needless_range_loop)]
#[inline]
pub(crate) fn sha3_keccak_nof4_f1600<const N: usize>(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    match HaveAvx2::check() {
        Some(_) if N > 1 => super::sha3_keccak4_f1600_shim::sha3_keccak4_f1600(a, rc),
        _ => {
            for i in 0..N {
                super::sha3_keccak_f1600::sha3_keccak_f1600(&mut a[i], rc);
            }
        }
    }
}
