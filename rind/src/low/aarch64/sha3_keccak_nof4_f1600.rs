// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::sha3_keccak_f1600::sha3_keccak_f1600;
use super::sha3_keccak_f1600_alt::sha3_keccak_f1600 as sha3_keccak_f1600_alt;
use super::sha3_keccak2_f1600::sha3_keccak2_f1600;

/// Compute Keccak-f1600 on the first `N` states in `a`, for `N` from one to
/// four.
// The fallback indexes rather than iterates, which `proofs/` reasons about
// more simply.
#[allow(clippy::needless_range_loop)]
#[inline]
pub(crate) fn sha3_keccak_nof4_f1600<const N: usize>(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    match super::cpu::HaveSha3::check() {
        // SAFETY: This branch is only called if the CPU has the SHA3 feature.
        // It permutes the states two at a time, then any odd one.
        Some(_) => unsafe {
            let (pairs, _) = a.as_chunks_mut::<2>();
            match N {
                1 => sha3_keccak_f1600_alt(&mut a[0], rc),
                2 => sha3_keccak2_f1600(&mut pairs[0], rc),
                3 => {
                    sha3_keccak2_f1600(&mut pairs[0], rc);
                    sha3_keccak_f1600_alt(&mut a[2], rc);
                }
                _ => {
                    sha3_keccak2_f1600(&mut pairs[0], rc);
                    sha3_keccak2_f1600(&mut pairs[1], rc);
                }
            }
        },
        None => {
            for i in 0..N {
                sha3_keccak_f1600(&mut a[i], rc);
            }
        }
    }
}
