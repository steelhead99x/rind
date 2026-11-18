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
    match super::cpu::HaveSha3::check_keccak() {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::low::aarch64::cpu::HaveSha3;
    use crate::mid::sha3::RC;

    fn states(seed: u64) -> [[u64; 25]; 2] {
        let mut x = seed;
        core::array::from_fn(|_| {
            core::array::from_fn(|_| {
                x = x
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                x
            })
        })
    }

    // Only Apple targets run the SHA3 kernels, so this checks them against
    // the scalar code on any CPU with the instructions.
    #[test]
    fn sha3_kernels_match_scalar() {
        let Some(_) = HaveSha3::check() else {
            return;
        };
        for seed in 0..32 {
            let a = states(seed);
            let mut want = a;
            for s in &mut want {
                sha3_keccak_f1600(s, &RC);
            }

            let mut two = a;
            // SAFETY: the CPU has the SHA3 feature.
            unsafe { sha3_keccak2_f1600(&mut two, &RC) };
            assert_eq!(two, want);

            let mut one = a[0];
            // SAFETY: the CPU has the SHA3 feature.
            unsafe { sha3_keccak_f1600_alt(&mut one, &RC) };
            assert_eq!(one, want[0]);
        }
    }

    // Valgrind hides SHA3, and only Apple targets run these kernels, so
    // `admin/ct-qemu` traces them here, on secret states.
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_sha3_kernels() {
        use crate::low::aarch64::ct_qemu;

        HaveSha3::check().expect("SHA3");
        let mut a = states(ct_qemu::seed());
        // SAFETY: the CPU has the SHA3 feature.
        ct_qemu::traced(|| unsafe { sha3_keccak2_f1600(&mut a, &RC) });
        // SAFETY: the CPU has the SHA3 feature.
        ct_qemu::traced(|| unsafe { sha3_keccak_f1600_alt(&mut a[0], &RC) });
    }
}
