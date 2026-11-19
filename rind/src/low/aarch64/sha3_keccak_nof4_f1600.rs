// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::sha3_keccak_f1600_alt::sha3_keccak_f1600 as sha3_keccak_f1600_alt;
use super::sha3_keccak2_f1600::sha3_keccak2_f1600;
use super::sha3_keccak4_f1600::sha3_keccak4_f1600;
use super::sha3_keccak4_f1600_alt::sha3_keccak4_f1600 as sha3_keccak4_f1600_alt;

/// Compute Keccak-f1600 on the first `N` states in `a`, for `N` from one to
/// four.
///
/// Where Keccak-f does not run on the SHA3 instructions alone, four states run
/// as one scalar state beside NEON pairs, which keeps the scalar pipes busy;
/// fewer run one at a time, since the hybrid always permutes all four.
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
        None if N == 4 => match super::cpu::HaveSha3::check() {
            // SAFETY: This branch is only called if the CPU has the SHA3 feature.
            Some(_) => unsafe { sha3_keccak4_f1600(a, rc) },
            None => sha3_keccak4_f1600_alt(a, rc),
        },
        // One state at a time, on the single-state dispatch, which runs
        // `_alt2` on Cortex-A72.
        None => {
            for i in 0..N {
                super::sha3_keccak_f1600_mux::sha3_keccak_f1600(&mut a[i], rc);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::low::aarch64::cpu::HaveSha3;
    use crate::low::aarch64::sha3_keccak_f1600::sha3_keccak_f1600;
    use crate::mid::sha3::RC;

    fn states(seed: u64) -> [[u64; 25]; 4] {
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

    fn scalar(a: [[u64; 25]; 4]) -> [[u64; 25]; 4] {
        let mut want = a;
        for s in &mut want {
            sha3_keccak_f1600(s, &RC);
        }
        want
    }

    // The NEON and scalar hybrid runs on every aarch64 CPU without SHA3.
    #[test]
    fn neon_hybrid_matches_scalar() {
        for seed in 0..32 {
            let a = states(seed);
            let mut four = a;
            sha3_keccak4_f1600_alt(&mut four, &RC);
            assert_eq!(four, scalar(a));
        }
    }

    // Which kernels run depends on the target, so this checks every SHA3
    // kernel against the scalar code on any CPU with the instructions.
    #[test]
    fn sha3_kernels_match_scalar() {
        let Some(_) = HaveSha3::check() else {
            return;
        };
        for seed in 0..32 {
            let a = states(seed);
            let want = scalar(a);

            let mut four = a;
            // SAFETY: the CPU has the SHA3 feature.
            unsafe { sha3_keccak4_f1600(&mut four, &RC) };
            assert_eq!(four, want);

            let mut two = [a[0], a[1]];
            // SAFETY: the CPU has the SHA3 feature.
            unsafe { sha3_keccak2_f1600(&mut two, &RC) };
            assert_eq!(two, want[..2]);

            let mut one = a[0];
            // SAFETY: the CPU has the SHA3 feature.
            unsafe { sha3_keccak_f1600_alt(&mut one, &RC) };
            assert_eq!(one, want[0]);
        }
    }

    // Valgrind hides SHA3, so `admin/ct-qemu` traces the SHA3 kernels here,
    // on secret states.
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_sha3_kernels() {
        use crate::low::aarch64::ct_qemu;

        HaveSha3::check().expect("SHA3");
        let mut a = states(ct_qemu::seed());
        // SAFETY: the CPU has the SHA3 feature.
        ct_qemu::traced(|| unsafe { sha3_keccak4_f1600(&mut a, &RC) });
        let (pairs, _) = a.as_chunks_mut::<2>();
        // SAFETY: the CPU has the SHA3 feature.
        ct_qemu::traced(|| unsafe { sha3_keccak2_f1600(&mut pairs[0], &RC) });
        // SAFETY: the CPU has the SHA3 feature.
        ct_qemu::traced(|| unsafe { sha3_keccak_f1600_alt(&mut a[0], &RC) });
    }
}
