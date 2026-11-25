// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Compute Keccak-f1600 on one state: on the SHA3 instructions where
/// `HaveSha3::check_keccak` allows, else in scalar code, which on Cortex-A72
/// is s2n-bignum's `_alt2` (see `cpu::keccak_alt2`).
#[inline]
pub(crate) fn sha3_keccak_f1600(a: &mut [u64; 25], rc: &[u64; 24]) {
    match super::cpu::HaveSha3::check_keccak() {
        // SAFETY: This branch is only called if the CPU has the SHA3 feature.
        Some(_) => unsafe { super::sha3_keccak_f1600_alt::sha3_keccak_f1600(a, rc) },
        None => {
            if super::cpu::keccak_alt2() {
                super::sha3_keccak_f1600_alt2::sha3_keccak_f1600(a, rc)
            } else {
                super::sha3_keccak_f1600::sha3_keccak_f1600(a, rc)
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mid::sha3::RC;

    // Each scalar kernel against the other, on every core, whichever the
    // dispatch picks.
    #[test]
    fn alt2_matches_scalar() {
        let mut x = 1u64;
        for _ in 0..32 {
            let a: [u64; 25] = core::array::from_fn(|_| {
                x = x
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                x
            });
            let (mut want, mut got, mut mux) = (a, a, a);
            super::super::sha3_keccak_f1600::sha3_keccak_f1600(&mut want, &RC);
            super::super::sha3_keccak_f1600_alt2::sha3_keccak_f1600(&mut got, &RC);
            sha3_keccak_f1600(&mut mux, &RC);
            assert_eq!(got, want);
            assert_eq!(mux, want);
        }
    }
}
