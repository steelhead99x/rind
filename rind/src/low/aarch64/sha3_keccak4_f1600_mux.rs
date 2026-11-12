// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// On my aarch64 computer, sha3_keccak2_f1600 is way more than 2x faster than
/// sha3_keccak4_f1600.  So this function simply calls it twice.
#[inline]
pub(crate) fn sha3_keccak4_f1600(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    super::sha3_keccak_nof4_f1600::sha3_keccak_nof4_f1600::<4>(a, rc)
}
