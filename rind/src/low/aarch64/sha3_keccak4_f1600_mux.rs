// Written for Graviola by Joe Birr-Pixton, 2026.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Compute Keccak-f1600 on four states: as two pairs on the SHA3 instructions
/// where `HaveSha3::check_keccak` allows them, one at a time otherwise.
#[inline]
pub(crate) fn sha3_keccak4_f1600(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    super::sha3_keccak_nof4_f1600::sha3_keccak_nof4_f1600::<4>(a, rc)
}
