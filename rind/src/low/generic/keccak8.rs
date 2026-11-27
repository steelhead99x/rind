// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Computes Keccak-f1600 on the first `n` of the eight states in `a`, from
/// one to eight, four at a time: the backend's four-way routine on each
/// group of four, fewer as `sha3_keccak_nof4_f1600` runs them. The states
/// past `n` are left unspecified.
pub(crate) fn sha3_keccak_nof8_f1600(a: &mut [[u64; 25]; 8], n: usize, rc: &[u64; 24]) {
    let (halves, _) = a.as_chunks_mut::<4>();
    if n > 4 {
        crate::low::sha3_keccak4_f1600(&mut halves[0], rc);
        nof4(&mut halves[1], n - 4, rc);
    } else {
        nof4(&mut halves[0], n, rc);
    }
}

/// The first `n` of four states, from one to four.
fn nof4(a: &mut [[u64; 25]; 4], n: usize, rc: &[u64; 24]) {
    match n {
        4 => crate::low::sha3_keccak4_f1600(a, rc),
        3 => crate::low::sha3_keccak_nof4_f1600::<3>(a, rc),
        2 => crate::low::sha3_keccak_nof4_f1600::<2>(a, rc),
        _ => crate::low::sha3_keccak_nof4_f1600::<1>(a, rc),
    }
}
