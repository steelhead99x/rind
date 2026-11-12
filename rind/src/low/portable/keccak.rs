// Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
// Copyright (c) 2022-2023 HACL* Contributors
// SPDX-License-Identifier: Apache-2.0
//
// Keccak-f[1600], from HACL*'s verified `Hacl_Hash_SHA3` at commit
// f557259007db9933442dde10aa995c1b00bd3446: the permutation that
// `dist/gcc-compatible/Hacl_Hash_SHA3.c` inlines into each absorb and squeeze,
// step for step in Rust. Its rotation and lane tables are public constants,
// so no index or branch depends on the state.

/// The rotations of the lanes rho visits, in pi's order.
const ROTC: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

/// The lanes pi moves each rotated lane to, starting from lane 1.
const PILN: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4, 15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

/// Keccak-f[1600] on `s`. The round constants are FIPS 202's, which `_rc`
/// holds too; the other backends' routines take them as an argument.
pub(crate) fn sha3_keccak_f1600(s: &mut [u64; 25], _rc: &[u64; 24]) {
    for rc in RC {
        // theta
        let c: [u64; 5] =
            core::array::from_fn(|i| s[i] ^ s[i + 5] ^ s[i + 10] ^ s[i + 15] ^ s[i + 20]);
        for i in 0..5 {
            let d = c[(i + 4) % 5] ^ c[(i + 1) % 5].rotate_left(1);
            for j in 0..5 {
                s[i + 5 * j] ^= d;
            }
        }

        // rho and pi
        let mut current = s[1];
        for (y, r) in PILN.into_iter().zip(ROTC) {
            let temp = s[y];
            s[y] = current.rotate_left(r);
            current = temp;
        }

        // chi
        for row in s.as_chunks_mut::<5>().0 {
            let r = *row;
            for i in 0..5 {
                row[i] = r[i] ^ (!r[(i + 1) % 5] & r[(i + 2) % 5]);
            }
        }

        // iota
        s[0] ^= rc;
    }
}

/// Keccak-f[1600] on all four states in `a`, one at a time.
pub(crate) fn sha3_keccak4_f1600(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    sha3_keccak_nof4_f1600::<4>(a, rc)
}

/// Keccak-f[1600] on the first `N` states in `a`, one at a time.
pub(crate) fn sha3_keccak_nof4_f1600<const N: usize>(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    for s in &mut a[..N] {
        sha3_keccak_f1600(s, rc);
    }
}

/// FIPS 202's round constants, HACL*'s `Hacl_Hash_SHA3_keccak_rndc`.
const RC: [u64; 24] = [
    0x0000000000000001,
    0x0000000000008082,
    0x800000000000808a,
    0x8000000080008000,
    0x000000000000808b,
    0x0000000080000001,
    0x8000000080008081,
    0x8000000000008009,
    0x000000000000008a,
    0x0000000000000088,
    0x0000000080008009,
    0x000000008000000a,
    0x000000008000808b,
    0x800000000000008b,
    0x8000000000008089,
    0x8000000000008003,
    0x8000000000008002,
    0x8000000000000080,
    0x000000000000800a,
    0x800000008000000a,
    0x8000000080008081,
    0x8000000000008080,
    0x0000000080000001,
    0x8000000080008008,
];

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // Keccak-f[1600] of the zero state, twice, from the Keccak team's
    // `KeccakF-1600-IntermediateValues.txt`.
    #[test]
    fn zero_state() {
        let mut s = [0u64; 25];
        sha3_keccak_f1600(&mut s, &RC);
        assert_eq!(
            s[..3],
            [0xf1258f7940e1dde7, 0x84d5ccf933c0478a, 0xd598261ea65aa9ee]
        );
        assert_eq!(s[24], 0xeaf1ff7b5ceca249);
        sha3_keccak_f1600(&mut s, &RC);
        assert_eq!(
            s[..3],
            [0x2d5c954df96ecb3c, 0x6a332cd07057b56d, 0x093d8d1270d76b6c]
        );
        assert_eq!(s[24], 0x20d06cd26a8fbf5c);
    }

    #[test]
    fn widths() {
        let mut single = [0u64; 25];
        sha3_keccak_f1600(&mut single, &RC);

        let mut one = [[0u64; 25]; 4];
        sha3_keccak_nof4_f1600::<1>(&mut one, &RC);
        assert_eq!(one[0], single);
        assert_eq!(one[1], [0; 25]);
        assert_eq!(one[3], [0; 25]);

        let mut four = [[1u64; 25]; 4];
        let mut each = [1u64; 25];
        sha3_keccak_f1600(&mut each, &RC);
        sha3_keccak4_f1600(&mut four, &RC);
        assert_eq!(four, [each; 4]);

        let mut none = [[7u64; 25]; 4];
        sha3_keccak_nof4_f1600::<0>(&mut none, &RC);
        assert_eq!(none, [[7u64; 25]; 4]);
    }
}
