// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Keccak-f[1600], one round at a time as s2n-bignum's `keccak_round`
//! (`keccak_spec.ml` at b4f17ee7) states it, so `proofs/Rind/Portable/Keccak.lean`
//! proves it against the spec the other backends' routines are proven
//! against. The lanes are locals and their rotations constants, so no index
//! or branch depends on the state.

/// Keccak-f[1600] on `s`, round `i` with constant `rc[i]`.
// Indexed rather than iterated, which `proofs/` reasons about more simply.
#[allow(clippy::needless_range_loop)]
pub(crate) fn sha3_keccak_f1600(s: &mut [u64; 25], rc: &[u64; 24]) {
    for i in 0..24 {
        *s = round(s, rc[i]);
    }
}

/// One round on the lanes of `a`, lane `5 * y + x` holding FIPS 202's
/// `A[x, y]`, and named `axy` here.
#[inline(always)]
fn round(a: &[u64; 25], rc: u64) -> [u64; 25] {
    let a00 = a[0];
    let a10 = a[1];
    let a20 = a[2];
    let a30 = a[3];
    let a40 = a[4];
    let a01 = a[5];
    let a11 = a[6];
    let a21 = a[7];
    let a31 = a[8];
    let a41 = a[9];
    let a02 = a[10];
    let a12 = a[11];
    let a22 = a[12];
    let a32 = a[13];
    let a42 = a[14];
    let a03 = a[15];
    let a13 = a[16];
    let a23 = a[17];
    let a33 = a[18];
    let a43 = a[19];
    let a04 = a[20];
    let a14 = a[21];
    let a24 = a[22];
    let a34 = a[23];
    let a44 = a[24];

    // theta
    let c0 = a00 ^ (a01 ^ (a02 ^ (a03 ^ a04)));
    let c1 = a10 ^ (a11 ^ (a12 ^ (a13 ^ a14)));
    let c2 = a20 ^ (a21 ^ (a22 ^ (a23 ^ a24)));
    let c3 = a30 ^ (a31 ^ (a32 ^ (a33 ^ a34)));
    let c4 = a40 ^ (a41 ^ (a42 ^ (a43 ^ a44)));
    let d0 = c4 ^ c1.rotate_left(1);
    let d1 = c0 ^ c2.rotate_left(1);
    let d2 = c1 ^ c3.rotate_left(1);
    let d3 = c2 ^ c4.rotate_left(1);
    let d4 = c3 ^ c0.rotate_left(1);

    // rho and pi
    let b00 = a00 ^ d0;
    let b01 = (a30 ^ d3).rotate_left(28);
    let b02 = (a10 ^ d1).rotate_left(1);
    let b03 = (a40 ^ d4).rotate_left(27);
    let b04 = (a20 ^ d2).rotate_left(62);
    let b10 = (a11 ^ d1).rotate_left(44);
    let b11 = (a41 ^ d4).rotate_left(20);
    let b12 = (a21 ^ d2).rotate_left(6);
    let b13 = (a01 ^ d0).rotate_left(36);
    let b14 = (a31 ^ d3).rotate_left(55);
    let b20 = (a22 ^ d2).rotate_left(43);
    let b21 = (a02 ^ d0).rotate_left(3);
    let b22 = (a32 ^ d3).rotate_left(25);
    let b23 = (a12 ^ d1).rotate_left(10);
    let b24 = (a42 ^ d4).rotate_left(39);
    let b30 = (a33 ^ d3).rotate_left(21);
    let b31 = (a13 ^ d1).rotate_left(45);
    let b32 = (a43 ^ d4).rotate_left(8);
    let b33 = (a23 ^ d2).rotate_left(15);
    let b34 = (a03 ^ d0).rotate_left(41);
    let b40 = (a44 ^ d4).rotate_left(14);
    let b41 = (a24 ^ d2).rotate_left(61);
    let b42 = (a04 ^ d0).rotate_left(18);
    let b43 = (a34 ^ d3).rotate_left(56);
    let b44 = (a14 ^ d1).rotate_left(2);

    // chi and iota
    [
        b00 ^ (!b10 & b20) ^ rc,
        b10 ^ (!b20 & b30),
        b20 ^ (!b30 & b40),
        b30 ^ (!b40 & b00),
        b40 ^ (!b00 & b10),
        b01 ^ (!b11 & b21),
        b11 ^ (!b21 & b31),
        b21 ^ (!b31 & b41),
        b31 ^ (!b41 & b01),
        b41 ^ (!b01 & b11),
        b02 ^ (!b12 & b22),
        b12 ^ (!b22 & b32),
        b22 ^ (!b32 & b42),
        b32 ^ (!b42 & b02),
        b42 ^ (!b02 & b12),
        b03 ^ (!b13 & b23),
        b13 ^ (!b23 & b33),
        b23 ^ (!b33 & b43),
        b33 ^ (!b43 & b03),
        b43 ^ (!b03 & b13),
        b04 ^ (!b14 & b24),
        b14 ^ (!b24 & b34),
        b24 ^ (!b34 & b44),
        b34 ^ (!b44 & b04),
        b44 ^ (!b04 & b14),
    ]
}

/// Keccak-f[1600] on all four states in `a`, one at a time.
pub(crate) fn sha3_keccak4_f1600(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    sha3_keccak_nof4_f1600::<4>(a, rc)
}

/// Keccak-f[1600] on the first `N` states in `a`, one at a time.
#[allow(clippy::needless_range_loop)]
pub(crate) fn sha3_keccak_nof4_f1600<const N: usize>(a: &mut [[u64; 25]; 4], rc: &[u64; 24]) {
    for i in 0..N {
        sha3_keccak_f1600(&mut a[i], rc);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::mid::sha3::RC;

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
}
