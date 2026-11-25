// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-256's Montgomery multiplication, squaring, addition, and subtraction modulo
//! p = 2^256 - 2^224 + 2^192 + 2^96 - 1, on OpenSSL's `ecp_nistz256-armv4`
//! routines `ecp_nistz256_mul_mont`, `ecp_nistz256_sqr_mont`,
//! `ecp_nistz256_add`, and `ecp_nistz256_sub`.
//!
//! The assembly is OpenSSL's, imported by `admin/import-openssl`: integer
//! code with no branch, predicated instruction, or address that depends on
//! its operands. It is not formally verified: its correctness rests on its
//! use and testing in OpenSSL, and on rind's tests of it against
//! fiat-crypto, rind's `umaal` schedule, Wycheproof, and aws-lc-rs.
//!
//! Both compute `x * y / 2^256 mod p` for `x` and `y` below p, and return a
//! value below p. Nothing else in OpenSSL's file is imported: no point
//! routine, table gather, or table.

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("ecp_nistz256_mul_mont")]
    fn ecp_nistz256_mul_mont(r: *mut [u32; 8], a: *const [u32; 8], b: *const [u32; 8]);

    #[link_name = aws_lc_symbol!("ecp_nistz256_sqr_mont")]
    fn ecp_nistz256_sqr_mont(r: *mut [u32; 8], a: *const [u32; 8]);

    #[link_name = aws_lc_symbol!("ecp_nistz256_add")]
    fn ecp_nistz256_add(r: *mut [u32; 8], a: *const [u32; 8], b: *const [u32; 8]);

    #[link_name = aws_lc_symbol!("ecp_nistz256_sub")]
    fn ecp_nistz256_sub(r: *mut [u32; 8], a: *const [u32; 8], b: *const [u32; 8]);
}

// As in `keccak1600_armv4`: ARM mode, then the target's `.fpu` again. The
// routines use no NEON, so no `.fpu` change is needed to assemble them.
core::arch::global_asm!(
    ".text",
    ".code 32",
    ".globl {ecp_nistz256_mul_mont}",
    ".globl {ecp_nistz256_sqr_mont}",
    ".globl {ecp_nistz256_add}",
    ".globl {ecp_nistz256_sub}",
    include_str!("openssl/ecp_nistz256-armv4.s"),
    ecp_nistz256_mul_mont = sym ecp_nistz256_mul_mont,
    ecp_nistz256_sqr_mont = sym ecp_nistz256_sqr_mont,
    ecp_nistz256_add = sym ecp_nistz256_add,
    ecp_nistz256_sub = sym ecp_nistz256_sub,
);

/// `x * y / 2^256 mod p_256`, for `x` and `y` below p.
pub(crate) fn mul_mont(x: &[u32; 8], y: &[u32; 8]) -> [u32; 8] {
    let mut r = [0; 8];
    // SAFETY: each pointer is to eight words, and the routine reads `x` and
    // `y` and writes `r`, which are distinct here.
    unsafe { asm_call!(unsafe extern "C" ecp_nistz256_mul_mont(&mut r, x, y)) };
    r
}

/// `x^2 / 2^256 mod p_256`, for `x` below p.
pub(crate) fn sqr_mont(x: &[u32; 8]) -> [u32; 8] {
    let mut r = [0; 8];
    // SAFETY: as in `mul_mont`.
    unsafe { asm_call!(unsafe extern "C" ecp_nistz256_sqr_mont(&mut r, x)) };
    r
}

/// `x + y mod p_256`, for `x` and `y` below p.
pub(crate) fn add(x: &[u32; 8], y: &[u32; 8]) -> [u32; 8] {
    let mut r = [0; 8];
    // SAFETY: as in `mul_mont`.
    unsafe { asm_call!(unsafe extern "C" ecp_nistz256_add(&mut r, x, y)) };
    r
}

/// `x - y mod p_256`, for `x` and `y` below p.
pub(crate) fn sub(x: &[u32; 8], y: &[u32; 8]) -> [u32; 8] {
    let mut r = [0; 8];
    // SAFETY: as in `mul_mont`.
    unsafe { asm_call!(unsafe extern "C" ecp_nistz256_sub(&mut r, x, y)) };
    r
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use fiat_crypto::p256_32 as fp;
    use fp::fiat_p256_montgomery_domain_field_element as Fe;
    use proptest::prelude::*;

    use super::*;

    /// p_256, least significant word first.
    const P: [u32; 8] = [
        0xffff_ffff,
        0xffff_ffff,
        0xffff_ffff,
        0,
        0,
        0,
        1,
        0xffff_ffff,
    ];

    /// `x - p` if that does not borrow, else `x`, which fully reduces any
    /// `x < 2p`.
    fn reduce(x: [u32; 8], m: &[u32; 8]) -> [u32; 8] {
        let mut diff = [0u32; 8];
        let mut borrow = 0u64;
        for i in 0..8 {
            let d = u64::from(x[i])
                .wrapping_sub(u64::from(m[i]))
                .wrapping_sub(borrow);
            diff[i] = d as u32;
            borrow = (d >> 63) & 1;
        }
        if borrow == 0 { diff } else { x }
    }

    /// `x - d`, for an `x` whose low word is at least `d`.
    fn minus(mut x: [u32; 8], d: u32) -> [u32; 8] {
        x[0] -= d;
        x
    }

    /// Edge values below p: zero, one, p - 1 and p - 2, every 2^k and
    /// 2^k - 1, and the Montgomery form of one.
    fn edges() -> Vec<[u32; 8]> {
        let mut v = vec![[0; 8], minus(P, 1), minus(P, 2)];
        let mut one = [0; 8];
        one[0] = 1;
        v.push(one);
        // R mod p = 2^256 - p.
        v.push([
            1,
            0,
            0,
            0xffff_ffff,
            0xffff_ffff,
            0xffff_ffff,
            0xffff_fffe,
            0,
        ]);
        for k in 0..256 {
            let mut x = [0u32; 8];
            x[k / 32] = 1 << (k % 32);
            v.push(reduce(x, &P));
            let mut y = [0u32; 8];
            for bit in 0..=k {
                y[bit / 32] |= 1 << (bit % 32);
            }
            v.push(reduce(y, &P));
        }
        v
    }

    fn check(x: &[u32; 8], y: &[u32; 8]) {
        let (fx, fy) = (Fe(*x), Fe(*y));
        let mut want = Fe([0; 8]);
        fp::fiat_p256_mul(&mut want, &fx, &fy);
        assert_eq!(mul_mont(x, y), want.0, "mul {x:08x?} {y:08x?}");
        fp::fiat_p256_square(&mut want, &fx);
        assert_eq!(sqr_mont(x), want.0, "sqr {x:08x?}");
        fp::fiat_p256_add(&mut want, &fx, &fy);
        assert_eq!(add(x, y), want.0, "add {x:08x?} {y:08x?}");
        fp::fiat_p256_sub(&mut want, &fx, &fy);
        assert_eq!(sub(x, y), want.0, "sub {x:08x?} {y:08x?}");
    }

    #[test]
    fn matches_fiat_edges() {
        let edges = edges();
        for x in &edges {
            for y in &edges {
                check(x, y);
            }
        }
    }

    /// The edge values for an input of a random proptest.
    fn below_p() -> impl Strategy<Value = [u32; 8]> {
        let word = prop_oneof![
            Just(0),
            Just(1),
            Just(u32::MAX - 1),
            Just(u32::MAX),
            Just(1 << 31),
            any::<u32>(),
        ];
        // Every 256-bit value is below 2p, so one subtraction reduces it.
        prop_oneof![
            4 => any::<[u32; 8]>(),
            4 => proptest::array::uniform8(word),
        ]
        .prop_map(|x| reduce(x, &P))
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2000))]

        #[test]
        fn matches_fiat(x in below_p(), y in below_p()) {
            let (fx, fy) = (Fe(x), Fe(y));
            let mut want = Fe([0; 8]);
            fp::fiat_p256_mul(&mut want, &fx, &fy);
            prop_assert_eq!(mul_mont(&x, &y), want.0);
            fp::fiat_p256_square(&mut want, &fx);
            prop_assert_eq!(sqr_mont(&x), want.0);
            fp::fiat_p256_add(&mut want, &fx, &fy);
            prop_assert_eq!(add(&x, &y), want.0);
            fp::fiat_p256_sub(&mut want, &fx, &fy);
            prop_assert_eq!(sub(&x, &y), want.0);
        }
    }

    // `admin/ct-qemu` traces these under qemu-arm, twice, with different
    // seeds, and fails unless the instruction and memory addresses match.

    fn seeded(salt: u64) -> [u32; 8] {
        let mut s = super::super::ct_qemu::seed() ^ salt;
        let mut x = [0u32; 8];
        for w in &mut x {
            // splitmix64.
            s = s.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = s;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            *w = (z ^ (z >> 31)) as u32;
        }
        // Below 2^255, so below p.
        x[7] &= 0x7fff_ffff;
        x
    }

    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_nistz256_mul() {
        let (x, y) = (seeded(1), seeded(2));
        super::super::ct_qemu::traced(|| mul_mont(&x, &y));
    }

    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_nistz256_sqr() {
        let x = seeded(3);
        super::super::ct_qemu::traced(|| sqr_mont(&x));
    }

    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_nistz256_add() {
        let (x, y) = (seeded(4), seeded(5));
        super::super::ct_qemu::traced(|| add(&x, &y));
    }

    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_nistz256_sub() {
        let (x, y) = (seeded(6), seeded(7));
        super::super::ct_qemu::traced(|| sub(&x, &y));
    }

    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_ecdh_p256() {
        use crate::agreement::{ECDH_P256, PrivateKey};

        let mut peer_scalar = [1u8; 32];
        peer_scalar[31] = 2;
        let peer = PrivateKey::from_scalar(&ECDH_P256, &peer_scalar).unwrap();
        let peer = peer.public_key().as_ref().to_vec();
        // Every byte comes from the seed except the leading one, which
        // stays zero, so the scalar is below the order.
        let seed = super::super::ct_qemu::seed().to_le_bytes();
        let mut scalar: Vec<u8> = seed.iter().cycle().take(32).copied().collect();
        scalar[0] = 0;
        if scalar.iter().all(|&byte| byte == 0) {
            scalar[31] = 1;
        }
        super::super::ct_qemu::traced(|| {
            let key = PrivateKey::from_scalar(&ECDH_P256, &scalar).unwrap();
            key.agree(&peer).is_ok()
        });
    }
}
