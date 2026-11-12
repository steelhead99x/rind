// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Schedules s2n-bignum's elliptic-curve routines for this core's multiplier.
//!
//! The sibling modules without a `_narrow` suffix are s2n-bignum's `_alt`
//! schedules, written for cores that issue `umulh` widely: Apple's, and
//! Neoverse V1, V2, V3, and N2. The `_narrow` modules are the other
//! schedules, for cores whose high multiply is lightly pipelined.
//! Cortex-A76 retires a `umulh` once every four cycles, and there the
//! narrow X25519 is the one aws-lc runs. Both are correct on every
//! core rind supports; a core this crate does not recognise runs the
//! narrow schedule. `cpu::wide_multiplier` is the choice.

#[inline]
pub(crate) fn bignum_invsqrt_p25519(z: &mut [u64; 4], x: &[u64; 4]) -> u64 {
    if super::cpu::wide_multiplier() {
        super::bignum_invsqrt_p25519::bignum_invsqrt_p25519(z, x)
    } else {
        super::bignum_invsqrt_p25519_narrow::bignum_invsqrt_p25519(z, x)
    }
}

#[inline]
pub(crate) fn bignum_madd_n25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4], c: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::bignum_madd_n25519::bignum_madd_n25519(z, x, y, c)
    } else {
        super::bignum_madd_n25519_narrow::bignum_madd_n25519(z, x, y, c)
    }
}

#[inline]
pub(crate) fn bignum_mul_p25519(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::bignum_mul_p25519::bignum_mul_p25519(z, x, y)
    } else {
        super::bignum_mul_p25519_narrow::bignum_mul_p25519(z, x, y)
    }
}

#[inline]
pub(crate) fn bignum_sqr_p25519(z: &mut [u64; 4], x: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::bignum_sqr_p25519::bignum_sqr_p25519(z, x)
    } else {
        super::bignum_sqr_p25519_narrow::bignum_sqr_p25519(z, x)
    }
}

#[inline]
pub(crate) fn curve25519_x25519(res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::curve25519_x25519::curve25519_x25519(res, scalar, point)
    } else {
        super::curve25519_x25519_narrow::curve25519_x25519(res, scalar, point)
    }
}

#[inline]
pub(crate) fn curve25519_x25519base(res: &mut [u64; 4], scalar: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::curve25519_x25519base::curve25519_x25519base(res, scalar)
    } else {
        super::curve25519_x25519base_narrow::curve25519_x25519base(res, scalar)
    }
}

#[inline]
pub(crate) fn edwards25519_decode(z: &mut [u64; 8], c: &[u8; 32]) -> bool {
    if super::cpu::wide_multiplier() {
        super::edwards25519_decode::edwards25519_decode(z, c)
    } else {
        super::edwards25519_decode_narrow::edwards25519_decode(z, c)
    }
}

#[inline]
pub(crate) fn edwards25519_epadd(p3: &mut [u64; 16], p1: &[u64; 16], p2: &[u64; 16]) {
    if super::cpu::wide_multiplier() {
        super::edwards25519_epadd::edwards25519_epadd(p3, p1, p2)
    } else {
        super::edwards25519_epadd_narrow::edwards25519_epadd(p3, p1, p2)
    }
}

#[inline]
pub(crate) fn edwards25519_epdouble(p3: &mut [u64; 16], p1: &[u64; 12]) {
    if super::cpu::wide_multiplier() {
        super::edwards25519_epdouble::edwards25519_epdouble(p3, p1)
    } else {
        super::edwards25519_epdouble_narrow::edwards25519_epdouble(p3, p1)
    }
}

#[inline]
pub(crate) fn edwards25519_pdouble(p3: &mut [u64; 12], p1: &[u64; 12]) {
    if super::cpu::wide_multiplier() {
        super::edwards25519_pdouble::edwards25519_pdouble(p3, p1)
    } else {
        super::edwards25519_pdouble_narrow::edwards25519_pdouble(p3, p1)
    }
}

#[inline]
pub(crate) fn edwards25519_scalarmulbase(res: &mut [u64; 8], scalar: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::edwards25519_scalarmulbase::edwards25519_scalarmulbase(res, scalar)
    } else {
        super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(res, scalar)
    }
}

#[inline]
pub(crate) fn edwards25519_scalarmuldouble(
    res: &mut [u64; 8],
    scalar: &[u64; 4],
    point: &[u64; 8],
    bscalar: &[u64; 4],
) {
    if super::cpu::wide_multiplier() {
        super::edwards25519_scalarmuldouble::edwards25519_scalarmuldouble(
            res, scalar, point, bscalar,
        )
    } else {
        super::edwards25519_scalarmuldouble_narrow::edwards25519_scalarmuldouble(
            res, scalar, point, bscalar,
        )
    }
}

#[inline]
pub(crate) fn p256_montjmixadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 8]) {
    if super::cpu::wide_multiplier() {
        super::p256_montjmixadd::p256_montjmixadd(p3, p1, p2)
    } else {
        super::p256_montjmixadd_narrow::p256_montjmixadd(p3, p1, p2)
    }
}

#[inline]
pub(crate) fn p256_scalarmul(res: &mut [u64; 8], scalar: &[u64; 4], point: &[u64; 8]) {
    if super::cpu::wide_multiplier() {
        super::p256_scalarmul::p256_scalarmul(res, scalar, point)
    } else {
        super::p256_scalarmul_narrow::p256_scalarmul(res, scalar, point)
    }
}

#[inline]
pub(crate) fn p256_scalarmulbase(res: &mut [u64; 8], scalar: &[u64; 4], table: &[[u64; 256]; 43]) {
    if super::cpu::wide_multiplier() {
        super::p256_scalarmulbase::p256_scalarmulbase(res, scalar, table)
    } else {
        super::p256_scalarmulbase_narrow::p256_scalarmulbase(res, scalar, table)
    }
}

#[inline]
pub(crate) fn p384_montjmixadd(p3: &mut [u64; 18], p1: &[u64; 18], p2: &[u64; 12]) {
    if super::cpu::wide_multiplier() {
        super::p384_montjmixadd::p384_montjmixadd(p3, p1, p2)
    } else {
        super::p384_montjmixadd_narrow::p384_montjmixadd(p3, p1, p2)
    }
}

#[inline]
pub(crate) fn p384_montjscalarmul(res: &mut [u64; 18], scalar: &[u64; 6], point: &[u64; 18]) {
    if super::cpu::wide_multiplier() {
        super::p384_montjscalarmul::p384_montjscalarmul(res, scalar, point)
    } else {
        super::p384_montjscalarmul_narrow::p384_montjscalarmul(res, scalar, point)
    }
}

#[inline]
pub(crate) fn p521_jadd(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 27]) {
    if super::cpu::wide_multiplier() {
        super::p521_jadd::p521_jadd(p3, p1, p2)
    } else {
        super::p521_jadd_narrow::p521_jadd(p3, p1, p2)
    }
}

#[inline]
pub(crate) fn p521_jdouble(p3: &mut [u64; 27], p1: &[u64; 27]) {
    if super::cpu::wide_multiplier() {
        super::p521_jdouble::p521_jdouble(p3, p1)
    } else {
        super::p521_jdouble_narrow::p521_jdouble(p3, p1)
    }
}

#[inline]
pub(crate) fn p521_jmixadd(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 18]) {
    if super::cpu::wide_multiplier() {
        super::p521_jmixadd::p521_jmixadd(p3, p1, p2)
    } else {
        super::p521_jmixadd_narrow::p521_jmixadd(p3, p1, p2)
    }
}

#[inline]
pub(crate) fn p521_jscalarmul(res: &mut [u64; 27], scalar: &[u64; 9], point: &[u64; 27]) {
    if super::cpu::wide_multiplier() {
        super::p521_jscalarmul::p521_jscalarmul(res, scalar, point)
    } else {
        super::p521_jscalarmul_narrow::p521_jscalarmul(res, scalar, point)
    }
}

#[cfg(test)]
mod tests {
    /// Both schedules agree on these inputs. The points are on the curve,
    /// which is the precondition the scalar-multiplication proofs state.
    #[test]
    fn schedules_agree() {
        let scalar = [
            0x0123_4567_89ab_cdef,
            0xfedc_ba98_7654_3210,
            0x0f0e_0d0c_0b0a_0908,
            0x0706_0504_0302_0100,
        ];
        let point = [9, 0, 0, 0];
        let mut wide = [0; 4];
        let mut narrow = [0; 4];
        super::super::curve25519_x25519::curve25519_x25519(&mut wide, &scalar, &point);
        super::super::curve25519_x25519_narrow::curve25519_x25519(&mut narrow, &scalar, &point);
        assert_eq!(wide, narrow);
        super::super::curve25519_x25519base::curve25519_x25519base(&mut wide, &scalar);
        super::super::curve25519_x25519base_narrow::curve25519_x25519base(&mut narrow, &scalar);
        assert_eq!(wide, narrow);

        let mut wide8 = [0; 8];
        let mut narrow8 = [0; 8];
        super::super::edwards25519_scalarmulbase::edwards25519_scalarmulbase(&mut wide8, &scalar);
        super::super::edwards25519_scalarmulbase_narrow::edwards25519_scalarmulbase(
            &mut narrow8,
            &scalar,
        );
        assert_eq!(wide8, narrow8);

        // P-256's generator, affine, little-endian limbs.
        let g = [
            0xf4a1_3945_d898_c296,
            0x7703_7d81_2deb_33a0,
            0xf8bc_e6e5_63a4_40f2,
            0x6b17_d1f2_e12c_4247,
            0xcbb6_4068_37bf_51f5,
            0x2bce_3357_6b31_5ece,
            0x8ee7_eb4a_7c0f_9e16,
            0x4fe3_42e2_fe1a_7f9b,
        ];
        let two = [2, 0, 0, 0];
        super::super::p256_scalarmul::p256_scalarmul(&mut wide8, &two, &g);
        super::super::p256_scalarmul_narrow::p256_scalarmul(&mut narrow8, &two, &g);
        assert_eq!(wide8, narrow8);
    }
}
