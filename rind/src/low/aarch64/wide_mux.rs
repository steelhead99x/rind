// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Schedules s2n-bignum's elliptic-curve routines for this core's multiplier.
//!
//! The sibling modules without a `_narrow` suffix are s2n-bignum's `_alt`
//! schedules, written for cores that issue `umulh` widely. The `_narrow`
//! modules are the other schedules. Cortex-A76 retires a `umulh` once
//! every four cycles, and there the narrow X25519 is the one aws-lc runs.
//! Both are correct on every core. Linux selects narrow only for
//! Cortex-A72, Cortex-A76, and Neoverse N1; every other core, including
//! one this crate does not recognise, keeps `_alt`. `cpu::wide_multiplier`
//! is the choice.

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
pub(crate) fn bignum_montmul_p256(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::bignum_montmul_p256::bignum_montmul_p256(z, x, y)
    } else {
        super::bignum_montmul_p256_narrow::bignum_montmul_p256(z, x, y)
    }
}

#[inline]
pub(crate) fn bignum_montmul_p384(z: &mut [u64; 6], x: &[u64; 6], y: &[u64; 6]) {
    if super::cpu::wide_multiplier() {
        super::bignum_montmul_p384::bignum_montmul_p384(z, x, y)
    } else {
        super::bignum_montmul_p384_narrow::bignum_montmul_p384(z, x, y)
    }
}

#[inline]
pub(crate) fn bignum_montsqr_p256(z: &mut [u64; 4], x: &[u64; 4]) {
    if super::cpu::wide_multiplier() {
        super::bignum_montsqr_p256::bignum_montsqr_p256(z, x)
    } else {
        super::bignum_montsqr_p256_narrow::bignum_montsqr_p256(z, x)
    }
}

#[inline]
pub(crate) fn bignum_montsqr_p384(z: &mut [u64; 6], x: &[u64; 6]) {
    if super::cpu::wide_multiplier() {
        super::bignum_montsqr_p384::bignum_montsqr_p384(z, x)
    } else {
        super::bignum_montsqr_p384_narrow::bignum_montsqr_p384(z, x)
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
pub(crate) fn bignum_mul_p521(z: &mut [u64; 9], x: &[u64; 9], y: &[u64; 9]) {
    if super::cpu::wide_multiplier() {
        super::bignum_mul_p521::bignum_mul_p521(z, x, y)
    } else {
        super::bignum_mul_p521_narrow::bignum_mul_p521(z, x, y)
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
pub(crate) fn bignum_sqr_p521(z: &mut [u64; 9], x: &[u64; 9]) {
    if super::cpu::wide_multiplier() {
        super::bignum_sqr_p521::bignum_sqr_p521(z, x)
    } else {
        super::bignum_sqr_p521_narrow::bignum_sqr_p521(z, x)
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
pub(crate) fn p256_montjadd(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 12]) {
    if super::cpu::wide_multiplier() {
        super::p256_montjadd::p256_montjadd(p3, p1, p2)
    } else {
        super::p256_montjadd_narrow::p256_montjadd(p3, p1, p2)
    }
}

#[inline]
pub(crate) fn p256_montjdouble(p3: &mut [u64; 12], p1: &[u64; 12]) {
    if super::cpu::wide_multiplier() {
        super::p256_montjdouble::p256_montjdouble(p3, p1)
    } else {
        super::p256_montjdouble_narrow::p256_montjdouble(p3, p1)
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
pub(crate) fn p384_montjadd(p3: &mut [u64; 18], p1: &[u64; 18], p2: &[u64; 18]) {
    if super::cpu::wide_multiplier() {
        super::p384_montjadd::p384_montjadd(p3, p1, p2)
    } else {
        super::p384_montjadd_narrow::p384_montjadd(p3, p1, p2)
    }
}

#[inline]
pub(crate) fn p384_montjdouble(p3: &mut [u64; 18], p1: &[u64; 18]) {
    if super::cpu::wide_multiplier() {
        super::p384_montjdouble::p384_montjdouble(p3, p1)
    } else {
        super::p384_montjdouble_narrow::p384_montjdouble(p3, p1)
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
    /// Both schedules agree. The cases live in `schedules`, which regeneration
    /// of this file does not overwrite.
    #[test]
    fn schedules_agree() {
        super::super::schedules::agree();
    }
}
