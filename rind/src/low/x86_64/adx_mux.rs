// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Picks s2n-bignum's routines that use BMI2 and ADX where the CPU has them,
//! and otherwise their `_alt` twins, which use only `mul`, `adc`, and `sbb`.
//! Without ADX, Ed25519 verification on CPUs with AVX2 runs a port of
//! curve25519-dalek's AVX2 backend instead.
//!
//! The Karatsuba multipliers and `bignum_emontredc_8n` have no `_alt` twin;
//! `super::mont` picks RSA's multiplication instead.

use super::cpu::{HaveAvx2, HaveBmi2Adx};

macro_rules! mux {
    ($($name:ident / $alt:ident ($($arg:ident: $ty:ty),*) $(-> $ret:ty)?;)*) => {$(
        #[inline]
        pub(crate) fn $name($($arg: $ty),*) $(-> $ret)? {
            match HaveBmi2Adx::check() {
                Some(_) => super::$name::$name($($arg),*),
                None => super::$alt::$alt($($arg),*),
            }
        }
    )*};
}

mux! {
    bignum_demont_p256 / bignum_demont_p256_alt(z: &mut [u64; 4], x: &[u64; 4]);
    bignum_montmul_p256 / bignum_montmul_p256_alt(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]);
    bignum_montsqr_p256 / bignum_montsqr_p256_alt(z: &mut [u64; 4], x: &[u64; 4]);
    bignum_tomont_p256 / bignum_tomont_p256_alt(z: &mut [u64; 4], x: &[u64; 4]);
    p256_montjadd / p256_montjadd_alt(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 12]);
    p256_montjdouble / p256_montjdouble_alt(p3: &mut [u64; 12], p1: &[u64; 12]);
    p256_montjmixadd / p256_montjmixadd_alt(p3: &mut [u64; 12], p1: &[u64; 12], p2: &[u64; 8]);
    p256_scalarmul / p256_scalarmul_alt(res: &mut [u64; 8], scalar: &[u64; 4], point: &[u64; 8]);

    bignum_demont_p384 / bignum_demont_p384_alt(z: &mut [u64; 6], x: &[u64; 6]);
    bignum_montmul_p384 / bignum_montmul_p384_alt(z: &mut [u64; 6], x: &[u64; 6], y: &[u64; 6]);
    bignum_montsqr_p384 / bignum_montsqr_p384_alt(z: &mut [u64; 6], x: &[u64; 6]);
    bignum_tomont_p384 / bignum_tomont_p384_alt(z: &mut [u64; 6], x: &[u64; 6]);
    p384_montjadd / p384_montjadd_alt(p3: &mut [u64; 18], p1: &[u64; 18], p2: &[u64; 18]);
    p384_montjdouble / p384_montjdouble_alt(p3: &mut [u64; 18], p1: &[u64; 18]);
    p384_montjmixadd / p384_montjmixadd_alt(p3: &mut [u64; 18], p1: &[u64; 18], p2: &[u64; 12]);
    p384_montjscalarmul / p384_montjscalarmul_alt(res: &mut [u64; 18], scalar: &[u64; 6], point: &[u64; 18]);

    bignum_mod_n521 / bignum_mod_n521_alt(z: &mut [u64; 9], x: &[u64; 9]);
    bignum_mul_p521 / bignum_mul_p521_alt(z: &mut [u64; 9], x: &[u64; 9], y: &[u64; 9]);
    bignum_sqr_p521 / bignum_sqr_p521_alt(z: &mut [u64; 9], x: &[u64; 9]);
    p521_jadd / p521_jadd_alt(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 27]);
    p521_jdouble / p521_jdouble_alt(p3: &mut [u64; 27], p1: &[u64; 27]);
    p521_jmixadd / p521_jmixadd_alt(p3: &mut [u64; 27], p1: &[u64; 27], p2: &[u64; 18]);
    p521_jscalarmul / p521_jscalarmul_alt(res: &mut [u64; 27], scalar: &[u64; 9], point: &[u64; 27]);

    bignum_madd_n25519 / bignum_madd_n25519_alt(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4], c: &[u64; 4]);
    curve25519_x25519 / curve25519_x25519_alt(res: &mut [u64; 4], scalar: &[u64; 4], point: &[u64; 4]);
    curve25519_x25519base / curve25519_x25519base_alt(res: &mut [u64; 4], scalar: &[u64; 4]);
    edwards25519_decode / edwards25519_decode_alt(z: &mut [u64; 8], c: &[u8; 32]) -> bool;
    edwards25519_scalarmulbase / edwards25519_scalarmulbase_alt(res: &mut [u64; 8], scalar: &[u64; 4]);

    bignum_invsqrt_p25519 / bignum_invsqrt_p25519_alt(z: &mut [u64; 4], x: &[u64; 4]) -> u64;
    bignum_mul_p25519 / bignum_mul_p25519_alt(z: &mut [u64; 4], x: &[u64; 4], y: &[u64; 4]);
    bignum_sqr_p25519 / bignum_sqr_p25519_alt(z: &mut [u64; 4], x: &[u64; 4]);
    edwards25519_epadd / edwards25519_epadd_alt(p3: &mut [u64; 16], p1: &[u64; 16], p2: &[u64; 16]);
    edwards25519_epdouble / edwards25519_epdouble_alt(p3: &mut [u64; 16], p1: &[u64; 12]);
    edwards25519_pdouble / edwards25519_pdouble_alt(p3: &mut [u64; 12], p1: &[u64; 12]);
}

/// Ed25519 verification's `[scalar]point + [bscalar]B`, for scalars below
/// 2^255. Without ADX, CPUs with AVX2 run curve25519-dalek's AVX2 backend,
/// which measured faster than the `_alt` routine there.
#[inline]
pub(crate) fn edwards25519_scalarmuldouble(
    res: &mut [u64; 8],
    scalar: &[u64; 4],
    point: &[u64; 8],
    bscalar: &[u64; 4],
) {
    match HaveBmi2Adx::check() {
        Some(_) => super::edwards25519_scalarmuldouble::edwards25519_scalarmuldouble(
            res, scalar, point, bscalar,
        ),
        None => match HaveAvx2::check() {
            Some(token) => super::edwards25519_scalarmuldouble_avx2::edwards25519_scalarmuldouble(
                res, scalar, point, bscalar, token,
            ),
            None => super::edwards25519_scalarmuldouble_alt::edwards25519_scalarmuldouble_alt(
                res, scalar, point, bscalar,
            ),
        },
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(super) mod tests {
    use super::super::*;

    // Every other test runs only the form this CPU picks, so on a CPU with
    // BMI2 and ADX, each pair is checked against each other here. Field
    // elements are reduced, as the routines require; the point routines are
    // straight-line field arithmetic, so off-curve points exercise them as
    // well as real ones.
    #[test]
    fn alt_matches_bmi2_adx() {
        if super::HaveBmi2Adx::check().is_none() {
            return;
        }

        let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
        for _ in 0..64 {
            same1(
                &mut rng,
                255,
                bignum_demont_p256::bignum_demont_p256,
                bignum_demont_p256_alt::bignum_demont_p256_alt,
            );
            same1(
                &mut rng,
                255,
                bignum_montsqr_p256::bignum_montsqr_p256,
                bignum_montsqr_p256_alt::bignum_montsqr_p256_alt,
            );
            same1(
                &mut rng,
                255,
                bignum_tomont_p256::bignum_tomont_p256,
                bignum_tomont_p256_alt::bignum_tomont_p256_alt,
            );
            same2(
                &mut rng,
                255,
                bignum_montmul_p256::bignum_montmul_p256,
                bignum_montmul_p256_alt::bignum_montmul_p256_alt,
            );
            same1(
                &mut rng,
                255,
                p256_montjdouble::p256_montjdouble,
                p256_montjdouble_alt::p256_montjdouble_alt,
            );
            same2(
                &mut rng,
                255,
                p256_montjadd::p256_montjadd,
                p256_montjadd_alt::p256_montjadd_alt,
            );
            same2(
                &mut rng,
                255,
                p256_montjmixadd::p256_montjmixadd,
                p256_montjmixadd_alt::p256_montjmixadd_alt,
            );
            same2(
                &mut rng,
                255,
                p256_scalarmul::p256_scalarmul,
                p256_scalarmul_alt::p256_scalarmul_alt,
            );

            same1(
                &mut rng,
                383,
                bignum_demont_p384::bignum_demont_p384,
                bignum_demont_p384_alt::bignum_demont_p384_alt,
            );
            same1(
                &mut rng,
                383,
                bignum_montsqr_p384::bignum_montsqr_p384,
                bignum_montsqr_p384_alt::bignum_montsqr_p384_alt,
            );
            same1(
                &mut rng,
                383,
                bignum_tomont_p384::bignum_tomont_p384,
                bignum_tomont_p384_alt::bignum_tomont_p384_alt,
            );
            same2(
                &mut rng,
                383,
                bignum_montmul_p384::bignum_montmul_p384,
                bignum_montmul_p384_alt::bignum_montmul_p384_alt,
            );
            same1(
                &mut rng,
                383,
                p384_montjdouble::p384_montjdouble,
                p384_montjdouble_alt::p384_montjdouble_alt,
            );
            same2(
                &mut rng,
                383,
                p384_montjadd::p384_montjadd,
                p384_montjadd_alt::p384_montjadd_alt,
            );
            same2(
                &mut rng,
                383,
                p384_montjmixadd::p384_montjmixadd,
                p384_montjmixadd_alt::p384_montjmixadd_alt,
            );
            same2(
                &mut rng,
                383,
                p384_montjscalarmul::p384_montjscalarmul,
                p384_montjscalarmul_alt::p384_montjscalarmul_alt,
            );

            same1(
                &mut rng,
                520,
                bignum_mod_n521::bignum_mod_n521,
                bignum_mod_n521_alt::bignum_mod_n521_alt,
            );
            same1(
                &mut rng,
                520,
                bignum_sqr_p521::bignum_sqr_p521,
                bignum_sqr_p521_alt::bignum_sqr_p521_alt,
            );
            same2(
                &mut rng,
                520,
                bignum_mul_p521::bignum_mul_p521,
                bignum_mul_p521_alt::bignum_mul_p521_alt,
            );
            same1(
                &mut rng,
                520,
                p521_jdouble::p521_jdouble,
                p521_jdouble_alt::p521_jdouble_alt,
            );
            same2(
                &mut rng,
                520,
                p521_jadd::p521_jadd,
                p521_jadd_alt::p521_jadd_alt,
            );
            same2(
                &mut rng,
                520,
                p521_jmixadd::p521_jmixadd,
                p521_jmixadd_alt::p521_jmixadd_alt,
            );
            same2(
                &mut rng,
                520,
                p521_jscalarmul::p521_jscalarmul,
                p521_jscalarmul_alt::p521_jscalarmul_alt,
            );

            same1(
                &mut rng,
                255,
                curve25519_x25519base::curve25519_x25519base,
                curve25519_x25519base_alt::curve25519_x25519base_alt,
            );
            same2(
                &mut rng,
                256,
                curve25519_x25519::curve25519_x25519,
                curve25519_x25519_alt::curve25519_x25519_alt,
            );
            same1(
                &mut rng,
                256,
                edwards25519_scalarmulbase::edwards25519_scalarmulbase,
                edwards25519_scalarmulbase_alt::edwards25519_scalarmulbase_alt,
            );

            same2(
                &mut rng,
                254,
                bignum_mul_p25519::bignum_mul_p25519,
                bignum_mul_p25519_alt::bignum_mul_p25519_alt,
            );
            same1(
                &mut rng,
                254,
                bignum_sqr_p25519::bignum_sqr_p25519,
                bignum_sqr_p25519_alt::bignum_sqr_p25519_alt,
            );
            same2(
                &mut rng,
                254,
                edwards25519_epadd::edwards25519_epadd,
                edwards25519_epadd_alt::edwards25519_epadd_alt,
            );
            same1(
                &mut rng,
                254,
                edwards25519_epdouble::edwards25519_epdouble,
                edwards25519_epdouble_alt::edwards25519_epdouble_alt,
            );
            same1(
                &mut rng,
                254,
                edwards25519_pdouble::edwards25519_pdouble,
                edwards25519_pdouble_alt::edwards25519_pdouble_alt,
            );

            let x = rng.field::<4>(254);
            let (mut want, mut got) = ([0; 4], [0; 4]);
            assert_eq!(
                bignum_invsqrt_p25519::bignum_invsqrt_p25519(&mut want, &x),
                bignum_invsqrt_p25519_alt::bignum_invsqrt_p25519_alt(&mut got, &x)
            );
            assert_eq!(want, got);

            let (x, y, c) = (
                rng.words::<4>(256),
                rng.words::<4>(256),
                rng.words::<4>(256),
            );
            let (mut want, mut got) = ([0; 4], [0; 4]);
            bignum_madd_n25519::bignum_madd_n25519(&mut want, &x, &y, &c);
            bignum_madd_n25519_alt::bignum_madd_n25519_alt(&mut got, &x, &y, &c);
            assert_eq!(want, got);

            // A real point for the double scalar multiplication, which
            // decodes it first.
            let mut point = [0; 8];
            edwards25519_scalarmulbase::edwards25519_scalarmulbase(&mut point, &rng.words(256));
            let mut encoded = [0u8; 32];
            for (chunk, word) in encoded
                .as_chunks_mut::<8>()
                .0
                .iter_mut()
                .zip(rng.words::<4>(256))
            {
                *chunk = word.to_le_bytes();
            }
            let (mut want, mut got) = ([0; 8], [0; 8]);
            assert_eq!(
                edwards25519_decode::edwards25519_decode(&mut want, &encoded),
                edwards25519_decode_alt::edwards25519_decode_alt(&mut got, &encoded)
            );
            assert_eq!(want, got);
            let (scalar, bscalar) = (rng.words::<4>(256), rng.words::<4>(256));
            edwards25519_scalarmuldouble::edwards25519_scalarmuldouble(
                &mut want, &scalar, &point, &bscalar,
            );
            edwards25519_scalarmuldouble_alt::edwards25519_scalarmuldouble_alt(
                &mut got, &scalar, &point, &bscalar,
            );
            assert_eq!(want, got);
        }
    }

    fn same1<const N: usize, const M: usize>(
        rng: &mut Rng,
        bits: u32,
        want: fn(&mut [u64; M], &[u64; N]),
        got: fn(&mut [u64; M], &[u64; N]),
    ) {
        let x = rng.field(bits);
        let (mut a, mut b) = ([0; M], [0; M]);
        want(&mut a, &x);
        got(&mut b, &x);
        assert_eq!(a, b);
    }

    fn same2<const N: usize, const K: usize, const M: usize>(
        rng: &mut Rng,
        bits: u32,
        want: fn(&mut [u64; M], &[u64; N], &[u64; K]),
        got: fn(&mut [u64; M], &[u64; N], &[u64; K]),
    ) {
        let (x, y) = (rng.field(bits), rng.field(bits));
        let (mut a, mut b) = ([0; M], [0; M]);
        want(&mut a, &x, &y);
        got(&mut b, &x, &y);
        assert_eq!(a, b);
    }

    /// splitmix64, so failures reproduce.
    pub(in super::super) struct Rng(pub(in super::super) u64);

    impl Rng {
        pub(in super::super) fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        /// `N` words holding a value below 2^`bits`.
        pub(in super::super) fn words<const N: usize>(&mut self, bits: u32) -> [u64; N] {
            core::array::from_fn(|i| {
                let low = 64 * i as u32;
                match bits.saturating_sub(low) {
                    0 => 0,
                    b if b >= 64 => self.next(),
                    b => self.next() & ((1 << b) - 1),
                }
            })
        }

        /// Field elements of a curve whose prime exceeds 2^`bits`, packed
        /// into an array of whole coordinates.
        pub(in super::super) fn field<const N: usize>(&mut self, bits: u32) -> [u64; N] {
            let words = bits.div_ceil(64) as usize;
            let mut out = [0; N];
            for chunk in out.chunks_mut(words) {
                let element = self.words::<9>(bits);
                chunk.copy_from_slice(&element[..chunk.len()]);
            }
            out
        }
    }
}
