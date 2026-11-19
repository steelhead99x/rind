// Copyright (c) The mldsa-native project authors
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT

//! Plastering over the differences between (eg) mldsa_ntt() between x86-64
//! and aarch64.
//!
//! Each picks s2n-bignum's AVX2 routine where the CPU has AVX2, and otherwise
//! the portable port of mldsa-native's C. The AVX2 transforms keep
//! coefficients in their own order, which [`mldsa_nttunpack`] produces from
//! the natural one, so a process never mixes them: the CPU's features are
//! read once.

use super::cpu::HaveAvx2;
use crate::low;
use crate::low::generic::mldsa_poly::{self as portable, MldsaPoly, rows};

mod qdata;
use qdata::QDATA;

/// Forward number-theoretic transform from ML-DSA
pub(crate) fn mldsa_ntt(a: &mut [i32; 256]) {
    match HaveAvx2::check() {
        Some(_) => super::mldsa_ntt::mldsa_ntt(a, &QDATA.0),
        None => portable::mldsa_ntt(a),
    }
}

/// Inverse number-theoretic transform from ML-DSA, multiplying by `2^32`
pub(crate) fn mldsa_intt(a: &mut [i32; 256]) {
    match HaveAvx2::check() {
        Some(_) => super::mldsa_intt::mldsa_intt(a, &QDATA.0),
        None => portable::mldsa_intt(a),
    }
}

/// Permutes NTT-domain coefficients sampled in natural order into the order
/// [`mldsa_ntt`] produces
pub(crate) fn mldsa_nttunpack(a: &mut [i32; 256]) {
    match HaveAvx2::check() {
        Some(_) => super::mldsa_nttunpack::mldsa_nttunpack(a),
        None => portable::mldsa_nttunpack(a),
    }
}

/// Pointwise Montgomery multiplication in the NTT domain
pub(crate) fn mldsa_pointwise(c: &mut [i32; 256], a: &[i32; 256], b: &[i32; 256]) {
    match HaveAvx2::check() {
        Some(_) => super::mldsa_pointwise::mldsa_pointwise(c, a, b, &POINTWISE_QDATA.0),
        None => portable::mldsa_pointwise(c, a, b),
    }
}

/// Pointwise Montgomery multiply-accumulate of two vectors in the NTT domain
pub(crate) fn mldsa_pointwise_acc(c: &mut [i32; 256], a: &[MldsaPoly], b: &[MldsaPoly]) {
    assert_eq!(a.len(), b.len());
    match (HaveAvx2::check(), a.len()) {
        (Some(_), 4) => {
            super::mldsa_pointwise_acc_l4::mldsa_pointwise_acc_l4(c, rows(a), rows(b), &QDATA.0)
        }
        (Some(_), 5) => {
            super::mldsa_pointwise_acc_l5::mldsa_pointwise_acc_l5(c, rows(a), rows(b), &QDATA.0)
        }
        (Some(_), 7) => {
            super::mldsa_pointwise_acc_l7::mldsa_pointwise_acc_l7(c, rows(a), rows(b), &QDATA.0)
        }
        _ => portable::mldsa_pointwise_acc(c, a, b),
    }
}

macro_rules! unary {
    ($($name:ident: $doc:literal),*) => {$(
        #[doc = $doc]
        pub(crate) fn $name(a: &mut [i32; 256]) {
            match HaveAvx2::check() {
                Some(_) => super::$name::$name(a),
                None => portable::$name(a),
            }
        }
    )*};
}

unary!(
    mldsa_reduce: "Reduces coefficients to `[-6283009, 6283008]`",
    mldsa_caddq: "Adds `q` to negative coefficients"
);

/// 1 if any coefficient's magnitude is at least `bound`, else 0
pub(crate) fn mldsa_chknorm(a: &[i32; 256], bound: u64) -> u64 {
    match HaveAvx2::check() {
        Some(_) => super::mldsa_chknorm::mldsa_chknorm(a, bound),
        None => portable::mldsa_chknorm(a, bound),
    }
}

macro_rules! binary {
    ($($name:ident($x:ident: $x_ty:ty, $y:ident: $y_ty:ty): $doc:literal),*) => {$(
        #[doc = $doc]
        pub(crate) fn $name($x: $x_ty, $y: $y_ty) {
            match HaveAvx2::check() {
                Some(_) => super::$name::$name($x, $y),
                None => portable::$name($x, $y),
            }
        }
    )*};
}

binary!(
    mldsa_decompose_32(a1: &mut [i32; 256], a0: &mut [i32; 256]):
        "Splits coefficients into high and low parts for `gamma2 = (q - 1) / 32`",
    mldsa_decompose_88(a1: &mut [i32; 256], a0: &mut [i32; 256]):
        "Splits coefficients into high and low parts for `gamma2 = (q - 1) / 88`",
    mldsa_poly_use_hint_32(a: &mut [i32; 256], h: &[i32; 256]):
        "Corrects high parts by hints for `gamma2 = (q - 1) / 32`",
    mldsa_poly_use_hint_88(a: &mut [i32; 256], h: &[i32; 256]):
        "Corrects high parts by hints for `gamma2 = (q - 1) / 88`",
    mldsa_polyz_unpack_17(r: &mut [i32; 256], b: &[u8; 576]):
        "Unpacks a signature's `z` for `gamma1 = 2^17`",
    mldsa_polyz_unpack_19(r: &mut [i32; 256], b: &[u8; 640]):
        "Unpacks a signature's `z` for `gamma1 = 2^19`"
);

/// Rejection-samples coefficients below `q` from `buf` into `r[offset..]`,
/// returning how many of `r` are now written. Its time depends on public
/// values alone: `buf` expands the public seed `rho`.
pub(crate) fn mldsa_rej_uniform_vartime(r: &mut [i32; 256], offset: usize, buf: &[u8]) -> usize {
    if let (Some(_), 0, Ok(buf)) = (HaveAvx2::check(), offset, buf.try_into()) {
        return super::mldsa_rej_uniform_vartime::mldsa_rej_uniform_vartime(
            r,
            buf,
            &MLDSA_REJ_UNIFORM_TABLE,
        ) as usize;
    }
    portable::mldsa_rej_uniform_vartime(r, offset, buf)
}

macro_rules! rej_eta {
    ($($name:ident($len:literal): $doc:literal),*) => {$(
        #[doc = $doc]
        ///
        /// Which nibbles are rejected is public, as FIPS 204 allows: the
        /// accepted values are independent of it.
        pub(crate) fn $name(r: &mut [i32; 256], offset: usize, buf: &[u8]) -> usize {
            if let (Some(_), 0, Ok(buf)) = (HaveAvx2::check(), offset, <&[u8; $len]>::try_from(buf)) {
                low::ct::public_slice(buf);
                let n = super::$name::$name(r, buf, &MLDSA_REJ_UNIFORM_TABLE) as usize;
                low::ct::secret_slice(&r[..n]);
                return n;
            }
            portable::$name(r, offset, buf)
        }
    )*};
}

rej_eta!(
    mldsa_rej_uniform_eta2_vartime(136):
        "Rejection-samples coefficients in `[-2, 2]` from the nibbles of `buf` into `r[offset..]`",
    mldsa_rej_uniform_eta4_vartime(272):
        "Rejection-samples coefficients in `[-4, 4]` from the nibbles of `buf` into `r[offset..]`"
);

/// For each 8-bit mask, the indices of its set bits, packed low first.
const fn rej_uniform_table() -> [u8; 2048] {
    let mut t = [0; 2048];
    let mut m = 0;
    while m < 256 {
        let (mut n, mut i) = (0, 0);
        while i < 8 {
            if (m >> i) & 1 == 1 {
                t[m * 8 + n] = i as u8;
                n += 1;
            }
            i += 1;
        }
        m += 1;
    }
    t
}

pub(super) const MLDSA_REJ_UNIFORM_TABLE: [u8; 2048] = rej_uniform_table();

#[repr(align(32))]
struct Coeffs<const N: usize>([i32; N]);

/// `q^-1 mod 2^32` and `q` in eight lanes each, as s2n-bignum's
/// `mldsa_pointwise_x86` orders them: its accumulating siblings take
/// [`QDATA`]'s opposite order.
const POINTWISE_QDATA: Coeffs<16> = Coeffs([
    58728449, 58728449, 58728449, 58728449, 58728449, 58728449, 58728449, 58728449, 8380417,
    8380417, 8380417, 8380417, 8380417, 8380417, 8380417, 8380417,
]);
