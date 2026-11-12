// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-256's Montgomery multiplication and squaring on 64-bit limbs, mod p and
//! mod n, for `p256`: fiat-crypto's, proven correct, whose carry chains a
//! 64-bit target keeps in registers.

use super::fiat_p256 as fp;
use super::fiat_p256_scalar as fs;
use super::p256::{Fe, Fs};

/// `x * y / 2^256 mod p_256`, for `x` and `y` below p.
pub(super) fn fe_mul(x: &Fe, y: &Fe) -> Fe {
    let mut r = Fe([0; 4]);
    fp::fiat_p256_mul(&mut r, x, y);
    r
}

/// `x^2 / 2^256 mod p_256`, for `x` below p.
pub(super) fn fe_sqr(x: &Fe) -> Fe {
    let mut r = Fe([0; 4]);
    fp::fiat_p256_square(&mut r, x);
    r
}

/// `x * y / 2^256 mod n_256`, for `x` and `y` below n.
pub(super) fn fs_mul(x: &Fs, y: &Fs) -> Fs {
    let mut r = Fs([0; 4]);
    fs::fiat_p256_scalar_mul(&mut r, x, y);
    r
}

/// `x^2 / 2^256 mod n_256`, for `x` below n.
pub(super) fn fs_sqr(x: &Fs) -> Fs {
    let mut r = Fs([0; 4]);
    fs::fiat_p256_scalar_square(&mut r, x);
    r
}
