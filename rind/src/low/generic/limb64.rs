// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The portable public-key arithmetic on 64-bit limbs, for 64-bit targets
//! and wasm32 with its `wide-arithmetic` feature, which form a 128-bit
//! product in one or two multiply instructions, for a quarter of
//! [`super::limb32`]'s products.
//!
//! Each module here is also `limb32`'s, over 32-bit limbs.

use core::mem::MaybeUninit;

use fiat_crypto::{
    p256_64 as fiat_p256, p256_scalar_64 as fiat_p256_scalar, p384_64 as fiat_p384,
    p384_scalar_64 as fiat_p384_scalar, p521_64 as fiat_p521,
};

/// One limb.
type Limb = u64;
/// Twice a limb, which holds a product of two and two more limbs.
type Wide = u128;

/// `x`'s limbs, which are its words, so `_buf` goes unused and unwritten.
fn limbs<'a>(x: &'a [u64], _buf: &mut [MaybeUninit<Limb>]) -> &'a [Limb] {
    x
}

/// Copies `x`'s limbs into the words of `z`, as far as both go.
fn join(x: &[Limb], z: &mut [u64]) {
    let n = x.len().min(z.len());
    z[..n].copy_from_slice(&x[..n]);
}

#[path = "mont.rs"]
#[allow(
    clippy::duplicate_mod,
    clippy::modulo_one,
    clippy::useless_conversion,
    trivial_numeric_casts,
    reason = "shared with `limb32`, whose limbs are narrower than a word"
)]
pub(crate) mod mont;
#[path = "p256.rs"]
#[allow(
    clippy::duplicate_mod,
    clippy::modulo_one,
    clippy::useless_conversion,
    trivial_numeric_casts,
    reason = "shared with `limb32`, whose limbs are narrower than a word"
)]
pub(crate) mod p256;
#[path = "p256_mul64.rs"]
mod p256_mul;
#[path = "p384.rs"]
#[allow(
    clippy::duplicate_mod,
    clippy::modulo_one,
    clippy::useless_conversion,
    trivial_numeric_casts,
    reason = "shared with `limb32`, whose limbs are narrower than a word"
)]
pub(crate) mod p384;
#[path = "p384_mul64.rs"]
mod p384_mul;
#[path = "p521.rs"]
#[allow(
    clippy::duplicate_mod,
    clippy::modulo_one,
    clippy::useless_conversion,
    trivial_numeric_casts,
    reason = "shared with `limb32`, whose limbs are narrower than a word"
)]
pub(crate) mod p521;
