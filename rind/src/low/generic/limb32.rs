// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The portable public-key arithmetic on 32-bit limbs, for 32-bit targets,
//! armv7 among them, whose 32 by 32-bit product is one instruction where a
//! 64-bit limb's high half would be a library call. wasm32 is one: it
//! multiplies 64-bit values natively, but only to their low half without
//! its `wide-arithmetic` instructions, which stable Rust enables from 1.101.
//! The build script picks the width, as `rind_limb`.
//!
//! Each module here is also [`super::limb64`]'s, over 64-bit limbs.

use fiat_crypto::{
    p256_32 as fiat_p256, p256_scalar_32 as fiat_p256_scalar, p384_32 as fiat_p384,
    p384_scalar_32 as fiat_p384_scalar, p521_32 as fiat_p521,
};

/// One limb.
type Limb = u32;
/// Twice a limb, which holds a product of two and two more limbs.
type Wide = u64;

/// `x`'s limbs, low first, which `buf` holds.
fn limbs<'a, const N: usize>(x: &[u64], buf: &'a mut [Limb; N]) -> &'a [Limb] {
    let buf = &mut buf[..2 * x.len()];
    for (pair, word) in buf.as_chunks_mut::<2>().0.iter_mut().zip(x) {
        *pair = [*word as u32, (*word >> 32) as u32];
    }
    buf
}

/// Joins pairs of `x`'s limbs into the words of `z`, as far as both go.
fn join(x: &[Limb], z: &mut [u64]) {
    for (z, [lo, hi]) in z.iter_mut().zip(x.as_chunks::<2>().0) {
        *z = u64::from(*lo) | u64::from(*hi) << 32;
    }
}

#[path = "mont.rs"]
#[allow(clippy::duplicate_mod, reason = "shared with `limb64`")]
pub(crate) mod mont;
#[path = "p256.rs"]
#[allow(clippy::duplicate_mod, reason = "shared with `limb64`")]
pub(crate) mod p256;
#[path = "p256_mul32.rs"]
mod p256_mul;
#[path = "p384.rs"]
#[allow(clippy::duplicate_mod, reason = "shared with `limb64`")]
pub(crate) mod p384;
#[path = "p384_mul32.rs"]
mod p384_mul;
#[path = "p521.rs"]
#[allow(clippy::duplicate_mod, reason = "shared with `limb64`")]
pub(crate) mod p521;
