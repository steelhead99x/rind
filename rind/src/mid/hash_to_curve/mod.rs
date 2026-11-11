// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Hashing bytes to P-256, P-384, and P-521.
//!
//! The suites are RFC 9380's `P256_XMD:SHA-256_SSWU_RO_`,
//! `P384_XMD:SHA-384_SSWU_RO_`, and `P521_XMD:SHA-512_SSWU_RO_`:
//! `expand_message_xmd` over rind's SHA-2, `hash_to_field`, and the simplified
//! SWU map. There is no public API. [`expand`] and [`swu`] are the shared
//! pieces; each curve module exposes `hash_to_curve`, `hash_to_field`, and
//! `hash_to_scalar` for the OPRF and FROST.
//!
//! The map and `sqrt_ratio` are the straight-line procedures in RFC 9380
//! Appendix F.2 and F.2.1.2. They call the field operations the NIST curves
//! already run, so the correctness argument is the same as those curves':
//! s2n-bignum's verified routines on x86_64 and aarch64, and fiat-crypto's
//! proven field arithmetic on armv7 and the portable backend. See [`swu`].
//!
//! `_NU_` encodings and edwards25519's Elligator 2 map are not implemented.

mod expand;
mod swu;

pub(crate) use expand::ExpandError;
pub(in crate::mid) use expand::{expand_sha256, expand_sha384, expand_sha512};
pub(in crate::mid) use swu::{Affine, SwuConstants, SwuField, add_affine, map_to_curve, reduce_be};

/// A point produced by `hash_to_curve`, in big-endian coordinates.
///
/// `infinity` is 1 when the point is the identity, and then `x` and `y` are
/// zero. The flag is a secret: select on it, do not branch.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct HashedPoint<const N: usize> {
    /// The affine x coordinate, or zero at infinity.
    pub(crate) x: [u8; N],
    /// The affine y coordinate, or zero at infinity.
    pub(crate) y: [u8; N],
    /// 1 at the point at infinity, otherwise 0.
    pub(crate) infinity: u8,
}

#[cfg(test)]
mod tests;

/// Map both field elements and add the points. The cofactor of each suite is 1.
pub(super) fn hash_to_curve_ro<F: SwuField>(u0: F, u1: F, c: &SwuConstants<F>) -> Affine<F> {
    add_affine(map_to_curve(u0, c), map_to_curve(u1, c), c.a)
}
