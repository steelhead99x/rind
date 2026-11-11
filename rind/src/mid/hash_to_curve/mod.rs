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
/// [`Debug`] redacts the coordinates. [`PartialEq`] compares them in constant time.
#[derive(Clone, Copy)]
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

impl<const N: usize> core::fmt::Debug for HashedPoint<N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_struct("HashedPoint").finish_non_exhaustive()
    }
}

impl<const N: usize> PartialEq for HashedPoint<N> {
    fn eq(&self, other: &Self) -> bool {
        // `bool`'s `&` does not skip the later comparisons.
        crate::low::ct_equal(&self.x, &other.x)
            & crate::low::ct_equal(&self.y, &other.y)
            & crate::low::ct_equal(&[self.infinity], &[other.infinity])
    }
}

impl<const N: usize> Eq for HashedPoint<N> {}

/// Map both field elements and add the points. The cofactor of each suite is 1.
pub(super) fn hash_to_curve_ro<F: SwuField>(u0: F, u1: F, c: &SwuConstants<F>) -> Affine<F> {
    add_affine(map_to_curve(u0, c), map_to_curve(u1, c), c.a)
}

type ExpandFn = fn(&[u8], &[u8], &mut [u8]) -> Result<(), ExpandError>;

/// `expand_message_xmd` of `L` bytes, then one reduction. The caller holds an [`Entry`].
pub(in crate::mid) fn expand_reduced<T, const L: usize>(
    msg: &[u8],
    dst: &[u8],
    expand: ExpandFn,
    reduce: impl FnOnce(&[u8]) -> T,
) -> Result<T, ExpandError> {
    let mut uniform = [0u8; L];
    expand(msg, dst, &mut uniform)?;
    Ok(reduce(&uniform))
}

/// Widest `L` a suite passes to [`expand_two`]. Two elements fit on the stack.
const MAX_ELEMENT: usize = 128;

/// `expand_message_xmd` of `2L` bytes, split into the two field elements the
/// random-oracle suite maps. The caller holds an [`Entry`].
///
/// `L` is the suite length, at most [`MAX_ELEMENT`]. The bytes stay on the
/// stack: a `Vec` would panic if the allocator refused a buffer derived from
/// the message.
pub(in crate::mid) fn expand_two<const L: usize>(
    msg: &[u8],
    dst: &[u8],
    expand: ExpandFn,
) -> Result<([u8; L], [u8; L]), ExpandError> {
    if L == 0 || L > MAX_ELEMENT {
        return Err(ExpandError::OutputLength);
    }
    let mut uniform = [0u8; MAX_ELEMENT * 2];
    let len = L * 2;
    expand(msg, dst, &mut uniform[..len])?;
    let mut u0 = [0u8; L];
    let mut u1 = [0u8; L];
    u0.copy_from_slice(&uniform[..L]);
    u1.copy_from_slice(&uniform[L..len]);
    Ok((u0, u1))
}
