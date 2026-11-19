// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on aarch64.
//!
//! The NEON fill of [`super::argon2_neon`]: SHA3's `xar` fill on Apple cores
//! that have it, and the plain NEON fill with its scalar rider everywhere
//! else. Both measured faster than the portable permutation on every core
//! tried (see quest/m4/protocols/argon2-simd.md for the numbers); the SHA3
//! fill loses to the portable permutation on a Neoverse-N2, so only Apple
//! takes it.

use crate::low::generic::argon2::Argon2Block;

/// Argon2's compression function, as `low::generic::argon2` defines it.
pub(crate) fn argon2_compress(x: &Argon2Block, y: &Argon2Block, out: &mut Argon2Block, xor: bool) {
    super::argon2_neon::compress_selected(x, y, out, xor);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dispatch_matches_portable() {
        crate::low::generic::argon2::assert_matches_portable(argon2_compress);
    }
}
