// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on aarch64: the NEON fill in
//! [`super::argon2_neon`], with the kernel [`super::argon2_neon::Fill::select`]
//! picks for this core.

use crate::low::generic::argon2::Argon2Block;

/// Argon2's compression function, as `low::generic::argon2` defines it.
pub(crate) fn argon2_compress(x: &Argon2Block, y: &Argon2Block, out: &mut Argon2Block, xor: bool) {
    super::argon2_neon::compress_selected(x, y, out, xor);
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::super::argon2_neon::{Fill, compress};
    use super::super::cpu::HaveSha3;
    use crate::low::generic::argon2::assert_matches_portable;

    /// What dispatch runs matches the portable permutation.
    #[test]
    fn dispatch_matches_portable() {
        assert_matches_portable(super::argon2_compress);
    }

    /// Each kernel dispatch can pick matches the portable permutation, forced
    /// whichever one this core would pick. SHA3's needs a CPU with SHA3.
    #[test]
    fn each_fill_matches_portable() {
        for fill in [Fill::Neon, Fill::Sha3] {
            if matches!(fill, Fill::Sha3) && HaveSha3::check().is_none() {
                continue;
            }
            assert_matches_portable(|x, y, out, xor| compress(fill, out, x, y, xor));
        }
    }
}
