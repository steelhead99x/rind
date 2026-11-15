// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The portable backend's Poly1305: 26-bit limbs in `generic::poly1305_32`
//! when the pointer is 32 bits or `rind_limb` is 32, and 64-bit limbs in
//! `generic::poly1305` otherwise, as x86_64 runs without SSE4.1. Neither
//! counts its input, so neither limits an AEAD's message length.

#[cfg(all(
    rind_backend = "portable",
    target_pointer_width = "64",
    not(rind_limb = "32")
))]
pub(crate) use crate::low::generic::poly1305::Poly1305;
#[cfg(all(
    rind_backend = "portable",
    any(target_pointer_width = "32", rind_limb = "32")
))]
pub(crate) use crate::low::generic::poly1305_32::Poly1305;
