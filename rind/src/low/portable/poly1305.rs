// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The portable backend's Poly1305, chosen by `rind_limb` from `build.rs`:
//! 26-bit limbs in `generic::poly1305_32` when that is 32, and 64-bit limbs
//! in `generic::poly1305` when it is 64, including wasm32 with
//! `wide-arithmetic`. x86_64's own backend runs without SSE4.1 and does not
//! use this module. Neither implementation counts its input, so neither
//! limits an AEAD's message length.

#[cfg(all(rind_backend = "portable", not(rind_limb = "32")))]
pub(crate) use crate::low::generic::poly1305::Poly1305;
#[cfg(all(rind_backend = "portable", rind_limb = "32"))]
pub(crate) use crate::low::generic::poly1305_32::Poly1305;
