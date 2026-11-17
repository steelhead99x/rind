// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Poly1305 on armv7, on the 26-bit limbs in `generic::poly1305_32`.
//!
//! 32-bit Arm NEON intrinsics are unstable on the toolchain this crate builds
//! with, so this backend does not ship a NEON Poly1305.

pub(crate) use crate::low::generic::poly1305_32::Poly1305;
