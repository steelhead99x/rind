// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Intel's MXCSR mitigation where it has nothing to do: see `mcdt.rs`.

/// Holds nothing.
#[must_use]
pub(crate) struct Mcdt;

impl Mcdt {
    /// Does nothing.
    #[inline]
    pub(crate) fn enter() -> Self {
        Self
    }
}
