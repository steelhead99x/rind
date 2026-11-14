// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Unpublished ACVP module wrapper.
//!
//! [`serve`] speaks the byte protocol of BoringSSL's and aws-lc's `acvptool`
//! on stdin and stdout. `acvptool` keeps ACVP's sessions and JSON; this
//! process only runs the per-algorithm operations. It does not keep the
//! ACVP session.

mod ops;
mod protocol;

pub use ops::{Reply, Wrapper};
pub use protocol::serve;
