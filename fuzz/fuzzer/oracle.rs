//! The independent oracles of the curves and Ed25519, which share no code
//! with the path rind runs on this tier: the differential tests' own, from
//! `rind/tests/oracle`, over the textbook reference on armv7 and the
//! portable backend.

// Each target uses some of these.
#![allow(dead_code)]

#[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
#[path = "../../rind/src/test/reference.rs"]
pub(crate) mod reference;

#[path = "../../rind/tests/oracle/ed25519.rs"]
pub(crate) mod ed25519;
#[path = "../../rind/tests/oracle/nist.rs"]
mod nist;

#[allow(unused_imports)]
pub(crate) use nist::*;
