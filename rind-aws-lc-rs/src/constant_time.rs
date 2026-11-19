//! Constant-time comparison.

// With `fips`, the comparison runs in the module.
#[cfg(feature = "fips")]
use rind_fips as rind;

use crate::error;

/// Checks in constant time that `a` and `b` hold the same bytes.
pub fn verify_slices_are_equal(a: &[u8], b: &[u8]) -> Result<(), error::Unspecified> {
    rind::constant_time::verify(a, b).map_err(error::unspecified)
}
