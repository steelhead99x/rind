// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Variable-time operations on a secret that `admin/ct-vartime` must find, so a scan that
//! finds nothing fails, and for the x86_64 backend one under Intel's MXCSR
//! mitigation that it must not. Only that scan builds with `--cfg rind_vartime_planted`.

/// A divide instruction, or on a 32-bit target, a call to the compiler's
/// 64-bit division routine.
fn planted_division(secret: u64, by: u64) -> u64 {
    secret / by
}

/// A call to the compiler's 128-bit division routine, which 32-bit ARM and
/// x86 lack.
fn planted_wide_division(secret: u128, by: u128) -> u128 {
    secret / by
}

/// A floating-point multiply, which is slow for a subnormal operand.
fn planted_float(secret: f64, by: f64) -> f64 {
    secret * by
}

/// A 32x32->64-bit multiply, `umull` on 32-bit ARM, which a Cortex-M3 ends
/// early on small operands. The scan of the `rind_mul16` build, which
/// refuses every long multiply in Poly1305's `blocks` and `finish`, must
/// find it where it refuses them.
fn planted_long_multiply(secret: u32, by: u32) -> u64 {
    u64::from(secret) * u64::from(by)
}

// Nothing calls them, so these keep them in rind's rlib.
#[used]
static DIVISION: fn(u64, u64) -> u64 = planted_division;
#[used]
static WIDE_DIVISION: fn(u128, u128) -> u128 = planted_wide_division;
#[used]
static FLOAT: fn(f64, f64) -> f64 = planted_float;
#[used]
static LONG_MULTIPLY: fn(u32, u32) -> u64 = planted_long_multiply;

#[cfg(rind_backend = "x86_64")]
use core::arch::x86_64::{__m128i, _mm_mul_epu32};

/// A `pmuludq`, which Intel's MXCSR mitigation covers, outside it.
#[cfg(rind_backend = "x86_64")]
#[inline(never)]
fn planted_mcdt(secret: __m128i, by: __m128i) -> __m128i {
    // Safe from Rust 1.87 where SSE2 is enabled, `unsafe` before.
    #[allow(unused_unsafe)]
    // SAFETY: every x86_64 target enables SSE2.
    unsafe {
        _mm_mul_epu32(secret, by)
    }
}

/// The same multiply under the mitigation, which the scan must not report.
#[cfg(rind_backend = "x86_64")]
#[inline(never)]
fn planted_mcdt_mitigated(secret: __m128i, by: __m128i) -> __m128i {
    let _mcdt = super::Mcdt::enter();
    mitigated_mcdt(secret, by)
}

#[cfg(rind_backend = "x86_64")]
#[inline(never)]
fn mitigated_mcdt(secret: __m128i, by: __m128i) -> __m128i {
    #[allow(unused_unsafe)]
    // SAFETY: every x86_64 target enables SSE2.
    unsafe {
        _mm_mul_epu32(secret, by)
    }
}

// The MXCSR scan starts from the symbols rind exports, so these are.
#[cfg(rind_backend = "x86_64")]
#[unsafe(no_mangle)]
#[used]
static RIND_PLANTED_MCDT: fn(__m128i, __m128i) -> __m128i = planted_mcdt;
#[cfg(rind_backend = "x86_64")]
#[unsafe(no_mangle)]
#[used]
static RIND_PLANTED_MCDT_MITIGATED: fn(__m128i, __m128i) -> __m128i = planted_mcdt_mitigated;
