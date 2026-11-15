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

/// A `mul` of two raw 16-bit halves, with bit 31 clear. ARM7TDMI and XScale
/// end that multiply early. The ARMv5TE scan must reject it.
#[inline(never)]
fn planted_raw_half_multiply(secret: u32, by: u32) -> u32 {
    (secret & 0xffff).wrapping_mul(by & 0xffff)
}

/// A `mul` by five. The factor is hidden so the compiler does not turn it
/// into a shift and an add, which would not be the multiply the scan looks
/// for. The ARMv5TE scan must reject it: neither operand is an `orr` of
/// `#0x80000000`.
#[inline(never)]
fn planted_multiply_by_five(secret: u32) -> u32 {
    let factor = core::hint::black_box(5u32);
    core::hint::black_box(secret).wrapping_mul(factor)
}

/// The branch RV32I can emit for a select on a secret bit. The RV32I scan
/// must reject it. The instructions are written out so the compiler cannot
/// turn them back into a shift.
#[cfg(target_arch = "riscv32")]
#[inline(never)]
fn planted_secret_branch(mut secret: u32, addend: u32) -> u32 {
    let mut bit = 0u32;
    // SAFETY: the instructions read only the named registers and write
    // `secret` and `bit`. There is no memory operand.
    unsafe {
        core::arch::asm!(
            "andi {bit}, {secret}, 1",
            "beqz {bit}, 2f",
            "mv {secret}, {addend}",
            "2:",
            bit = out(reg) bit,
            secret = inout(reg) secret,
            addend = in(reg) addend,
            options(nomem, nostack),
        );
    }
    let _ = bit;
    secret
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
#[used]
static RAW_HALF_MULTIPLY: fn(u32, u32) -> u32 = planted_raw_half_multiply;
#[used]
static MULTIPLY_BY_FIVE: fn(u32) -> u32 = planted_multiply_by_five;
#[cfg(target_arch = "riscv32")]
#[used]
static SECRET_BRANCH: fn(u32, u32) -> u32 = planted_secret_branch;

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
