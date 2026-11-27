// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::sync::atomic::{AtomicU8, Ordering};

/// Proof that the CPU has the ARMv8 Crypto Extension in AArch32: NEON, AES,
/// PMULL, SHA-1, and SHA-256.
///
/// ARMv8 cores ship the extension as one unit, so one token covers all of it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveCryptoExt(());

impl HaveCryptoExt {
    /// Detects the extension once, then answers from the cached result.
    pub(crate) fn check() -> Option<Self> {
        (features() & CRYPTO_EXT != 0).then_some(Self(()))
    }
}

/// Proof that the CPU has NEON, which many ARMv7 cores without the crypto
/// extension have too.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveNeon(());

impl HaveNeon {
    /// Detects NEON once, then answers from the cached result.
    pub(crate) fn check() -> Option<Self> {
        (features() & NEON != 0).then_some(Self(()))
    }
}

const NEON: u8 = 1 << 0;
const CRYPTO_EXT: u8 = 1 << 1;
const DETECTED: u8 = 1 << 7;

static FEATURES: AtomicU8 = AtomicU8::new(0);

/// The detected features, read from the kernel once. Inlined, so a check is
/// a load and a test, with the first call's detection out of line.
#[inline]
fn features() -> u8 {
    match FEATURES.load(Ordering::Relaxed) {
        0 => detect_once(),
        features => features,
    }
}

#[cold]
#[inline(never)]
fn detect_once() -> u8 {
    let features = detect() | DETECTED;
    FEATURES.store(features, Ordering::Relaxed);
    features
}

/// Reads the features the kernel reports to 32-bit processes, as aws-lc does
/// (`crypto/fipsmodule/cpucap/cpu_arm_linux.c`). A kernel that omits
/// `AT_HWCAP2` gets the portable code: aws-lc parses `/proc/cpuinfo` for those
/// early ARMv8 Android kernels instead, which rind does not.
#[cfg(any(target_os = "linux", target_os = "android"))]
fn detect() -> u8 {
    // Bits from the kernel's arch/arm/include/uapi/asm/hwcap.h.
    const HWCAP_NEON: libc::c_ulong = 1 << 12;
    const HWCAP2_AES: libc::c_ulong = 1 << 0;
    const HWCAP2_PMULL: libc::c_ulong = 1 << 1;
    const HWCAP2_SHA1: libc::c_ulong = 1 << 2;
    const HWCAP2_SHA2: libc::c_ulong = 1 << 3;

    // SAFETY: `getauxval` only reads the process's auxiliary vector, and
    // returns 0 for an entry it lacks.
    let (hwcap, hwcap2) = unsafe {
        (
            libc::getauxval(libc::AT_HWCAP),
            libc::getauxval(libc::AT_HWCAP2),
        )
    };
    let neon = test_toggle("neon", hwcap & HWCAP_NEON != 0);
    let crypto_ext = neon
        && test_toggle("aes", hwcap2 & HWCAP2_AES != 0)
        && test_toggle("pmull", hwcap2 & HWCAP2_PMULL != 0)
        && test_toggle("sha1", hwcap2 & HWCAP2_SHA1 != 0)
        && test_toggle("sha2", hwcap2 & HWCAP2_SHA2 != 0);
    (if neon { NEON } else { 0 }) | (if crypto_ext { CRYPTO_EXT } else { 0 })
}

/// Other operating systems report the features differently, so they get the
/// portable code.
#[cfg(not(any(target_os = "linux", target_os = "android")))]
fn detect() -> u8 {
    0
}

/// `detected`, unless `RIND_CPU_DISABLE_<id>` denies it, as on x86_64, so a
/// CPU with the extension also tests the portable code.
#[cfg(any(target_os = "linux", target_os = "android"))]
fn test_toggle(id: &str, detected: bool) -> bool {
    detected && !crate::low::cpu_denied(id)
}

/// armv7 has no data-independent timing mode to enable.
pub(crate) fn enter_cpu_state() -> u32 {
    0
}

/// Nothing to restore, since `enter_cpu_state` changed nothing.
pub(crate) fn leave_cpu_state(_old: u32) {}

/// Effectively memset(ptr, 0, len), but not visible to optimiser
///
/// # Safety:
/// There must be `len` writable bytes at `ptr`; with no alignment
/// requirement.
pub(in crate::low) unsafe fn zero_bytes(ptr: *mut u8, len: usize) {
    // ARMv7 Linux and Android allow unaligned word stores, so the by-16 loop
    // needs no aligned start.
    //
    // SAFETY: inline assembly. all written registers are listed as clobbers.
    unsafe {
        core::arch::asm!(
            // by-16 loop
            "   2:  subs {len}, {len}, #16",
            "       blo 3f",
            "       str {zero}, [{ptr}], #4",
            "       str {zero}, [{ptr}], #4",
            "       str {zero}, [{ptr}], #4",
            "       str {zero}, [{ptr}], #4",
            "       b 2b",
            // by-4 loop, over the 0 to 15 bytes left
            "   3:  add {len}, {len}, #16",
            "   4:  subs {len}, {len}, #4",
            "       blo 5f",
            "       str {zero}, [{ptr}], #4",
            "       b 4b",
            // by-1 loop, over the 0 to 3 bytes left
            "   5:  add {len}, {len}, #4",
            "   6:  subs {len}, {len}, #1",
            "       blo 7f",
            "       strb {zero}, [{ptr}], #1",
            "       b 6b",
            "   7:",

            ptr = inout(reg) ptr => _,
            len = inout(reg) len => _,
            zero = in(reg) 0u32,
            options(nostack),
        )
    }
}

unsafe extern "C" {
    #[link_name = aws_lc_symbol!("ct_compare_16")]
    fn compare_16(a: *const [u8; 16], b: *const [u8; 16]) -> u32;

    #[link_name = aws_lc_symbol!("ct_compare_bytes")]
    fn compare_bytes(a: *const u8, b: *const u8, len: usize) -> u32;
}

// The compares are A32 on every target, Thumb-2 ones included, so
// `proofs/hol-light/armv7/` proves the one copy each target runs: a Thumb-2
// caller reaches them through the linker's BLX, and their return interworks.
// `compare_16` reads each block as four unaligned words; `compare_bytes`
// ORs together the XOR of each pair of bytes, so its result is below 256.
core::arch::global_asm!(
    ".text",
    ".code 32",
    ".p2align 2",
    ".globl {compare_16}",
    ".hidden {compare_16}",
    ".type {compare_16}, %function",
    "{compare_16}:",
    "   ldr r2, [r0]",
    "   ldr r3, [r1]",
    "   eor r12, r2, r3",
    "   ldr r2, [r0, #4]",
    "   ldr r3, [r1, #4]",
    "   eor r2, r2, r3",
    "   orr r12, r12, r2",
    "   ldr r2, [r0, #8]",
    "   ldr r3, [r1, #8]",
    "   eor r2, r2, r3",
    "   orr r12, r12, r2",
    "   ldr r2, [r0, #12]",
    "   ldr r3, [r1, #12]",
    "   eor r2, r2, r3",
    "   orr r0, r12, r2",
    "   bx lr",
    ".size {compare_16}, .-{compare_16}",
    "",
    ".p2align 2",
    ".globl {compare_bytes}",
    ".hidden {compare_bytes}",
    ".type {compare_bytes}, %function",
    "{compare_bytes}:",
    "   push {{r4, lr}}",
    "   mov r3, #0",
    "2: subs r2, r2, #1",
    "   blo 3f",
    "   ldrb r12, [r0], #1",
    "   ldrb r4, [r1], #1",
    "   eor r12, r12, r4",
    "   orr r3, r3, r12",
    "   b 2b",
    "3: mov r0, r3",
    "   pop {{r4, pc}}",
    ".size {compare_bytes}, .-{compare_bytes}",
    compare_16 = sym compare_16,
    compare_bytes = sym compare_bytes,
);

/// Compares the first `min(a.len(), b.len())` bytes of `a` and `b`, reading
/// every one of them whatever their values.
///
/// Returns zero if they are equal, otherwise non-zero.
pub(in crate::low) fn ct_compare_bytes(a: &[u8], b: &[u8]) -> u8 {
    let len = a.len().min(b.len());
    // SAFETY: reads `len` bytes from `a` and `b`, which both hold.
    let acc = unsafe { asm_call!(unsafe extern "C" compare_bytes(a.as_ptr(), b.as_ptr(), len)) };
    acc as u8
}

/// Compares two 16-byte blocks, such as AEAD tags, in constant time.
///
/// Returns zero if `a == b`, otherwise non-zero.
pub(in crate::low) fn ct_compare_16(a: &[u8; 16], b: &[u8; 16]) -> usize {
    // SAFETY: reads the 16 bytes of `a` and `b`.
    unsafe { asm_call!(unsafe extern "C" compare_16(a, b)) as usize }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::abi::call;

    #[test]
    fn abi() {
        let mut bytes = [0xffu8; 100];
        // SAFETY: `bytes` is 100 writable bytes.
        unsafe { call!(unsafe zero_bytes, bytes.as_mut_ptr(), 100) };
        assert_eq!(bytes, [0; 100]);
        let (a, b) = ([1u8; 37], [2u8; 37]);
        assert_ne!(ct_compare_bytes(&a, &b), 0);
        assert_eq!(ct_compare_bytes(&a, &a), 0);
        assert_ne!(ct_compare_16(&[1; 16], &[2; 16]), 0);
        assert_eq!(ct_compare_16(&[1; 16], &[1; 16]), 0);
    }

    // CI runs the armv7 suite on a CPU model with NEON and the extension and
    // one without either, and names which, so neither run silently tests only
    // one path. Valgrind sees NEON but hides the extension.
    #[test]
    fn detects_the_expected_cpu() {
        if let Some(expected) = std::env::var_os("RIND_TEST_ARM_NEON") {
            assert_eq!(HaveNeon::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_ARM_CRYPTO_EXT") {
            assert_eq!(HaveCryptoExt::check().is_some(), expected == "1");
        }
    }
}
