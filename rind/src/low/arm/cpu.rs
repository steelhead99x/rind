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

#[cfg(all(
    not(any(debug_assertions, rind_cpu_disable)),
    any(target_os = "linux", target_os = "android")
))]
fn test_toggle(_id: &str, detected: bool) -> bool {
    detected
}

/// Lets a debug build, or a release one with `--cfg rind_cpu_disable`, deny a
/// feature with `RIND_CPU_DISABLE_<id>`, as on x86_64, so a CPU with the
/// extension also tests the portable code.
#[cfg(all(
    any(debug_assertions, rind_cpu_disable),
    any(target_os = "linux", target_os = "android")
))]
fn test_toggle(id: &str, detected: bool) -> bool {
    if std::env::var(format!("RIND_CPU_DISABLE_{id}")).is_ok() {
        println!("DEBUG: denying cpuid {id:?}");
        false
    } else {
        detected
    }
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

/// Compares the first `min(a.len(), b.len())` bytes of `a` and `b`, reading
/// every one of them whatever their values.
///
/// Returns zero if they are equal, otherwise non-zero.
pub(in crate::low) fn ct_compare_bytes(a: &[u8], b: &[u8]) -> u8 {
    let (len, a, b) = (a.len().min(b.len()), a.as_ptr(), b.as_ptr());
    let mut acc = 0u32;
    // SAFETY: inline assembly. all written registers are listed as clobbers.
    unsafe {
        core::arch::asm!(
            "   2:  subs {len}, {len}, #1",
            "       blo 3f",
            "       ldrb {tmpa}, [{a}], #1",
            "       ldrb {tmpb}, [{b}], #1",
            "       eor {tmpa}, {tmpa}, {tmpb}",
            "       orr {acc}, {acc}, {tmpa}",
            "       b 2b",
            "   3:",

            a = inout(reg) a => _,
            b = inout(reg) b => _,
            len = inout(reg) len => _,
            acc = inout(reg) acc,
            tmpa = out(reg) _,
            tmpb = out(reg) _,
            options(readonly, nostack),
        )
    }
    acc as u8
}

/// Compares two 16-byte blocks, such as AEAD tags, in constant time.
///
/// Returns zero if `a == b`, otherwise non-zero. The words are combined in
/// assembly so the compiler cannot split the test into early exits.
pub(in crate::low) fn ct_compare_16(a: &[u8; 16], b: &[u8; 16]) -> usize {
    let (a, b) = (u128::from_ne_bytes(*a), u128::from_ne_bytes(*b));
    let mut diff = a as u32;
    // SAFETY: register-only arithmetic.
    unsafe {
        core::arch::asm!(
            "eor {diff}, {diff}, {b0}",
            "eor {a1}, {a1}, {b1}",
            "eor {a2}, {a2}, {b2}",
            "eor {a3}, {a3}, {b3}",
            "orr {diff}, {diff}, {a1}",
            "orr {a2}, {a2}, {a3}",
            "orr {diff}, {diff}, {a2}",
            diff = inout(reg) diff,
            a1 = inout(reg) (a >> 32) as u32 => _,
            a2 = inout(reg) (a >> 64) as u32 => _,
            a3 = inout(reg) (a >> 96) as u32 => _,
            b0 = in(reg) b as u32,
            b1 = in(reg) (b >> 32) as u32,
            b2 = in(reg) (b >> 64) as u32,
            b3 = in(reg) (b >> 96) as u32,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    diff as usize
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
        assert_ne!(call!(ct_compare_bytes, &a, &b), 0);
        assert_ne!(call!(ct_compare_16, &[1; 16], &[2; 16]), 0);
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
