// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::sync::atomic::{AtomicU8, Ordering};

pub(crate) fn enter_cpu_state() -> u32 {
    dit::maybe_enable()
}

pub(crate) fn leave_cpu_state(old: u32) {
    dit::maybe_disable(old);
}

/// Effectively memset(ptr, 0, len), but not visible to optimiser
///
/// # Safety:
/// There must be `len` writable bytes at `ptr`; with no alignment
/// requirement.
pub(in crate::low) unsafe fn zero_bytes(ptr: *mut u8, len: usize) {
    // SAFETY: inline assembly.
    unsafe {
        core::arch::asm!(
            "       eor {zero}.16b, {zero}.16b, {zero}.16b",
            // by-16 loop
            "   2:  cmp {len}, #16",
            "       blt 3f",
            "       st1 {{{zero}.16b}}, [{ptr}]",
            "       add {ptr}, {ptr}, #16",
            "       sub {len}, {len}, #16",
            "       b 2b",
            // by-8 loop
            "   3:  cmp {len}, #8",
            "       blt 4f",
            "       str xzr, [{ptr}], #8",
            "       sub {len}, {len}, #8",
            "       b 3b",
            // by-1 loop
            "   4:  subs {len}, {len}, #1",
            "       blt 5f",
            "       strb wzr, [{ptr}], #1",
            "       b 4b",
            "   5:  ",

            ptr = inout(reg) ptr => _,
            len = inout(reg) len => _,

            // clobbers
            zero = out(vreg) _,
        )
    }
}

/// Compares the first `min(a.len(), b.len())` bytes of `a` and `b`, reading
/// every one of them whatever their values.
///
/// Returns zero if they are equal, otherwise non-zero.
#[inline(never)]
pub(in crate::low) fn ct_compare_bytes(a: &[u8], b: &[u8]) -> u8 {
    let (len, a, b) = (a.len().min(b.len()), a.as_ptr(), b.as_ptr());
    let acc: u64;
    // SAFETY: reads `len` bytes from `a` and `b`, which both hold.
    // Its registers are fixed, and it is never inlined, so its proof in
    // `proofs/hol-light/aarch64/ct_compare_bytes.ml` is of one copy.
    unsafe {
        core::arch::asm!(
            "   2: cmp  x2, 0",
            "      beq  3f",
            "      ldrb w4, [x0]",
            "      ldrb w5, [x1]",
            "      eor  w4, w4, w5",
            "      orr  w3, w3, w4",
            "      add  x0, x0, 1",
            "      add  x1, x1, 1",
            "      sub  x2, x2, 1",
            "      b    2b",
            "   3:  ",
            inout("x0") a => _,
            inout("x1") b => _,
            inout("x2") len => _,
            inout("x3") 0u64 => acc,
            out("x4") _,
            out("x5") _,
            options(nostack, readonly),
        );
    }
    acc as u8
}

/// Compares two 16-byte blocks, such as AEAD tags, in constant time.
///
/// Returns zero if `a == b`, otherwise non-zero. The words are combined in
/// assembly so the compiler cannot split the test into early exits.
#[inline(never)]
pub(in crate::low) fn ct_compare_16(a: &[u8; 16], b: &[u8; 16]) -> usize {
    let (a, b) = (u128::from_ne_bytes(*a), u128::from_ne_bytes(*b));
    let diff: u64;
    // SAFETY: register-only arithmetic, proven in
    // `proofs/hol-light/aarch64/ct_compare_16.ml`.
    unsafe {
        core::arch::asm!(
            "eor x0, x0, x2",
            "eor x1, x1, x3",
            "orr x0, x0, x1",
            inout("x0") a as u64 => diff,
            inout("x1") (a >> 64) as u64 => _,
            in("x2") b as u64,
            in("x3") (b >> 64) as u64,
            options(pure, nomem, nostack, preserves_flags),
        );
    }
    diff as usize
}

/// Proof that the CPU has the crypto extension: AES, PMULL, SHA-1, and
/// SHA-256.
///
/// Cores without it (such as the Raspberry Pi 4's Cortex-A72) lack all of it,
/// so one token covers it.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveCryptoExt(());

impl HaveCryptoExt {
    /// Detects the extension once, then answers from the cached result.
    pub(crate) fn check() -> Option<Self> {
        has(CRYPTO_EXT).then_some(Self(()))
    }
}

/// Token type reflecting the check for the SHA3 CPU feature
///
/// A value of this type is proof that the CPU dynamic feature check has happened.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSha3(());

impl HaveSha3 {
    pub(crate) fn check() -> Option<Self> {
        has(SHA3).then_some(Self(()))
    }

    /// The token where Keccak-f runs on the SHA3 instructions: only on Apple
    /// targets, whose cores run them on every SIMD unit. Other cores, such as
    /// Neoverse N2, run them on fewer, so scalar Keccak-f measured twice as
    /// fast there; mlkem-native and verified-garbage choose the same way, by
    /// target, so Linux on Apple's cores runs scalar code too.
    pub(crate) fn check_keccak() -> Option<Self> {
        if cfg!(target_vendor = "apple") {
            Self::check()
        } else {
            None
        }
    }
}

/// Proof that the CPU has SVE2, which pyca/verified-garbage's fastest
/// ChaCha20-Poly1305 uses, as Armv9 cores such as Neoverse N2 and V2 and the
/// Cortex-A710 and X2 on have, and Apple's do not.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSve2(());

impl HaveSve2 {
    pub(crate) fn check() -> Option<Self> {
        has(SVE2).then_some(Self(()))
    }
}

const CRYPTO_EXT: u8 = 1 << 1;
const SHA3: u8 = 1 << 2;
const DIT: u8 = 1 << 3;
#[cfg(target_vendor = "apple")]
const SB: u8 = 1 << 4;
const SVE2: u8 = 1 << 5;
const DETECTED: u8 = 1 << 7;

/// Those the target enables at compile time, which every CPU that runs the
/// binary has. Rust's `aes` covers PMULL, and its `sha2` SHA-1.
const ENABLED: u8 = (if cfg!(all(target_feature = "aes", target_feature = "sha2")) {
    CRYPTO_EXT
} else {
    0
}) | (if cfg!(target_feature = "sha3") {
    SHA3
} else {
    0
}) | (if cfg!(target_feature = "sve2") {
    SVE2
} else {
    0
});

/// Whether the CPU has the feature `wanted`.
///
/// True at compile time for a feature the target enables (`cpu_enabled`):
/// Apple's targets, which enable the crypto extension and SHA3, carry no
/// table-free AES. A build that can deny a feature still asks.
#[inline]
fn has(wanted: u8) -> bool {
    use super::super::{CPU_DENIABLE, cpu_enabled};
    cpu_enabled(CPU_DENIABLE, u32::from(ENABLED), u32::from(wanted))
        || features() & wanted == wanted
}

static FEATURES: AtomicU8 = AtomicU8::new(0);

/// The detected features, read once. Inlined, so a check is a load and a
/// test, with the first call's detection out of line.
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

fn detect() -> u8 {
    // `std` asks the OS, which alone may read the CPU's ID registers. Without
    // one there is no portable way to ask, so a target with no OS runs what
    // it enables at compile time, as `std` does on an OS it cannot ask.
    #[cfg(rind_std)]
    use std::arch::is_aarch64_feature_detected as detected;
    #[cfg(not(rind_std))]
    macro_rules! detected {
        // Rust's `aes` target feature covers PMULL too.
        ("pmull") => {
            cfg!(target_feature = "aes")
        };
        ($feature:tt) => {
            cfg!(target_feature = $feature)
        };
    }

    let crypto_ext = test_toggle("aes", detected!("aes"))
        && test_toggle("pmull", detected!("pmull"))
        // Rust's `sha2` covers the SHA-1 instructions too.
        && test_toggle("sha2", detected!("sha2"));
    let sha3 = test_toggle("sha3", detected!("sha3"));
    let sve2 = test_toggle("sve2", detected!("sve2"));
    let dit = test_toggle("dit", detected!("dit"));
    let features = (if crypto_ext { CRYPTO_EXT } else { 0 })
        | (if sha3 { SHA3 } else { 0 })
        | (if sve2 { SVE2 } else { 0 })
        | (if dit { DIT } else { 0 });
    #[cfg(target_vendor = "apple")]
    let features = features
        | if test_toggle("sb", detected!("sb")) {
            SB
        } else {
            0
        };
    features
}

// Set on every core whose OS reports it, which a hypervisor, Windows, or a
// BSD may not (PLATFORMS.md): Arm says some cores with DIT, such as
// Neoverse V1, may run the instructions it covers in data-dependent time
// without it, and strongly recommends that software set it (KA005181,
// https://developer.arm.com/documentation/ka005181/1-0/). On
// Apple's cores from the M3 it also turns off the data memory-dependent
// prefetcher that GoFetch reads secrets through.
mod dit {
    pub(super) fn maybe_enable() -> u32 {
        if super::features() & super::DIT != 0 {
            // SAFETY: in this branch, we verified `dit` cpu feature is supported
            match unsafe { read() } {
                0 => {
                    // SAFETY: in this branch, we verified `dit` cpu feature is supported
                    unsafe {
                        write(1);
                    };
                    1
                }
                _ => 0,
            }
        } else {
            0
        }
    }

    pub(super) fn maybe_disable(we_enabled: u32) {
        if we_enabled > 0 {
            // SAFETY: `we_enabled > 0` implies `dit` cpu feature was supported earlier
            unsafe { write(0) }
        }
    }

    #[target_feature(enable = "dit")]
    pub(super) fn read() -> u32 {
        let mut out: u64;
        // SAFETY: `mrs _, DIT` is defined only if `dit` cpu feature is supported
        unsafe {
            core::arch::asm!(
                "mrs {r}, DIT",
                r = out(reg) out,
            );
        }

        const DIT: u64 = 0x01000000;
        (out & DIT == DIT) as u32
    }

    #[target_feature(enable = "dit")]
    pub(super) fn write(on: u32) {
        if on > 0 {
            // SAFETY: `msr DIT, _` is defined only if `dit` cpu feature is supported
            unsafe { core::arch::asm!("msr DIT, #1") }
            // Arm requires no barrier after a PSTATE write, but Apple asks
            // for a speculation barrier after setting DIT, so that nothing
            // after it runs speculatively without DIT.
            #[cfg(target_vendor = "apple")]
            if super::features() & super::SB != 0 {
                // SAFETY: in this branch, we verified `sb` cpu feature is supported
                unsafe { speculation_barrier() }
            } else {
                // SAFETY: Armv8.0 barriers, Apple's choice for cores without `sb`.
                unsafe { core::arch::asm!("dsb nsh", "isb sy", options(nostack, preserves_flags)) }
            }
        } else {
            // SAFETY: `msr DIT, _` is defined only if `dit` cpu feature is supported
            unsafe { core::arch::asm!("msr DIT, #0") }
        }
    }

    /// Runs nothing after it speculatively until everything before it completes.
    #[cfg(target_vendor = "apple")]
    #[target_feature(enable = "sb")]
    pub(super) fn speculation_barrier() {
        // SAFETY: `sb` is defined only if `sb` cpu feature is supported
        unsafe { core::arch::asm!("sb", options(nostack, preserves_flags)) }
    }
}

/// `detected`, unless `RIND_CPU_DISABLE_<id>` denies it, so a CPU with the
/// crypto extension also tests the code for one without.
fn test_toggle(id: &str, detected: bool) -> bool {
    detected && !crate::low::cpu_denied(id)
}

/// Read-only prefetch hint.
pub(in crate::low) fn prefetch_ro<T>(ptr: *const T) {
    // SAFETY: inline assembly
    unsafe {
        core::arch::asm!(
            "prfm pldl1strm, [{ptr}]",
            ptr = in(reg) ptr,
            options(readonly, nostack)
        );
    }
}

/// The first CPU feature the FIPS module requires that this CPU lacks.
///
/// The module requires the crypto extension, which every core it is tested
/// on has, so its vpaes and NEON GHASH paths, which no tested core runs,
/// need no ACVP run of their own.
#[cfg(rind_fips)]
pub(crate) fn missing_cpu_feature() -> Option<&'static str> {
    (features() & CRYPTO_EXT == 0).then_some("aes, pmull, and sha2")
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
        call!(prefetch_ro::<u8>, bytes.as_ptr());
        if std::arch::is_aarch64_feature_detected!("dit") {
            // SAFETY: the CPU has DIT, which this leaves as it found it.
            unsafe {
                let on = call!(unsafe dit::read);
                call!(unsafe dit::write, on);
            }
        }
        #[cfg(target_vendor = "apple")]
        if std::arch::is_aarch64_feature_detected!("sb") {
            // SAFETY: the CPU has SB.
            unsafe { call!(unsafe dit::speculation_barrier) };
        }
        let (a, b) = ([1u8; 37], [2u8; 37]);
        assert_ne!(call!(ct_compare_bytes, &a, &b), 0);
        assert_ne!(call!(ct_compare_16, &[1; 16], &[2; 16]), 0);
    }

    /// Whether std detects every feature named, less those `RIND_CPU_DISABLE_<id>`
    /// denies.
    macro_rules! available {
        ($($name:tt),+) => {
            true $(&& std::arch::is_aarch64_feature_detected!($name) && !crate::low::cpu_denied($name))+
        };
    }

    // Each check names the features its kernels need, which the OS reports
    // independently of the bits `detect` packs them into.
    #[test]
    fn checks_need_their_features() {
        assert_eq!(
            HaveCryptoExt::check().is_some(),
            available!("aes", "pmull", "sha2")
        );
        assert_eq!(HaveSha3::check().is_some(), available!("sha3"));
        assert_eq!(
            HaveSha3::check_keccak().is_some(),
            cfg!(target_vendor = "apple") && available!("sha3")
        );
        assert_eq!(HaveSve2::check().is_some(), available!("sve2"));
        #[cfg(target_vendor = "apple")]
        assert_eq!(features() & SB != 0, available!("sb"));
    }

    // CI runs the aarch64 suite on a CPU with the crypto extension, then
    // again with it denied, and names which, so neither run silently tests
    // only one path. Under valgrind, which hides SHA3, it names that too.
    #[test]
    fn detects_the_expected_cpu() {
        if let Some(expected) = std::env::var_os("RIND_TEST_ARM_CRYPTO_EXT") {
            assert_eq!(HaveCryptoExt::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_ARM_SHA3") {
            assert_eq!(HaveSha3::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_ARM_SVE2") {
            assert_eq!(HaveSve2::check().is_some(), expected == "1");
        }
    }

    // A core that runs `mrs DIT` has DIT, whatever the OS reports, so a child
    // process runs it, on a Unix OS, which reports the illegal instruction
    // as a signal. A hypervisor may hide DIT, as GitHub's arm64 runners'
    // does, but no OS reports it on a core without it, and macOS reports it
    // on every core with it.
    #[cfg(unix)]
    #[test]
    #[cfg_attr(
        feature = "__ctgrind",
        ignore = "valgrind hides DIT from the test but not from its child"
    )]
    fn enables_dit_whenever_the_os_reports_it() {
        let has_dit = child_reads_dit();
        let reported = std::arch::is_aarch64_feature_detected!("dit");
        assert!(has_dit || !reported, "the OS reports DIT the core lacks");
        #[cfg(target_vendor = "apple")]
        assert_eq!(reported, has_dit);

        let expected = test_toggle("dit", reported);
        assert_eq!(features() & DIT != 0, expected);
        // A DIT the OS hides or the caller denies is left alone.
        if has_dit && !expected {
            // SAFETY: this core has DIT, though rind may not set it.
            unsafe { dit::write(0) };
            drop(crate::low::Entry::new_secret());
            let _held = crate::cpu::Dit::hold();
            // SAFETY: as above.
            assert_eq!(unsafe { dit::read() }, 0);
        }
        if expected {
            // SAFETY: this core has DIT. Cleared, so only an `Entry` can set
            // it.
            unsafe { dit::write(0) };
            let outer = crate::low::Entry::new_secret();
            // SAFETY: as above.
            assert_eq!(unsafe { dit::read() }, expected as u32);
            // A nested `Entry` leaves DIT to the outer one.
            drop(crate::low::Entry::new_secret());
            // SAFETY: as above.
            assert_eq!(unsafe { dit::read() }, expected as u32);
            drop(outer);
            // SAFETY: as above.
            assert_eq!(unsafe { dit::read() }, 0);
        }
    }

    #[test]
    fn dit_hold_keeps_dit_on_across_calls() {
        if features() & DIT == 0 {
            // Nothing to hold, and nothing to read DIT with.
            drop(crate::cpu::Dit::hold());
            return;
        }
        // SAFETY: this core has DIT. Cleared, so only the guard can set it.
        unsafe { dit::write(0) };
        let first = crate::cpu::Dit::hold();
        // A call under the guard, and a nested guard, leave DIT to it.
        drop(crate::low::Entry::new_secret());
        drop(crate::cpu::Dit::hold());
        // SAFETY: as above.
        assert_eq!(unsafe { dit::read() }, 1);
        // Guards may drop out of order: DIT waits for the last.
        let second = crate::cpu::Dit::hold();
        drop(first);
        // SAFETY: as above.
        assert_eq!(unsafe { dit::read() }, 1);
        drop(second);
        // SAFETY: as above.
        assert_eq!(unsafe { dit::read() }, 0);
    }

    #[cfg(unix)]
    fn child_reads_dit() -> bool {
        let test = concat!(module_path!(), "::reads_dit");
        let test = test.split_once("::").unwrap().1;
        // Under qemu-user, as `just qemu aarch64` runs the tests on another
        // host, the child needs qemu too.
        let mut runner = std::env::var("CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER")
            .ok()
            .filter(|_| cfg!(all(target_os = "linux", target_env = "gnu")))
            .unwrap_or_default()
            .split_whitespace()
            .map(std::ffi::OsString::from)
            .collect::<Vec<_>>();
        runner.push(std::env::current_exe().unwrap().into());
        let out = std::process::Command::new(&runner[0])
            .args(&runner[1..])
            .args([test, "--exact", "--nocapture"])
            .env("RIND_TEST_READ_DIT", "1")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        if out.status.success() {
            assert!(stdout.contains("read DIT"), "{test} did not run:\n{stdout}");
            return true;
        }
        let illegal = std::os::unix::process::ExitStatusExt::signal(&out.status) == Some(4);
        assert!(illegal, "{test} failed with {}:\n{stdout}", out.status);
        false
    }

    /// Runs `mrs DIT` for `child_reads_dit`, which an illegal instruction
    /// kills on a core without DIT.
    #[cfg(unix)]
    #[test]
    fn reads_dit() {
        if std::env::var_os("RIND_TEST_READ_DIT").is_some() {
            let pstate: u64;
            // SAFETY: on a core without DIT this raises an illegal
            // instruction, which is the answer the parent wants.
            unsafe { core::arch::asm!("mrs {}, S3_3_C4_C2_5", out(reg) pstate) };
            println!("read DIT: {pstate:#x}");
        }
    }
}
