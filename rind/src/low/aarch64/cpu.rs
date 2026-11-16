// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::sync::atomic::{AtomicU8, Ordering};

pub(crate) fn enter_cpu_state() -> u32 {
    #[cfg(target_vendor = "apple")]
    return dit::maybe_enable();
    #[cfg(not(target_vendor = "apple"))]
    0
}

pub(crate) fn leave_cpu_state(old: u32) {
    #[cfg(target_vendor = "apple")]
    dit::maybe_disable(old);
    #[cfg(not(target_vendor = "apple"))]
    let _ = old;
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
        (features() & CRYPTO_EXT != 0).then_some(Self(()))
    }
}

/// Token type reflecting the check for the SHA3 CPU feature
///
/// A value of this type is proof that the CPU dynamic feature check has happened.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSha3(());

impl HaveSha3 {
    pub(crate) fn check() -> Option<Self> {
        (features() & SHA3 != 0).then_some(Self(()))
    }
}

const CRYPTO_EXT: u8 = 1 << 1;
const SHA3: u8 = 1 << 2;
#[cfg(target_vendor = "apple")]
const DIT: u8 = 1 << 3;
#[cfg(target_vendor = "apple")]
const SB: u8 = 1 << 4;
const DETECTED: u8 = 1 << 7;

/// Whether this core should run s2n-bignum's `_alt` schedules.
///
/// Those are written for cores that issue `umulh` widely. The narrow
/// schedules run only for a core whose `MIDR_EL1` names Cortex-A72,
/// Cortex-A76, or Neoverse N1. Every other core keeps `_alt`, including one
/// this crate does not recognise, which is what aarch64 ran before the
/// dispatch. Both schedules are correct on every core.
///
/// The part is read here, on the first call, and not from
/// [`HaveCryptoExt`] or [`HaveSha3`]. Neither read opens a file.
#[inline]
pub(crate) fn wide_multiplier() -> bool {
    match WIDE.load(Ordering::Relaxed) {
        WIDE_UNSET => detect_wide_once(),
        WIDE_ALT => true,
        _ => false,
    }
}

static FEATURES: AtomicU8 = AtomicU8::new(0);
/// Separate from [`FEATURES`], so an AES or SHA check does not read the
/// part. `0` means the choice has not been made.
static WIDE: AtomicU8 = AtomicU8::new(WIDE_UNSET);
const WIDE_UNSET: u8 = 0;
const WIDE_NARROW: u8 = 1;
const WIDE_ALT: u8 = 2;

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
    use std::arch::is_aarch64_feature_detected as detected;

    // Hardware features only. The part list is `wide_multiplier`'s, so a
    // seccomp filter that kills `open` still runs AES, SHA, and NEON.
    let crypto_ext = test_toggle("aes", detected!("aes"))
        && test_toggle("pmull", detected!("pmull"))
        // Rust's `sha2` covers the SHA-1 instructions too.
        && test_toggle("sha2", detected!("sha2"));
    let sha3 = test_toggle("sha3", detected!("sha3"));
    let features = (if crypto_ext { CRYPTO_EXT } else { 0 }) | (if sha3 { SHA3 } else { 0 });
    #[cfg(target_vendor = "apple")]
    let features = features
        | if test_toggle("dit", detected!("dit")) {
            DIT
        } else {
            0
        }
        | if test_toggle("sb", detected!("sb")) {
            SB
        } else {
            0
        };
    features
}

/// `RIND_CPU_DISABLE_wide_mul` selects the narrow schedules, and
/// `RIND_CPU_FORCE_wide_mul` the `_alt` ones, in a debug build or a release
/// build with `--cfg rind_cpu_disable`. A release build without that cfg
/// compiles both reads out. Disable wins.
///
/// `_alt` is scalar base Armv8 and runs on every core rind supports, so
/// forcing it cannot fault. [`test_toggle`] does not take a force flag:
/// forcing NEON or AES on a core that lacks the instructions faults.
fn wide_toggle(detected: bool) -> bool {
    feature_toggle("wide_mul", detected, true)
}

#[cold]
#[inline(never)]
fn detect_wide_once() -> bool {
    let wide = wide_toggle(detect_wide_multiplier());
    WIDE.store(if wide { WIDE_ALT } else { WIDE_NARROW }, Ordering::Relaxed);
    wide
}

/// Apple's cores are wide. On Linux, so is every part except the known
/// narrow ones.
///
/// Called only from [`wide_multiplier`], never from an AES, SHA, or NEON
/// check. Linux reads `MIDR_EL1` with `mrs` when `AT_HWCAP` has
/// `HWCAP_CPUID`; the kernel emulates that read, so detection makes no
/// system call and opens no file, and a seccomp filter that kills `open`
/// cannot fire here. A kernel without `HWCAP_CPUID` (before Linux 4.11),
/// Android (`target_os` is not `linux`), Windows on ARM, and FreeBSD never
/// see a part, so they stay on `_alt` rather than guessing a narrow core.
///
/// This is the read aws-lc makes (`crypto/fipsmodule/cpucap/cpu_aarch64_linux.c`
/// lines 19-23 and 74-75 at `5ed12cce`), gated on the same bit because
/// valgrind cannot decode the register without it. Like aws-lc, it sees the
/// core the first call ran on. On a chip that mixes core types, the choice
/// follows that core and is then cached; both schedules are correct and
/// constant time on every core, so only speed depends on it.
fn detect_wide_multiplier() -> bool {
    #[cfg(target_os = "linux")]
    {
        // A debug build, or a release one with `--cfg rind_cpu_disable`, can
        // name a fixture instead of the host's register. Release builds
        // compile this out. `admin/mutants` runs the debug tests, so a mutant
        // that returns a constant fails the fixture whose answer is the other
        // one.
        #[cfg(any(debug_assertions, rind_cpu_disable))]
        if let Some(midr) = midr_fixture() {
            return midr.is_none_or(wide_from_midr);
        }
        read_midr().is_none_or(wide_from_midr)
    }
    #[cfg(not(target_os = "linux"))]
    true
}

/// `RIND_TEST_MIDR=narrow|wide|none` stands in for `MIDR_EL1`: a
/// Cortex-A76 r4p1, a Neoverse V1 r1p1, or a kernel without `HWCAP_CPUID`.
#[cfg(all(target_os = "linux", any(debug_assertions, rind_cpu_disable)))]
fn midr_fixture() -> Option<Option<u64>> {
    let midr = match std::env::var("RIND_TEST_MIDR").ok().as_deref() {
        Some("narrow") => Some(0x414f_d0b1),
        Some("wide") => Some(0x411f_d401),
        Some("none") => None,
        _ => return None,
    };
    Some(midr)
}

/// `MIDR_EL1`, or `None` when the kernel does not emulate EL0 reads of the
/// ID registers.
#[cfg(target_os = "linux")]
fn read_midr() -> Option<u64> {
    // SAFETY: `getauxval` reads the auxiliary vector the kernel passed at
    // exec. It makes no system call.
    let hwcap = unsafe { libc::getauxval(libc::AT_HWCAP) };
    if hwcap & libc::HWCAP_CPUID == 0 {
        return None;
    }
    let midr: u64;
    // SAFETY: with `HWCAP_CPUID` set, Linux traps and emulates an EL0 read
    // of `MIDR_EL1` (Documentation/arch/arm64/cpu-feature-registers.rst),
    // so this does not fault.
    unsafe {
        core::arch::asm!(
            "mrs {}, midr_el1",
            out(reg) midr,
            options(nomem, nostack, preserves_flags)
        );
    }
    Some(midr)
}

/// Whether the core `midr` names should run the `_alt` schedules.
///
/// The implementer is bits 31:24 and the part number bits 15:4. Variant,
/// architecture, and revision do not change the multiplier, so they are
/// ignored.
#[cfg(any(target_os = "linux", test))]
fn wide_from_midr(midr: u64) -> bool {
    !narrow_part((midr >> 24) & 0xff, (midr >> 4) & 0xfff)
}

/// `MIDR_EL1` implementer and part.
///
/// Cortex-A72 (`0xd08`), Cortex-A76 (`0xd0b`), and Neoverse N1 (`0xd0c`)
/// are the narrow parts. A76 is the Pi 5's core. N1 is the same multiplier
/// class, and SUPERCOP measured the narrow schedules faster there. A72 is
/// the same lightly pipelined `umulh`. Anything else, including Neoverse
/// V1 (`0xd40`), N2 (`0xd49`), V2 (`0xd4f`), V3 (`0xd84`), Apple (`0x61`),
/// and Microsoft Cobalt 100 (`0x6d` / `0xd49`), is not narrow.
///
/// aws-lc's `CRYPTO_is_ARMv8_wide_multiplier_capable` allowlists only V1,
/// V2, V3, and Apple, and defaults to the narrow schedules. This crate
/// defaults to `_alt`, and keeps N2 and Cobalt there because `_alt` was
/// measured faster on N2.
#[cfg(any(target_os = "linux", test))]
fn narrow_part(implementer: u64, part: u64) -> bool {
    implementer == 0x41 && matches!(part, 0xd08 | 0xd0b | 0xd0c)
}

// DIT changes what runs only on Apple's cores, where from the M3 it turns off
// the data memory-dependent prefetcher that GoFetch reads secrets through. Arm
// says it has no effect on any current Arm core, so elsewhere rind skips the
// cost of setting it.
#[cfg(target_vendor = "apple")]
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
    #[target_feature(enable = "sb")]
    pub(super) fn speculation_barrier() {
        // SAFETY: `sb` is defined only if `sb` cpu feature is supported
        unsafe { core::arch::asm!("sb", options(nostack, preserves_flags)) }
    }
}

fn test_toggle(id: &str, detected: bool) -> bool {
    feature_toggle(id, detected, false)
}

/// Deny with `RIND_CPU_DISABLE_<id>`. When `force` is set, also force with
/// `RIND_CPU_FORCE_<id>`. Disable wins. A release build without
/// `--cfg rind_cpu_disable` compiles both reads out.
#[cfg(not(any(debug_assertions, rind_cpu_disable)))]
fn feature_toggle(_id: &str, detected: bool, _force: bool) -> bool {
    detected
}

/// Lets a debug build, or a release one with `--cfg rind_cpu_disable`, deny a
/// feature with `RIND_CPU_DISABLE_<id>`, as on x86_64, so a CPU with the
/// crypto extension also tests the code for one without.
#[cfg(any(debug_assertions, rind_cpu_disable))]
fn feature_toggle(id: &str, detected: bool, force: bool) -> bool {
    if std::env::var_os(format!("RIND_CPU_DISABLE_{id}")).is_some() {
        // The FIPS module honours the mask in its release build, where its
        // caller's stdout is not its own.
        #[cfg(not(rind_fips))]
        println!("DEBUG: denying cpuid {id:?}");
        return false;
    }
    if force && std::env::var_os(format!("RIND_CPU_FORCE_{id}")).is_some() {
        #[cfg(not(rind_fips))]
        println!("DEBUG: forcing cpuid {id:?}");
        return true;
    }
    detected
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

/// Re-exec this test binary. qemu-user is cargo's runner, not a kernel
/// binfmt handler, so a child of a cross test needs that runner too. A
/// native run leaves the variable unset and execs the binary itself.
#[cfg(all(test, any(debug_assertions, rind_cpu_disable)))]
pub(super) fn reexec() -> std::process::Command {
    let exe = std::env::current_exe().unwrap();
    let Ok(runner) = std::env::var("CARGO_TARGET_AARCH64_UNKNOWN_LINUX_GNU_RUNNER") else {
        return std::process::Command::new(exe);
    };
    let mut parts = runner.split_whitespace();
    let mut cmd = std::process::Command::new(parts.next().unwrap());
    cmd.args(parts);
    cmd.arg(exe);
    cmd
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
        #[cfg(target_vendor = "apple")]
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

    /// Whether std detects every feature named, less those `test_toggle`
    /// denies.
    macro_rules! available {
        ($($name:tt),+) => {
            true $(&& std::arch::is_aarch64_feature_detected!($name) && !denied($name))+
        };
    }

    fn denied(name: &str) -> bool {
        cfg!(any(debug_assertions, rind_cpu_disable))
            && std::env::var(format!("RIND_CPU_DISABLE_{name}")).is_ok()
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
        if let Some(expected) = std::env::var_os("RIND_TEST_ARM_WIDE_MUL") {
            assert_eq!(wide_multiplier(), expected == "1");
        }
    }

    #[test]
    fn midr_selects_known_narrow_cores() {
        // Cortex-A72 r0p3, Cortex-A76 r4p1 (the Pi 5), and Neoverse N1 r3p1.
        for midr in [0x410f_d083, 0x414f_d0b1, 0x413f_d0c1] {
            assert!(!wide_from_midr(midr), "{midr:#x}");
        }
        // Variant and revision do not matter, and the upper 32 bits are
        // reserved.
        for variant in 0..16u64 {
            for revision in 0..16u64 {
                let midr = 0x410f_d0b0 | (variant << 20) | revision;
                assert!(!wide_from_midr(midr), "{midr:#x}");
                assert!(!wide_from_midr(midr | (u64::MAX << 32)), "{midr:#x}");
            }
        }
        // Measured wide cores, and parts this crate has not measured
        // (Cortex-A55 `0xd05`, Cortex-A78 `0xd41`).
        for part in [0xd40, 0xd49, 0xd4f, 0xd84, 0xd05, 0xd41] {
            let midr = 0x410f_0000 | (part << 4);
            assert!(wide_from_midr(midr), "{part:#x}");
        }
        // Apple M1, Cobalt 100, a Qualcomm part, and the narrow part numbers
        // from implementers other than Arm, which are other cores.
        assert!(wide_from_midr(0x610f_0230));
        assert!(wide_from_midr(0x6d0f_d490));
        assert!(wide_from_midr(0x510f_0010));
        for implementer in [0x00, 0x42, 0x51, 0x61, 0xc0] {
            for part in [0xd08u64, 0xd0b, 0xd0c] {
                let midr = (implementer << 24) | 0x000f_0000 | (part << 4);
                assert!(wide_from_midr(midr), "{midr:#x}");
            }
        }
        // An empty register, and a narrow part number shifted into the
        // revision or variant field, name no narrow core.
        assert!(wide_from_midr(0));
        assert!(wide_from_midr(0x4100_000b));
        assert!(wide_from_midr(0x41d0_b000));
    }

    // The override is process-wide, so each case is a child. Disable wins
    // over force. A release build without `--cfg rind_cpu_disable` compiles
    // the read out, and this test with it.
    #[cfg(any(debug_assertions, rind_cpu_disable))]
    #[test]
    fn wide_mul_env_overrides() {
        const CHILD: &str = "RIND_TEST_WIDE_TOGGLE";
        if let Some(mode) = std::env::var_os(CHILD) {
            assert_eq!(wide_multiplier(), mode == "wide");
            println!("{CHILD} done");
            return;
        }
        for (mode, disable, force) in [
            ("narrow", true, true),
            ("wide", false, true),
            ("narrow", true, false),
        ] {
            let mut cmd = reexec();
            // `--exact` matches the harness name, not the function's last
            // component. `module_path!` includes the crate, which libtest drops.
            let test = concat!(module_path!(), "::wide_mul_env_overrides");
            let test = test.split_once("::").unwrap().1;
            cmd.args([test, "--exact", "--nocapture"])
                .env(CHILD, mode)
                .env_remove("RIND_CPU_DISABLE_wide_mul")
                .env_remove("RIND_CPU_FORCE_wide_mul");
            if disable {
                cmd.env("RIND_CPU_DISABLE_wide_mul", "1");
            }
            if force {
                cmd.env("RIND_CPU_FORCE_wide_mul", "1");
            }
            let output = cmd.output().unwrap();
            let stdout = String::from_utf8_lossy(&output.stdout);
            // The marker proves the child ran even when FIPS suppresses CPU
            // logging. Outside FIPS, disable wins and prints the denial.
            let line = if disable {
                "DEBUG: denying cpuid \"wide_mul\""
            } else {
                "DEBUG: forcing cpuid \"wide_mul\""
            };
            assert!(
                output.status.success()
                    && stdout.contains(&format!("{CHILD} done"))
                    && (cfg!(rind_fips) || stdout.contains(line)),
                "{mode}: {line}\n{stdout}{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
    }

    /// AES, SHA, and NEON checks do not read the part. A child that only
    /// runs those checks leaves the multiplier unread.
    #[cfg(any(debug_assertions, rind_cpu_disable))]
    #[test]
    fn hw_checks_leave_the_multiplier_unread() {
        const CHILD: &str = "RIND_TEST_HW_LEAVES_WIDE";
        if std::env::var_os(CHILD).is_some() {
            let _ = HaveCryptoExt::check();
            let _ = HaveSha3::check();
            #[cfg(rind_fips)]
            let _ = missing_cpu_feature();
            assert_eq!(WIDE.load(Ordering::Relaxed), WIDE_UNSET);
            println!("{CHILD} done");
            return;
        }
        let mut cmd = reexec();
        let test = concat!(module_path!(), "::hw_checks_leave_the_multiplier_unread");
        let test = test.split_once("::").unwrap().1;
        cmd.args([test, "--exact", "--nocapture"]).env(CHILD, "1");
        let output = cmd.output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            output.status.success() && stdout.contains(&format!("{CHILD} done")),
            "{stdout}{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    // A core that runs `mrs DIT` has DIT, whatever the OS reports, so a child
    // process runs it.
    #[cfg(target_vendor = "apple")]
    #[test]
    fn enables_dit_whenever_the_cpu_has_it() {
        let has_dit = child_reads_dit();

        let expected = test_toggle("dit", has_dit);
        assert_eq!(features() & DIT != 0, expected);
        // A denied DIT is left alone, as under `admin/ctgrind`, whose
        // valgrind runs no DIT instruction.
        if has_dit && !expected {
            // SAFETY: this core has DIT, though `test_toggle` denies it.
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

    #[cfg(target_vendor = "apple")]
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

    #[cfg(target_vendor = "apple")]
    fn child_reads_dit() -> bool {
        let test = concat!(module_path!(), "::reads_dit");
        let test = test.split_once("::").unwrap().1;
        let out = std::process::Command::new(std::env::current_exe().unwrap())
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
    #[cfg(target_vendor = "apple")]
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

    /// The register and `detect_wide_multiplier` name the same schedule, and
    /// the register is one of the cores Linux lists. A mutant that returns a
    /// constant survives on a host with that answer;
    /// [`midr_fixture_selects_the_schedule`] has both answers.
    #[cfg(target_os = "linux")]
    #[test]
    fn detected_value_matches_midr() {
        let midr = read_midr();
        assert_eq!(detect_wide_multiplier(), midr.is_none_or(wide_from_midr));
        // qemu-user shows the host's sysfs, which has no aarch64 registers,
        // so this part runs only on an aarch64 kernel that lists them.
        let listed: Vec<u64> = (0..4096)
            .map_while(|cpu| {
                let dir = format!("/sys/devices/system/cpu/cpu{cpu}");
                std::path::Path::new(&dir).exists().then_some(dir)
            })
            .filter_map(|dir| {
                let path = format!("{dir}/regs/identification/midr_el1");
                let text = std::fs::read_to_string(path).ok()?;
                u64::from_str_radix(text.trim().trim_start_matches("0x"), 16).ok()
            })
            .collect();
        if let (Some(midr), false) = (midr, listed.is_empty()) {
            assert!(listed.contains(&midr), "{midr:#x} not in {listed:x?}");
        }
    }

    /// `narrow` is Cortex-A76, `wide` is Neoverse V1, `none` has no
    /// `HWCAP_CPUID`.
    #[cfg(all(target_os = "linux", any(debug_assertions, rind_cpu_disable)))]
    #[test]
    fn midr_fixture_selects_the_schedule() {
        const CHILD: &str = "RIND_TEST_MIDR_CHILD";
        if std::env::var_os(CHILD).is_some() {
            let mode = std::env::var("RIND_TEST_MIDR").unwrap();
            let wide = detect_wide_multiplier();
            assert_eq!(wide, mode != "narrow", "{mode}");
            println!("{CHILD} {mode}");
            return;
        }
        for mode in ["narrow", "wide", "none"] {
            let stdout = run_child(
                concat!(module_path!(), "::midr_fixture_selects_the_schedule"),
                &[(CHILD, "1"), ("RIND_TEST_MIDR", mode)],
            );
            assert!(stdout.contains(&format!("{CHILD} {mode}")), "{stdout}");
        }
    }

    /// The first schedule choice, and the first X25519 after it, survive a
    /// filter that kills the process on `openat` or `openat2`, and one that
    /// sends `SIGSYS` with no handler installed. Either would end the child
    /// if detection opened a file.
    #[cfg(all(target_os = "linux", any(debug_assertions, rind_cpu_disable)))]
    #[test]
    fn detection_opens_no_file() {
        const CHILD: &str = "RIND_TEST_NO_OPEN";
        if let Some(action) = std::env::var_os(CHILD) {
            let action = if action == "kill" {
                libc::SECCOMP_RET_KILL_PROCESS
            } else {
                libc::SECCOMP_RET_TRAP
            };
            assert_eq!(WIDE.load(Ordering::Relaxed), WIDE_UNSET);
            let expected = read_midr().is_none_or(wide_from_midr);
            match install_openat_filter(action) {
                Ok(()) => {
                    let wide = wide_multiplier();
                    let _ = HaveCryptoExt::check();
                    let mut out = [0; 4];
                    super::super::wide_mux::curve25519_x25519(
                        &mut out,
                        &[1, 0, 0, 0],
                        &[9, 0, 0, 0],
                    );
                    assert_ne!(out, [0; 4]);
                    // Disable and force still apply on top of detection.
                    assert_eq!(wide, wide_toggle(expected));
                    println!("{CHILD} done");
                }
                Err(err) if seccomp_unavailable(&err) => {
                    // qemu-user rejects `PR_SET_SECCOMP` (`ENOSYS` or
                    // `EINVAL`) for a filter the kernel would accept. A
                    // native kernel that rejects only this filter still
                    // fails the test.
                    println!("{CHILD} skipped");
                }
                Err(err) => panic!("seccomp: {err}"),
            }
            return;
        }
        for action in ["kill", "trap"] {
            let stdout = run_child(
                concat!(module_path!(), "::detection_opens_no_file"),
                &[(CHILD, action)],
            );
            assert!(
                stdout.contains(&format!("{CHILD} done"))
                    || stdout.contains(&format!("{CHILD} skipped")),
                "{action}: {stdout}"
            );
        }
    }

    #[cfg(all(target_os = "linux", any(debug_assertions, rind_cpu_disable)))]
    fn run_child(test: &str, env: &[(&str, &str)]) -> String {
        let mut cmd = reexec();
        let name = test.split_once("::").unwrap().1;
        cmd.args([name, "--exact", "--nocapture"]);
        for (key, value) in env {
            cmd.env(key, value);
        }
        let output = cmd.output().unwrap();
        let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
        assert!(
            output.status.success(),
            "{test}\n{stdout}{}",
            String::from_utf8_lossy(&output.stderr)
        );
        stdout
    }

    /// `true` when this kernel will not install any seccomp filter.
    ///
    /// An allow-all filter is valid, so `EINVAL` or `ENOSYS` from it means
    /// the platform (qemu-user, here) has no seccomp, rather than that the
    /// trap filter above is malformed.
    #[cfg(all(target_os = "linux", any(debug_assertions, rind_cpu_disable)))]
    fn seccomp_unavailable(err: &std::io::Error) -> bool {
        if !matches!(err.raw_os_error(), Some(libc::ENOSYS | libc::EINVAL)) {
            return false;
        }
        let mut allow = [libc::sock_filter {
            code: 0x06, // BPF_RET | BPF_K
            jt: 0,
            jf: 0,
            k: libc::SECCOMP_RET_ALLOW,
        }];
        matches!(
            install_filter(&mut allow).map_err(|err| err.raw_os_error()),
            Err(Some(libc::ENOSYS | libc::EINVAL))
        )
    }

    /// Answers `openat` and `openat2` with `action`. Other calls are
    /// allowed, so the test can still print.
    #[cfg(all(target_os = "linux", any(debug_assertions, rind_cpu_disable)))]
    fn install_openat_filter(action: u32) -> std::io::Result<()> {
        // BPF_LD | BPF_W | BPF_ABS, BPF_JMP | BPF_JEQ | BPF_K, BPF_RET | BPF_K.
        let mut filter = [
            libc::sock_filter {
                code: 0x20,
                jt: 0,
                jf: 0,
                k: 0,
            },
            libc::sock_filter {
                code: 0x15,
                jt: 2,
                jf: 0,
                k: 56,
            },
            libc::sock_filter {
                code: 0x15,
                jt: 1,
                jf: 0,
                k: 437,
            },
            libc::sock_filter {
                code: 0x06,
                jt: 0,
                jf: 0,
                k: libc::SECCOMP_RET_ALLOW,
            },
            libc::sock_filter {
                code: 0x06,
                jt: 0,
                jf: 0,
                k: action,
            },
        ];
        install_filter(&mut filter)
    }

    #[cfg(all(target_os = "linux", any(debug_assertions, rind_cpu_disable)))]
    fn install_filter(filter: &mut [libc::sock_filter]) -> std::io::Result<()> {
        let prog = libc::sock_fprog {
            len: filter.len() as libc::c_ushort,
            filter: filter.as_mut_ptr(),
        };
        // SAFETY: `prog` points at `filter` for the duration of the call.
        // `PR_SET_NO_NEW_PRIVS` is required before a seccomp filter.
        unsafe {
            if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
            if libc::prctl(libc::PR_SET_SECCOMP, libc::SECCOMP_MODE_FILTER, &prog, 0, 0) != 0 {
                return Err(std::io::Error::last_os_error());
            }
        }
        Ok(())
    }
}
