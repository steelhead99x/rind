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

/// Returns the first CPU feature we require unconditionally that this CPU lacks.
///
/// The FIPS module also requires the crypto extension, which every core it
/// is tested on has, so its vpaes and NEON GHASH paths, which no tested core
/// runs, need no ACVP run of their own.
pub(crate) fn missing_cpu_feature() -> Option<&'static str> {
    if features() & NEON == 0 {
        return Some("neon");
    }
    if cfg!(rind_fips) && features() & CRYPTO_EXT == 0 {
        return Some("aes, pmull, and sha2");
    }
    None
}

const NEON: u8 = 1 << 0;
const CRYPTO_EXT: u8 = 1 << 1;
const SHA3: u8 = 1 << 2;
#[cfg(target_vendor = "apple")]
const DIT: u8 = 1 << 3;
/// s2n-bignum's `_alt` schedules, for a core whose 64×64→128 multiply is wide.
const WIDE_MUL: u8 = 1 << 4;
const DETECTED: u8 = 1 << 7;

/// Whether this core should run s2n-bignum's `_alt` schedules.
///
/// Those are written for cores that issue `umulh` widely. The narrow
/// schedules run only for a core Linux names as Cortex-A72, Cortex-A76, or
/// Neoverse N1. Every other core keeps `_alt`, including one this crate
/// does not recognise, which is what aarch64 ran before the dispatch.
/// Both schedules are correct on every core.
#[inline]
pub(crate) fn wide_multiplier() -> bool {
    features() & WIDE_MUL != 0
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
    use std::arch::is_aarch64_feature_detected as detected;

    let neon = test_toggle("neon", detected!("neon"));
    let crypto_ext = test_toggle("aes", detected!("aes"))
        && test_toggle("pmull", detected!("pmull"))
        // Rust's `sha2` covers the SHA-1 instructions too.
        && test_toggle("sha2", detected!("sha2"));
    let sha3 = test_toggle("sha3", detected!("sha3"));
    let wide = wide_toggle(detect_wide_multiplier());
    let features = (if neon { NEON } else { 0 })
        | (if crypto_ext { CRYPTO_EXT } else { 0 })
        | (if sha3 { SHA3 } else { 0 })
        | (if wide { WIDE_MUL } else { 0 });
    #[cfg(target_vendor = "apple")]
    let features = features
        | if test_toggle("dit", detected!("dit")) {
            DIT
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
/// forcing it cannot fault. A force toggle must not be added for a feature
/// whose instructions can.
fn wide_toggle(detected: bool) -> bool {
    #[cfg(any(debug_assertions, rind_cpu_disable))]
    {
        if std::env::var_os("RIND_CPU_DISABLE_wide_mul").is_some() {
            // As `test_toggle`: the FIPS module's stdout is its caller's.
            #[cfg(not(rind_fips))]
            println!("DEBUG: denying cpuid \"wide_mul\"");
            return false;
        }
        if std::env::var_os("RIND_CPU_FORCE_wide_mul").is_some() {
            #[cfg(not(rind_fips))]
            println!("DEBUG: forcing cpuid \"wide_mul\"");
            return true;
        }
    }
    detected
}

/// Apple's cores are wide. On Linux, so is every part except the known
/// narrow ones.
///
/// Detection reads `/proc/cpuinfo` on Linux only, and only the parts online
/// at that moment: a core hotplugged later is not seen. Apple's platforms
/// name the vendor in the target, so they need no file. A sandbox that
/// cannot read the file, Android (`target_os` is not `linux`, including a
/// build that cannot open the file), and Windows on ARM never see a part
/// list, so they stay on `_alt` rather than guessing a narrow core. FreeBSD
/// does too. Both schedules are correct on every core.
fn detect_wide_multiplier() -> bool {
    if cfg!(target_vendor = "apple") {
        return true;
    }
    if cfg!(target_os = "linux") {
        return std::fs::read_to_string("/proc/cpuinfo")
            .map(|text| wide_from_cpuinfo(&text))
            .unwrap_or(true);
    }
    true
}

/// Whether `text` should run the `_alt` schedules.
///
/// That is every listing except one whose parts are all known narrow cores.
/// No part, an unknown part, or a mix with anything else stays on `_alt`:
/// a chip this crate has not measured keeps the code it ran before.
fn wide_from_cpuinfo(text: &str) -> bool {
    let mut saw = false;
    let mut all_narrow = true;
    let mut implementer = None;
    for line in text.lines() {
        let Some((key, value)) = line.split_once(':') else {
            continue;
        };
        let (key, value) = (key.trim(), value.trim());
        if key == "processor" {
            implementer = None;
        } else if key.eq_ignore_ascii_case("CPU implementer") {
            implementer = parse_cpu_id(value);
        } else if key.eq_ignore_ascii_case("CPU part") {
            saw = true;
            all_narrow &= narrow_part(implementer, parse_cpu_id(value));
        }
    }
    !(saw && all_narrow)
}

fn parse_cpu_id(value: &str) -> Option<u64> {
    let value = value
        .strip_prefix("0x")
        .or_else(|| value.strip_prefix("0X"))
        .unwrap_or(value);
    u64::from_str_radix(value, 16).ok()
}

/// MIDR implementer and part, as Linux prints them in `/proc/cpuinfo`.
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
fn narrow_part(implementer: Option<u64>, part: Option<u64>) -> bool {
    matches!(
        (implementer, part),
        (Some(0x41), Some(0xd08 | 0xd0b | 0xd0c))
    )
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
        } else {
            // SAFETY: `msr DIT, _` is defined only if `dit` cpu feature is supported
            unsafe { core::arch::asm!("msr DIT, #0") }
        }
    }
}

#[cfg(not(any(debug_assertions, rind_cpu_disable)))]
fn test_toggle(_id: &str, detected: bool) -> bool {
    detected
}

/// Lets a debug build, or a release one with `--cfg rind_cpu_disable`, deny a
/// feature with `RIND_CPU_DISABLE_<id>`, as on x86_64, so a CPU with the
/// crypto extension also tests the code for one without.
#[cfg(any(debug_assertions, rind_cpu_disable))]
fn test_toggle(id: &str, detected: bool) -> bool {
    if std::env::var(format!("RIND_CPU_DISABLE_{id}")).is_ok() {
        // The FIPS module honours the mask in its release build, where its
        // caller's stdout is not its own.
        #[cfg(not(rind_fips))]
        println!("DEBUG: denying cpuid {id:?}");
        false
    } else {
        detected
    }
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
        assert_eq!(missing_cpu_feature().is_none(), available!("neon"));
        assert_eq!(
            HaveCryptoExt::check().is_some(),
            available!("aes", "pmull", "sha2")
        );
        assert_eq!(HaveSha3::check().is_some(), available!("sha3"));
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
    fn cpuinfo_selects_known_narrow_cores() {
        let pi5 = "\
processor	: 0
CPU implementer	: 0x41
CPU part	: 0xd0b
processor	: 1
cpu implementer	: 0x41
cpu part	: 0xd0b
";
        assert!(!wide_from_cpuinfo(pi5));
        assert!(!wide_from_cpuinfo(
            "CPU implementer	: 0x41\nCPU part	: 0xd08\n"
        ));
        assert!(!wide_from_cpuinfo(
            "CPU implementer	: 0x41\nCPU part	: 0xd0c\n"
        ));
        // Measured wide cores, and parts this crate has not measured.
        for part in ["0xd40", "0xd49", "0xd4f", "0xd84", "0xd05", "0xd41"] {
            let text = format!("CPU implementer	: 0x41\nCPU part	: {part}\n");
            assert!(wide_from_cpuinfo(&text), "{part}");
        }
        assert!(wide_from_cpuinfo(
            "CPU implementer	: 0x61\nCPU part	: 0x023\n"
        ));
        assert!(wide_from_cpuinfo(
            "CPU implementer	: 0x6d\nCPU part	: 0xd49\n"
        ));
        // A wide core beside a narrow one keeps `_alt`.
        assert!(wide_from_cpuinfo(
            "\
processor	: 0
CPU implementer	: 0x41
CPU part	: 0xd40
processor	: 1
CPU implementer	: 0x41
CPU part	: 0xd0b
"
        ));
        // An unmeasured little core beside an A76 keeps `_alt` too.
        assert!(wide_from_cpuinfo(
            "\
processor	: 0
CPU implementer	: 0x41
CPU part	: 0xd0b
processor	: 1
CPU implementer	: 0x41
CPU part	: 0xd05
"
        ));
        assert!(wide_from_cpuinfo(""));
        assert!(wide_from_cpuinfo("processor	: 0\n"));
        // A part that arrives before its implementer, or an unknown
        // implementer, has not been identified, so it stays on `_alt`.
        assert!(wide_from_cpuinfo(
            "CPU part	: 0xd0b\nCPU implementer	: 0x41\n"
        ));
        assert!(wide_from_cpuinfo(
            "CPU implementer	: 0x51\nCPU part	: 0x001\n"
        ));
        // A later processor that omits the implementer is unknown.
        assert!(wide_from_cpuinfo(
            "\
processor	: 0
CPU implementer	: 0x41
CPU part	: 0xd0b
processor	: 1
CPU part	: 0xd0b
"
        ));
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
            // Disable wins, so a child with both set prints the denial.
            let line = if disable {
                "DEBUG: denying cpuid \"wide_mul\""
            } else {
                "DEBUG: forcing cpuid \"wide_mul\""
            };
            assert!(
                output.status.success() && stdout.contains(line),
                "{mode}: {line}\n{stdout}{}",
                String::from_utf8_lossy(&output.stderr)
            );
        }
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
}
