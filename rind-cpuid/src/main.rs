#[cfg(not(any(
    target_arch = "x86_64",
    target_arch = "aarch64",
    all(target_arch = "arm", any(target_os = "linux", target_os = "android"))
)))]
fn main() {
    println!("only for x86_64, aarch64, and 32-bit arm Linux or Android");
}

#[cfg(target_arch = "x86_64")]
fn main() {
    use std::arch::x86_64::__cpuid;

    // "GenuineIntel", spread over ebx, edx, and ecx.
    // `__cpuid` is safe from Rust 1.94 but `unsafe` on the 1.90 MSRV.
    #[allow(unused_unsafe)]
    // SAFETY: every x86_64 CPU has `cpuid`.
    let id = unsafe { __cpuid(0) };
    let intel = (id.ebx, id.edx, id.ecx) == (0x756e_6547, 0x4965_6e69, 0x6c65_746e);

    // Every feature `rind/src/low/x86_64/cpu.rs` reads, so the scans show
    // which dispatch paths each CPU selects, plus `sha512`, which rind records
    // and does not dispatch on.
    let cpuid = [
        ("intel", intel),
        ("adx", is_x86_feature_detected!("adx")),
        ("aes", is_x86_feature_detected!("aes")),
        ("vaes", is_x86_feature_detected!("vaes")),
        ("pclmulqdq", is_x86_feature_detected!("pclmulqdq")),
        ("vpclmulqdq", is_x86_feature_detected!("vpclmulqdq")),
        ("bmi1", is_x86_feature_detected!("bmi1")),
        ("bmi2", is_x86_feature_detected!("bmi2")),
        ("movbe", is_x86_feature_detected!("movbe")),
        ("popcnt", is_x86_feature_detected!("popcnt")),
        ("ssse3", is_x86_feature_detected!("ssse3")),
        ("sse4.1", is_x86_feature_detected!("sse4.1")),
        ("avx", is_x86_feature_detected!("avx")),
        ("avx2", is_x86_feature_detected!("avx2")),
        ("avx512f", is_x86_feature_detected!("avx512f")),
        ("avx512dq", is_x86_feature_detected!("avx512dq")),
        ("avx512ifma", is_x86_feature_detected!("avx512ifma")),
        ("avx512bw", is_x86_feature_detected!("avx512bw")),
        ("avx512vl", is_x86_feature_detected!("avx512vl")),
        ("avx512vbmi", is_x86_feature_detected!("avx512vbmi")),
        ("avx512vbmi2", is_x86_feature_detected!("avx512vbmi2")),
        ("sha", is_x86_feature_detected!("sha")),
        ("sha512", is_x86_feature_detected!("sha512")),
    ];
    let has = |name| cpuid.iter().any(|&(n, v)| n == name && v);

    let avx512_aes_gcm = ["avx512f", "avx512bw", "avx512vl", "vaes", "vpclmulqdq"]
        .into_iter()
        .all(has);

    let cpuid = cpuid
        .iter()
        .map(|(name, v)| format!("\"{name}\": {}", *v as u8))
        .collect::<Vec<_>>()
        .join(", ");
    println!(
        "{{ \"cpuid\": {{ {cpuid} }}, \"supports_avx512_aes_gcm\": {} }}",
        avx512_aes_gcm as u8,
    );
}

#[cfg(target_arch = "aarch64")]
fn main() {
    use std::arch::is_aarch64_feature_detected;

    let aes = is_aarch64_feature_detected!("aes");
    let dit = is_aarch64_feature_detected!("dit");
    let neon = is_aarch64_feature_detected!("neon");
    let pmull = is_aarch64_feature_detected!("pmull");
    let sha2 = is_aarch64_feature_detected!("sha2");
    let sha3 = is_aarch64_feature_detected!("sha3");
    let wide_mul = wide_multiplier();

    println!(
        "{{ \"cpuid\": {{ \"aes\": {}, \"dit\": {}, \"neon\": {}, \"pmull\": {}, \
        \"sha2\": {}, \"sha3\": {}, \"wide_mul\": {} }} }}",
        aes as u8, dit as u8, neon as u8, pmull as u8, sha2 as u8, sha3 as u8, wide_mul as u8,
    );
}

/// Whether rind's aarch64 backend runs s2n-bignum's `_alt` (wide-multiplier)
/// schedules on this core, as a release build of rind picks them: the narrow
/// ones run only on Linux, when the kernel emulates EL0 reads of `MIDR_EL1`
/// (`HWCAP_CPUID`) and the register names Cortex-A72, Cortex-A76, or
/// Neoverse N1. Every other core and OS keeps `_alt`.
///
/// This repeats `read_midr` and `narrow_part` in
/// `rind/src/low/aarch64/cpu.rs`; keep the part list in step with
/// `narrow_part`. It reports the core, so it does not see the debug-only
/// `RIND_CPU_DISABLE_wide_mul` and `RIND_CPU_FORCE_wide_mul`, which a release
/// build compiles out, or the portable backend, which has no `_alt` schedule.
#[cfg(target_arch = "aarch64")]
fn wide_multiplier() -> bool {
    #[cfg(target_os = "linux")]
    {
        // SAFETY: `getauxval` reads the auxiliary vector the kernel passed at
        // exec. It makes no system call.
        let hwcap = unsafe { libc::getauxval(libc::AT_HWCAP) };
        if hwcap & libc::HWCAP_CPUID == 0 {
            return true;
        }
        let midr: u64;
        // SAFETY: with `HWCAP_CPUID` set, Linux traps and emulates an EL0
        // read of `MIDR_EL1` (Documentation/arch/arm64/cpu-feature-registers.rst),
        // so this does not fault.
        unsafe {
            core::arch::asm!(
                "mrs {}, midr_el1",
                out(reg) midr,
                options(nomem, nostack, preserves_flags)
            );
        }
        // Implementer is bits 31:24 and part number bits 15:4; Arm is 0x41.
        let implementer = (midr >> 24) & 0xff;
        let part = (midr >> 4) & 0xfff;
        !(implementer == 0x41 && matches!(part, 0xd08 | 0xd0b | 0xd0c))
    }
    #[cfg(not(target_os = "linux"))]
    true
}

/// 32-bit ARM Linux and Android: the features the kernel reports to a 32-bit
/// process, which is all `rind/src/low/arm/cpu.rs` reads. Like the aarch64
/// probe, it does not link the library.
#[cfg(all(target_arch = "arm", any(target_os = "linux", target_os = "android")))]
fn main() {
    // SAFETY: `getauxval` only reads the process's auxiliary vector, and
    // returns 0 for an entry it lacks.
    let (hwcap, hwcap2) = unsafe {
        (
            libc::getauxval(libc::AT_HWCAP) as u64,
            libc::getauxval(libc::AT_HWCAP2) as u64,
        )
    };
    let f = arm::decode(hwcap, hwcap2);

    println!(
        "{{ \"cpuid\": {{ \"neon\": {}, \"aes\": {}, \"pmull\": {}, \"sha1\": {}, \
        \"sha2\": {}, \"crc32\": {} }}, \"supports_crypto_ext\": {}, \
        \"hwcap\": {hwcap}, \"hwcap2\": {hwcap2} }}",
        f.neon as u8,
        f.aes as u8,
        f.pmull as u8,
        f.sha1 as u8,
        f.sha2 as u8,
        f.crc32 as u8,
        f.crypto_ext() as u8,
    );
}

/// Decodes the kernel's `AT_HWCAP` and `AT_HWCAP2` words for 32-bit ARM, with
/// the bits of Linux's `arch/arm/include/uapi/asm/hwcap.h`. Pure, so it is
/// tested on every host.
#[cfg(any(target_arch = "arm", test))]
mod arm {
    const HWCAP_NEON: u64 = 1 << 12;
    const HWCAP2_AES: u64 = 1 << 0;
    const HWCAP2_PMULL: u64 = 1 << 1;
    const HWCAP2_SHA1: u64 = 1 << 2;
    const HWCAP2_SHA2: u64 = 1 << 3;
    const HWCAP2_CRC32: u64 = 1 << 4;

    #[derive(Debug, PartialEq, Eq)]
    pub struct Features {
        pub neon: bool,
        pub aes: bool,
        pub pmull: bool,
        pub sha1: bool,
        pub sha2: bool,
        /// Recorded, and not dispatched on: rind runs no CRC32 instruction.
        pub crc32: bool,
    }

    impl Features {
        /// Whether rind runs the ARMv8 Crypto Extension in AArch32: NEON, AES,
        /// PMULL, SHA-1, and SHA-256 together, as `HaveCryptoExt::check` does
        /// in `rind/src/low/arm/cpu.rs`; keep the two in step.
        pub fn crypto_ext(&self) -> bool {
            self.neon && self.aes && self.pmull && self.sha1 && self.sha2
        }
    }

    pub fn decode(hwcap: u64, hwcap2: u64) -> Features {
        Features {
            neon: hwcap & HWCAP_NEON != 0,
            aes: hwcap2 & HWCAP2_AES != 0,
            pmull: hwcap2 & HWCAP2_PMULL != 0,
            sha1: hwcap2 & HWCAP2_SHA1 != 0,
            sha2: hwcap2 & HWCAP2_SHA2 != 0,
            crc32: hwcap2 & HWCAP2_CRC32 != 0,
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        /// A Fire TV Stick (Cortex-A53, 32-bit Fire OS 7.7, kernel 4.4.162):
        /// the extension in AArch32.
        #[test]
        fn cortex_a53_with_crypto_extension() {
            let f = decode(0x3f_b0d6, 0x1f);
            assert_eq!(
                f,
                Features {
                    neon: true,
                    aes: true,
                    pmull: true,
                    sha1: true,
                    sha2: true,
                    crc32: true,
                }
            );
            assert!(f.crypto_ext());
        }

        /// NEON without the extension, as on a Cortex-A9 or A15.
        #[test]
        fn neon_without_crypto_extension() {
            let f = decode(HWCAP_NEON | 0x1_0000, 0);
            assert!(f.neon);
            assert!(!f.aes && !f.pmull && !f.sha1 && !f.sha2 && !f.crc32);
            assert!(!f.crypto_ext());
        }

        /// A kernel that omits `AT_HWCAP2` reports no extension, and rind runs
        /// its portable and NEON code, as `detect` in `low/arm/cpu.rs` does.
        #[test]
        fn missing_hwcap2_is_no_extension() {
            assert!(!decode(0x3f_b0d6, 0).crypto_ext());
        }

        /// The extension is one unit: any bit missing denies it.
        #[test]
        fn every_crypto_bit_is_needed() {
            for bit in [HWCAP2_AES, HWCAP2_PMULL, HWCAP2_SHA1, HWCAP2_SHA2] {
                let hwcap2 = (HWCAP2_AES | HWCAP2_PMULL | HWCAP2_SHA1 | HWCAP2_SHA2) & !bit;
                assert!(!decode(HWCAP_NEON, hwcap2).crypto_ext(), "{bit:#x}");
            }
            // The extension without NEON is not a thing rind runs.
            assert!(!decode(0, 0x1f).crypto_ext());
        }

        /// CRC32 is reported and does not enable the extension.
        #[test]
        fn crc32_alone() {
            let f = decode(HWCAP_NEON, HWCAP2_CRC32);
            assert!(f.crc32 && !f.crypto_ext());
        }
    }

    /// On a 32-bit ARM Linux or Android host, `getauxval` agrees with the
    /// `Features` line of `/proc/cpuinfo`, which names the same bits.
    #[cfg(all(
        test,
        target_arch = "arm",
        any(target_os = "linux", target_os = "android")
    ))]
    mod host {
        use super::*;

        #[test]
        fn auxv_matches_proc_cpuinfo() {
            // SAFETY: `getauxval` only reads the auxiliary vector.
            let (hwcap, hwcap2) = unsafe {
                (
                    libc::getauxval(libc::AT_HWCAP) as u64,
                    libc::getauxval(libc::AT_HWCAP2) as u64,
                )
            };
            let f = decode(hwcap, hwcap2);
            let cpuinfo = std::fs::read_to_string("/proc/cpuinfo").unwrap();
            let line = cpuinfo
                .lines()
                .find(|l| l.starts_with("Features"))
                .expect("a Features line");
            // Take the words after the colon, so `Features:` and `Features\t:` both work.
            let (_, list) = line.split_once(':').expect("a colon in the Features line");
            let has = |name: &str| list.split_whitespace().any(|w| w == name);
            assert_eq!(f.neon, has("neon"), "{line}");
            assert_eq!(f.aes, has("aes"), "{line}");
            assert_eq!(f.pmull, has("pmull"), "{line}");
            assert_eq!(f.sha1, has("sha1"), "{line}");
            assert_eq!(f.sha2, has("sha2"), "{line}");
            assert_eq!(f.crc32, has("crc32"), "{line}");
        }
    }
}
