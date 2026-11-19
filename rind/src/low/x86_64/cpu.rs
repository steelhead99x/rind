// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::arch::x86_64::*;
use core::sync::atomic::{AtomicU32, Ordering};

pub(crate) fn enter_cpu_state() -> u32 {
    // DOIT: "Data Operand Independent Timing" -- turning this on
    // is under kernel control, because MSRs are privileged.
    // <https://www.intel.com/content/www/us/en/developer/articles/technical/software-security-guidance/best-practices/data-operand-independent-timing-isa-guidance.html>
    0
}

/// Nothing to restore, since `enter_cpu_state` changed nothing. Vector
/// registers hold scratch, not owned secrets, so like aws-lc we leave them.
pub(crate) fn leave_cpu_state(_old: u32) {}

/// Effectively memset(ptr, 0, len), but not visible to optimiser
///
/// # Safety
/// The caller must ensure that there are `len` bytes writable at `ptr`,
/// and that the pointed-to object has a safe all-zeroes representation.
/// (see `low::generic::zeroise` which expresses this within the type system).
pub(in crate::low) unsafe fn zero_bytes(ptr: *mut u8, len: usize) {
    match HaveAvx2::check() {
        // SAFETY: the caller's guarantee, and the token proves AVX2
        Some(_) => unsafe { zero_bytes_avx2(ptr, len) },
        // SAFETY: the caller's guarantee, and every x86_64 CPU has SSE2
        None => unsafe { zero_bytes_sse2(ptr, len) },
    }
}

#[target_feature(enable = "avx,avx2")]
unsafe fn zero_bytes_avx2(ptr: *mut u8, len: usize) {
    // Typed so rustc sees a 256-bit register written and ends the function
    // with `vzeroupper`, sparing the SSE code that runs next a transition.
    let _zero: __m256i;
    // SAFETY: writes to `len` bytes at `ptr`, which the caller guarantees
    unsafe {
        core::arch::asm!(
            "       vpxor   {zero}, {zero}, {zero}",
            // by-32 loop
            "   2:  cmp {len}, 32",
            "       jl  3f",
            "       vmovdqu [{ptr}], {zero}",
            "       add {ptr}, 32",
            "       sub {len}, 32",
            "       jmp 2b",
            // by-8 loop
            "   3:  cmp {len}, 8",
            "       jl  4f",
            "       mov qword ptr [{ptr}], 0",
            "       add {ptr}, 8",
            "       sub {len}, 8",
            "       jmp 3b",
            // by-1 loop
            "   4:  sub {len}, 1",
            "       jl  5f",
            "       mov byte ptr [{ptr}], 0",
            "       add {ptr}, 1",
            "       jmp 4b",
            "   5:  ",

            ptr = inout(reg) ptr => _,
            len = inout(reg) len => _,

            zero = out(ymm_reg) _zero,
        )
    }
}

unsafe fn zero_bytes_sse2(ptr: *mut u8, len: usize) {
    // SAFETY: writes to `len` bytes at `ptr`, which the caller guarantees
    unsafe {
        core::arch::asm!(
            "       pxor    {zero}, {zero}",
            // by-16 loop
            "   2:  cmp {len}, 16",
            "       jl  3f",
            "       movdqu  [{ptr}], {zero}",
            "       add {ptr}, 16",
            "       sub {len}, 16",
            "       jmp 2b",
            // by-8 loop
            "   3:  cmp {len}, 8",
            "       jl  4f",
            "       mov qword ptr [{ptr}], 0",
            "       add {ptr}, 8",
            "       sub {len}, 8",
            "       jmp 3b",
            // by-1 loop
            "   4:  sub {len}, 1",
            "       jl  5f",
            "       mov byte ptr [{ptr}], 0",
            "       add {ptr}, 1",
            "       jmp 4b",
            "   5:  ",

            ptr = inout(reg) ptr => _,
            len = inout(reg) len => _,

            // clobbers
            zero = out(xmm_reg) _,
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
    let acc: u32;
    // SAFETY: reads `len` bytes from `a` and `b`, which both hold.
    // Its registers are fixed, and it is never inlined, so its proof in
    // `proofs/hol-light/x86_64/ct_compare_bytes.ml` is of one copy.
    unsafe {
        core::arch::asm!(
            "   2: cmp   rdx, 0",
            "      je    3f",
            "      movzx ecx, byte ptr [rdi]",
            "      movzx r8d, byte ptr [rsi]",
            "      xor   ecx, r8d",
            "      or    eax, ecx",
            "      add   rdi, 1",
            "      add   rsi, 1",
            "      sub   rdx, 1",
            "      jmp   2b",
            "   3:  ",
            inout("rdi") a => _,
            inout("rsi") b => _,
            inout("rdx") len => _,
            inout("eax") 0u32 => acc,
            out("ecx") _,
            out("r8d") _,
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
    // `proofs/hol-light/x86_64/ct_compare_16.ml`.
    unsafe {
        core::arch::asm!(
            "xor rax, rdx",
            "xor rcx, r8",
            "or  rax, rcx",
            inout("rax") a as u64 => diff,
            inout("rcx") (a >> 64) as u64 => _,
            in("rdx") b as u64,
            in("r8") (b >> 64) as u64,
            options(pure, nomem, nostack),
        );
    }
    diff as usize
}

/// Token type reflecting the check for CPU features needed for AVX512-AES-GCM
///
/// A value of this type is proof that the CPU dynamic feature check has happened.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx512ForAesGcm(());

impl HaveAvx512ForAesGcm {
    pub(crate) fn check() -> Option<Self> {
        match has(AES_GCM_BASE | AVX512F | AVX512BW | AVX512VL | VPCLMULQDQ | VAES) {
            true => Some(Self(())),
            false => None,
        }
    }
}

/// Token type reflecting the check for CPU features needed for VAES-AES-GCM
/// on 256-bit vectors.
///
/// A value of this type is proof that the CPU dynamic feature check has happened.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveVaesAvx2ForAesGcm(());

impl HaveVaesAvx2ForAesGcm {
    pub(crate) fn check() -> Option<Self> {
        match has(AES_GCM_BASE | VPCLMULQDQ | VAES) {
            true => Some(Self(())),
            false => None,
        }
    }

    /// Vale's AES-GCM, for short messages, runs here too.
    pub(crate) fn avx_movbe(self) -> HaveAvxMovbeForAesGcm {
        HaveAvxMovbeForAesGcm(())
    }
}

/// Proof that the CPU has AVX and MOVBE, with AES-NI and PCLMULQDQ, which
/// Vale's AES-GCM uses.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvxMovbeForAesGcm(());

impl HaveAvxMovbeForAesGcm {
    pub(crate) fn check() -> Option<Self> {
        has(AES | PCLMULQDQ | SSSE3 | SSE41 | AVX | MOVBE).then_some(Self(()))
    }
}

/// Token type reflecting the check for CPU features needed for AVX512-ML-KEM
///
/// A value of this type is proof that the CPU dynamic feature check has happened.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx512ForMlKem(());

impl HaveAvx512ForMlKem {
    pub(crate) fn check() -> Option<Self> {
        // It runs inside rind's AVX2 ML-KEM. It needs no VL, which every CPU
        // with VBMI2 has, but asking for it keeps ML-KEM-768 off this sampler
        // wherever VG's AVX-512 key generation does not run.
        match has(AVX2_KERNELS | AVX512F | AVX512BW | AVX512VL | AVX512VBMI | AVX512VBMI2) {
            true => Some(Self(())),
            false => None,
        }
    }
}

/// Proof that the CPU has what pyca/verified-garbage's AVX-512 ML-KEM-768
/// runs: AVX-512 F, BW, and VL, with AVX and AVX2.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx512ForVgMlKem(());

impl HaveAvx512ForVgMlKem {
    pub(crate) fn check() -> Option<Self> {
        has(AVX | AVX2 | AVX512F | AVX512BW | AVX512VL).then_some(Self(()))
    }
}

/// Proof that the CPU has what RSA with AVX-512 IFMA runs: AVX-512 F, VL,
/// and IFMA, AVX, BMI2, and ADX, pyca/verified-garbage's `_FEATURES`, and the
/// DQ and BW that aws-lc's `CRYPTO_is_AVX512IFMA_capable` also asks for, as
/// its dual RSAZ runs `kmovb`. Every CPU with IFMA has them all.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx512ForRsa(());

impl HaveAvx512ForRsa {
    pub(crate) fn check() -> Option<Self> {
        has(AVX | AVX512F | AVX512DQ | AVX512BW | AVX512VL | AVX512IFMA | BMI2 | ADX)
            .then_some(Self(()))
    }

    /// Whether the CPU has AVX-512 FP16 too, as Intel's cores with two
    /// 512-bit multipliers do and AMD's Zen 4 and 5 do not: VG picks its
    /// 512-bit CRT for 2048-bit keys by it.
    pub(crate) fn fp16(self) -> bool {
        has(AVX512FP16)
    }
}

/// Proof that the CPU has what pyca/verified-garbage's X25519 and Ed25519
/// for AVX-512 IFMA run: AVX-512 F, VL, and IFMA, with AVX, AVX2, BMI1,
/// BMI2, and ADX, the union of their `_FEATURES`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveIfmaForCurve25519(());

impl HaveIfmaForCurve25519 {
    pub(crate) fn check() -> Option<Self> {
        has(AVX | AVX2 | BMI1 | BMI2 | ADX | AVX512F | AVX512VL | AVX512IFMA).then_some(Self(()))
    }
}

/// Token type reflecting the check for CPU features needed for SHA1 using SHA-NI,
/// and the SSSE3 and SSE4.1 its rounds also use
///
/// A value of this type is proof that the CPU dynamic feature check has happened.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSha1(());

impl HaveSha1 {
    pub(crate) fn check() -> Option<Self> {
        match has(SHA | SSSE3 | SSE41) {
            true => Some(Self(())),
            false => None,
        }
    }
}

/// Token type reflecting the check for CPU features needed for SHA256 using SHA-NI,
/// and the SSSE3 and SSE4.1 its rounds also use
///
/// A value of this type is proof that the CPU dynamic feature check has happened.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSha256(());

impl HaveSha256 {
    pub(crate) fn check() -> Option<Self> {
        match has(SHA | SSSE3 | SSE41) {
            true => Some(Self(())),
            false => None,
        }
    }
}

/// Proof that the CPU has AVX2, and the BMI1, BMI2, POPCNT, and SSSE3 that
/// rind's AVX2 kernels also use: ChaCha20, SHA-1, SHA-2, ML-KEM, the 4-way
/// Keccak-f, and the constant-time table selects.
///
/// Without it, aws-lc's SSSE3, AVX, or scalar routines, a portable port of
/// mlkem-native's ML-KEM arithmetic, scalar Keccak-f, and SSE2 selects run
/// instead.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx2(());

impl HaveAvx2 {
    pub(crate) fn check() -> Option<Self> {
        has(AVX2_KERNELS).then_some(Self(()))
    }
}

/// Proof that the CPU has AVX-512 F and VL, with what `HaveAvx2` proves:
/// what pyca/verified-garbage's "AVX-512 VL" ChaCha20 needs, on zmm vectors.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx512Vl(());

impl HaveAvx512Vl {
    pub(crate) fn check() -> Option<Self> {
        has(AVX2_KERNELS | AVX512F | AVX512VL).then_some(Self(()))
    }
}

/// Proof that the CPU has AVX-512 IFMA, with what `HaveAvx512Vl` proves:
/// what OpenSSL's base 2^44 Poly1305 needs (F, VL, and IFMA, the check
/// OpenSSL's `poly1305_init` makes), beside verified-garbage's AVX-512 VL
/// ChaCha20.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx512Ifma(());

impl HaveAvx512Ifma {
    pub(crate) fn check() -> Option<Self> {
        has(AVX2_KERNELS | AVX512F | AVX512VL | AVX512IFMA).then_some(Self(()))
    }
}

/// Proof that the CPU has AES-NI and PCLMULQDQ, and the SSSE3 and SSE4.1
/// their kernels also use: rind's AES-GCM and GHASH intrinsics, and aws-lc's
/// AES-CTR.
///
/// Without it, aws-lc's vpaes and SSSE3 GHASH, or ports of its SSE2 AES and
/// integer GHASH where the CPU also lacks SSSE3, run instead, and
/// `has_aes_hardware()` is false, as aws-lc's `EVP_has_aes_hardware` is.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAesHardware(());

impl HaveAesHardware {
    pub(crate) fn check() -> Option<Self> {
        has(AES | PCLMULQDQ | SSSE3 | SSE41).then_some(Self(()))
    }
}

/// Proof that the CPU has AVX, which aws-lc's AVX SHA routines use, and the
/// SSSE3 they also use.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx(());

impl HaveAvx {
    pub(crate) fn check() -> Option<Self> {
        has(AVX | SSSE3).then_some(Self(()))
    }
}

/// Proof that the CPU has SSSE3, which aws-lc's vpaes, GHASH, ChaCha20,
/// SHA-1, and SHA-256 routines for CPUs without AES-NI or AVX2 use.
///
/// Without it, aws-lc's integer SHA-1 and SHA-256 routines, ports of its
/// constant-time AES and GHASH in SSE2 and integer code, and HACL*'s ChaCha20
/// rounds run instead.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSsse3(());

impl HaveSsse3 {
    pub(crate) fn check() -> Option<Self> {
        has(SSSE3).then_some(Self(()))
    }
}

/// Proof that the CPU has SSE4.1, and the SSSE3 it implies, which aws-lc's
/// one-pass ChaCha20-Poly1305 uses.
///
/// Without it, ChaCha20 and Poly1305 run in separate passes.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSse41(());

impl HaveSse41 {
    pub(crate) fn check() -> Option<Self> {
        has(SSSE3 | SSE41).then_some(Self(()))
    }
}

/// Proof that the CPU has BMI2 and ADX, which s2n-bignum's fastest x86_64
/// routines use (`mulx`, `adcx`, and `adox`).
///
/// Without them, each routine's `_alt` twin runs instead.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveBmi2Adx(());

impl HaveBmi2Adx {
    pub(crate) fn check() -> Option<Self> {
        has(BMI2 | ADX).then_some(Self(()))
    }
}

/// Proof that the CPU has what pyca/verified-garbage's BMI2 and ADX P-256
/// routines run: BMI2, ADX, AVX, and AVX2.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAdxForVgP256(());

impl HaveAdxForVgP256 {
    pub(crate) fn check() -> Option<Self> {
        has(BMI2 | ADX | AVX | AVX2).then_some(Self(()))
    }
}

/// Proof that the CPU has what pyca/verified-garbage's AVX-512 IFMA P-256
/// ECDH and ECDSA verification run: AVX-512 F, VL, and IFMA, with what
/// [`HaveAdxForVgP256`] proves.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveIfmaForVgP256(());

impl HaveIfmaForVgP256 {
    pub(crate) fn check() -> Option<Self> {
        has(BMI2 | ADX | AVX | AVX2 | AVX512F | AVX512VL | AVX512IFMA).then_some(Self(()))
    }
}

/// Whether the CPU is Intel's, for code that is fastest on one vendor's cores.
pub(crate) fn is_intel() -> bool {
    has(INTEL)
}

const AES: u32 = 1 << 0;
const VAES: u32 = 1 << 1;
const PCLMULQDQ: u32 = 1 << 2;
const VPCLMULQDQ: u32 = 1 << 3;
const BMI2: u32 = 1 << 4;
const ADX: u32 = 1 << 5;
const POPCNT: u32 = 1 << 6;
const SSSE3: u32 = 1 << 7;
const AVX: u32 = 1 << 8;
const AVX2: u32 = 1 << 9;
const AVX512F: u32 = 1 << 10;
const AVX512BW: u32 = 1 << 11;
const AVX512VL: u32 = 1 << 12;
const AVX512VBMI: u32 = 1 << 13;
const AVX512VBMI2: u32 = 1 << 14;
const SHA: u32 = 1 << 15;
const SSE41: u32 = 1 << 16;
const MOVBE: u32 = 1 << 17;
const AVX512DQ: u32 = 1 << 18;
const AVX512IFMA: u32 = 1 << 19;
const BMI1: u32 = 1 << 20;
const AVX512FP16: u32 = 1 << 22;
const INTEL: u32 = 1 << 30;
/// What rind's AVX2 kernels use, for [`HaveAvx2`].
const AVX2_KERNELS: u32 = AVX | AVX2 | BMI1 | BMI2 | POPCNT | SSSE3;
/// What the AES-GCM kernels for wider vectors build on: the AVX2 ISA, AES-NI
/// and PCLMULQDQ for their key schedule and tail, and SSE4.1 and MOVBE for
/// Vale's AES-GCM, which short messages run without AVX-512. Every VAES CPU
/// has them all.
const AES_GCM_BASE: u32 = AES | PCLMULQDQ | SSSE3 | SSE41 | AVX | AVX2 | MOVBE;
const DETECTED: u32 = 1 << 31;

/// Whether the CPU has every feature in `wanted`.
#[inline]
fn has(wanted: u32) -> bool {
    features() & wanted == wanted
}

static FEATURES: AtomicU32 = AtomicU32::new(0);

/// The detected features, read once: `cpuid` is slow, and traps to the
/// hypervisor in a VM. Inlined, so a check is a load and a test, with the
/// first call's detection out of line.
#[inline]
fn features() -> u32 {
    match FEATURES.load(Ordering::Relaxed) {
        0 => detect_once(),
        features => features,
    }
}

#[cold]
#[inline(never)]
fn detect_once() -> u32 {
    let features = detect() | DETECTED;
    FEATURES.store(features, Ordering::Relaxed);
    features
}

/// The features rind tests for, with `std`'s name for each, which
/// `RIND_CPU_DISABLE_<name>` takes without its dots.
macro_rules! named {
    ($($bit:ident: $name:tt),+ $(,)?) => {
        const NAMED: &[(u32, &str)] = &[$(($bit, $name)),+];

        /// Those the target enables at compile time, which every CPU that
        /// runs the binary has, as `is_x86_feature_detected!` also reports.
        const ENABLED: u32 = 0 $(| if cfg!(target_feature = $name) { $bit } else { 0 })+;

        /// What `std` detects, which `detect` must match.
        #[cfg(test)]
        fn std_detected() -> u32 {
            0 $(| if is_x86_feature_detected!($name) { $bit } else { 0 })+
        }
    };
}

named! {
    AES: "aes",
    VAES: "vaes",
    PCLMULQDQ: "pclmulqdq",
    VPCLMULQDQ: "vpclmulqdq",
    BMI1: "bmi1",
    BMI2: "bmi2",
    ADX: "adx",
    POPCNT: "popcnt",
    SSSE3: "ssse3",
    SSE41: "sse4.1",
    AVX: "avx",
    AVX2: "avx2",
    AVX512F: "avx512f",
    AVX512DQ: "avx512dq",
    AVX512IFMA: "avx512ifma",
    AVX512BW: "avx512bw",
    AVX512VL: "avx512vl",
    AVX512VBMI: "avx512vbmi",
    AVX512VBMI2: "avx512vbmi2",
    AVX512FP16: "avx512fp16",
    SHA: "sha",
    MOVBE: "movbe",
}

fn detect() -> u32 {
    // Valgrind runs ADX instructions but hides them from `cpuid`
    // (https://bugs.kde.org/show_bug.cgi?id=494162), so `admin/ctgrind` builds
    // with this switch to check the ADX routines rather than their `_alt`
    // twins.
    // See UPSTREAM.md, "Valgrind hides ADX from `cpuid`".
    let valgrind = if option_env!("VALGRIND_BUG_494162").is_some() {
        ADX
    } else {
        0
    };
    let found = decode(registers()) | ENABLED | valgrind;
    let intel = if found & INTEL != 0 && !super::super::cpu_denied("intel") {
        INTEL
    } else {
        0
    };
    NAMED
        .iter()
        .filter(|&&(bit, name)| found & bit != 0 && !super::super::cpu_denied(name))
        .fold(intel, |features, &(bit, _)| features | bit)
}

/// The `cpuid` and `xgetbv` registers that name the features rind tests for.
#[derive(Clone, Copy, Default)]
struct Registers {
    intel: bool,
    /// Leaf 1's ECX, or zero where the CPU has no leaf 1.
    ecx1: u32,
    /// Leaf 7's EBX, ECX, and EDX, or zero where the CPU has no leaf 7.
    ebx7: u32,
    ecx7: u32,
    edx7: u32,
    /// XCR0, or `None` where the OS has not enabled `xgetbv`.
    xcr0: Option<u64>,
}

/// Reads the registers `decode` reads.
#[allow(unused_unsafe)]
fn registers() -> Registers {
    let mut found = Registers::default();
    // An SGX enclave cannot trust `cpuid`, so `std` reports nothing there.
    if cfg!(target_env = "sgx") {
        return found;
    }
    // `__cpuid` is safe from Rust 1.94 but `unsafe` on the 1.90 MSRV.
    // SAFETY: every x86_64 CPU has `cpuid`, and no leaf past the highest it
    // reports is read.
    let leaf0 = unsafe { __cpuid(0) };
    // "GenuineIntel", spread over ebx, edx, and ecx.
    found.intel = (leaf0.ebx, leaf0.edx, leaf0.ecx) == (0x756e_6547, 0x4965_6e69, 0x6c65_746e);
    if leaf0.eax >= 1 {
        // SAFETY: as above.
        found.ecx1 = unsafe { __cpuid(1) }.ecx;
    }
    if leaf0.eax >= 7 {
        // SAFETY: as above.
        let leaf7 = unsafe { __cpuid_count(7, 0) };
        (found.ebx7, found.ecx7, found.edx7) = (leaf7.ebx, leaf7.ecx, leaf7.edx);
    }
    // XSAVE, and OSXSAVE: the OS has enabled `xgetbv`.
    if found.ecx1 & (1 << 26 | 1 << 27) == 1 << 26 | 1 << 27 {
        // SAFETY: the CPU has XSAVE, and the OS has enabled it.
        found.xcr0 = Some(unsafe { _xgetbv(0) });
    }
    found
}

/// What the registers say the CPU has and the OS saves the state of, read
/// as `std`'s `is_x86_feature_detected!` reads them (its
/// `std_detect/src/detect/os/x86.rs`), so a hosted build picks the paths it
/// did with `std`, and a build without an OS can ask too: `cpuid` and
/// `xgetbv` need none. A kernel that never enabled the AVX or AVX-512 state
/// in XCR0 gets no AVX tier, rather than a fault on its first `vmovdqu`.
fn decode(r: Registers) -> u32 {
    let bit = |register: u32, at: u32| register >> at & 1 != 0;
    let mut features = 0;
    let mut set = |on: bool, feature: u32| {
        if on {
            features |= feature;
        }
    };
    set(r.intel, INTEL);
    set(bit(r.ecx1, 1), PCLMULQDQ);
    set(bit(r.ecx1, 9), SSSE3);
    set(bit(r.ecx1, 19), SSE41);
    set(bit(r.ecx1, 22), MOVBE);
    set(bit(r.ecx1, 23), POPCNT);
    set(bit(r.ecx1, 25), AES);
    set(bit(r.ebx7, 3), BMI1);
    set(bit(r.ebx7, 8), BMI2);
    set(bit(r.ebx7, 19), ADX);
    set(bit(r.ebx7, 29), SHA);
    set(bit(r.ecx7, 9), VAES);
    set(bit(r.ecx7, 10), VPCLMULQDQ);

    let xcr0 = r.xcr0.unwrap_or(0);
    // The OS saves the SSE and AVX state.
    if xcr0 & 0b110 == 0b110 {
        set(bit(r.ecx1, 28), AVX);
        set(bit(r.ebx7, 5), AVX2);
        // And the AVX-512 state. Rust's `avx512f` implies FMA and F16C,
        // which Intel does not promise with it, so `std` requires them.
        let (fma, f16c) = (bit(r.ecx1, 12), bit(r.ecx1, 29));
        if xcr0 & 0b1110_0000 == 0b1110_0000 && fma && f16c {
            set(bit(r.ebx7, 16), AVX512F);
            set(bit(r.ebx7, 17), AVX512DQ);
            set(bit(r.ebx7, 21), AVX512IFMA);
            set(bit(r.ebx7, 30), AVX512BW);
            set(bit(r.ebx7, 31), AVX512VL);
            set(bit(r.ecx7, 1), AVX512VBMI);
            set(bit(r.ecx7, 6), AVX512VBMI2);
            set(bit(r.edx7, 23), AVX512FP16);
        }
    }

    // Some Skylakes report BMI1 and BMI2 without them (Intel's erratum
    // SKL052); all of those lack AVX, so `std` drops both on Intel's CPUs
    // without it.
    if r.intel && features & AVX == 0 {
        features &= !(BMI1 | BMI2);
    }
    features
}

// --- Safe abstractions over common intrinsics operations ---

/// Prefetch both `table` and `table[stride]`
///
/// `table[stride]` may lie outside `table`: its address is computed with
/// wrapping arithmetic, and prefetching doesn't need a valid pointer.
#[target_feature(enable = "sse")]
#[inline]
pub(crate) fn prefetch<T>(table: &[T], stride: usize) {
    // `_mm_prefetch` is safe on newer Rust but `unsafe` on the 1.90 MSRV.
    #[allow(unused_unsafe)]
    // SAFETY: a prefetch never faults and is not architecturally visible.
    unsafe {
        _mm_prefetch(table.as_ptr().cast(), _MM_HINT_T0);
        _mm_prefetch(table.as_ptr().wrapping_add(stride).cast(), _MM_HINT_T0);
    }
}

/// The first CPU feature the FIPS module requires that this CPU lacks.
///
/// The module requires what every x86_64 server since Broadwell and Zen has,
/// so the paths for older CPUs, which no tested CPU runs, need no ACVP run of
/// their own: the SSE2 and vpaes AES, the integer and SSSE3 GHASH, and
/// s2n-bignum's `_alt` routines for CPUs without ADX.
#[cfg(rind_fips)]
pub(crate) fn missing_cpu_feature() -> Option<&'static str> {
    [
        (AES, "aes"),
        (PCLMULQDQ, "pclmulqdq"),
        (SSSE3, "ssse3"),
        (SSE41, "sse4.1"),
        (POPCNT, "popcnt"),
        (MOVBE, "movbe"),
        (AVX, "avx"),
        (AVX2, "avx2"),
        (BMI1, "bmi1"),
        (BMI2, "bmi2"),
        (ADX, "adx"),
    ]
    .into_iter()
    .find_map(|(bit, name)| (!has(bit)).then_some(name))
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::abi::call;

    #[test]
    fn abi() {
        let mut bytes = [0xffu8; 100];
        // SAFETY: `bytes` is 100 writable bytes, and every x86_64 CPU has
        // SSE2; AVX2 is checked.
        unsafe {
            call!(unsafe zero_bytes_sse2, bytes.as_mut_ptr(), 100);
            if is_x86_feature_detected!("avx2") {
                call!(unsafe zero_bytes_avx2, bytes.as_mut_ptr(), 100);
            }
        }
        assert_eq!(bytes, [0; 100]);
        let (a, b) = ([1u8; 37], [2u8; 37]);
        assert_ne!(call!(ct_compare_bytes, &a, &b), 0);
        assert_ne!(call!(ct_compare_16, &[1; 16], &[2; 16]), 0);
    }

    /// Whether std detects every feature named, less those `RIND_CPU_DISABLE_<id>`
    /// denies.
    macro_rules! available {
        ($($name:tt),+) => {
            true $(&& is_x86_feature_detected!($name) && !crate::low::cpu_denied($name))+
        };
    }

    /// The registers decode as `std` reads them on this host.
    #[test]
    fn detects_what_std_does() {
        assert_eq!((decode(registers()) | ENABLED) & !INTEL, std_detected());
    }

    /// Where each feature's bit is, and the registers `decode` needs before
    /// it reads any bit that hangs on AVX-512 support: the OS saving every
    /// vector state, and FMA and F16C.
    const FMA_F16C: u32 = 1 << 12 | 1 << 29;
    /// The registers `BITS` names.
    #[derive(Clone, Copy)]
    enum Leaf {
        Ecx1,
        Ebx7,
        Ecx7,
        Edx7,
    }

    impl Leaf {
        fn of(self, r: &mut Registers) -> &mut u32 {
            match self {
                Self::Ecx1 => &mut r.ecx1,
                Self::Ebx7 => &mut r.ebx7,
                Self::Ecx7 => &mut r.ecx7,
                Self::Edx7 => &mut r.edx7,
            }
        }
    }

    const BITS: &[(Leaf, u32, u32)] = &[
        (Leaf::Ecx1, 1, PCLMULQDQ),
        (Leaf::Ecx1, 9, SSSE3),
        (Leaf::Ecx1, 19, SSE41),
        (Leaf::Ecx1, 22, MOVBE),
        (Leaf::Ecx1, 23, POPCNT),
        (Leaf::Ecx1, 25, AES),
        (Leaf::Ecx1, 28, AVX),
        (Leaf::Ebx7, 3, BMI1),
        (Leaf::Ebx7, 5, AVX2),
        (Leaf::Ebx7, 8, BMI2),
        (Leaf::Ebx7, 16, AVX512F),
        (Leaf::Ebx7, 17, AVX512DQ),
        (Leaf::Ebx7, 19, ADX),
        (Leaf::Ebx7, 21, AVX512IFMA),
        (Leaf::Ebx7, 29, SHA),
        (Leaf::Ebx7, 30, AVX512BW),
        (Leaf::Ebx7, 31, AVX512VL),
        (Leaf::Ecx7, 1, AVX512VBMI),
        (Leaf::Ecx7, 6, AVX512VBMI2),
        (Leaf::Ecx7, 9, VAES),
        (Leaf::Ecx7, 10, VPCLMULQDQ),
        (Leaf::Edx7, 23, AVX512FP16),
    ];

    /// Each feature is read from its own bit, and from no other.
    #[test]
    fn decodes_each_bit() {
        let base = Registers {
            ecx1: FMA_F16C,
            xcr0: Some(u64::MAX),
            ..Registers::default()
        };
        assert_eq!(decode(base), 0);
        for &(leaf, at, feature) in BITS {
            let mut r = base;
            *leaf.of(&mut r) |= 1 << at;
            assert_eq!(decode(r), feature, "bit {at}");
        }
        assert_eq!(BITS.len(), NAMED.len());
    }

    /// The AVX features need the OS to save the AVX state, and the AVX-512
    /// ones its AVX-512 state, FMA, and F16C, as `std` requires.
    #[test]
    fn decodes_vector_features_only_where_the_os_saves_them() {
        let all = Registers {
            intel: false,
            ecx1: u32::MAX,
            ebx7: u32::MAX,
            ecx7: u32::MAX,
            edx7: u32::MAX,
            xcr0: Some(u64::MAX),
        };
        let named = NAMED.iter().fold(0, |all, &(bit, _)| all | bit);
        assert_eq!(decode(all), named);
        assert_eq!(decode(Registers { intel: true, ..all }), named | INTEL);

        let avx512 = AVX512F
            | AVX512DQ
            | AVX512IFMA
            | AVX512BW
            | AVX512VL
            | AVX512VBMI
            | AVX512VBMI2
            | AVX512FP16;
        let avx = AVX | AVX2 | avx512;
        for xcr0 in [None, Some(0), Some(0b010), Some(0b100), Some(!0b110)] {
            assert_eq!(decode(Registers { xcr0, ..all }), named & !avx, "{xcr0:?}");
        }
        for xcr0 in [0b110, 0b0110_0110, 0b1010_0110, 0b1100_0110] {
            let r = Registers {
                xcr0: Some(xcr0),
                ..all
            };
            assert_eq!(decode(r), named & !avx512, "{xcr0:#x}");
        }
        for missing in [1 << 12, 1 << 29] {
            let r = Registers {
                ecx1: !missing,
                ..all
            };
            assert_eq!(decode(r), named & !avx512);
        }
    }

    /// Intel's CPUs without AVX lose BMI1 and BMI2 (erratum SKL052); other
    /// vendors' keep them.
    #[test]
    fn drops_bmi_on_intel_without_avx() {
        let r = Registers {
            ebx7: 1 << 3 | 1 << 8,
            ..Registers::default()
        };
        assert_eq!(decode(r), BMI1 | BMI2);
        assert_eq!(decode(Registers { intel: true, ..r }), INTEL);
        let avx = Registers {
            intel: true,
            ecx1: 1 << 28,
            xcr0: Some(0b110),
            ..r
        };
        assert_eq!(decode(avx), INTEL | AVX | BMI1 | BMI2);
    }

    // Each feature has a bit of its own, so no check can pass for one
    // feature because the CPU has another. A CPU with every feature cannot
    // show that by itself.
    #[test]
    fn features_have_distinct_bits() {
        let bits = [
            AES,
            VAES,
            PCLMULQDQ,
            VPCLMULQDQ,
            BMI2,
            ADX,
            POPCNT,
            SSSE3,
            AVX,
            AVX2,
            AVX512F,
            AVX512BW,
            AVX512VL,
            AVX512VBMI,
            AVX512VBMI2,
            SHA,
            SSE41,
            MOVBE,
            AVX512DQ,
            AVX512IFMA,
            BMI1,
            AVX512FP16,
            INTEL,
            DETECTED,
        ];
        let all = bits.iter().fold(0, |all, bit| {
            assert!(bit.is_power_of_two());
            all | bit
        });
        assert_eq!(all.count_ones() as usize, bits.len());
    }

    // Each check names the features its kernels need, which `cpuid` reports
    // independently of the bits `detect` packs them into.
    #[test]
    fn checks_need_their_features() {
        let adx = (is_x86_feature_detected!("adx") || option_env!("VALGRIND_BUG_494162").is_some())
            && !crate::low::cpu_denied("adx");
        let gcm = available!(
            "aes",
            "pclmulqdq",
            "ssse3",
            "sse4.1",
            "avx",
            "avx2",
            "movbe"
        );
        let checks = [
            (
                HaveAvx512ForAesGcm::check().is_some(),
                gcm && available!("avx512f", "avx512bw", "avx512vl", "vpclmulqdq", "vaes"),
            ),
            (
                HaveVaesAvx2ForAesGcm::check().is_some(),
                gcm && available!("vpclmulqdq", "vaes"),
            ),
            (
                HaveAvxMovbeForAesGcm::check().is_some(),
                available!("aes", "pclmulqdq", "ssse3", "sse4.1", "avx", "movbe"),
            ),
            (
                HaveAvx512ForMlKem::check().is_some(),
                available!("avx", "avx2", "bmi1", "bmi2", "popcnt", "ssse3")
                    && available!(
                        "avx512f",
                        "avx512bw",
                        "avx512vl",
                        "avx512vbmi",
                        "avx512vbmi2"
                    ),
            ),
            (
                HaveAvx512ForVgMlKem::check().is_some(),
                available!("avx", "avx2", "avx512f", "avx512bw", "avx512vl"),
            ),
            (
                HaveAvx512ForRsa::check().is_some(),
                adx && available!(
                    "avx",
                    "avx512f",
                    "avx512dq",
                    "avx512bw",
                    "avx512vl",
                    "avx512ifma",
                    "bmi2"
                ),
            ),
            (
                HaveAvx512ForRsa::check().is_some_and(HaveAvx512ForRsa::fp16),
                adx && available!(
                    "avx",
                    "avx512f",
                    "avx512dq",
                    "avx512bw",
                    "avx512vl",
                    "avx512ifma",
                    "bmi2"
                ) && available!("avx512fp16"),
            ),
            (
                HaveIfmaForCurve25519::check().is_some(),
                adx && available!(
                    "avx",
                    "avx2",
                    "bmi1",
                    "bmi2",
                    "avx512f",
                    "avx512vl",
                    "avx512ifma"
                ),
            ),
            (
                HaveSha1::check().is_some(),
                available!("sha", "ssse3", "sse4.1"),
            ),
            (
                HaveSha256::check().is_some(),
                available!("sha", "ssse3", "sse4.1"),
            ),
            (
                HaveAvx2::check().is_some(),
                available!("avx", "avx2", "bmi1", "bmi2", "popcnt", "ssse3"),
            ),
            (
                HaveAvx512Vl::check().is_some(),
                available!("avx", "avx2", "bmi1", "bmi2", "popcnt", "ssse3")
                    && available!("avx512f", "avx512vl"),
            ),
            (
                HaveAesHardware::check().is_some(),
                available!("aes", "pclmulqdq", "ssse3", "sse4.1"),
            ),
            (HaveAvx::check().is_some(), available!("avx", "ssse3")),
            (HaveSsse3::check().is_some(), available!("ssse3")),
            (HaveSse41::check().is_some(), available!("ssse3", "sse4.1")),
            (HaveBmi2Adx::check().is_some(), available!("bmi2") && adx),
            (
                HaveAdxForVgP256::check().is_some(),
                adx && available!("bmi2", "avx", "avx2"),
            ),
            (
                HaveIfmaForVgP256::check().is_some(),
                adx && available!("bmi2", "avx", "avx2")
                    && available!("avx512f", "avx512vl", "avx512ifma"),
            ),
        ];
        for (i, (check, expected)) in checks.into_iter().enumerate() {
            assert_eq!(check, expected, "check {i}");
        }

        // SAFETY: every x86_64 CPU has `cpuid`.
        #[allow(unused_unsafe)]
        let id = unsafe { __cpuid(0) };
        let vendor = [id.ebx, id.edx, id.ecx].map(u32::to_le_bytes);
        assert_eq!(
            is_intel(),
            vendor.as_flattened() == b"GenuineIntel" && !crate::low::cpu_denied("intel")
        );
    }

    // CI runs the suite again with features denied, and names the path each
    // run expects, so no run silently tests only the fastest one.
    #[test]
    fn detects_the_expected_cpu() {
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_BMI2_ADX") {
            assert_eq!(HaveBmi2Adx::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AVX2") {
            assert_eq!(HaveAvx2::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AVX") {
            assert_eq!(HaveAvx::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AES_HARDWARE") {
            assert_eq!(HaveAesHardware::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_SSSE3") {
            assert_eq!(HaveSsse3::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_SSE41") {
            assert_eq!(HaveSse41::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_SHA") {
            assert_eq!(HaveSha256::check().is_some(), expected == "1");
            assert_eq!(HaveSha1::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_VAES_AES_GCM") {
            assert_eq!(HaveVaesAvx2ForAesGcm::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AVX_MOVBE_AES_GCM") {
            assert_eq!(HaveAvxMovbeForAesGcm::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AVX512_AES_GCM") {
            assert_eq!(HaveAvx512ForAesGcm::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AVX512_ML_KEM") {
            assert_eq!(HaveAvx512ForMlKem::check().is_some(), expected == "1");
        }
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AVX512_RSA") {
            assert_eq!(HaveAvx512ForRsa::check().is_some(), expected == "1");
        }
        // Every CPU and SDE model with AVX-512 IFMA has the rest of what
        // either needs, so RSA's tiers name X25519's and Ed25519's too.
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_AVX512_RSA") {
            assert_eq!(HaveIfmaForCurve25519::check().is_some(), expected == "1");
        }
    }
}
