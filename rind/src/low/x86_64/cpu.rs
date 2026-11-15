// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::arch::x86_64::*;
use core::sync::atomic::{AtomicU8, AtomicU32, Ordering};

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
        // It runs inside rind's AVX2 ML-KEM.
        match has(AVX2_KERNELS | AVX512F | AVX512BW | AVX512VBMI | AVX512VBMI2) {
            true => Some(Self(())),
            false => None,
        }
    }
}

/// Proof that the CPU has AVX-512 IFMA, with the F, DQ, BW, and VL that
/// aws-lc's `CRYPTO_is_AVX512IFMA_capable` also asks for, and BMI2: what
/// aws-lc's dual RSAZ exponentiation runs.
///
/// Without it, RSA's CRT runs its two exponentiations one at a time.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveAvx512ForRsa(());

impl HaveAvx512ForRsa {
    pub(crate) fn check() -> Option<Self> {
        has(AVX512F | AVX512DQ | AVX512IFMA | AVX512BW | AVX512VL | BMI2).then_some(Self(()))
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

/// Proof that the CPU has the SHA512 instructions, and the AVX2 that
/// OpenSSL's routine for them also uses.
#[derive(Clone, Copy, Debug)]
pub(crate) struct HaveSha512(());

impl HaveSha512 {
    pub(crate) fn check() -> Option<Self> {
        has(SHA512 | AVX | AVX2).then_some(Self(()))
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

macro_rules! cached_tokens {
    ($($name:ident),+ $(,)?) => {$(
        impl $name {
            /// Rebuilds a token the SHA path cache already proved.
            pub(super) const fn cached() -> Self {
                Self(())
            }
        }
    )+};
}

cached_tokens!(
    HaveSha1, HaveSha256, HaveAvx, HaveAvx2, HaveSsse3, HaveSha512
);

/// Remembers a non-zero `pick` in `slot`. `0` means empty, so `pick` must
/// not return it. Concurrent callers may all run `pick`; it has to agree.
pub(super) fn cached_tag(slot: &AtomicU8, pick: impl FnOnce() -> u8) -> u8 {
    match slot.load(Ordering::Acquire) {
        0 => {
            let tag = pick();
            // Zero means empty. A zero tag would be read as a miss forever.
            assert_ne!(tag, 0, "a cached feature tag is never zero");
            match slot.compare_exchange(0, tag, Ordering::Release, Ordering::Acquire) {
                Ok(_) => tag,
                Err(stored) => stored,
            }
        }
        tag => tag,
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
const SHA512: u32 = 1 << 21;
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

/// CPUID leaves the bare-metal detector reads. `xcr0` is `None` when
/// `XGETBV` would raise `#UD`, because XSAVE or OSXSAVE is clear.
#[cfg(any(test, target_os = "none"))]
struct CpuidLeaves {
    intel: bool,
    leaf1_ecx: u32,
    /// Leaf 7, subleaf 0.
    leaf7_ebx: u32,
    leaf7_ecx: u32,
    /// Leaf 7, subleaf 1, EAX. SHA512 is reported here, not in subleaf 0.
    leaf7_sub1_eax: u32,
    xcr0: Option<u32>,
}

#[cfg(any(test, target_os = "none"))]
fn read_cpuid_leaves() -> CpuidLeaves {
    // `__cpuid` is safe from Rust 1.94 but `unsafe` on the 1.90 MSRV.
    #[allow(unused_unsafe)]
    // SAFETY: every x86_64 CPU implements CPUID.
    let id = unsafe { __cpuid(0) };
    let intel = (id.ebx, id.edx, id.ecx) == (0x756e_6547, 0x4965_6e69, 0x6c65_746e);
    if id.eax < 1 {
        return CpuidLeaves {
            intel,
            leaf1_ecx: 0,
            leaf7_ebx: 0,
            leaf7_ecx: 0,
            leaf7_sub1_eax: 0,
            xcr0: None,
        };
    }
    // `__cpuid` is safe from Rust 1.94 but `unsafe` on the 1.90 MSRV.
    #[allow(unused_unsafe)]
    // SAFETY: every x86_64 CPU implements CPUID. Leaf 1 exists here.
    let leaf1 = unsafe { __cpuid(1) };
    let (leaf7_ebx, leaf7_ecx, leaf7_sub1_eax) = if id.eax >= 7 {
        #[allow(unused_unsafe)]
        // SAFETY: CPUID reported a maximum leaf of at least 7.
        let leaf7 = unsafe { __cpuid(7) };
        #[allow(unused_unsafe)]
        // SAFETY: as above. Subleaf 1 is zero when the CPU does not have it.
        let sub1 = unsafe { __cpuid_count(7, 1) };
        (leaf7.ebx, leaf7.ecx, sub1.eax)
    } else {
        (0, 0, 0)
    };
    CpuidLeaves {
        intel,
        leaf1_ecx: leaf1.ecx,
        leaf7_ebx,
        leaf7_ecx,
        leaf7_sub1_eax,
        xcr0: os_xcr0(leaf1.ecx),
    }
}

#[cfg(any(test, target_os = "none"))]
fn os_xcr0(leaf1_ecx: u32) -> Option<u32> {
    const XSAVE: u32 = 1 << 26;
    const OSXSAVE: u32 = 1 << 27;
    if leaf1_ecx & (XSAVE | OSXSAVE) != XSAVE | OSXSAVE {
        return None;
    }
    // SAFETY: CPUID reports XSAVE and OSXSAVE, so XGETBV of XCR0 does not
    // raise #UD. The features below use only the low 32 bits of XCR0.
    let xcr0 = unsafe { _xgetbv(0) };
    Some((xcr0 & 0xffff_ffff) as u32)
}

/// The same bits `is_x86_feature_detected!` would set for the features rind
/// asks about, from CPUID and XCR0, with no OS and no `std`.
///
/// AVX, AVX2, AVX-512, and SHA512 need the XSAVE and OSXSAVE CPUID bits and
/// the matching XCR0 bits: without XSAVE the OS cannot have enabled that
/// state, so a present `xcr0` is ignored. AVX-512 also needs FMA and F16C,
/// which Rust's detector requires because its assembler treats `avx512f` as
/// implying them. Intel's Skylake erratum SKL052 reports BMI1 and BMI2 on
/// parts that do not implement them and do not have AVX; those bits are
/// cleared, as in std.
#[cfg(any(test, target_os = "none"))]
fn feature_bits(leaves: CpuidLeaves) -> u32 {
    let bit = |reg: u32, index: u32| reg & (1 << index) != 0;
    let xcr0 = leaves.xcr0.unwrap_or(0);
    // std reads XCR0 only when both XSAVE and OSXSAVE are set. An `xcr0`
    // without those bits did not come from a kernel that enabled the state.
    let xsave = (1 << 26) | (1 << 27);
    let os_state = leaves.xcr0.is_some() && (leaves.leaf1_ecx & xsave) == xsave;
    let os_avx = os_state && xcr0 & 6 == 6;
    let os_avx512 = os_avx && xcr0 & 0xe0 == 0xe0;
    let f16c = bit(leaves.leaf1_ecx, 29);
    let fma = os_avx && bit(leaves.leaf1_ecx, 12);
    let avx512 = os_avx512 && f16c && fma;

    let mut bits = 0u32;
    if bit(leaves.leaf1_ecx, 25) {
        bits |= AES;
    }
    if bit(leaves.leaf1_ecx, 1) {
        bits |= PCLMULQDQ;
    }
    if bit(leaves.leaf1_ecx, 9) {
        bits |= SSSE3;
    }
    if bit(leaves.leaf1_ecx, 19) {
        bits |= SSE41;
    }
    if bit(leaves.leaf1_ecx, 22) {
        bits |= MOVBE;
    }
    if bit(leaves.leaf1_ecx, 23) {
        bits |= POPCNT;
    }
    if bit(leaves.leaf7_ebx, 19) {
        bits |= ADX;
    }
    if bit(leaves.leaf7_ebx, 29) {
        bits |= SHA;
    }
    if bit(leaves.leaf7_ebx, 3) {
        bits |= BMI1;
    }
    if bit(leaves.leaf7_ebx, 8) {
        bits |= BMI2;
    }
    if bit(leaves.leaf7_ecx, 9) {
        bits |= VAES;
    }
    if bit(leaves.leaf7_ecx, 10) {
        bits |= VPCLMULQDQ;
    }
    if os_avx {
        if bit(leaves.leaf1_ecx, 28) {
            bits |= AVX;
        }
        if bit(leaves.leaf7_ebx, 5) {
            bits |= AVX2;
        }
        if bit(leaves.leaf7_sub1_eax, 0) {
            bits |= SHA512;
        }
    }
    if avx512 {
        if bit(leaves.leaf7_ebx, 16) {
            bits |= AVX512F;
        }
        if bit(leaves.leaf7_ebx, 17) {
            bits |= AVX512DQ;
        }
        if bit(leaves.leaf7_ebx, 21) {
            bits |= AVX512IFMA;
        }
        if bit(leaves.leaf7_ebx, 30) {
            bits |= AVX512BW;
        }
        if bit(leaves.leaf7_ebx, 31) {
            bits |= AVX512VL;
        }
        if bit(leaves.leaf7_ecx, 1) {
            bits |= AVX512VBMI;
        }
        if bit(leaves.leaf7_ecx, 6) {
            bits |= AVX512VBMI2;
        }
    }
    if leaves.intel && bits & AVX == 0 {
        bits &= !(BMI1 | BMI2);
    }
    if leaves.intel {
        bits |= INTEL;
    }
    bits
}

#[cfg(target_os = "none")]
fn detect() -> u32 {
    // No `RIND_CPU_DISABLE_*` here: bare metal has no environment to read.
    feature_bits(read_cpuid_leaves())
}

#[cfg(not(target_os = "none"))]
fn detect() -> u32 {
    macro_rules! detect {
        ($name:tt, $bit:expr) => {
            if test_toggle($name, is_x86_feature_detected!($name)) {
                $bit
            } else {
                0
            }
        };
    }

    // "GenuineIntel", spread over ebx, edx, and ecx.
    // `__cpuid` is safe from Rust 1.94 but `unsafe` on the 1.90 MSRV.
    #[allow(unused_unsafe)]
    // SAFETY: every x86_64 CPU has `cpuid`.
    let id = unsafe { __cpuid(0) };
    let intel = (id.ebx, id.edx, id.ecx) == (0x756e_6547, 0x4965_6e69, 0x6c65_746e);

    // Valgrind runs ADX instructions but hides them from `cpuid`
    // (https://bugs.kde.org/show_bug.cgi?id=494162), so `admin/ctgrind` builds
    // with this switch to check the ADX routines rather than their `_alt`
    // twins.
    // See UPSTREAM.md, "Valgrind hides ADX from `cpuid`".
    let adx = is_x86_feature_detected!("adx") || option_env!("VALGRIND_BUG_494162").is_some();

    (if test_toggle("intel", intel) {
        INTEL
    } else {
        0
    }) | (if test_toggle("adx", adx) { ADX } else { 0 })
        | detect!("aes", AES)
        | detect!("vaes", VAES)
        | detect!("pclmulqdq", PCLMULQDQ)
        | detect!("vpclmulqdq", VPCLMULQDQ)
        | detect!("bmi1", BMI1)
        | detect!("bmi2", BMI2)
        | detect!("popcnt", POPCNT)
        | detect!("ssse3", SSSE3)
        | detect!("sse4.1", SSE41)
        | detect!("avx", AVX)
        | detect!("avx2", AVX2)
        | detect!("avx512f", AVX512F)
        | detect!("avx512dq", AVX512DQ)
        | detect!("avx512ifma", AVX512IFMA)
        | detect!("avx512bw", AVX512BW)
        | detect!("avx512vl", AVX512VL)
        | detect!("avx512vbmi", AVX512VBMI)
        | detect!("avx512vbmi2", AVX512VBMI2)
        | detect!("sha", SHA)
        | detect!("sha512", SHA512)
        | detect!("movbe", MOVBE)
}

#[cfg(all(not(target_os = "none"), not(any(debug_assertions, rind_cpu_disable))))]
fn test_toggle(_id: &str, detected: bool) -> bool {
    detected
}

/// Lets a debug build deny a feature with `RIND_CPU_DISABLE_<id>`, so a CPU
/// with it also tests the code for one without. `--cfg rind_cpu_disable`
/// does the same for a release build, so benches and ctgrind time and check
/// the code that ships; only `RUSTFLAGS` sets it, never a dependent crate.
/// The variable drops the dot from `sse4.1`, since shells drop variables
/// whose names have one. Bare metal has no environment to read.
#[cfg(all(not(target_os = "none"), any(debug_assertions, rind_cpu_disable)))]
fn test_toggle(id: &str, detected: bool) -> bool {
    if std::env::var(format!("RIND_CPU_DISABLE_{}", id.replace('.', ""))).is_ok() {
        // The FIPS module honours the mask in its release build, where its
        // caller's stdout is not its own.
        #[cfg(not(rind_fips))]
        println!("DEBUG: denying cpuid {id:?}");
        false
    } else {
        detected
    }
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

    /// Whether std detects every feature named, less those `test_toggle`
    /// denies.
    macro_rules! available {
        ($($name:tt),+) => {
            true $(&& is_x86_feature_detected!($name) && !denied($name))+
        };
    }

    fn denied(name: &str) -> bool {
        cfg!(any(debug_assertions, rind_cpu_disable))
            && std::env::var(format!("RIND_CPU_DISABLE_{}", name.replace('.', ""))).is_ok()
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
            SHA512,
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
            && !denied("adx");
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
                    && available!("avx512f", "avx512bw", "avx512vbmi", "avx512vbmi2"),
            ),
            (
                HaveAvx512ForRsa::check().is_some(),
                available!(
                    "avx512f",
                    "avx512dq",
                    "avx512ifma",
                    "avx512bw",
                    "avx512vl",
                    "bmi2"
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
                HaveSha512::check().is_some(),
                available!("sha512", "avx", "avx2"),
            ),
            (
                HaveAesHardware::check().is_some(),
                available!("aes", "pclmulqdq", "ssse3", "sse4.1"),
            ),
            (HaveAvx::check().is_some(), available!("avx", "ssse3")),
            (HaveSsse3::check().is_some(), available!("ssse3")),
            (HaveSse41::check().is_some(), available!("ssse3", "sse4.1")),
            (HaveBmi2Adx::check().is_some(), available!("bmi2") && adx),
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
            vendor.as_flattened() == b"GenuineIntel" && !denied("intel")
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
        if let Some(expected) = std::env::var_os("RIND_TEST_X86_SHA512") {
            assert_eq!(HaveSha512::check().is_some(), expected == "1");
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
    }

    fn leaves(
        intel: bool,
        leaf1_ecx: u32,
        leaf7_ebx: u32,
        leaf7_ecx: u32,
        leaf7_sub1_eax: u32,
        xcr0: Option<u32>,
    ) -> CpuidLeaves {
        CpuidLeaves {
            intel,
            leaf1_ecx,
            leaf7_ebx,
            leaf7_ecx,
            leaf7_sub1_eax,
            xcr0,
        }
    }

    /// This host's CPUID agrees with std, which is what a hosted build runs.
    #[test]
    fn bare_metal_detection_matches_std() {
        let bits = feature_bits(read_cpuid_leaves());
        assert_eq!(bits & AES != 0, is_x86_feature_detected!("aes"));
        assert_eq!(bits & VAES != 0, is_x86_feature_detected!("vaes"));
        assert_eq!(bits & PCLMULQDQ != 0, is_x86_feature_detected!("pclmulqdq"));
        assert_eq!(
            bits & VPCLMULQDQ != 0,
            is_x86_feature_detected!("vpclmulqdq")
        );
        assert_eq!(bits & BMI1 != 0, is_x86_feature_detected!("bmi1"));
        assert_eq!(bits & BMI2 != 0, is_x86_feature_detected!("bmi2"));
        assert_eq!(bits & ADX != 0, is_x86_feature_detected!("adx"));
        assert_eq!(bits & POPCNT != 0, is_x86_feature_detected!("popcnt"));
        assert_eq!(bits & SSSE3 != 0, is_x86_feature_detected!("ssse3"));
        assert_eq!(bits & AVX != 0, is_x86_feature_detected!("avx"));
        assert_eq!(bits & AVX2 != 0, is_x86_feature_detected!("avx2"));
        assert_eq!(bits & AVX512F != 0, is_x86_feature_detected!("avx512f"));
        assert_eq!(bits & AVX512DQ != 0, is_x86_feature_detected!("avx512dq"));
        assert_eq!(
            bits & AVX512IFMA != 0,
            is_x86_feature_detected!("avx512ifma")
        );
        assert_eq!(bits & AVX512BW != 0, is_x86_feature_detected!("avx512bw"));
        assert_eq!(bits & AVX512VL != 0, is_x86_feature_detected!("avx512vl"));
        assert_eq!(
            bits & AVX512VBMI != 0,
            is_x86_feature_detected!("avx512vbmi")
        );
        assert_eq!(
            bits & AVX512VBMI2 != 0,
            is_x86_feature_detected!("avx512vbmi2")
        );
        assert_eq!(bits & SHA != 0, is_x86_feature_detected!("sha"));
        assert_eq!(bits & SSE41 != 0, is_x86_feature_detected!("sse4.1"));
        assert_eq!(bits & MOVBE != 0, is_x86_feature_detected!("movbe"));
        assert_eq!(bits & SHA512 != 0, is_x86_feature_detected!("sha512"));
    }

    #[test]
    fn avx_requires_osxsave_and_xcr0() {
        const XSAVE: u32 = 1 << 26;
        const OSXSAVE: u32 = 1 << 27;
        const AVX_BIT: u32 = 1 << 28;
        let ecx = XSAVE | OSXSAVE | AVX_BIT;
        assert_eq!(feature_bits(leaves(false, ecx, 0, 0, 0, None)) & AVX, 0);
        assert_eq!(
            feature_bits(leaves(false, ecx, 0, 0, 0, Some(0x2))) & AVX,
            0
        );
        assert_ne!(
            feature_bits(leaves(false, ecx, 0, 0, 0, Some(0x6))) & AVX,
            0
        );
        // The AVX feature bit without XSAVE still cannot touch YMM.
        assert_eq!(
            feature_bits(leaves(false, AVX_BIT, 0, 0, 0, Some(0x6))) & AVX,
            0
        );
    }

    #[test]
    fn intel_without_avx_drops_bmi() {
        const BMI1_BIT: u32 = 1 << 3;
        const BMI2_BIT: u32 = 1 << 8;
        let bits = feature_bits(leaves(true, 0, BMI1_BIT | BMI2_BIT, 0, 0, None));
        assert_eq!(bits & (BMI1 | BMI2), 0);
        assert_ne!(bits & INTEL, 0);
        let bits = feature_bits(leaves(false, 0, BMI1_BIT | BMI2_BIT, 0, 0, None));
        assert_eq!(bits & (BMI1 | BMI2), BMI1 | BMI2);
        assert_eq!(bits & INTEL, 0);
    }

    #[test]
    fn avx512_needs_os_state_fma_and_f16c() {
        const XSAVE: u32 = 1 << 26;
        const OSXSAVE: u32 = 1 << 27;
        const AVX_BIT: u32 = 1 << 28;
        const FMA: u32 = 1 << 12;
        const F16C: u32 = 1 << 29;
        const AVX2_BIT: u32 = 1 << 5;
        const AVX512F_BIT: u32 = 1 << 16;
        let ready = XSAVE | OSXSAVE | AVX_BIT | FMA | F16C;
        let xcr = Some(0x6 | 0xe0);
        assert_ne!(
            feature_bits(leaves(false, ready, AVX512F_BIT | AVX2_BIT, 0, 0, xcr)) & AVX512F,
            0
        );
        let no_fma = XSAVE | OSXSAVE | AVX_BIT | F16C;
        assert_eq!(
            feature_bits(leaves(false, no_fma, AVX512F_BIT, 0, 0, xcr)) & AVX512F,
            0
        );
        assert_eq!(
            feature_bits(leaves(false, ready, AVX512F_BIT, 0, 0, Some(0x6))) & AVX512F,
            0
        );
    }

    #[test]
    fn sha512_needs_avx_os_support() {
        const XSAVE: u32 = 1 << 26;
        const OSXSAVE: u32 = 1 << 27;
        const AVX_BIT: u32 = 1 << 28;
        let ecx = XSAVE | OSXSAVE | AVX_BIT;
        assert_eq!(
            feature_bits(leaves(false, ecx, 0, 0, 1, Some(0x2))) & SHA512,
            0
        );
        assert_ne!(
            feature_bits(leaves(false, ecx, 0, 0, 1, Some(0x6))) & SHA512,
            0
        );
    }

    #[test]
    fn aes_ignores_xcr0() {
        const AES_BIT: u32 = 1 << 25;
        assert_ne!(feature_bits(leaves(false, AES_BIT, 0, 0, 0, None)) & AES, 0);
    }
}
