// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! AES-GCM on VAES and VPCLMULQDQ, with BoringSSL's `aes-gcm-avx2-x86_64` and
//! `aes-gcm-avx512-x86_64` kernels, imported by `admin/import-boringssl`.
//!
//! Only the AVX2 key setup, `gcm_init_vpclmulqdq_avx2`, is formally verified
//! (`proofs/Rind/X86_64/GcmInitAvx2.lean`). The rest's correctness rests on
//! its use and testing in BoringSSL and Linux, and on rind's tests of it
//! against the portable GHASH, Wycheproof, and aws-lc-rs. Both kernels
//! support in-place use.

use core::arch::x86_64::*;

use super::aes::HwKey;
use super::cpu::{HaveAvx512ForAesGcm, HaveVaesAvx2ForAesGcm};
use super::ghash::Ghash;

/// Which kernel runs, decided once from the CPU's features.
#[derive(Clone, Copy)]
enum Width {
    /// 256-bit vectors, for VAES cores without AVX-512.
    Avx2(HaveVaesAvx2ForAesGcm),
    /// 512-bit vectors.
    Avx512(HaveAvx512ForAesGcm),
}

/// Powers of a GHASH key: BoringSSL's `u128 Htable[16]`, as its kernel lays
/// them out.
#[repr(C, align(64))]
struct Htable([[u64; 2]; 16]);

/// A BoringSSL AES-GCM kernel, with the GHASH key it was made for.
pub(crate) struct VaesKernel {
    htable: Htable,
    width: Width,
}

impl VaesKernel {
    /// The 256-bit kernel, for the GHASH key `h`.
    pub(crate) fn avx2(h: u128, token: HaveVaesAvx2ForAesGcm) -> Self {
        Self::new(h, Width::Avx2(token))
    }

    /// The 512-bit kernel, for the GHASH key `h`.
    pub(crate) fn avx512(h: u128, token: HaveAvx512ForAesGcm) -> Self {
        Self::new(h, Width::Avx512(token))
    }

    fn new(h: u128, width: Width) -> Self {
        let words = [(h >> 64) as u64, h as u64];
        let mut htable = Htable([[0; 2]; 16]);
        // SAFETY: `htable` is an `Htable` and `words` two words. The token
        // proves the CPU has the kernel's features.
        unsafe {
            match width {
                Width::Avx2(_) => {
                    asm_call!(unsafe extern "sysv64" gcm_init_vpclmulqdq_avx2(&mut htable, &words))
                }
                Width::Avx512(_) => {
                    asm_call!(unsafe extern "sysv64" gcm_init_vpclmulqdq_avx512(&mut htable, &words))
                }
            }
        }
        Self { htable, width }
    }

    /// The GHASH key's powers in its table, H^n down to H^1: H^8 for the
    /// 256-bit kernel, after which its table holds their Karatsuba terms,
    /// and H^16 for the 512-bit one.
    pub(crate) fn powers(&self) -> &[__m128i] {
        let n = match self.width {
            Width::Avx2(_) => 8,
            Width::Avx512(_) => 16,
        };
        // SAFETY: an `Htable` is 16 blocks of 16 bytes, aligned for
        // `__m128i`, and every bit pattern is a valid `__m128i`.
        let blocks: &[__m128i; 16] = unsafe { &*(&raw const self.htable).cast() };
        &blocks[..n]
    }

    /// Encrypts (if `ENC`) or decrypts `inout` in place, from the counter
    /// block after `y0`, folding the ciphertext into `ghash`.
    pub(crate) fn cipher<const ENC: bool>(
        &self,
        key: &HwKey,
        y0: &[u8; 16],
        ghash: &mut Ghash<'_>,
        inout: &mut [u8],
    ) {
        let counter = add_to_counter(y0, 1);

        // The AVX2 kernel takes only whole blocks, so a partial last one is
        // done here; the AVX-512 kernel masks it.
        let bulk = match self.width {
            Width::Avx2(_) => inout.len() & !15,
            Width::Avx512(_) => inout.len(),
        };
        let (bulk, partial) = inout.split_at_mut(bulk);

        if !bulk.is_empty() {
            let mut xi = ghash.xi();
            let (inout, len, key, htable, xi_ptr) = (
                bulk.as_mut_ptr(),
                bulk.len(),
                key.as_aes_key(),
                &self.htable,
                &mut xi,
            );
            // SAFETY: `inout` is `len` readable and writable bytes, which the
            // kernels support in place, `key` is an `AES_KEY`, and the token
            // proves the CPU has the kernel's features. `len` is a multiple of
            // 16 for the AVX2 kernel.
            unsafe {
                match (self.width, ENC) {
                    (Width::Avx2(_), true) => {
                        asm_call!(unsafe extern "sysv64" aes_gcm_enc_update_vaes_avx2(
                            inout, inout, len, key, &counter, htable, xi_ptr,
                        ))
                    }
                    (Width::Avx2(_), false) => {
                        asm_call!(unsafe extern "sysv64" aes_gcm_dec_update_vaes_avx2(
                            inout, inout, len, key, &counter, htable, xi_ptr,
                        ))
                    }
                    (Width::Avx512(_), true) => {
                        asm_call!(unsafe extern "sysv64" aes_gcm_enc_update_vaes_avx512(
                            inout, inout, len, key, &counter, htable, xi_ptr,
                        ))
                    }
                    (Width::Avx512(_), false) => {
                        asm_call!(unsafe extern "sysv64" aes_gcm_dec_update_vaes_avx512(
                            inout, inout, len, key, &counter, htable, xi_ptr,
                        ))
                    }
                }
            }
            ghash.set_xi(&xi);
        }

        if !partial.is_empty() {
            // The kernel took `bulk.len() / 16` counter blocks, modulo 2^32
            // as GCM increments them.
            let keystream = key.encrypt_block(&add_to_counter(&counter, (bulk.len() / 16) as u32));
            if !ENC {
                ghash.add(partial);
            }
            for (b, k) in partial.iter_mut().zip(keystream) {
                *b ^= k;
            }
            if ENC {
                ghash.add(partial);
            }
        }
    }
}

/// `block` with `n` added to the big-endian 32-bit counter in its last four
/// bytes.
fn add_to_counter(block: &[u8; 16], n: u32) -> [u8; 16] {
    let [.., a, b, c, d] = *block;
    let ctr = u32::from_be_bytes([a, b, c, d]).wrapping_add(n);
    let mut out = [0u8; 16];
    // SAFETY: every x86_64 CPU has SSE2, and `block` and `out` are 16
    // readable and writable bytes. One vector store, so the kernel's 16-byte
    // load of it is forwarded.
    unsafe {
        let v = _mm_and_si128(
            _mm_loadu_si128(block.as_ptr().cast()),
            _mm_set_epi32(0, -1, -1, -1),
        );
        let ctr = _mm_slli_si128(_mm_cvtsi32_si128(i32::from_le_bytes(ctr.to_be_bytes())), 12);
        _mm_storeu_si128(out.as_mut_ptr().cast(), _mm_or_si128(v, ctr));
    }
    out
}

/// A table the kernels load, aligned so no load splits a cache line.
#[repr(C, align(64))]
struct Table<const N: usize>([u64; N]);

static AVX2_BSWAP_MASK: Table<2> = Table(include!("boringssl/aes-gcm-avx2-x86_64.bswap_mask.rs"));
static AVX2_GFPOLY: Table<2> = Table(include!("boringssl/aes-gcm-avx2-x86_64.gfpoly.rs"));
static AVX2_GFPOLY_AND_INTERNAL_CARRYBIT: Table<2> = Table(include!(
    "boringssl/aes-gcm-avx2-x86_64.gfpoly_and_internal_carrybit.rs"
));
static AVX2_CTR_PATTERN: Table<4> = Table(include!("boringssl/aes-gcm-avx2-x86_64.ctr_pattern.rs"));
static AVX2_INC_2BLOCKS: Table<4> = Table(include!("boringssl/aes-gcm-avx2-x86_64.inc_2blocks.rs"));

static AVX512_BSWAP_MASK: Table<2> =
    Table(include!("boringssl/aes-gcm-avx512-x86_64.bswap_mask.rs"));
static AVX512_GFPOLY: Table<2> = Table(include!("boringssl/aes-gcm-avx512-x86_64.gfpoly.rs"));
static AVX512_GFPOLY_AND_INTERNAL_CARRYBIT: Table<2> = Table(include!(
    "boringssl/aes-gcm-avx512-x86_64.gfpoly_and_internal_carrybit.rs"
));
static AVX512_CTR_PATTERN: Table<8> =
    Table(include!("boringssl/aes-gcm-avx512-x86_64.ctr_pattern.rs"));
static AVX512_INC_4BLOCKS: Table<2> =
    Table(include!("boringssl/aes-gcm-avx512-x86_64.inc_4blocks.rs"));

/// Declares a kernel as a naked function over BoringSSL's text, binding each
/// table it loads.
///
/// They take the System V ABI on every OS, since their text is BoringSSL's ELF
/// and Mach-O flavors, which read their arguments from its registers.
macro_rules! kernel {
    (fn $name:ident($($arg:ident: $ty:ty),* $(,)?); $($op:ident = $table:ident),* $(,)?) => {
        #[unsafe(naked)]
        unsafe extern "sysv64" fn $name($($arg: $ty),*) {
            #[cfg(not(target_vendor = "apple"))]
            core::arch::naked_asm!(
                include_str!(concat!("boringssl/", stringify!($name), ".linux.s")),
                $($op = sym $table,)*
                options(att_syntax),
            );
            #[cfg(target_vendor = "apple")]
            core::arch::naked_asm!(
                include_str!(concat!("boringssl/", stringify!($name), ".apple.s")),
                $($op = sym $table,)*
                options(att_syntax),
            );
        }
    };
}

kernel! {
    fn gcm_init_vpclmulqdq_avx2(htable: *mut Htable, h: *const [u64; 2]);
    gfpoly = AVX2_GFPOLY,
    gfpoly_and_internal_carrybit = AVX2_GFPOLY_AND_INTERNAL_CARRYBIT,
}
kernel! {
    fn aes_gcm_enc_update_vaes_avx2(
        input: *const u8,
        output: *mut u8,
        len: usize,
        key: *const u8,
        ivec: *const [u8; 16],
        htable: *const Htable,
        xi: *mut [u8; 16],
    );
    bswap_mask = AVX2_BSWAP_MASK,
    ctr_pattern = AVX2_CTR_PATTERN,
    gfpoly = AVX2_GFPOLY,
    inc_2blocks = AVX2_INC_2BLOCKS,
}
kernel! {
    fn aes_gcm_dec_update_vaes_avx2(
        input: *const u8,
        output: *mut u8,
        len: usize,
        key: *const u8,
        ivec: *const [u8; 16],
        htable: *const Htable,
        xi: *mut [u8; 16],
    );
    bswap_mask = AVX2_BSWAP_MASK,
    ctr_pattern = AVX2_CTR_PATTERN,
    gfpoly = AVX2_GFPOLY,
    inc_2blocks = AVX2_INC_2BLOCKS,
}

kernel! {
    fn gcm_init_vpclmulqdq_avx512(htable: *mut Htable, h: *const [u64; 2]);
    gfpoly = AVX512_GFPOLY,
    gfpoly_and_internal_carrybit = AVX512_GFPOLY_AND_INTERNAL_CARRYBIT,
}
kernel! {
    fn aes_gcm_enc_update_vaes_avx512(
        input: *const u8,
        output: *mut u8,
        len: usize,
        key: *const u8,
        ivec: *const [u8; 16],
        htable: *const Htable,
        xi: *mut [u8; 16],
    );
    bswap_mask = AVX512_BSWAP_MASK,
    ctr_pattern = AVX512_CTR_PATTERN,
    gfpoly = AVX512_GFPOLY,
    inc_4blocks = AVX512_INC_4BLOCKS,
}
kernel! {
    fn aes_gcm_dec_update_vaes_avx512(
        input: *const u8,
        output: *mut u8,
        len: usize,
        key: *const u8,
        ivec: *const [u8; 16],
        htable: *const Htable,
        xi: *mut [u8; 16],
    );
    bswap_mask = AVX512_BSWAP_MASK,
    ctr_pattern = AVX512_CTR_PATTERN,
    gfpoly = AVX512_GFPOLY,
    inc_4blocks = AVX512_INC_4BLOCKS,
}
