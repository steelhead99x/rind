// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
// AVX2 kernel inspired by YuriMyakotin/ChaCha20-SIMD

//! ChaCha20. Where the CPU has AVX2: from 256 bytes, pyca/verified-garbage's
//! AVX2 routine, or its AVX-512 VL one where the CPU has that too, imported
//! by `admin/import-vg`; below that, rind's two-block AVX2 kernel from two
//! blocks, and HACL*'s verified rounds in general-purpose registers for one.
//! VG's AVX2 routine runs what follows its eight-block loop on four-, two-,
//! and one-block paths, which lost to the kernel, so on either routine a
//! remainder of 65 to 255 bytes after the last whole 512-byte group runs on
//! the kernel. Where the CPU has SSSE3 but not AVX2, aws-lc's `chacha-x86_64`
//! SSSE3 routine, four blocks at a time, above 128 bytes, as aws-lc runs it,
//! imported by `admin/import-aws-lc`; otherwise HACL*'s rounds, where aws-lc
//! runs integer code.
//!
//! verified-garbage proves its routines correct and constant time in Lean,
//! over its own models of the instructions, which `admin/prove vg`
//! cosimulates. `proofs/Rind/X86_64/VgChaCha20.lean` restates VG's theorems
//! as axioms and proves the glue around them, `proofs/Rind/X86_64/ChaCha20Avx2.lean`
//! proves the kernel against RFC 8439 over Lean models of its intrinsics,
//! which `admin/prove` tests against the CPU, and
//! `proofs/Rind/X86_64/ChaCha20Cipher.lean` proves the bytes `cipher` writes
//! at every length the block counter covers on those and HACL*'s rounds, taking the aws-lc SSSE3
//! routine's contract as the hypothesis `Ssse3`. That assembly is not formally
//! verified: its correctness rests on rind's tests of it against HACL*'s
//! rounds at each length from 129 to 1700 bytes, and on its use in OpenSSL,
//! BoringSSL, and aws-lc.

use core::arch::x86_64::*;
use core::mem::MaybeUninit;

use super::cpu::{HaveAvx2, HaveAvx512Vl, HaveSsse3};
use super::vg;
use crate::low::generic::chacha20;

pub(crate) struct ChaCha20 {
    /// As little-endian words, which on x86_64 are also the bytes VG reads.
    key: [u32; 8],
    /// The block counter, then the 96-bit nonce.
    counter_nonce: [u32; 4],
    vg: Option<Vg>,
    ssse3: Option<HaveSsse3>,
}

/// Which of verified-garbage's routines the CPU runs.
#[derive(Clone, Copy)]
enum Vg {
    Avx2(HaveAvx2),
    Avx512Vl(HaveAvx512Vl),
}

impl ChaCha20 {
    /// `nonce` is the little-endian block counter followed by the 96-bit nonce.
    pub(crate) fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        Self {
            key: words(key),
            counter_nonce: words(nonce),
            vg: match (HaveAvx512Vl::check(), HaveAvx2::check()) {
                (Some(t), _) => Some(Vg::Avx512Vl(t)),
                (None, Some(t)) => Some(Vg::Avx2(t)),
                (None, None) => None,
            },
            ssse3: HaveSsse3::check(),
        }
    }

    /// XORs the keystream into `buffer`, starting at the current block, then
    /// moves the counter past every block it touched.
    ///
    /// The 32-bit counter must not pass 2^32 - 1, which callers rule out
    /// with `mid::chacha20::check_counter`.
    pub(crate) fn cipher(&mut self, buffer: &mut [u8]) {
        match (self.vg, self.ssse3, buffer.len()) {
            (Some(vg), _, len @ VG_MIN_LEN..) => {
                // VG's AVX2 routine runs what follows its eight-block loop
                // on narrower paths, which lose to the kernel for two to
                // four blocks.
                let tail = match len % 512 {
                    tail @ 65..VG_MIN_LEN => tail,
                    _ => 0,
                };
                let (whole, rest) = buffer.split_at_mut(len - tail);
                cipher_vg(vg, &self.key, &self.counter_nonce, whole);
                if !rest.is_empty() {
                    let mut counter_nonce = self.counter_nonce;
                    counter_nonce[0] = counter_nonce[0].wrapping_add((whole.len() / 64) as u32);
                    // SAFETY: either of VG's tokens proves the `avx2` cpu feature.
                    unsafe { cipher_avx2(&self.key, &counter_nonce, rest) };
                }
            }
            // SAFETY: either of VG's tokens proves the `avx2` cpu feature.
            (Some(_), _, 65..) => unsafe { cipher_avx2(&self.key, &self.counter_nonce, buffer) },
            // SAFETY: the buffer is at least `SSSE3_4X_MIN_LEN` bytes.
            (None, Some(t), SSSE3_4X_MIN_LEN..) => unsafe {
                cipher_ssse3_4x(t, &self.key, &self.counter_nonce, buffer)
            },
            // As in aws-lc, which runs integer code here. The kernel computes
            // one block as a single serial chain, which Zen 5's two-cycle
            // vector latency makes slower than this.
            _ => chacha20::cipher(&self.key, &self.counter_nonce, buffer),
        }
        self.counter_nonce[0] =
            self.counter_nonce[0].wrapping_add(buffer.len().div_ceil(64) as u32);
    }
}

/// verified-garbage's streaming state, which only its routines read or
/// write, and which they read only where they have written: 768 bytes,
/// aligned to a cache line as VG's own wrapper aligns it.
#[repr(C, align(64))]
struct VgState(MaybeUninit<[u64; 96]>);

// One wrapper per routine, each a single call, so that a proof can state
// each routine's contract about its own wrapper.
impl VgState {
    /// A state for `init` to start.
    #[inline(always)]
    fn uninit() -> Self {
        Self(MaybeUninit::uninit())
    }

    /// verified-garbage's `vg_chacha20_init`: starts the keystream for `key`
    /// at the block counter and nonce `counter_nonce`.
    #[inline(always)]
    fn init(&mut self, key: &[u32; 8], counter_nonce: &[u32; 4]) {
        // Little-endian words are the bytes VG reads.
        let (key, counter_nonce) = (
            key.as_ptr().cast::<[u8; 32]>(),
            counter_nonce.as_ptr().cast::<[u8; 16]>(),
        );
        // SAFETY: `self` is 768 writable bytes, `key` 32 readable bytes, and
        // `counter_nonce` 16. `self` is exclusively borrowed, so it overlaps
        // neither input, which VG lets overlap each other; and none overlaps
        // the return address or wraps the address space, as no object does.
        unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_chacha20_init::vg_chacha20_init)(self.0.as_mut_ptr(), key, counter_nonce))
        }
    }

    /// verified-garbage's `vg_chacha20_apply_avx2`: XORs the next
    /// `buffer.len()` bytes of the keystream into `buffer` and returns 1, or
    /// returns 0 and changes nothing if fewer are left.
    ///
    /// # Safety
    ///
    /// `init` must have started the state: the routine branches on the count
    /// of keystream left that `init` writes.
    #[inline(always)]
    unsafe fn apply_avx2(&mut self, _: HaveAvx2, buffer: &mut [u8]) -> u32 {
        // SAFETY: `self` is 768 readable and writable bytes, of which the
        // routine reads only those `init`, which the caller ensures has run,
        // or the routine itself wrote, and `buffer` is `len`; they are
        // distinct objects, so neither overlaps the other, the return
        // address, or the stack below it, or wraps the address space. The
        // token proves the `avx` and `avx2` cpu features.
        unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_chacha20_apply_avx2::vg_chacha20_apply_avx2)(self.0.as_mut_ptr(), buffer.as_mut_ptr(), buffer.len()))
        }
    }

    /// verified-garbage's `vg_chacha20_apply_avx512vl`, as `apply_avx2`.
    ///
    /// # Safety
    ///
    /// As `apply_avx2`'s.
    #[inline(always)]
    unsafe fn apply_avx512vl(&mut self, _: HaveAvx512Vl, buffer: &mut [u8]) -> u32 {
        // SAFETY: as `apply_avx2`'s; the token proves the routine's cpu
        // features.
        unsafe {
            asm_call!(unsafe extern "sysv64" (vg::vg_chacha20_apply_avx512vl::vg_chacha20_apply_avx512vl)(self.0.as_mut_ptr(), buffer.as_mut_ptr(), buffer.len()))
        }
    }
}

/// XORs the keystream for `key` and `counter_nonce` into `buffer` on
/// verified-garbage's routines: `init` starts the keystream at the block
/// counter, and `apply` XORs it in. Out of line, so the paths that don't
/// run it don't set up its 768-byte, cache-aligned frame.
#[inline(never)]
fn cipher_vg(vg: Vg, key: &[u32; 8], counter_nonce: &[u32; 4], buffer: &mut [u8]) {
    let mut state = VgState::uninit();
    state.init(key, counter_nonce);
    let ok = match vg {
        // SAFETY: `init` has started the state.
        Vg::Avx2(t) => unsafe { state.apply_avx2(t, buffer) },
        // SAFETY: `init` has started the state.
        Vg::Avx512Vl(t) => unsafe { state.apply_avx512vl(t, buffer) },
    };
    // `apply` refuses, leaving `buffer` as it was, only a keystream past
    // block 2^32 - 1, which the callers rule out: never pass on plaintext.
    assert_eq!(ok, 1, "ChaCha20 block counter would overflow");
}

/// aws-lc's SSSE3 routine, four blocks at a time.
///
/// # Safety
///
/// `buffer` must not be empty: given no bytes, the routine's byte loop
/// counts its length down past zero, out of the buffer.
unsafe fn cipher_ssse3_4x(
    _: HaveSsse3,
    key: &[u32; 8],
    counter_nonce: &[u32; 4],
    buffer: &mut [u8],
) {
    let (ptr, len) = (buffer.as_mut_ptr(), buffer.len());
    // SAFETY: `buffer` is `len` readable and writable bytes, at least one as
    // the caller ensures, which the routine allows to alias exactly, and
    // `key` and `counter_nonce` are 8 and 4 words. The token proves the
    // `ssse3` cpu feature. Its 32-bit counter wraps unspecified past 2^32
    // blocks, which callers rule out.
    unsafe {
        asm_call!(unsafe extern "sysv64" chacha20_ctr32_ssse3_4x(ptr, ptr, len, key, counter_nonce))
    }
}

/// `bytes` as little-endian words.
//
// Indexes rather than splitting into chunks, which Aeneas cannot translate,
// so `proofs/` can prove `cipher`.
fn words<const B: usize, const W: usize>(bytes: &[u8; B]) -> [u32; W] {
    const { assert!(B == 4 * W) };
    let mut words = [0; W];
    for i in 0..W {
        words[i] = u32::from_le_bytes([
            bytes[4 * i],
            bytes[4 * i + 1],
            bytes[4 * i + 2],
            bytes[4 * i + 3],
        ]);
    }
    words
}

/// From this length verified-garbage's routines run, and from it on, a
/// remainder of 65 to 255 bytes after the last whole 512-byte group runs on
/// the two-block kernel instead: VG's AVX2 routine runs them on narrower paths
/// than its eight-block loop, which lost to the kernel by up to 1.73x on
/// Arrow Lake.
const VG_MIN_LEN: usize = 256;

/// From this length aws-lc runs its SSSE3 routine, which computes four
/// blocks at a time, rather than its integer one.
const SSSE3_4X_MIN_LEN: usize = 129;

/// Counters, a counter increment, and four of them, as the routine loads
/// them.
#[repr(C, align(64))]
struct Words([u32; 32]);

/// The rotate-by-16 and -24 shuffle masks, then the ChaCha20 constant, as
/// the routine loads them.
#[repr(C, align(64))]
struct Bytes([u8; 49]);

static ZERO: Words = Words(include!("aws_lc/chacha-x86_64.zero.rs"));
static ROT16: Bytes = Bytes(include!("aws_lc/chacha-x86_64.rot16.rs"));

// The routine takes the System V ABI on every OS, since its text is aws-lc's
// ELF and Mach-O flavors, which read their arguments from its registers.

#[unsafe(naked)]
unsafe extern "sysv64" fn chacha20_ctr32_ssse3_4x(
    out: *mut u8,
    input: *const u8,
    len: usize,
    key: *const [u32; 8],
    counter_nonce: *const [u32; 4],
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/ChaCha20_ctr32_ssse3_4x.linux.s"),
        zero = sym ZERO,
        rot16 = sym ROT16,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/ChaCha20_ctr32_ssse3_4x.apple.s"),
        zero = sym ZERO,
        rot16 = sym ROT16,
        options(att_syntax),
    );
}

macro_rules! rotate_left {
    ($reg:expr, 8) => {
        // this is a byte shuffle leftwards, except little-endian
        _mm256_shuffle_epi8(
            $reg,
            _mm256_set_epi8(
                14, 13, 12, 15, 10, 9, 8, 11, 6, 5, 4, 7, 2, 1, 0, 3, 14, 13, 12, 15, 10, 9, 8, 11,
                6, 5, 4, 7, 2, 1, 0, 3,
            ),
        )
    };
    ($reg:expr, 16) => {
        // this is a two-byte shuffle leftwards, except little-endian
        _mm256_shuffle_epi8(
            $reg,
            _mm256_set_epi8(
                13, 12, 15, 14, 9, 8, 11, 10, 5, 4, 7, 6, 1, 0, 3, 2, 13, 12, 15, 14, 9, 8, 11, 10,
                5, 4, 7, 6, 1, 0, 3, 2,
            ),
        )
    };
    ($reg:expr, $rot:literal) => {
        _mm256_or_si256(
            _mm256_slli_epi32($reg, $rot),
            _mm256_srli_epi32($reg, 32 - $rot),
        )
    };
}

/// The kernel, two blocks at a time, for the lengths below verified-garbage's
/// routines and their short tails.
//
// Indexes and loads values rather than splitting into chunks and loading
// through pointers, which Aeneas cannot translate, so `proofs/` can prove it.
#[target_feature(enable = "avx2")]
fn cipher_avx2(key: &[u32; 8], counter_nonce: &[u32; 4], buffer: &mut [u8]) {
    let mut counter = counter_nonce[0];
    let mut done = 0;
    while done < buffer.len() {
        let n = if buffer.len() - done < 128 {
            buffer.len() - done
        } else {
            128
        };
        core_2x(key, counter_nonce, counter, &mut buffer[done..done + n]);
        counter = counter.wrapping_add(2);
        done += n;
    }
}

/// XORs the two keystream blocks from block `counter` into `xor_out`, of up
/// to 128 bytes: the first block's state in each vector's low 128-bit lane,
/// the second's in its high lane, a row of the state each.
#[target_feature(enable = "avx2")]
#[inline]
fn core_2x(key: &[u32; 8], counter_nonce: &[u32; 4], counter: u32, xor_out: &mut [u8]) {
    let save_a = _mm256_setr_epi32(
        0x6170_7865,
        0x3320_646e,
        0x7962_2d32,
        0x6b20_6574,
        0x6170_7865,
        0x3320_646e,
        0x7962_2d32,
        0x6b20_6574,
    );
    let save_b = _mm256_setr_epi32(
        key[0] as i32,
        key[1] as i32,
        key[2] as i32,
        key[3] as i32,
        key[0] as i32,
        key[1] as i32,
        key[2] as i32,
        key[3] as i32,
    );
    let save_c = _mm256_setr_epi32(
        key[4] as i32,
        key[5] as i32,
        key[6] as i32,
        key[7] as i32,
        key[4] as i32,
        key[5] as i32,
        key[6] as i32,
        key[7] as i32,
    );
    let save_d = _mm256_setr_epi32(
        counter as i32,
        counter_nonce[1] as i32,
        counter_nonce[2] as i32,
        counter_nonce[3] as i32,
        counter.wrapping_add(1) as i32,
        counter_nonce[1] as i32,
        counter_nonce[2] as i32,
        counter_nonce[3] as i32,
    );
    let mut a = save_a;
    let mut b = save_b;
    let mut c = save_c;
    let mut d = save_d;

    for _ in 0..10usize {
        a = _mm256_add_epi32(a, b);
        d = _mm256_xor_si256(d, a);
        d = rotate_left!(d, 16);

        c = _mm256_add_epi32(c, d);
        b = _mm256_xor_si256(b, c);
        b = rotate_left!(b, 12);

        a = _mm256_add_epi32(a, b);
        d = _mm256_xor_si256(d, a);
        d = rotate_left!(d, 8);

        c = _mm256_add_epi32(c, d);
        b = _mm256_xor_si256(b, c);
        b = rotate_left!(b, 7);

        // Turn the diagonals into columns.
        b = _mm256_shuffle_epi32(b, 0b00_11_10_01);
        c = _mm256_shuffle_epi32(c, 0b01_00_11_10);
        d = _mm256_shuffle_epi32(d, 0b10_01_00_11);

        a = _mm256_add_epi32(a, b);
        d = _mm256_xor_si256(d, a);
        d = rotate_left!(d, 16);

        c = _mm256_add_epi32(c, d);
        b = _mm256_xor_si256(b, c);
        b = rotate_left!(b, 12);

        a = _mm256_add_epi32(a, b);
        d = _mm256_xor_si256(d, a);
        d = rotate_left!(d, 8);

        c = _mm256_add_epi32(c, d);
        b = _mm256_xor_si256(b, c);
        b = rotate_left!(b, 7);

        // And back.
        b = _mm256_shuffle_epi32(b, 0b10_01_00_11);
        c = _mm256_shuffle_epi32(c, 0b01_00_11_10);
        d = _mm256_shuffle_epi32(d, 0b00_11_10_01);
    }

    let a = _mm256_add_epi32(a, save_a);
    let b = _mm256_add_epi32(b, save_b);
    let c = _mm256_add_epi32(c, save_c);
    let d = _mm256_add_epi32(d, save_d);

    // The keystream in order: the first block's rows, then the second's.
    let k0 = _mm256_permute2x128_si256(a, b, 0x20);
    let k1 = _mm256_permute2x128_si256(c, d, 0x20);
    let k2 = _mm256_permute2x128_si256(a, b, 0x31);
    let k3 = _mm256_permute2x128_si256(c, d, 0x31);

    let mut ks = [0u8; 128];
    ks[0..32].copy_from_slice(&store_256(k0));
    ks[32..64].copy_from_slice(&store_256(k1));
    ks[64..96].copy_from_slice(&store_256(k2));
    ks[96..128].copy_from_slice(&store_256(k3));
    let ks = &ks[..xor_out.len()];
    for i in 0..ks.len() {
        xor_out[i] ^= ks[i];
    }
}

/// `v`'s bytes, the lowest first, as `_mm256_storeu_si256` stores them.
#[target_feature(enable = "avx2")]
#[inline]
fn store_256(v: __m256i) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    bytes[0..4].copy_from_slice(&(_mm256_extract_epi32(v, 0) as u32).to_le_bytes());
    bytes[4..8].copy_from_slice(&(_mm256_extract_epi32(v, 1) as u32).to_le_bytes());
    bytes[8..12].copy_from_slice(&(_mm256_extract_epi32(v, 2) as u32).to_le_bytes());
    bytes[12..16].copy_from_slice(&(_mm256_extract_epi32(v, 3) as u32).to_le_bytes());
    bytes[16..20].copy_from_slice(&(_mm256_extract_epi32(v, 4) as u32).to_le_bytes());
    bytes[20..24].copy_from_slice(&(_mm256_extract_epi32(v, 5) as u32).to_le_bytes());
    bytes[24..28].copy_from_slice(&(_mm256_extract_epi32(v, 6) as u32).to_le_bytes());
    bytes[28..32].copy_from_slice(&(_mm256_extract_epi32(v, 7) as u32).to_le_bytes());
    bytes
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::x86_64::adx_mux::tests::Rng;
    use crate::low::x86_64::ct_sde;
    use crate::low::{ct, hchacha20};

    // The CPU's fastest path hides the others from every other test, so
    // each path the CPU can run is checked against HACL*'s rounds directly,
    // under a key `admin/ctgrind` keeps secret: the dispatch for each of
    // verified-garbage's routines, SSSE3, and none, and VG's routines and
    // the two-block kernel alone, at every length through the paths'
    // boundaries and past VG's eight- and sixteen-block loops and the
    // kernel's tails, each continued by a second call, which a whole number
    // of blocks leaves contiguous.
    #[test]
    fn paths_match() {
        let key = core::array::from_fn(|i| i as u8);
        ct::secret_slice(&key);
        let nonce = core::array::from_fn(|i| (i * 7) as u8);
        let base = ChaCha20::new(&key, &nonce);
        let vgs = [
            HaveAvx512Vl::check().map(Vg::Avx512Vl),
            HaveAvx2::check().map(Vg::Avx2),
        ];
        let mut paths = vec![ChaCha20 {
            vg: None,
            ssse3: None,
            ..base
        }];
        if let Some(t) = HaveSsse3::check() {
            paths.push(ChaCha20 {
                vg: None,
                ssse3: Some(t),
                ..base
            });
        }
        for vg in vgs.into_iter().flatten() {
            paths.push(ChaCha20 {
                vg: Some(vg),
                ..base
            });
        }
        type Alone = fn(&ChaCha20, &mut [u8]);
        let mut alone: Vec<(&str, Alone)> = Vec::new();
        if HaveAvx512Vl::check().is_some() {
            alone.push(("VG AVX-512 VL", |c, b| {
                cipher_vg(
                    Vg::Avx512Vl(HaveAvx512Vl::check().unwrap()),
                    &c.key,
                    &c.counter_nonce,
                    b,
                )
            }));
        }
        if HaveAvx2::check().is_some() {
            alone.push(("VG AVX2", |c, b| {
                cipher_vg(
                    Vg::Avx2(HaveAvx2::check().unwrap()),
                    &c.key,
                    &c.counter_nonce,
                    b,
                )
            }));
            // SAFETY: the check proves the `avx2` cpu feature.
            alone.push(("kernel", |c, b| unsafe {
                cipher_avx2(&c.key, &c.counter_nonce, b)
            }));
        }

        for len in 0..=1700 {
            let mut want = vec![0x5a; len + 200];
            let (first, second) = want.split_at_mut(len);
            let mut counter_nonce = base.counter_nonce;
            chacha20::cipher(&base.key, &counter_nonce, first);
            counter_nonce[0] += len.div_ceil(64) as u32;
            chacha20::cipher(&base.key, &counter_nonce, second);
            ct::public_slice(&want);

            for (i, path) in paths.iter().enumerate() {
                let mut c = ChaCha20 { ..*path };
                let mut got = vec![0x5a; len + 200];
                let (first, second) = got.split_at_mut(len);
                c.cipher(first);
                c.cipher(second);
                ct::public_slice(&got);
                assert_eq!(got, want, "path {i}, {len} bytes, then 200");

                if len % 64 == 0 {
                    let mut whole = vec![0x5a; len + 200];
                    ChaCha20 { ..*path }.cipher(&mut whole);
                    ct::public_slice(&whole);
                    assert_eq!(whole, want, "path {i}, {len} bytes, then 200, at once");
                }
            }
            for (name, f) in &alone {
                let mut got = vec![0x5a; len];
                f(&base, &mut got);
                ct::public_slice(&got);
                assert_eq!(got, want[..len], "{name}, {len} bytes");
            }
        }
    }

    /// verified-garbage's routines refuse a keystream past block 2^32 - 1,
    /// which rind's callers never ask for, so the call panics rather than
    /// return the buffer unencrypted; the last block itself is allowed.
    #[test]
    fn vg_counter_limit() {
        let Some(t) = HaveAvx2::check() else { return };
        let nonce = [u32::MAX, 0, 0, 0];
        let mut last = [0u8; 64];
        cipher_vg(Vg::Avx2(t), &[0; 8], &nonce, &mut last);
        assert_ne!(last, [0; 64]);
        let mut past = [0u8; 65];
        let refused = std::panic::catch_unwind(core::panic::AssertUnwindSafe(|| {
            cipher_vg(Vg::Avx2(t), &[0; 8], &nonce, &mut past)
        }));
        assert!(refused.is_err());
        assert_eq!(past, [0; 65]);
    }

    // verified-garbage's AVX-512 VL routine, which valgrind cannot run, with
    // a secret key, nonce, and message, for `admin/ct-sde`: its wide loop
    // and a tail of single blocks and a partial one. The block counter is
    // public, and VG's contract lets the time depend on it.
    #[test]
    #[ignore = "admin/ct-sde runs it under Intel SDE"]
    fn ct_sde_chacha20() {
        let mut rng = Rng(ct_sde::seed());
        let t = HaveAvx512Vl::check().expect("AVX-512 VL");
        let key: [u32; 8] = core::array::from_fn(|_| rng.next() as u32);
        let mut nonce: [u32; 4] = core::array::from_fn(|_| rng.next() as u32);
        nonce[0] = 1;
        let mut msg: Vec<u8> = (0..1024 + 512 + 3 * 64 + 9)
            .map(|_| rng.next() as u8)
            .collect();
        ct_sde::traced(|| cipher_vg(Vg::Avx512Vl(t), &key, &nonce, &mut msg));
    }

    #[test]
    fn test_vectors() {
        // From draft-agl-tls-chacha20poly1305-04 section 7
        let mut c = ChaCha20::new(&[0u8; 32], &[0u8; 16]);
        let mut block = [0u8; 64];
        c.cipher(&mut block);
        assert_eq!(
            block,
            [
                0x76, 0xb8, 0xe0, 0xad, 0xa0, 0xf1, 0x3d, 0x90, 0x40, 0x5d, 0x6a, 0xe5, 0x53, 0x86,
                0xbd, 0x28, 0xbd, 0xd2, 0x19, 0xb8, 0xa0, 0x8d, 0xed, 0x1a, 0xa8, 0x36, 0xef, 0xcc,
                0x8b, 0x77, 0x0d, 0xc7, 0xda, 0x41, 0x59, 0x7c, 0x51, 0x57, 0x48, 0x8d, 0x77, 0x24,
                0xe0, 0x3f, 0xb8, 0xd8, 0x4a, 0x37, 0x6a, 0x43, 0xb8, 0xf4, 0x15, 0x18, 0xa1, 0x1c,
                0xc3, 0x87, 0xb6, 0x69, 0xb2, 0xee, 0x65, 0x86
            ]
        );

        let mut key = [0u8; 32];
        key[31] = 0x01;
        let mut c = ChaCha20::new(&key, &[0u8; 16]);
        let mut block = [0u8; 64];
        c.cipher(&mut block);
        assert_eq!(
            block,
            [
                0x45, 0x40, 0xf0, 0x5a, 0x9f, 0x1f, 0xb2, 0x96, 0xd7, 0x73, 0x6e, 0x7b, 0x20, 0x8e,
                0x3c, 0x96, 0xeb, 0x4f, 0xe1, 0x83, 0x46, 0x88, 0xd2, 0x60, 0x4f, 0x45, 0x09, 0x52,
                0xed, 0x43, 0x2d, 0x41, 0xbb, 0xe2, 0xa0, 0xb6, 0xea, 0x75, 0x66, 0xd2, 0xa5, 0xd1,
                0xe7, 0xe2, 0x0d, 0x42, 0xaf, 0x2c, 0x53, 0xd7, 0x92, 0xb1, 0xc4, 0x3f, 0xea, 0x81,
                0x7e, 0x9a, 0xd2, 0x75, 0xae, 0x54, 0x69, 0x63
            ]
        );

        let mut nonce = [0u8; 16];
        nonce[15] = 0x01;
        let mut c = ChaCha20::new(&[0u8; 32], &nonce);
        let mut block = [0u8; 64];
        c.cipher(&mut block);
        assert_eq!(
            block[..60],
            [
                0xde, 0x9c, 0xba, 0x7b, 0xf3, 0xd6, 0x9e, 0xf5, 0xe7, 0x86, 0xdc, 0x63, 0x97, 0x3f,
                0x65, 0x3a, 0x0b, 0x49, 0xe0, 0x15, 0xad, 0xbf, 0xf7, 0x13, 0x4f, 0xcb, 0x7d, 0xf1,
                0x37, 0x82, 0x10, 0x31, 0xe8, 0x5a, 0x05, 0x02, 0x78, 0xa7, 0x08, 0x45, 0x27, 0x21,
                0x4f, 0x73, 0xef, 0xc7, 0xfa, 0x5b, 0x52, 0x77, 0x06, 0x2e, 0xb7, 0xa0, 0x43, 0x3e,
                0x44, 0x5f, 0x41, 0xe3
            ]
        );

        let mut nonce = [0u8; 16];
        nonce[8] = 0x01;
        let mut c = ChaCha20::new(&[0u8; 32], &nonce);
        let mut block = [0u8; 64];
        c.cipher(&mut block);
        assert_eq!(
            block,
            [
                0xef, 0x3f, 0xdf, 0xd6, 0xc6, 0x15, 0x78, 0xfb, 0xf5, 0xcf, 0x35, 0xbd, 0x3d, 0xd3,
                0x3b, 0x80, 0x09, 0x63, 0x16, 0x34, 0xd2, 0x1e, 0x42, 0xac, 0x33, 0x96, 0x0b, 0xd1,
                0x38, 0xe5, 0x0d, 0x32, 0x11, 0x1e, 0x4c, 0xaf, 0x23, 0x7e, 0xe5, 0x3c, 0xa8, 0xad,
                0x64, 0x26, 0x19, 0x4a, 0x88, 0x54, 0x5d, 0xdc, 0x49, 0x7a, 0x0b, 0x46, 0x6e, 0x7d,
                0x6b, 0xbd, 0xb0, 0x04, 0x1b, 0x2f, 0x58, 0x6b
            ]
        );

        let mut c = ChaCha20::new(
            &[
                0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
                0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
                0x1c, 0x1d, 0x1e, 0x1f,
            ],
            &[
                0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x02, 0x03, 0x04, 0x05,
                0x06, 0x07,
            ],
        );

        let mut block = [0u8; 256];
        c.cipher(&mut block);

        assert_eq!(
            block,
            [
                0xf7, 0x98, 0xa1, 0x89, 0xf1, 0x95, 0xe6, 0x69, 0x82, 0x10, 0x5f, 0xfb, 0x64, 0x0b,
                0xb7, 0x75, 0x7f, 0x57, 0x9d, 0xa3, 0x16, 0x02, 0xfc, 0x93, 0xec, 0x01, 0xac, 0x56,
                0xf8, 0x5a, 0xc3, 0xc1, 0x34, 0xa4, 0x54, 0x7b, 0x73, 0x3b, 0x46, 0x41, 0x30, 0x42,
                0xc9, 0x44, 0x00, 0x49, 0x17, 0x69, 0x05, 0xd3, 0xbe, 0x59, 0xea, 0x1c, 0x53, 0xf1,
                0x59, 0x16, 0x15, 0x5c, 0x2b, 0xe8, 0x24, 0x1a, 0x38, 0x00, 0x8b, 0x9a, 0x26, 0xbc,
                0x35, 0x94, 0x1e, 0x24, 0x44, 0x17, 0x7c, 0x8a, 0xde, 0x66, 0x89, 0xde, 0x95, 0x26,
                0x49, 0x86, 0xd9, 0x58, 0x89, 0xfb, 0x60, 0xe8, 0x46, 0x29, 0xc9, 0xbd, 0x9a, 0x5a,
                0xcb, 0x1c, 0xc1, 0x18, 0xbe, 0x56, 0x3e, 0xb9, 0xb3, 0xa4, 0xa4, 0x72, 0xf8, 0x2e,
                0x09, 0xa7, 0xe7, 0x78, 0x49, 0x2b, 0x56, 0x2e, 0xf7, 0x13, 0x0e, 0x88, 0xdf, 0xe0,
                0x31, 0xc7, 0x9d, 0xb9, 0xd4, 0xf7, 0xc7, 0xa8, 0x99, 0x15, 0x1b, 0x9a, 0x47, 0x50,
                0x32, 0xb6, 0x3f, 0xc3, 0x85, 0x24, 0x5f, 0xe0, 0x54, 0xe3, 0xdd, 0x5a, 0x97, 0xa5,
                0xf5, 0x76, 0xfe, 0x06, 0x40, 0x25, 0xd3, 0xce, 0x04, 0x2c, 0x56, 0x6a, 0xb2, 0xc5,
                0x07, 0xb1, 0x38, 0xdb, 0x85, 0x3e, 0x3d, 0x69, 0x59, 0x66, 0x09, 0x96, 0x54, 0x6c,
                0xc9, 0xc4, 0xa6, 0xea, 0xfd, 0xc7, 0x77, 0xc0, 0x40, 0xd7, 0x0e, 0xaf, 0x46, 0xf7,
                0x6d, 0xad, 0x39, 0x79, 0xe5, 0xc5, 0x36, 0x0c, 0x33, 0x17, 0x16, 0x6a, 0x1c, 0x89,
                0x4c, 0x94, 0xa3, 0x71, 0x87, 0x6a, 0x94, 0xdf, 0x76, 0x28, 0xfe, 0x4e, 0xaa, 0xf2,
                0xcc, 0xb2, 0x7d, 0x5a, 0xaa, 0xe0, 0xad, 0x7a, 0xd0, 0xf9, 0xd4, 0xb6, 0xad, 0x3b,
                0x54, 0x09, 0x87, 0x46, 0xd4, 0x52, 0x4d, 0x38, 0x40, 0x7a, 0x6d, 0xeb, 0x3a, 0xb7,
                0x8f, 0xab, 0x78, 0xc9
            ]
        );
    }

    #[test]
    fn xchacha_test_vectors() {
        // From draft-irtf-cfrg-xchacha-03, A.2
        // https://datatracker.ietf.org/doc/html/draft-irtf-cfrg-xchacha-03#appendix-A.2

        let key = [
            0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d,
            0x8e, 0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b,
            0x9c, 0x9d, 0x9e, 0x9f,
        ];
        let nonce = *b"@ABCDEFGHIJKLMNOPQRSTUVX";
        let mut counter_nonce = [0u8; 16];
        counter_nonce[8..].copy_from_slice(&nonce[16..]);
        let mut c = ChaCha20::new(
            &hchacha20(&key, nonce[..16].try_into().unwrap()),
            &counter_nonce,
        );

        let mut buffer = [
            0x54, 0x68, 0x65, 0x20, 0x64, 0x68, 0x6f, 0x6c, 0x65, 0x20, 0x28, 0x70, 0x72, 0x6f,
            0x6e, 0x6f, 0x75, 0x6e, 0x63, 0x65, 0x64, 0x20, 0x22, 0x64, 0x6f, 0x6c, 0x65, 0x22,
            0x29, 0x20, 0x69, 0x73, 0x20, 0x61, 0x6c, 0x73, 0x6f, 0x20, 0x6b, 0x6e, 0x6f, 0x77,
            0x6e, 0x20, 0x61, 0x73, 0x20, 0x74, 0x68, 0x65, 0x20, 0x41, 0x73, 0x69, 0x61, 0x74,
            0x69, 0x63, 0x20, 0x77, 0x69, 0x6c, 0x64, 0x20, 0x64, 0x6f, 0x67, 0x2c, 0x20, 0x72,
            0x65, 0x64, 0x20, 0x64, 0x6f, 0x67, 0x2c, 0x20, 0x61, 0x6e, 0x64, 0x20, 0x77, 0x68,
            0x69, 0x73, 0x74, 0x6c, 0x69, 0x6e, 0x67, 0x20, 0x64, 0x6f, 0x67, 0x2e, 0x20, 0x49,
            0x74, 0x20, 0x69, 0x73, 0x20, 0x61, 0x62, 0x6f, 0x75, 0x74, 0x20, 0x74, 0x68, 0x65,
            0x20, 0x73, 0x69, 0x7a, 0x65, 0x20, 0x6f, 0x66, 0x20, 0x61, 0x20, 0x47, 0x65, 0x72,
            0x6d, 0x61, 0x6e, 0x20, 0x73, 0x68, 0x65, 0x70, 0x68, 0x65, 0x72, 0x64, 0x20, 0x62,
            0x75, 0x74, 0x20, 0x6c, 0x6f, 0x6f, 0x6b, 0x73, 0x20, 0x6d, 0x6f, 0x72, 0x65, 0x20,
            0x6c, 0x69, 0x6b, 0x65, 0x20, 0x61, 0x20, 0x6c, 0x6f, 0x6e, 0x67, 0x2d, 0x6c, 0x65,
            0x67, 0x67, 0x65, 0x64, 0x20, 0x66, 0x6f, 0x78, 0x2e, 0x20, 0x54, 0x68, 0x69, 0x73,
            0x20, 0x68, 0x69, 0x67, 0x68, 0x6c, 0x79, 0x20, 0x65, 0x6c, 0x75, 0x73, 0x69, 0x76,
            0x65, 0x20, 0x61, 0x6e, 0x64, 0x20, 0x73, 0x6b, 0x69, 0x6c, 0x6c, 0x65, 0x64, 0x20,
            0x6a, 0x75, 0x6d, 0x70, 0x65, 0x72, 0x20, 0x69, 0x73, 0x20, 0x63, 0x6c, 0x61, 0x73,
            0x73, 0x69, 0x66, 0x69, 0x65, 0x64, 0x20, 0x77, 0x69, 0x74, 0x68, 0x20, 0x77, 0x6f,
            0x6c, 0x76, 0x65, 0x73, 0x2c, 0x20, 0x63, 0x6f, 0x79, 0x6f, 0x74, 0x65, 0x73, 0x2c,
            0x20, 0x6a, 0x61, 0x63, 0x6b, 0x61, 0x6c, 0x73, 0x2c, 0x20, 0x61, 0x6e, 0x64, 0x20,
            0x66, 0x6f, 0x78, 0x65, 0x73, 0x20, 0x69, 0x6e, 0x20, 0x74, 0x68, 0x65, 0x20, 0x74,
            0x61, 0x78, 0x6f, 0x6e, 0x6f, 0x6d, 0x69, 0x63, 0x20, 0x66, 0x61, 0x6d, 0x69, 0x6c,
            0x79, 0x20, 0x43, 0x61, 0x6e, 0x69, 0x64, 0x61, 0x65, 0x2e,
        ];
        c.cipher(&mut buffer);

        let expected = [
            0x45, 0x59, 0xab, 0xba, 0x4e, 0x48, 0xc1, 0x61, 0x02, 0xe8, 0xbb, 0x2c, 0x05, 0xe6,
            0x94, 0x7f, 0x50, 0xa7, 0x86, 0xde, 0x16, 0x2f, 0x9b, 0x0b, 0x7e, 0x59, 0x2a, 0x9b,
            0x53, 0xd0, 0xd4, 0xe9, 0x8d, 0x8d, 0x64, 0x10, 0xd5, 0x40, 0xa1, 0xa6, 0x37, 0x5b,
            0x26, 0xd8, 0x0d, 0xac, 0xe4, 0xfa, 0xb5, 0x23, 0x84, 0xc7, 0x31, 0xac, 0xbf, 0x16,
            0xa5, 0x92, 0x3c, 0x0c, 0x48, 0xd3, 0x57, 0x5d, 0x4d, 0x0d, 0x2c, 0x67, 0x3b, 0x66,
            0x6f, 0xaa, 0x73, 0x10, 0x61, 0x27, 0x77, 0x01, 0x09, 0x3a, 0x6b, 0xf7, 0xa1, 0x58,
            0xa8, 0x86, 0x42, 0x92, 0xa4, 0x1c, 0x48, 0xe3, 0xa9, 0xb4, 0xc0, 0xda, 0xec, 0xe0,
            0xf8, 0xd9, 0x8d, 0x0d, 0x7e, 0x05, 0xb3, 0x7a, 0x30, 0x7b, 0xbb, 0x66, 0x33, 0x31,
            0x64, 0xec, 0x9e, 0x1b, 0x24, 0xea, 0x0d, 0x6c, 0x3f, 0xfd, 0xdc, 0xec, 0x4f, 0x68,
            0xe7, 0x44, 0x30, 0x56, 0x19, 0x3a, 0x03, 0xc8, 0x10, 0xe1, 0x13, 0x44, 0xca, 0x06,
            0xd8, 0xed, 0x8a, 0x2b, 0xfb, 0x1e, 0x8d, 0x48, 0xcf, 0xa6, 0xbc, 0x0e, 0xb4, 0xe2,
            0x46, 0x4b, 0x74, 0x81, 0x42, 0x40, 0x7c, 0x9f, 0x43, 0x1a, 0xee, 0x76, 0x99, 0x60,
            0xe1, 0x5b, 0xa8, 0xb9, 0x68, 0x90, 0x46, 0x6e, 0xf2, 0x45, 0x75, 0x99, 0x85, 0x23,
            0x85, 0xc6, 0x61, 0xf7, 0x52, 0xce, 0x20, 0xf9, 0xda, 0x0c, 0x09, 0xab, 0x6b, 0x19,
            0xdf, 0x74, 0xe7, 0x6a, 0x95, 0x96, 0x74, 0x46, 0xf8, 0xd0, 0xfd, 0x41, 0x5e, 0x7b,
            0xee, 0x2a, 0x12, 0xa1, 0x14, 0xc2, 0x0e, 0xb5, 0x29, 0x2a, 0xe7, 0xa3, 0x49, 0xae,
            0x57, 0x78, 0x20, 0xd5, 0x52, 0x0a, 0x1f, 0x3f, 0xb6, 0x2a, 0x17, 0xce, 0x6a, 0x7e,
            0x68, 0xfa, 0x7c, 0x79, 0x11, 0x1d, 0x88, 0x60, 0x92, 0x0b, 0xc0, 0x48, 0xef, 0x43,
            0xfe, 0x84, 0x48, 0x6c, 0xcb, 0x87, 0xc2, 0x5f, 0x0a, 0xe0, 0x45, 0xf0, 0xcc, 0xe1,
            0xe7, 0x98, 0x9a, 0x9a, 0xa2, 0x20, 0xa2, 0x8b, 0xdd, 0x48, 0x27, 0xe7, 0x51, 0xa2,
            0x4a, 0x6d, 0x5c, 0x62, 0xd7, 0x90, 0xa6, 0x63, 0x93, 0xb9, 0x31, 0x11, 0xc1, 0xa5,
            0x5d, 0xd7, 0x42, 0x1a, 0x10, 0x18, 0x49, 0x74, 0xc7, 0xc5,
        ];

        assert_eq!(buffer, expected);
    }
}
