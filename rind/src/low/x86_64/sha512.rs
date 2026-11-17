// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-512 compression: OpenSSL's AVX2 routine from `sha512-x86_64`, imported
//! by `admin/import-openssl`, and aws-lc's AVX and scalar ones, imported by
//! `admin/import-aws-lc`.
//!
//! aws-lc-verification's SAW proof covers aws-lc's AVX routine, as aws-lc
//! builds it, and rind's HOL Light proof in `proofs/hol-light/` covers
//! OpenSSL's AVX2 routine, as rind builds it; nothing verifies the scalar one.
//!
//! CPUs with the SHA512 instructions, from Arrow Lake and Lunar Lake on, run
//! the AVX2 routine too. Intel's data-independent-timing list omits
//! `VSHA512RNDS2`, `VSHA512MSG1`, and `VSHA512MSG2`, so
//! [`sha512_compress_blocks`] never runs them. Only
//! [`sha512_compress_blocks_public`], whose every input is public, does.

use core::arch::x86_64::{
    __m256i, _mm256_add_epi64, _mm256_blend_epi32, _mm256_castsi256_si128, _mm256_loadu_si256,
    _mm256_permute2x128_si256, _mm256_permute4x64_epi64, _mm256_set_epi64x,
    _mm256_sha512msg1_epi64, _mm256_sha512msg2_epi64, _mm256_sha512rnds2_epi64,
    _mm256_shuffle_epi8, _mm256_storeu_si256,
};
use std::sync::OnceLock;

use super::cpu::{HaveAvx, HaveAvx2, HaveSha512, is_intel};

/// The SHA-512 routine this CPU runs, with the proof it may.
#[derive(Clone, Copy)]
enum Path {
    Avx2(HaveAvx2),
    Avx(HaveAvx),
    Nohw,
}

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    // The routines run their loop at least once, so zero blocks would read
    // past `blocks`.
    if blocks.is_empty() {
        return;
    }
    match path() {
        // SAFETY: `blocks` is a whole number of blocks, and not empty.
        Path::Avx2(token) => unsafe { compress_avx2(token, state, blocks) },
        // SAFETY: as above.
        Path::Avx(token) => unsafe { compress_avx(token, state, blocks) },
        // SAFETY: as above.
        Path::Nohw => unsafe { compress_nohw(state, blocks) },
    }
}

fn path() -> Path {
    // Picked once, rather than testing several features on every compression.
    static PATH: OnceLock<Path> = OnceLock::new();
    *PATH.get_or_init(pick)
}

fn pick() -> Path {
    if let Some(token) = HaveAvx2::check() {
        Path::Avx2(token)
    } else if let Some(token) = HaveAvx::check().filter(|_| is_intel()) {
        // The AVX routine is the faster on Intel's cores and the slower on
        // AMD's, so rind picks by vendor as aws-lc does.
        Path::Avx(token)
    } else {
        Path::Nohw
    }
}

/// As [`sha512_compress_blocks`], for SHA-512 whose every input is public:
/// Ed25519 verification's `SHA-512(R || A || M)`, of a signature, a public
/// key, and the message. Where the CPU has the SHA512 instructions it runs
/// them, whose timing Intel does not promise is independent of the data, so
/// nothing secret may reach here: not the digest, HMAC, or HKDF APIs, nor
/// Ed25519 signing or key generation. `admin/ct-vartime.toml` lists
/// [`compress_sha512ext`] as public for this caller alone.
pub(crate) fn sha512_compress_blocks_public(state: &mut [u64; 8], blocks: &[u8]) {
    #[cfg(test)]
    tests::PUBLIC_CALLS.with(|n| n.set(n.get() + 1));
    assert!(blocks.len().is_multiple_of(128));
    if blocks.is_empty() {
        return;
    }
    match HaveSha512::check() {
        // SAFETY: the token proves the SHA512 instructions and AVX2, and
        // `blocks` is a whole number of blocks.
        Some(token) => unsafe { compress_sha512ext(token, state, blocks) },
        None => sha512_compress_blocks(state, blocks),
    }
}

/// The round constants once each, for the SHA512 instructions, which take
/// four of them at a time.
#[repr(C, align(32))]
struct SingleTable([u64; 80]);

static K512_SINGLE: SingleTable = SingleTable({
    let mut k = [0u64; 80];
    let mut i = 0;
    while i < 80 {
        // `K512` holds each pair of constants twice.
        k[i] = K512.0[(i / 2) * 4 + i % 2];
        i += 1;
    }
    k
});

/// Rounds `4I .. 4I + 4` of [`compress_sha512ext`], with the message
/// schedule's share of the work: `VSHA512MSG2` finishing `W[4I + 4 ..]`
/// from the `VSHA512MSG1` two groups back, `W[4I - 3 .. 4I + 1]`, and
/// `W[4I .. 4I + 4]`, then `VSHA512MSG1` starting `W[4I + 12 ..]`.
#[inline]
#[target_feature(enable = "sha512,avx2")]
fn sha512ext_group<const I: usize>(abef: &mut __m256i, cdgh: &mut __m256i, w: &mut [__m256i; 4]) {
    // SAFETY: `I` is at most 19, so the four constants lie within the table.
    let k = unsafe { _mm256_loadu_si256(K512_SINGLE.0.as_ptr().add(4 * I).cast()) };
    let wk = _mm256_add_epi64(w[I % 4], k);
    *cdgh = _mm256_sha512rnds2_epi64(*cdgh, *abef, _mm256_castsi256_si128(wk));
    let wk = _mm256_permute2x128_si256::<0x01>(wk, wk);
    *abef = _mm256_sha512rnds2_epi64(*abef, *cdgh, _mm256_castsi256_si128(wk));
    if 3 <= I && I < 19 {
        let w7 = _mm256_blend_epi32::<0x3f>(
            _mm256_permute4x64_epi64::<0x1b>(w[I % 4]),
            _mm256_permute4x64_epi64::<0x39>(w[(I + 3) % 4]),
        );
        let next = _mm256_add_epi64(w[(I + 1) % 4], w7);
        w[(I + 1) % 4] = _mm256_sha512msg2_epi64(next, w[I % 4]);
    }
    if 1 <= I && I < 17 {
        w[(I + 3) % 4] = _mm256_sha512msg1_epi64(w[(I + 3) % 4], _mm256_castsi256_si128(w[I % 4]));
    }
}

/// Compresses `blocks` into `state` with the SHA512 instructions, two rounds
/// per `VSHA512RNDS2`, as Intel's reference for them does: `abef` and
/// `cdgh` hold the working variables, highest lane first, and `w` the
/// message schedule, four words a vector, `VSHA512MSG1` and `VSHA512MSG2`
/// extending it, with `VPBLENDD` supplying `W[t-7]`.
///
/// # Safety
///
/// `blocks` must be a whole number of blocks.
#[target_feature(enable = "sha512,avx2")]
unsafe fn compress_sha512ext(_: HaveSha512, state: &mut [u64; 8], blocks: &[u8]) {
    // Byte-swaps each 64-bit lane.
    let swap = _mm256_set_epi64x(
        0x08090a0b0c0d0e0f,
        0x0001020304050607,
        0x08090a0b0c0d0e0f,
        0x0001020304050607,
    );
    // SAFETY: `state` is 64 readable bytes.
    let (s0, s1) = unsafe {
        (
            _mm256_loadu_si256(state.as_ptr().cast()),
            _mm256_loadu_si256(state.as_ptr().add(4).cast()),
        )
    };
    // (f, e, b, a) and (h, g, d, c), lowest lane first.
    let mut abef = _mm256_permute4x64_epi64::<0x1b>(_mm256_permute2x128_si256::<0x20>(s0, s1));
    let mut cdgh = _mm256_permute4x64_epi64::<0x1b>(_mm256_permute2x128_si256::<0x31>(s0, s1));
    for block in blocks.as_chunks::<128>().0 {
        let (abef0, cdgh0) = (abef, cdgh);
        let load = |i: usize| {
            // SAFETY: `block` is 128 readable bytes, and `i` at most 3.
            _mm256_shuffle_epi8(
                unsafe { _mm256_loadu_si256(block.as_ptr().add(32 * i).cast()) },
                swap,
            )
        };
        let mut w: [__m256i; 4] = [load(0), load(1), load(2), load(3)];
        // Unrolled, so every index into `w` is a constant.
        macro_rules! groups {
            ($($i:literal)*) => {$(
                sha512ext_group::<$i>(&mut abef, &mut cdgh, &mut w);
            )*};
        }
        groups!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19);
        abef = _mm256_add_epi64(abef, abef0);
        cdgh = _mm256_add_epi64(cdgh, cdgh0);
    }
    let abef = _mm256_permute4x64_epi64::<0x1b>(abef);
    let cdgh = _mm256_permute4x64_epi64::<0x1b>(cdgh);
    // SAFETY: `state` is 64 writable bytes.
    unsafe {
        _mm256_storeu_si256(
            state.as_mut_ptr().cast(),
            _mm256_permute2x128_si256::<0x20>(abef, cdgh),
        );
        _mm256_storeu_si256(
            state.as_mut_ptr().add(4).cast(),
            _mm256_permute2x128_si256::<0x31>(abef, cdgh),
        );
    }
}

/// Compresses `blocks`, a whole number of them, into `state` with the AVX2
/// routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_avx2(_: HaveAvx2, state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, at least one, and the
    // token proves AVX2, BMI1, and BMI2.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha512_block_data_order_avx2(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// As [`compress_avx2`], with the AVX routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_avx(_: HaveAvx, state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, at least one, and the
    // token proves AVX.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha512_block_data_order_avx(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// As [`compress_avx2`], with the scalar routine.
///
/// # Safety
///
/// `blocks` must hold at least one whole block.
unsafe fn compress_nohw(state: &mut [u64; 8], blocks: &[u8]) {
    // SAFETY: `blocks` is `len / 128` readable blocks, at least one.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha512_block_data_order_nohw(state, blocks.as_ptr(), blocks.len() / 128))
    }
}

/// The round constants, each pair twice for the vector additions, then the
/// byte-swap mask, as the routines load them.
#[repr(C, align(64))]
struct Table([u64; 164]);

static K512: Table = Table(include!("aws_lc/sha512-x86_64.K512.rs"));

// The routines take the System V ABI on every OS, since their text is
// OpenSSL's and aws-lc's ELF and Mach-O flavors, which read their arguments
// from its registers.

#[unsafe(naked)]
unsafe extern "sysv64" fn sha512_block_data_order_avx2(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("openssl/sha512_block_data_order_avx2.linux.s"),
        K512 = sym K512,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("openssl/sha512_block_data_order_avx2.apple.s"),
        K512 = sym K512,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha512_block_data_order_avx(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_avx.linux.s"),
        K512 = sym K512,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_avx.apple.s"),
        K512 = sym K512,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha512_block_data_order_nohw(
    state: *mut [u64; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_nohw.linux.s"),
        K512 = sym K512,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha512_block_data_order_nohw.apple.s"),
        K512 = sym K512,
        options(att_syntax),
    );
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
pub(crate) mod tests {
    use super::*;
    use crate::low::ct;

    std::thread_local! {
        /// How many times this thread entered [`sha512_compress_blocks_public`].
        pub(crate) static PUBLIC_CALLS: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
    }

    // Every other test sees only the routine this CPU picks, so each the CPU
    // can run is checked against the scalar one here, on blocks
    // `admin/ctgrind` keeps secret: odd and even block counts, with distinct
    // bytes in every block. That checks Intel's AVX code, which only Intel
    // CPUs without AVX2 pick, on any CPU.
    #[test]
    fn paths_match_nohw() {
        let blocks: Vec<u8> = (0..5 * 128u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        ct::secret_slice(&blocks);
        for n in 1..=5 {
            let blocks = &blocks[..n * 128];
            let mut want = [
                0x6a09e667f3bcc908,
                0xbb67ae8584caa73b,
                0x3c6ef372fe94f82b,
                0xa54ff53a5f1d36f1,
                0x510e527fade682d1,
                0x9b05688c2b3e6c1f,
                0x1f83d9abfb41bd6b,
                0x5be0cd19137e2179,
            ];
            let start = want;
            // SAFETY: `blocks` holds `n` blocks, at least one.
            unsafe { compress_nohw(&mut want, blocks) };
            let want = ct::into_public(want);
            if let Some(token) = HaveAvx::check() {
                let mut got = start;
                // SAFETY: as above.
                unsafe { compress_avx(token, &mut got, blocks) };
                assert_eq!(ct::into_public(got), want, "avx, {n} blocks");
            }
            if let Some(token) = HaveAvx2::check() {
                let mut got = start;
                // SAFETY: as above.
                unsafe { compress_avx2(token, &mut got, blocks) };
                assert_eq!(ct::into_public(got), want, "avx2, {n} blocks");
            }
        }
    }

    // The public path, which runs the SHA512 instructions where the CPU has
    // them, against the scalar routine, on public blocks: every block count
    // to twelve, so each of its four schedule slots ends a block.
    #[test]
    fn public_matches_nohw() {
        let blocks: Vec<u8> = (0..12 * 128u32)
            .map(|i| (i.wrapping_mul(0x85ebca6b) >> 23) as u8)
            .collect();
        for n in 0..=12 {
            let blocks = &blocks[..n * 128];
            let start: [u64; 8] = core::array::from_fn(|i| {
                0x0123456789abcdef_u64.rotate_left(8 * i as u32) ^ n as u64
            });
            let mut want = start;
            if n > 0 {
                // SAFETY: `blocks` holds `n` blocks, at least one.
                unsafe { compress_nohw(&mut want, blocks) };
            }
            let mut got = start;
            sha512_compress_blocks_public(&mut got, blocks);
            assert_eq!(got, want, "{n} blocks");
            if let Some(token) = HaveSha512::check() {
                let mut got = start;
                // SAFETY: `blocks` is a whole number of blocks.
                unsafe { compress_sha512ext(token, &mut got, blocks) };
                assert_eq!(got, want, "sha512ext, {n} blocks");
            }
        }
    }
}
