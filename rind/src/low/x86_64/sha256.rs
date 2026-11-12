// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::arch::asm;
use core::arch::x86_64::{__m128i, _mm_storeu_si128};

// The SHA extensions' routines are `asm!` blocks with fixed registers, so
// that the bytes rind runs are those a HOL Light proof is about, and their
// rounds are LLVM's output of the intrinsics Graviola wrote. Each block reads
// the round constants and byte-swap mask from `K` through rcx, not at a
// relocation, which the block's bytes alone could not resolve. Out of line,
// so each block is in rind's build once.

/// Compresses `blocks`.
#[inline(never)]
pub(in crate::low) fn sha256_compress_blocks_shaext(
    state: &mut [u32; 8],
    blocks: &[u8],
    _token: super::cpu::HaveSha256,
) {
    assert!(blocks.len().is_multiple_of(64));
    // SAFETY: `_token` proves the caller checked the `sha`, `ssse3`, and
    // `sse4.1` features. The block reads `state`, `blocks.len() / 64` blocks
    // from `blocks`, and `K`, and writes `state`.
    unsafe {
        asm!(
            // ABCD and EFGH as the SHA extensions hold them: ABEF in xmm11
            // and CDGH in xmm10.
            "movdqu (%rdi), %xmm0",
            "movdqu 16(%rdi), %xmm1",
            "pshufd $177, %xmm0, %xmm0",
            "pshufd $27, %xmm1, %xmm10",
            "movdqa %xmm0, %xmm11",
            "palignr $8, %xmm10, %xmm11",
            "pblendw $240, %xmm0, %xmm10",
            "test %rdx, %rdx",
            "je 3f",
            "movdqa 256(%rcx), %xmm4",
            "2:",
            "movdqu (%rsi), %xmm14",
            "movdqu 16(%rsi), %xmm15",
            "movdqu 32(%rsi), %xmm1",
            "movdqu 48(%rsi), %xmm12",
            "add $64, %rsi",
            rounds!(),
            "sub $1, %rdx",
            "jne 2b",
            "3:",
            unload_state!(),
            "movdqu %xmm2, (%rdi)",
            "movdqu %xmm1, 16(%rdi)",
            in("rdi") state.as_mut_ptr(),
            inout("rsi") blocks.as_ptr() => _,
            inout("rdx") blocks.len() / 64 => _,
            in("rcx") K.0.as_ptr(),
            out("xmm0") _, out("xmm1") _, out("xmm2") _, out("xmm3") _,
            out("xmm4") _, out("xmm5") _, out("xmm6") _, out("xmm7") _,
            out("xmm8") _, out("xmm9") _, out("xmm10") _, out("xmm11") _,
            out("xmm12") _, out("xmm13") _, out("xmm14") _, out("xmm15") _,
            options(att_syntax, nostack),
        );
    }
}

/// The digest of `state` followed by `message`, padded and closed by
/// `length`.
///
/// The last block's whole lanes are loaded where they lie and the rest is
/// padded in registers, and the digest is returned in them, so no load
/// waits on a store that cannot forward.
#[inline(never)]
pub(in crate::low) fn sha256_finish_shaext(
    state: &[u32; 8],
    message: &[u8],
    length: [u8; 8],
    _token: super::cpu::HaveSha256,
) -> [u8; 32] {
    let (blocks, tail) = message.as_chunks::<64>();
    let padded = padded(tail, length);
    let (abcd, efgh): (__m128i, __m128i);
    // SAFETY: `_token` proves the caller checked the `sha`, `ssse3`, and
    // `sse4.1` features. The block reads `state`, `blocks.len()` blocks of
    // `message` and then `padded.lanes` lanes, or three when that is 4, all
    // within `tail`, and `K`. It takes the System V ABI's argument registers where it
    // can, and leaves rdi, so that few values move.
    unsafe {
        asm!(
            "movdqu (%rsi), %xmm0",
            "movdqu 16(%rsi), %xmm1",
            "pshufd $177, %xmm0, %xmm0",
            "pshufd $27, %xmm1, %xmm10",
            "movdqa %xmm0, %xmm11",
            "palignr $8, %xmm10, %xmm11",
            "pblendw $240, %xmm0, %xmm10",
            "movdqa 256(%rcx), %xmm4",
            // The message's whole blocks, counted down in rax, which the
            // last borrow leaves at -1 for the padded blocks.
            "3:",
            "sub $1, %rax",
            "jae 12f",
            // The padded block: r9 whole lanes from rdx, at most three, the
            // lane r10 and r11 hold, zeros, and r8 as the last lane's top
            // word unless that lane is r10 and r11's.
            "2:",
            "cmp $1, %r9",
            "jae 7f",
            "movq %r10, %xmm14",
            "movq %r11, %xmm0",
            "punpcklqdq %xmm0, %xmm14",
            "xor %r11d, %r11d",
            "movq %r11, %xmm15",
            "movq %r11, %xmm1",
            "9:",
            "movq %r8, %xmm12",
            "pshufd $78, %xmm12, %xmm12",
            "4:",
            rounds!(),
            "test %rax, %rax",
            "jns 3b",
            // The block after the padded one, when r9 is 4: zeros, then the
            // length.
            "cmp $4, %r9",
            "jne 5f",
            "xor %r9d, %r9d",
            "xor %r10d, %r10d",
            "xor %r11d, %r11d",
            "jmp 2b",
            "7:",
            "movdqu (%rdx), %xmm14",
            "je 8f",
            "movdqu 16(%rdx), %xmm15",
            "cmp $2, %r9",
            "je 13f",
            "movdqu 32(%rdx), %xmm1",
            "movq %r10, %xmm12",
            "movq %r11, %xmm0",
            "punpcklqdq %xmm0, %xmm12",
            "jmp 4b",
            "8:",
            "movq %r10, %xmm15",
            "movq %r11, %xmm0",
            "punpcklqdq %xmm0, %xmm15",
            "xor %r11d, %r11d",
            "movq %r11, %xmm1",
            "jmp 9b",
            "13:",
            "movq %r10, %xmm1",
            "movq %r11, %xmm0",
            "punpcklqdq %xmm0, %xmm1",
            "jmp 9b",
            "12:",
            "movdqu (%rdx), %xmm14",
            "movdqu 16(%rdx), %xmm15",
            "movdqu 32(%rdx), %xmm1",
            "movdqu 48(%rdx), %xmm12",
            "add $64, %rdx",
            "jmp 4b",
            "5:",
            unload_state!(),
            "pshufb %xmm4, %xmm2",
            "pshufb %xmm4, %xmm1",
            in("rsi") state.as_ptr(),
            inout("rdx") blocks.as_ptr() => _,
            inout("rax") blocks.len() => _,
            in("rcx") K.0.as_ptr(),
            in("r8") padded.length,
            inout("r9") padded.lanes => _,
            inout("r10") padded.end[0] => _,
            inout("r11") padded.end[1] => _,
            out("xmm0") _, out("xmm1") efgh, out("xmm2") abcd, out("xmm3") _,
            out("xmm4") _, out("xmm10") _, out("xmm11") _,
            out("xmm12") _, out("xmm13") _, out("xmm14") _, out("xmm15") _,
            options(att_syntax, nostack, readonly),
        );
    }
    let mut digest = [0u8; 32];
    // SAFETY: `digest` is 32 bytes and writable
    unsafe {
        _mm_storeu_si128(digest[0..].as_mut_ptr().cast(), abcd);
        _mm_storeu_si128(digest[16..].as_mut_ptr().cast(), efgh);
    }
    digest
}

/// The last block of a message, padded: whole lanes of the message's bytes,
/// read from where they are, then the lane where the message ends, then
/// zeros, closed by the length.
struct Padded {
    /// The message's whole 16-byte lanes in the block, or 4 when there are
    /// three and the length takes a block after this one.
    lanes: usize,
    /// The lane after them, as two little-endian words: the message's last
    /// bytes, the 0x80 that ends it, and, when it is the block's last lane
    /// and the length fits, the length.
    end: [u64; 2],
    /// The length, as the last lane's top word when that is not `end`, and
    /// in the block after this one.
    length: u64,
}

/// The last block of a message whose bytes past its whole blocks are
/// `tail`, under 64 bytes, padded and closed by `length`. A longer `tail`
/// hashes wrongly but reads only its own bytes, so it goes unchecked.
///
/// Leaves the whole lanes for the block to load 16 bytes at a time, and
/// reads the rest in loads of 8, 4, 2, and 1 bytes from the lane's start,
/// so each load is likely to lie within one store its writer made, and
/// forward from it: building the block from words read 8 bytes at a time
/// made a one-block SHA-256 twice as slow on Arrow Lake.
// Inline, so the words reach the block in registers: through memory, a
// one-block SHA-256 measured 7.7% slower.
#[inline(always)]
fn padded(tail: &[u8], length: [u8; 8]) -> Padded {
    let lanes = tail.len() / 16;
    let part = &tail[16 * lanes..];
    let mut end = match part.split_first_chunk::<8>() {
        Some((first, rest)) => [u64::from_le_bytes(*first), ended(rest)],
        None => [ended(part), 0],
    };
    let length = u64::from_le_bytes(length);
    if tail.len() + 1 + 8 > 64 {
        return Padded {
            lanes: 4,
            end,
            length,
        };
    }
    if lanes == 3 {
        end[1] |= length;
    }
    Padded { lanes, end, length }
}

/// `part`, under 8 bytes, then the 0x80 that ends a message, as a
/// little-endian word.
#[inline(always)]
fn ended(part: &[u8]) -> u64 {
    let mut word = 0x80 << (8 * part.len());
    let mut rest = part;
    let mut shift = 0;
    if let Some((four, after)) = rest.split_first_chunk::<4>() {
        word |= u64::from(u32::from_le_bytes(*four));
        rest = after;
        shift = 32;
    }
    if let Some((two, after)) = rest.split_first_chunk::<2>() {
        word |= u64::from(u16::from_le_bytes(*two)) << shift;
        rest = after;
        shift += 16;
    }
    if let Some(one) = rest.first() {
        word |= u64::from(*one) << shift;
    }
    word
}

/// Compresses the block whose bytes xmm14, xmm15, xmm1, and xmm12 hold into
/// ABEF and CDGH in xmm11 and xmm10, with the byte-swap mask in xmm4 and the
/// round constants at rcx.
macro_rules! rounds {
    () => {
        concat!(
            "pshufb %xmm4, %xmm14\n",
            "pshufb %xmm4, %xmm15\n",
            "movdqa %xmm14, %xmm0\n",
            "paddd (%rcx), %xmm0\n",
            "movdqa %xmm10, %xmm2\n",
            "sha256rnds2 %xmm0, %xmm11, %xmm2\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "movdqa %xmm11, %xmm3\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm15, %xmm0\n",
            "paddd 16(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "pshufb %xmm4, %xmm1\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm1, %xmm0\n",
            "pshufb %xmm4, %xmm12\n",
            "paddd 32(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "sha256msg1 %xmm15, %xmm14\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm12, %xmm0\n",
            "paddd 48(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "movdqa %xmm12, %xmm13\n",
            "palignr $4, %xmm1, %xmm13\n",
            "paddd %xmm14, %xmm13\n",
            "sha256msg2 %xmm12, %xmm13\n",
            "sha256msg1 %xmm1, %xmm15\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm13, %xmm0\n",
            "paddd 64(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "movdqa %xmm13, %xmm14\n",
            "palignr $4, %xmm12, %xmm14\n",
            "paddd %xmm15, %xmm14\n",
            "sha256msg2 %xmm13, %xmm14\n",
            "sha256msg1 %xmm12, %xmm1\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm14, %xmm0\n",
            "paddd 80(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "movdqa %xmm14, %xmm15\n",
            "palignr $4, %xmm13, %xmm15\n",
            "paddd %xmm1, %xmm15\n",
            "sha256msg2 %xmm14, %xmm15\n",
            "sha256msg1 %xmm13, %xmm12\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm15, %xmm0\n",
            "paddd 96(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "movdqa %xmm15, %xmm1\n",
            "palignr $4, %xmm14, %xmm1\n",
            "paddd %xmm12, %xmm1\n",
            "sha256msg2 %xmm15, %xmm1\n",
            "sha256msg1 %xmm14, %xmm13\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm1, %xmm0\n",
            "paddd 112(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "movdqa %xmm1, %xmm12\n",
            "palignr $4, %xmm15, %xmm12\n",
            "paddd %xmm13, %xmm12\n",
            "sha256msg2 %xmm1, %xmm12\n",
            "sha256msg1 %xmm15, %xmm14\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm12, %xmm0\n",
            "paddd 128(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "movdqa %xmm12, %xmm13\n",
            "palignr $4, %xmm1, %xmm13\n",
            "paddd %xmm14, %xmm13\n",
            "sha256msg2 %xmm12, %xmm13\n",
            "sha256msg1 %xmm1, %xmm15\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256msg1 %xmm12, %xmm1\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm13, %xmm0\n",
            "movdqa %xmm13, %xmm14\n",
            "palignr $4, %xmm12, %xmm14\n",
            "paddd 144(%rcx), %xmm0\n",
            "paddd %xmm15, %xmm14\n",
            "sha256msg2 %xmm13, %xmm14\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256msg1 %xmm13, %xmm12\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm14, %xmm0\n",
            "movdqa %xmm14, %xmm15\n",
            "palignr $4, %xmm13, %xmm15\n",
            "paddd 160(%rcx), %xmm0\n",
            "paddd %xmm1, %xmm15\n",
            "sha256msg2 %xmm14, %xmm15\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256msg1 %xmm14, %xmm13\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm15, %xmm0\n",
            "movdqa %xmm15, %xmm1\n",
            "palignr $4, %xmm14, %xmm1\n",
            "paddd 176(%rcx), %xmm0\n",
            "paddd %xmm12, %xmm1\n",
            "sha256msg2 %xmm15, %xmm1\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "sha256msg1 %xmm15, %xmm14\n",
            "movdqa %xmm1, %xmm12\n",
            "palignr $4, %xmm15, %xmm12\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "paddd %xmm13, %xmm12\n",
            "sha256msg2 %xmm1, %xmm12\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "sha256msg1 %xmm1, %xmm15\n",
            "movdqa %xmm12, %xmm13\n",
            "palignr $4, %xmm1, %xmm13\n",
            "movdqa %xmm1, %xmm0\n",
            "paddd 192(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "paddd %xmm14, %xmm13\n",
            "sha256msg2 %xmm12, %xmm13\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm13, %xmm1\n",
            "palignr $4, %xmm12, %xmm1\n",
            "movdqa %xmm12, %xmm0\n",
            "paddd 208(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "paddd %xmm15, %xmm1\n",
            "sha256msg2 %xmm13, %xmm1\n",
            "movdqa %xmm13, %xmm0\n",
            "paddd 224(%rcx), %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "paddd 240(%rcx), %xmm1\n",
            "pshufd $14, %xmm0, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "movdqa %xmm1, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm3, %xmm2\n",
            "pshufd $14, %xmm1, %xmm0\n",
            "sha256rnds2 %xmm0, %xmm2, %xmm3\n",
            "paddd %xmm3, %xmm11\n",
            "paddd %xmm2, %xmm10\n",
        )
    };
}
use rounds;

/// ABEF and CDGH in xmm11 and xmm10 as ABCD and EFGH in xmm2 and xmm1.
macro_rules! unload_state {
    () => {
        concat!(
            "pshufd $27, %xmm11, %xmm0\n",
            "pshufd $177, %xmm10, %xmm1\n",
            "movdqa %xmm0, %xmm2\n",
            "pblendw $240, %xmm1, %xmm2\n",
            "palignr $8, %xmm0, %xmm1\n",
        )
    };
}
use unload_state;

/// The round constants, then the byte-swap mask that turns each big-endian
/// word of a block, or of the digest, into a little-endian one.
#[repr(align(16))]
struct Aligned([u32; 68]);

static K: Aligned = Aligned([
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    0x00010203, 0x04050607, 0x08090a0b, 0x0c0d0e0f,
]);

/// SHA-256 without the SHA extensions on CPUs with AVX2, with OpenSSL's
/// `sha256_block_data_order_avx2`, imported by `admin/import-openssl`, which
/// computes the message schedule of two blocks at once.
pub(in crate::low) fn sha256_compress_blocks_avx2(
    state: &mut [u32; 8],
    blocks: &[u8],
    _token: super::cpu::HaveAvx2,
) {
    assert!(blocks.len().is_multiple_of(64));
    // The routine runs its loop at least once, so zero blocks would read past
    // `blocks`.
    if blocks.is_empty() {
        return;
    }
    // SAFETY: `blocks` is `blocks.len() / 64` readable blocks, and `_token`
    // proves AVX2, BMI1, and BMI2.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha256_block_data_order_avx2(state, blocks.as_ptr(), blocks.len() / 64))
    }
}

/// SHA-256 without the SHA extensions or AVX2 on Intel, with aws-lc's
/// `sha256_block_data_order_avx`, imported by `admin/import-aws-lc`. It
/// rotates with `shrd`, which is fast on Intel's cores and slow on pre-Zen
/// AMD's, so aws-lc runs it on Intel only, and so does rind.
pub(in crate::low) fn sha256_compress_blocks_avx(
    state: &mut [u32; 8],
    blocks: &[u8],
    _token: super::cpu::HaveAvx,
) {
    assert!(blocks.len().is_multiple_of(64));
    // As for the AVX2 routine.
    if blocks.is_empty() {
        return;
    }
    // SAFETY: `blocks` is `blocks.len() / 64` readable blocks, and `_token`
    // proves AVX.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha256_block_data_order_avx(state, blocks.as_ptr(), blocks.len() / 64))
    }
}

/// SHA-256 without the SHA extensions or AVX2 on other vendors' CPUs, with
/// aws-lc's `sha256_block_data_order_ssse3`, as aws-lc runs there.
pub(in crate::low) fn sha256_compress_blocks_ssse3(
    state: &mut [u32; 8],
    blocks: &[u8],
    _token: super::cpu::HaveSsse3,
) {
    assert!(blocks.len().is_multiple_of(64));
    // As for the AVX2 routine.
    if blocks.is_empty() {
        return;
    }
    // SAFETY: `blocks` is `blocks.len() / 64` readable blocks, and `_token`
    // proves SSSE3.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha256_block_data_order_ssse3(state, blocks.as_ptr(), blocks.len() / 64))
    }
}

/// SHA-256 on CPUs without SSSE3, with aws-lc's integer
/// `sha256_block_data_order_nohw`, as aws-lc runs there.
pub(in crate::low) fn sha256_compress_blocks_nohw(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    // As for the AVX2 routine.
    if blocks.is_empty() {
        return;
    }
    // SAFETY: `blocks` is `blocks.len() / 64` readable blocks.
    unsafe {
        asm_call!(unsafe extern "sysv64" sha256_block_data_order_nohw(state, blocks.as_ptr(), blocks.len() / 64))
    }
}

/// The round constants, each group of four twice for the vector additions,
/// then the byte-swap and shuffle masks, as the routines load them.
#[repr(C, align(64))]
struct Table([u32; 152]);

static K256: Table = Table(include!("aws_lc/sha256-x86_64.K256.rs"));

// The routines take the System V ABI on every OS, since their text is
// OpenSSL's and aws-lc's ELF and Mach-O flavors, which read their arguments
// from its registers.

#[unsafe(naked)]
unsafe extern "sysv64" fn sha256_block_data_order_avx2(
    state: *mut [u32; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("openssl/sha256_block_data_order_avx2.linux.s"),
        K256 = sym K256,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("openssl/sha256_block_data_order_avx2.apple.s"),
        K256 = sym K256,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha256_block_data_order_avx(
    state: *mut [u32; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_avx.linux.s"),
        K256 = sym K256,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_avx.apple.s"),
        K256 = sym K256,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha256_block_data_order_ssse3(
    state: *mut [u32; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_ssse3.linux.s"),
        K256 = sym K256,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_ssse3.apple.s"),
        K256 = sym K256,
        options(att_syntax),
    );
}

#[unsafe(naked)]
unsafe extern "sysv64" fn sha256_block_data_order_nohw(
    state: *mut [u32; 8],
    data: *const u8,
    blocks: usize,
) {
    #[cfg(not(target_vendor = "apple"))]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_nohw.linux.s"),
        K256 = sym K256,
        options(att_syntax),
    );
    #[cfg(target_vendor = "apple")]
    core::arch::naked_asm!(
        include_str!("aws_lc/sha256_block_data_order_nohw.apple.s"),
        K256 = sym K256,
        options(att_syntax),
    );
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::low::x86_64::cpu::{HaveAvx, HaveAvx2, HaveSha256, HaveSsse3};
    use crate::low::{ct, generic};

    const START: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    // The SHA extensions, AVX2, SSSE3, and the vendor hide all but one path from
    // every other test, so each the CPU can run is checked against the
    // portable code directly, on blocks `admin/ctgrind` keeps secret: odd and
    // even block counts, with distinct bytes in every block. That checks
    // Intel's AVX code, which only Intel CPUs without AVX2 pick, on any CPU.
    #[test]
    fn paths_match_generic() {
        let (ssse3, avx, avx2) = (HaveSsse3::check(), HaveAvx::check(), HaveAvx2::check());
        let sha = HaveSha256::check();
        let blocks: Vec<u8> = (0..5 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        ct::secret_slice(&blocks);
        for n in 0..=5 {
            let mut wanted = START;
            let blocks = &blocks[..n * 64];
            generic::sha256::sha256_compress_blocks(&mut wanted, blocks);
            let wanted = ct::into_public(wanted);

            let mut got = START;
            sha256_compress_blocks_nohw(&mut got, blocks);
            assert_eq!(ct::into_public(got), wanted, "nohw, {n} blocks");
            if let Some(token) = ssse3 {
                let mut got = START;
                sha256_compress_blocks_ssse3(&mut got, blocks, token);
                assert_eq!(ct::into_public(got), wanted, "ssse3, {n} blocks");
            }
            if let Some(token) = avx {
                let mut got = START;
                sha256_compress_blocks_avx(&mut got, blocks, token);
                assert_eq!(ct::into_public(got), wanted, "avx, {n} blocks");
            }
            if let Some(token) = avx2 {
                let mut got = START;
                sha256_compress_blocks_avx2(&mut got, blocks, token);
                assert_eq!(ct::into_public(got), wanted, "avx2, {n} blocks");
            }
            if let Some(token) = sha {
                let mut got = START;
                sha256_compress_blocks_shaext(&mut got, blocks, token);
                assert_eq!(ct::into_public(got), wanted, "shaext, {n} blocks");
            }
        }
    }

    // Every length up to three blocks, so every place the padding can fall
    // after zero to two whole blocks, with bytes past the message that must
    // not count.
    #[test]
    fn finish_matches_generic() {
        let Some(token) = HaveSha256::check() else {
            return;
        };
        let bytes: Vec<u8> = (0..4 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        let length = 0x0102030405060708u64.to_be_bytes();
        for len in 0..=3 * 64 {
            let message = &bytes[..len];
            let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
            let mut wanted = START;
            generic::sha256::sha256_compress_blocks(&mut wanted, blocks);
            let mut padded = [[0u8; 64]; 2];
            let padded = crate::low::pad(rest, length, &mut padded);
            generic::sha256::sha256_compress_blocks(&mut wanted, padded);
            let got = sha256_finish_shaext(&START, message, length, token);
            assert_eq!(got, crate::low::sha256_digest(&wanted), "{len} bytes");
        }
    }

    // The blocks declare every register they write; this checks they write
    // no other the ABI preserves, on input that takes both blocks' loops and
    // the finish's length block.
    #[test]
    fn abi() {
        let Some(token) = HaveSha256::check() else {
            return;
        };
        let message = [0x5a; 2 * 64 + 60];
        let mut wanted = START;
        generic::sha256::sha256_compress_blocks(&mut wanted, &message[..128]);
        let mut got = START;
        crate::low::abi::call!(
            sha256_compress_blocks_shaext,
            &mut got,
            &message[..128],
            token
        );
        assert_eq!(got, wanted);

        let length = 0x0102030405060708u64.to_be_bytes();
        let mut padded = [[0u8; 64]; 2];
        let padded = crate::low::pad(&message[128..], length, &mut padded);
        generic::sha256::sha256_compress_blocks(&mut wanted, padded);
        let got = crate::low::abi::call!(sha256_finish_shaext, &START, &message[..], length, token);
        assert_eq!(got, crate::low::sha256_digest(&wanted));
    }
}
