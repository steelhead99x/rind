// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256 compression in internal RAM on ESP-IDF Xtensa.
//!
//! The portable backend otherwise calls HACL*'s unrolled `sha256_update`
//! through libcrux-sha2. That body is about 12 KiB, so on an ESP32-S3 it
//! fills most of the 16 KiB flash instruction cache. This is FIPS 180-4
//! §4.1.2's functions and §6.2.2's schedule and rounds. The 16-word window
//! and the round constants follow `generic::sha256`, written for Graviola by
//! Joe Birr-Pixton; that module is compiled only in tests, so this file keeps
//! its own copy. The rotates, the block load, and the 16-round body are
//! written for this target. The first sixteen rounds load the block. One
//! sixteen-round schedule body then runs three times, for rounds 16..64.
//! Returning the working variables in rotated order keeps the loop edge from
//! moving them.
//!
//! LLVM's Xtensa backend (rustc 1.97.0.0, LLVM 21.1.3) does not emit
//! `ssai`/`src` for a rotate, so the rotate and the block-word load stay
//! asm. Each rotate is its own asm block so that block's SAR write cannot
//! interleave with another. ESP-IDF collects `.iram1.*` into IRAM. The
//! round constants are `.dram1.*`: a variable index cannot use a
//! PC-relative literal, and an IRAM instruction address is not a data
//! address. No branch or memory index depends on the message or the state.
//! Release builds of every other target leave this module out.
//!
//! The formulations below were compiled for `xtensa-esp32s3-espidf` at
//! opt-level 3 (`lto` off) and objdumped. Counts are dynamic instructions
//! in `sha256_compress_block`: the first sixteen rounds, the schedule body
//! three times, then the epilogue, plus one cycle when a load's result is
//! used by the next instruction. `ssai`/`src` is not an extra stall. IRAM
//! is the `.iram1` text plus its literal pool in the object file, before
//! the linker's alignment. None of this was timed on a board.
//!
//! | rotate | block word | IRAM | cycles |
//! |---|---|---:|---:|
//! | `ssai`/`src` asm | `l32i` + `ssai 8` asm | 4,324 | 3,545 |
//! | `u32::rotate_right`, `(x >> n) \| (x << (32 - n))`, or `unchecked_funnel_shr` | asm load | 5,253 | 4,421 |
//! | `u64` concatenation, then `>> n` | asm load | 5,364 | 4,998 |
//! | asm rotate | `from_be_bytes` or `read_unaligned` + `swap_bytes` | 5,107 | 3,917 |
//! | asm rotate | pre-pass `from_be_bytes` into the window | 5,171 | 3,983 |
//! | `rotate_right` | `from_be_bytes` | 6,118 | 4,841 |
//! | `u64` funnel | `from_be_bytes` | 6,098 | 5,303 |
//!
//! `u32::rotate_right` (the stable wrapper of `core::intrinsics::rotate_right`),
//! `(x >> n) | (x << (32 - n))`, and the unstable `unchecked_funnel_shr`
//! all become `llvm.fshl.i32(x, x, 32 - n)`. `SelectionDAGBuilder` rewrites
//! equal inputs to `ROTL` without asking whether `ROTL` is legal. This
//! backend expands `ROTL`/`ROTR`, so isel emits `srli` or `extui`, `slli`,
//! and `or`: three instructions, and a shift of 16 or more is `extui`. The
//! custom `FSHL` lowering, which would use `src`, never sees a rotate.
//! The `u64` form is a 64-bit shift, so it does become `movi.n` + `ssl` +
//! `src`, but the extra register pressure spills and the block is slower.
//! `ssai` has an empty TableGen pattern. No target feature or rustc flag
//! selects it.
//!
//! `from_be_bytes`, `read_unaligned` plus `swap_bytes`, and the pre-pass
//! all become `load i32 align 1` plus `llvm.bswap`. The backend does not
//! allow a misaligned `i32` load, so that is four `l8ui`, and `BSWAP` is
//! Expand, so the swap is a second byte permute and an `l32r` of `0xFF00`.
//! ESP32-S3 hardware does perform an unaligned `l32i`
//! (`XCHAL_UNALIGNED_LOAD_HW`).
//!
//! GCC already selects `ssai`/`src` for a constant rotate (`rotrsi3` in
//! `gcc/config/xtensa/xtensa.md`). A backend patch that would let this
//! file drop both asm blocks: mark `ROTL`/`ROTR` Custom and lower a
//! constant rotate to `ssai`/`src` (marking only `FSHL` Custom is not
//! enough), select `SSAI` for a constant funnel amount rather than
//! `MOVI` followed by `SSL` or `SSR`, allow misaligned `i32` loads on
//! cores with that hardware, and custom-lower `BSWAP` to the `ssai 8`
//! sequence. The request for `src` on `llvm.fshl`/`llvm.fshr` is
//! <https://github.com/espressif/llvm-project/issues/21>, closed by the
//! `ssl`/`ssr` path, which is not this sequence.

// FIPS 180-4 §4.1.2. `g ^ (e & (f ^ g))` is `(e & f) ^ (!e & g)`.
#[inline(always)]
fn ch(e: u32, f: u32, g: u32) -> u32 {
    g ^ (e & (f ^ g))
}

// `(a & b) ^ (c & (a ^ b))` is `(a & b) ^ (a & c) ^ (b & c)`.
#[inline(always)]
fn maj(a: u32, b: u32, c: u32) -> u32 {
    (a & b) ^ (c & (a ^ b))
}

// `ssai` writes SAR and `src` reads it, both inside this block. The block
// does not depend on SAR's previous value.
#[cfg(target_arch = "xtensa")]
#[inline(always)]
fn rotr<const N: u32>(x: u32) -> u32 {
    let y;
    // SAFETY: `ssai` and `src` are base Xtensa instructions. `N` is one of
    // 2, 6, 7, 11, 13, 17, 18, 19, 22, 25, each in `ssai`'s 0..32 range.
    // The only registers written are SAR and `y`. Nothing is loaded or stored.
    unsafe {
        core::arch::asm!(
            "ssai {n}",
            "src {y}, {x}, {x}",
            n = const N,
            x = in(reg) x,
            y = lateout(reg) y,
            options(pure, nomem, nostack),
        );
    }
    y
}

#[cfg(not(target_arch = "xtensa"))]
#[inline(always)]
fn rotr<const N: u32>(x: u32) -> u32 {
    x.rotate_right(N)
}

#[inline(always)]
fn bsig0(x: u32) -> u32 {
    rotr::<2>(x) ^ rotr::<13>(x) ^ rotr::<22>(x)
}

#[inline(always)]
fn bsig1(x: u32) -> u32 {
    rotr::<6>(x) ^ rotr::<11>(x) ^ rotr::<25>(x)
}

#[inline(always)]
fn ssig0(x: u32) -> u32 {
    rotr::<7>(x) ^ rotr::<18>(x) ^ (x >> 3)
}

#[inline(always)]
fn ssig1(x: u32) -> u32 {
    rotr::<17>(x) ^ rotr::<19>(x) ^ (x >> 10)
}

/// One round. The tuple is the rotated working state
/// `(T1+T2, a, b, c, d+T1, e, f, g)`.
#[inline(always)]
fn round(
    w: u32,
    k: u32,
    a: u32,
    b: u32,
    c: u32,
    d: u32,
    e: u32,
    f: u32,
    g: u32,
    h: u32,
) -> (u32, u32, u32, u32, u32, u32, u32, u32) {
    let t1 = h
        .wrapping_add(bsig1(e))
        .wrapping_add(ch(e, f, g))
        .wrapping_add(k)
        .wrapping_add(w);
    let new_e = d.wrapping_add(t1);
    let new_a = t1.wrapping_add(bsig0(a).wrapping_add(maj(a, b, c)));
    (new_a, a, b, c, new_e, e, f, g)
}

// `K[base + I]`, with `I` a literal so the load is a constant offset.
#[inline(always)]
fn round_constant<const I: usize>(kp: *const u32) -> u32 {
    // SAFETY: callers pass `I` in `0..16` and a `kp` at `K[0]`, `K[16]`,
    // `K[32]`, or `K[48]`, so `kp.add(I)` stays inside `K`. `K` is aligned
    // for `u32`, and `I` is a constant.
    unsafe { *kp.add(I) }
}

// Big-endian word `BYTE / 4` of the block. `BYTE` is a literal offset.
#[cfg(target_arch = "xtensa")]
#[inline(always)]
fn message_word<const BYTE: usize>(block: &[u8; 64]) -> u32 {
    let y;
    // SAFETY: `BYTE` is `0, 4, ..., 60`, so the four bytes lie in `block`.
    // ESP-IDF's Xtensa cores (ESP32, ESP32-S2, ESP32-S3) set
    // `XCHAL_UNALIGNED_LOAD_HW`, so `l32i` does not trap when `block` is not
    // word-aligned. The sequence is a byte swap of that little-endian load:
    // `ssai 8`, shift the high half down, then three `src`. It writes SAR,
    // `a14`, and `y`, and does not use the stack. The windowed ABI gives this
    // function its own `a14`; the operand list names it so the result cannot
    // land there. SAR is written and consumed before the block ends.
    unsafe {
        core::arch::asm!(
            "l32i a14, {p}, {byte}",
            "ssai 8",
            "srli {y}, a14, 16",
            "src {y}, {y}, a14",
            "src {y}, {y}, {y}",
            "src {y}, a14, {y}",
            p = in(reg) block.as_ptr(),
            byte = const BYTE,
            y = lateout(reg) y,
            out("a14") _,
            options(nostack, readonly),
        );
    }
    y
}

#[cfg(not(target_arch = "xtensa"))]
#[inline(always)]
fn message_word<const BYTE: usize>(block: &[u8; 64]) -> u32 {
    let (words, _) = block.as_chunks::<4>();
    u32::from_be_bytes(words[BYTE / 4])
}

// `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`, `SLOT = t mod 16`.
// The slot is the round number, not the message.
#[inline(always)]
fn schedule<const SLOT: usize>(w: &mut [u32; 16]) -> u32 {
    let w_t = ssig1(w[(SLOT + 14) & 15])
        .wrapping_add(w[(SLOT + 9) & 15])
        .wrapping_add(ssig0(w[(SLOT + 1) & 15]))
        .wrapping_add(w[SLOT]);
    w[SLOT] = w_t;
    w_t
}

// `$i` is a literal, so the word index and the constant's offset both fold.
macro_rules! message_rounds {
    ($w:ident, $block:ident, $kp:ident, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $($i:literal),*) => {
        $(
            {
                let kk = round_constant::<$i>($kp);
                let ww = message_word::<{ $i * 4 }>($block);
                $w[$i] = ww;
                ($a, $b, $c, $d, $e, $f, $g, $h) =
                    round(ww, kk, $a, $b, $c, $d, $e, $f, $g, $h);
            }
        )*
    };
}

macro_rules! schedule_rounds {
    ($w:ident, $kp:ident, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $($i:literal),*) => {
        $(
            {
                let kk = round_constant::<$i>($kp);
                let ww = schedule::<$i>(&mut $w);
                ($a, $b, $c, $d, $e, $f, $g, $h) =
                    round(ww, kk, $a, $b, $c, $d, $e, $f, $g, $h);
            }
        )*
    };
}

#[inline(never)]
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".iram1.rind_sha256_compress_block")
)]
fn sha256_compress_block(state: &mut [u32; 8], block: &[u8; 64]) {
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    // The message schedule, a 16-word window. The first 16 words are the
    // block; each later word replaces the one sixteen rounds behind it.
    let mut w = [0u32; 16];
    let kp = K.as_ptr();
    message_rounds!(
        w, block, kp, a, b, c, d, e, f, g, h, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
    );
    // SAFETY: `K` has 64 words. Each step below starts at word 16, 32, or 48.
    let mut kp = unsafe { kp.add(16) };
    let mut n = 0u32;
    while n < 3 {
        schedule_rounds!(
            w, kp, a, b, c, d, e, f, g, h, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
        );
        // SAFETY: the next start is word 32, 48, or 64. The last pointer is
        // not dereferenced; the loop ends first.
        kp = unsafe { kp.add(16) };
        n += 1;
    }

    // Add the chaining value from memory, so those eight words are not live
    // across the rounds.
    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

/// Whole-block SHA-256 compression, in IRAM on ESP-IDF Xtensa.
///
/// A short tail, which the caller does not pass, is left unchanged.
#[inline(never)]
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".iram1.rind_sha256_nblocks")
)]
pub(super) fn sha256_update_nblocks(st: &mut [u32; 8], mut blocks: &[u8]) {
    while let Some((block, rest)) = blocks.split_first_chunk::<64>() {
        sha256_compress_block(st, block);
        blocks = rest;
    }
}

// FIPS 180-4 §4.2.2.
#[cfg_attr(
    all(target_arch = "xtensa", target_os = "espidf"),
    unsafe(link_section = ".dram1.rind_sha256_k")
)]
static K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];
