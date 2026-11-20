// The 16-word schedule window follows `low/generic/sha256.rs`, written
// for Graviola by Joe Birr-Pixton, 2024. The round constants are that
// file's table, in `generic::sha256_k`. The 16-round body, the rotates,
// and the block load are rind's, for this target.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256 compression in internal RAM on ESP-IDF Xtensa.
//!
//! The portable backend otherwise calls HACL*'s unrolled `sha256_update`
//! through libcrux-sha2. That body is about 12 KiB, so on an ESP32-S3 it
//! fills most of the 16 KiB flash instruction cache. This is FIPS 180-4
//! §4.1.2's functions and §6.2.2's schedule and rounds. The first sixteen
//! rounds load the block. One sixteen-round schedule body then runs three
//! times, for rounds 16..64. Returning the working variables in rotated
//! order keeps the loop edge from moving them. A fully rolled 64-round
//! loop was slower than HACL* in IRAM on an ESP32-S3. This 16-round body,
//! at `3aaa3c6a`, takes about 0.76× that HACL*-in-IRAM time on a Seeed
//! XIAO ESP32-S3 (80 MHz flash, three runs), and about 0.65–0.74× main
//! from 1200 B to 16 KB. In that sha2 image the block symbol is 4,412
//! bytes, `.iram0.text` is 4,516 bytes above main, and the hold-style
//! heap is 282,856 bytes against main's 287,464. A standalone object
//! probe of the same tree reported a 4,256-byte block and 4,357 bytes of
//! IRAM sections; that probe is not the firmware image. HMAC and HKDF
//! were not in that pass. Host tests take the Rust fallbacks below, not
//! this asm.
//!
//! LLVM's Xtensa backend expands `rotate_right` into a shift pair and an
//! `or`. `ssai` plus `src` is the two-instruction rotate, and each rotate
//! is its own asm block so that block's SAR write cannot interleave with
//! another. A big-endian word is an `l32i` plus the same byte swap GCC
//! emits: this target's hardware performs an unaligned `l32i`, and LLVM
//! otherwise emits a byte load. ESP-IDF collects `.iram1.*` into IRAM.
//! The round constants are `.dram1.rind_sha256_k` (`generic::sha256_k`):
//! a variable index cannot use a PC-relative literal, and an IRAM
//! instruction address is not a data address.
//!
//! No branch or memory index depends on the message or the state. The
//! schedule window is indexed by the round number. The rotates and the
//! byte swap are fixed instruction sequences; the shift distance is a
//! const generic, not the secret. `l32i`, `ssai`, `src`, and `extui` do
//! not take a data-dependent number of cycles on this core, and `extui`
//! does not read SAR. A load can stall until its address is ready. That stall follows register
//! dependence, not the loaded value.
//!
//! `admin/esp32s3-sha256-layout` checks the linked image at opt-level 3,
//! which is the firmware's release profile: the block and the driver are
//! in IRAM, `K` is in `.dram1`, the block contains no call, and none of
//! those sections is relocated into flash text. opt-level 0 is not that
//! promise. A debug build may outline a helper into flash; do not run it
//! with the instruction cache off. Release builds of every other target
//! leave this module out.

use crate::low::generic::sha256_k::K;

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

// `ssai` writes SAR and `src` reads it, both inside this block. `src y, x, x`
// is a rotate right by SAR: the 64-bit value `{x, x}` shifted right by `N`,
// low 32 bits kept. The distance is a const generic in `ssai`'s 0..32
// immediate range, not data, so the two instructions are constant time.
//
// esp rustc 1.97.0.0 lists `sar` as a clobber-only `sreg` (caller-saved,
// like the other non-privileged special registers except LITBASE). The
// block names that write with `out("sar") _`. It is not `pure`: `pure`
// would tell LLVM the block has no side effects, and a later backend could
// keep a SAR value across it. The only other shifts in this module are the
// constant `>> 3` and `>> 10` in `ssig0` and `ssig1`, which the backend
// lowers to `srli` and which do not read SAR. The layout check requires
// each `ssai` immediate to be one of 2, 6, 7, 11, 13, 17, 18, 19, 22, 25
// followed by `src`, or the byte swap's `ssai 8`.
#[cfg(target_arch = "xtensa")]
#[inline(always)]
fn rotr<const N: u32>(x: u32) -> u32 {
    let y;
    // SAFETY: `ssai` and `src` are base Xtensa instructions. `N` is one of
    // 2, 6, 7, 11, 13, 17, 18, 19, 22, 25, each in `ssai`'s 0..32 range.
    // The only registers written are SAR and `y`. Nothing is loaded or
    // stored, and the block does not use the stack. `lateout` writes `y`
    // after `x` has been read, so the two may be the same register.
    // `out("sar") _` is a clobber: that class has no typed operand.
    unsafe {
        core::arch::asm!(
            "ssai {n}",
            "src {y}, {x}, {x}",
            n = const N,
            x = in(reg) x,
            y = lateout(reg) y,
            out("sar") _,
            options(nomem, nostack),
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

// `K` at a fixed offset from `kp`. `I` is a literal, so the load is a
// constant displacement and not a bounds check. A safe `K[base + I]` with
// a runtime `base` keeps a panic path, and at opt-level s/z that path is a
// call into flash. Copying this body three times would make every index a
// constant and drop the check, and would also triple the schedule. One
// body and a pointer keep the size and leave the block with no call.
#[inline(always)]
fn round_constant<const I: usize>(kp: *const u32) -> u32 {
    // SAFETY: callers pass `I` in `0..16` and a `kp` at `K[0]`, `K[16]`,
    // `K[32]`, or `K[48]`, so `kp.add(I)` stays inside `K`. `K` is aligned
    // for `u32`, and `I` is a constant. The load does not depend on the
    // message or the state.
    unsafe { kp.add(I).read() }
}

// Big-endian word `BYTE / 4` of the block. `BYTE` is a literal offset.
#[cfg(target_arch = "xtensa")]
#[inline(always)]
fn message_word<const BYTE: usize>(block: &[u8; 64]) -> u32 {
    let y;
    // SAFETY: `BYTE` is `0, 4, ..., 60`, so the four bytes lie in `block`.
    // ESP-IDF v5.5.1 sets `XCHAL_UNALIGNED_LOAD_HW` to 1 and
    // `XCHAL_UNALIGNED_LOAD_EXCEPTION` to 0 in
    // `components/xtensa/{esp32,esp32s3}/include/xtensa/config/core-isa.h`.
    // `admin/esp32s3-sha256-layout` builds those two targets. ESP32-S2's
    // header sets the same flags; this probe does not build it, so `l32i`
    // is checked here only for ESP32 and ESP32-S3. It does not trap and
    // does not call a helper when `block` is not word-aligned. The sequence
    // is a byte swap of that little-endian load: `ssai 8`, extract the high
    // half (`extui`: `srli`'s 4-bit shift cannot encode 16), then three
    // `src`. It writes SAR, `a14`, and `y`, and does not use the
    // stack. The windowed ABI and the call0 ABI both give this
    // function `a14` as a temporary; the operand list names it so the
    // compiler will not assign `p` or `y` there and will not keep a live
    // value in it. SAR is the same clobber-only `sreg` as in [`rotr`],
    // named here with `out("sar") _`, and the `ssai 8` is consumed by the
    // three `src` before the block ends. The address is the public block
    // cursor.
    // The loaded bytes are the message, and none of these instructions
    // branches or loops on them.
    unsafe {
        core::arch::asm!(
            "l32i a14, {p}, {byte}",
            "ssai 8",
            "extui {y}, a14, 16, 16",
            "src {y}, {y}, a14",
            "src {y}, {y}, {y}",
            "src {y}, a14, {y}",
            p = in(reg) block.as_ptr(),
            byte = const BYTE,
            y = lateout(reg) y,
            out("a14") _,
            out("sar") _,
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
fn schedule<const SLOT: usize>(w: &mut [core::mem::MaybeUninit<u32>; 16]) -> u32 {
    // SAFETY: the message rounds write every slot before the first call.
    // `SLOT` is `0..16`. A slot already written in this group is the new
    // schedule word the formula reads (`W[t-15]` when `SLOT` is 15); every
    // other read still holds the previous window. The write of this slot
    // happens after those reads. The indexes are constant.
    let w_t = unsafe {
        ssig1(w[(SLOT + 14) & 15].assume_init())
            .wrapping_add(w[(SLOT + 9) & 15].assume_init())
            .wrapping_add(ssig0(w[(SLOT + 1) & 15].assume_init()))
            .wrapping_add(w[SLOT].assume_init())
    };
    w[SLOT].write(w_t);
    w_t
}

// `$i` is a literal, so the word index and the constant's offset both fold.
macro_rules! message_rounds {
    ($w:ident, $block:ident, $kp:ident, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $($i:literal),*) => {
        $(
            {
                let kk = round_constant::<$i>($kp);
                let ww = message_word::<{ $i * 4 }>($block);
                $w[$i].write(ww);
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
    // Left uninitialized: a `[0; 16]` is a `memset`, and at opt-level s/z
    // that is a call. Rounds 0..16 write every word before a later round
    // reads it.
    let mut w = [const { core::mem::MaybeUninit::<u32>::uninit() }; 16];
    let kp = K.as_ptr();
    message_rounds!(
        w, block, kp, a, b, c, d, e, f, g, h, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
    );
    // SAFETY: `K` has 64 words. The next group starts at word 16.
    let mut kp = unsafe { kp.add(16) };
    // Three trips, a public count. Not a `for`: a range iterator is one of
    // the core helpers opt-level s/z outlines into flash.
    let mut n = 0u32;
    while n < 3 {
        schedule_rounds!(
            w, kp, a, b, c, d, e, f, g, h, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
        );
        // SAFETY: the next start is word 32, 48, or 64. The pointer at 64
        // is one past the end of `K` and is not dereferenced; the loop
        // ends first.
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
pub(super) fn sha256_update_nblocks(st: &mut [u32; 8], blocks: &[u8]) {
    // The length is public. `split_first_chunk` and `chunks` are core
    // iterators, and opt-level s/z can outline them into flash. A counter
    // and a pointer step leave the block call as the only call.
    let mut ptr = blocks.as_ptr();
    let mut n = 0usize;
    let whole = blocks.len() / 64;
    while n < whole {
        // SAFETY: `n < blocks.len() / 64`, so the 64 bytes at `ptr` are
        // inside `blocks`. The block may be unaligned. On Xtensa,
        // `message_word` loads it with `l32i`, which these cores perform
        // unaligned in hardware; other targets read it as bytes. The
        // reference does not outlive this call, and `blocks` is not
        // mutated through it.
        let block = unsafe { &*ptr.cast::<[u8; 64]>() };
        sha256_compress_block(st, block);
        // SAFETY: the next step is 64 bytes later, still inside `blocks`
        // or exactly one past the last whole block.
        ptr = unsafe { ptr.add(64) };
        n += 1;
    }
}
