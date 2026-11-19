// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! A rolled SHA-512 compression, for portable targets whose pointer is not
//! 64 bits.
//!
//! The portable backend otherwise calls HACL*'s `sha512_update`, which is
//! fully unrolled. On Xtensa that function is about 47 KiB, several times
//! the ESP32-S3's 16 KiB instruction cache, so every block streams its
//! code from flash. On that board the rolled loop takes about 0.033×
//! main's unrolled HACL* body, about 30×. That figure is the rolled loop
//! against that HACL* body. Against the rolled loop on the board, the IRAM
//! placement of the unrolled body takes 0.911 to 0.918 of its cycles.
//!
//! Two bodies, one per target, both following [`sha256`](sha256.rs) with
//! one 16-word window. `rolled` is a single 80-round loop that stays in a
//! few kilobytes, and every target but the ESP32-S3 runs it. `unrolled`
//! is the ESP32-S3's: sixteen-round groups with constant indexes, so that
//! no bounds check, iterator, or `memset` can outline into flash at
//! opt-level s or z, and its message load is the `l32i` sequence in
//! `be_u32`. Its code size is checked only on the ESP32-S3, which is why
//! no other target takes it. On `xtensa-esp32s3-espidf` it is placed in
//! IRAM (`.iram1.text`, literal pool included) and `K` in internal DRAM.
//! `xtensa-esp32s3-none-elf` keeps it in the ordinary flash sections.
//! `esp32s3-sha512-flash`, for an image whose IRAM is already full, drops
//! the unrolled body and runs `rolled` there too, with `K` in flash
//! `.rodata`: the unrolled body is about 18 KiB, which a 16 KiB
//! instruction cache cannot hold, and measured 11.3 to 13.1 times slower
//! than the rolled loop when it ran from flash (steelhead99x/rind-results,
//! `results/diag/esp32s3-pr94-pr87-pr85-2026-11-18`).
//! The driver `sha512_compress_blocks` stays in ordinary flash text, so
//! the update path is not a cache-off API. `admin/esp32s3-sha512-layout`
//! checks, at opt-level 3, s, and z, that the IRAM block loads nothing
//! from flash and calls nothing, prints its IRAM and literal-pool sizes,
//! and fails above its ceiling; it also runs the S3 build's message load
//! and a FIPS 180-4 compression under QEMU. ESP-IDF Xtensa SHA-256 is
//! rind's own IRAM body in `sha256_iram`, so this placement leaves
//! libcrux-sha2's sections as that crate built them.
//!
//! The round functions and the eighty `K` constants are FIPS 180-4 §4.1.3
//! and §4.2.3. The unit tests run FIPS 180-4's SHA-512 vectors through both
//! bodies and compare them on arbitrary chaining states, mark the block
//! secret so ctgrind checks both, and, on every backend except portable
//! with a pointer that is not 64 bits, compare with the compression the
//! backend ships (HACL* or aws-lc). On 64-bit portable targets, HACL*'s
//! unrolled form is still used.

macro_rules! CH {
    ($x:expr, $y:expr, $z:expr) => {
        ($x & $y) ^ (!$x & $z)
    };
}

macro_rules! MAJ {
    ($x:expr, $y:expr, $z:expr) => {
        ($x & $y) ^ ($x & $z) ^ ($y & $z)
    };
}

// Σ0, Σ1, σ0, σ1 of FIPS 180-4 §4.1.3.
macro_rules! BSIG0 {
    ($x:expr) => {
        $x.rotate_right(28) ^ $x.rotate_right(34) ^ $x.rotate_right(39)
    };
}

macro_rules! BSIG1 {
    ($x:expr) => {
        $x.rotate_right(14) ^ $x.rotate_right(18) ^ $x.rotate_right(41)
    };
}

macro_rules! SSIG0 {
    ($x:expr) => {
        $x.rotate_right(1) ^ $x.rotate_right(8) ^ ($x >> 7)
    };
}

macro_rules! SSIG1 {
    ($x:expr) => {
        $x.rotate_right(19) ^ $x.rotate_right(61) ^ ($x >> 6)
    };
}

// The body this target ships. Tests compile both. `esp32s3-sha512-flash`
// selects the rolled loop on the ESP32-S3, so the unrolled body is not
// built there.
#[cfg(any(not(rind_esp32s3), feature = "esp32s3-sha512-flash"))]
use rolled::sha512_compress_block;
#[cfg(all(rind_esp32s3, not(feature = "esp32s3-sha512-flash")))]
use unrolled::sha512_compress_block;

#[cfg(any(not(rind_esp32s3), feature = "esp32s3-sha512-flash", test))]
mod rolled {
    use super::K;

    #[inline(never)]
    pub(super) fn sha512_compress_block(state: &mut [u64; 8], block: &[u8; 128]) {
        // Sixteen big-endian words. The caller already holds a whole block,
        // so the conversion is once, ahead of the round loop, and the loop
        // does not carry a `try_into` panic path.
        let (words, _) = block.as_chunks::<8>();
        let mut a = state[0];
        let mut b = state[1];
        let mut c = state[2];
        let mut d = state[3];
        let mut e = state[4];
        let mut f = state[5];
        let mut g = state[6];
        let mut h = state[7];

        // A 16-word window into the whole W array, as in sha256.rs.
        let mut w: [u64; 16] = [0; 16];

        for t in 0..80 {
            // W[0..16] comes from the block; W[16..80] is
            //
            // W[t] = SSIG1(W[t - 2]) + W[t - 7] + SSIG0(W[t - 15]) + W[t - 16]
            //
            // with every index reduced mod 16 into the window. `W[t - 16]`
            // is the slot `W[t]` overwrites, `t % 16`.
            let w_t = if t < 16 {
                u64::from_be_bytes(words[t])
            } else {
                SSIG1!(w[(t - 2) % 16])
                    .wrapping_add(w[(t - 7) % 16])
                    .wrapping_add(SSIG0!(w[(t - 15) % 16]))
                    .wrapping_add(w[t % 16])
            };
            w[t % 16] = w_t;

            let t1 = h
                .wrapping_add(BSIG1!(e))
                .wrapping_add(CH!(e, f, g))
                .wrapping_add(K[t])
                .wrapping_add(w_t);
            let t2 = BSIG0!(a).wrapping_add(MAJ!(a, b, c));
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }

        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    }
}

#[cfg(any(all(rind_esp32s3, not(feature = "esp32s3-sha512-flash")), test))]
mod unrolled {
    use super::K;

    // One FIPS 180-4 round. Returning the working variables in rotated order
    // keeps a loop edge from moving them.
    #[inline(always)]
    fn sha512_round(
        w: u64,
        k: u64,
        a: u64,
        b: u64,
        c: u64,
        d: u64,
        e: u64,
        f: u64,
        g: u64,
        h: u64,
    ) -> (u64, u64, u64, u64, u64, u64, u64, u64) {
        let t1 = h
            .wrapping_add(BSIG1!(e))
            .wrapping_add(CH!(e, f, g))
            .wrapping_add(k)
            .wrapping_add(w);
        let t2 = BSIG0!(a).wrapping_add(MAJ!(a, b, c));
        (t1.wrapping_add(t2), a, b, c, d.wrapping_add(t1), e, f, g)
    }

    // `K` at a fixed offset from `kp`. `I` is a literal, so the load is a
    // constant displacement and not a bounds check. A safe `K[base + I]` with
    // a runtime `base` keeps a panic path, and at opt-level s/z that path is a
    // call into flash.
    #[inline(always)]
    fn round_constant<const I: usize>(kp: *const u64) -> u64 {
        // SAFETY: callers pass `I` in `0..16` and a `kp` at `K[0]`, `K[16]`,
        // `K[32]`, `K[48]`, or `K[64]`, so `kp.add(I)` stays inside `K`. `K` is
        // aligned for `u64`, and `I` is a constant. The load does not depend on
        // the message or the state.
        unsafe { kp.add(I).read() }
    }

    // Big-endian word at byte `BYTE + OFF`, both literal offsets. Two
    // parameters because a const argument cannot be `{ BYTE + 4 }` on stable,
    // but an `asm!` const operand can add them.
    #[cfg(target_arch = "xtensa")]
    #[inline(always)]
    fn be_u32<const BYTE: usize, const OFF: usize>(block: &[u8; 128]) -> u32 {
        let y;
        // SAFETY: the same `l32i` plus byte swap as `sha256_iram`'s message
        // load. This module is Xtensa only on the ESP32-S3 (`rind_esp32s3`:
        // its ESP-IDF and none-elf triples), the one core this load is
        // checked on. `BYTE + OFF` is a multiple of 4 in `0..128`. ESP-IDF
        // v5.5.1's ESP32-S3 `core-isa.h` sets `XCHAL_UNALIGNED_LOAD_HW` to 1
        // and `XCHAL_UNALIGNED_LOAD_EXCEPTION` to 0: Hardware Alignment with
        // no unaligned-load exception, so `l32i` returns the word at an
        // address that is not a multiple of 4. It does not trap, it does not
        // ignore the low bits, and it does not call a helper.
        // `admin/esp32s3-sha512-layout` checks that header, and runs this
        // sequence, including a block whose address is not a multiple of 4,
        // on QEMU's `esp32s3` CPU. That is the emulator's model of the core,
        // not a board measurement. The
        // sequence writes SAR, `a14`, and `y`, and does not use the stack. esp rustc
        // 1.97 lists `sar` as a clobber-only register, the same class
        // `sha256_iram` names with `out("sar") _`. The `ssai 8` is consumed by
        // the three `src` before the block ends. The address is the public
        // block cursor. The loaded bytes are the message, and none of these
        // instructions branches or loops on them.
        unsafe {
            core::arch::asm!(
                "l32i a14, {p}, {byte}",
                "ssai 8",
                "srli {y}, a14, 16",
                "src {y}, {y}, a14",
                "src {y}, {y}, {y}",
                "src {y}, a14, {y}",
                p = in(reg) block.as_ptr(),
                byte = const BYTE + OFF,
                y = lateout(reg) y,
                out("a14") _,
                out("sar") _,
                options(nostack, readonly),
            );
        }
        y
    }

    #[cfg(target_arch = "xtensa")]
    #[inline(always)]
    pub(super) fn message_word<const BYTE: usize>(block: &[u8; 128]) -> u64 {
        let hi = be_u32::<BYTE, 0>(block) as u64;
        let lo = be_u32::<BYTE, 4>(block) as u64;
        (hi << 32) | lo
    }

    #[cfg(not(target_arch = "xtensa"))]
    #[inline(always)]
    pub(super) fn message_word<const BYTE: usize>(block: &[u8; 128]) -> u64 {
        let (words, _) = block.as_chunks::<8>();
        u64::from_be_bytes(words[BYTE / 8])
    }

    // `W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16]`, `SLOT = t mod 16`.
    // The slot is the round number, not the message.
    #[inline(always)]
    fn schedule<const SLOT: usize>(w: &mut [core::mem::MaybeUninit<u64>; 16]) -> u64 {
        // SAFETY: the message rounds write every slot before the first call.
        // `SLOT` is `0..16`. A slot already written in this group is the new
        // schedule word the formula reads (`W[t-15]` when `SLOT` is 15); every
        // other read still holds the previous window. The write of this slot
        // happens after those reads. The indexes are constant.
        let w_t = unsafe {
            SSIG1!(w[(SLOT + 14) & 15].assume_init())
                .wrapping_add(w[(SLOT + 9) & 15].assume_init())
                .wrapping_add(SSIG0!(w[(SLOT + 1) & 15].assume_init()))
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
                    let ww = message_word::<{ $i * 8 }>($block);
                    $w[$i].write(ww);
                    ($a, $b, $c, $d, $e, $f, $g, $h) =
                        sha512_round(ww, kk, $a, $b, $c, $d, $e, $f, $g, $h);
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
                        sha512_round(ww, kk, $a, $b, $c, $d, $e, $f, $g, $h);
                }
            )*
        };
    }

    // IRAM on ESP32-S3 ESP-IDF only (`xtensa-esp32s3-espidf`; with the
    // `esp32s3-sha512-flash` feature this body is not built). ESP-IDF's
    // `soc.lf` puts `.iram1` and `.iram1.*` in instruction RAM. The flash
    // catch-all `*(.literal .literal.* .text .text.*)` is applied per input
    // file, so a `.text.*` body here would sit in flash text ahead of later
    // objects.
    // The Xtensa backend names the literal pool `.iram1.text.literal`, and
    // `l32r` reads that pool from IRAM. `K` is in `.dram1.rodata` (internal
    // DRAM). The layout probe checks opt-level 3, s, and z: each loads nothing
    // from flash and makes no call from this body. opt-level 0 is not a
    // cache-off guarantee. The length check in `sha512_compress_blocks` stays
    // in ordinary flash text. `xtensa-esp32s3-none-elf` keeps the ordinary
    // text section. ESP-IDF Xtensa SHA-256 is `sha256_iram`, already in IRAM.
    //
    // SAFETY: the attribute only selects the output section. The instructions
    // match the ordinary text placement, and ESP-IDF maps `.iram1` as executable.
    #[inline(never)]
    #[cfg_attr(
        all(target_arch = "xtensa", target_os = "espidf", rind_esp32s3),
        unsafe(link_section = ".iram1.text")
    )]
    pub(super) fn sha512_compress_block(state: &mut [u64; 8], block: &[u8; 128]) {
        let mut a = state[0];
        let mut b = state[1];
        let mut c = state[2];
        let mut d = state[3];
        let mut e = state[4];
        let mut f = state[5];
        let mut g = state[6];
        let mut h = state[7];

        // A 16-word window into the whole W array, as in sha256.rs. Left
        // uninitialized: a `[0; 16]` is a `memset`, and on the ESP32-S3 this
        // body is in IRAM, where a call into flash faults while the cache is
        // off. Rounds 0..16 write every word before a later round reads it.
        // The sixteen-round groups are the same shape as `sha256_iram`: a
        // `for` and a `K[t]` index keep a panic path that opt-level s/z can
        // outline into flash.
        let mut w = [const { core::mem::MaybeUninit::<u64>::uninit() }; 16];
        let kp = K.as_ptr();
        message_rounds!(
            w, block, kp, a, b, c, d, e, f, g, h, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14,
            15
        );
        // SAFETY: `K` has 80 words. The next group starts at word 16.
        let mut kp = unsafe { kp.add(16) };
        // Four trips, a public count. Not a `for`: a range iterator is one of
        // the core helpers opt-level s/z outlines into flash.
        let mut n = 0u32;
        while n < 4 {
            schedule_rounds!(
                w, kp, a, b, c, d, e, f, g, h, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
            );
            // SAFETY: the next start is word 32, 48, 64, or 80. The pointer at
            // 80 is one past the end of `K` and is not dereferenced; the loop
            // ends first.
            kp = unsafe { kp.add(16) };
            n += 1;
        }

        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    }
}

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));

    // `chunks` is a core iterator, and opt-level s/z can outline it. A
    // counter and a pointer step leave the block call as the only call
    // from this driver. The length assert above stays in ordinary flash
    // text; this function is not placed in IRAM.
    let mut ptr = blocks.as_ptr();
    let mut n = 0usize;
    let whole = blocks.len() / 128;
    while n < whole {
        // SAFETY: `n < blocks.len() / 128`, so the 128 bytes at `ptr` are
        // inside `blocks`. The block may be unaligned. On the ESP32-S3,
        // `unrolled::message_word` loads it with `l32i`, which that core
        // performs unaligned in hardware; other targets read it as bytes. The
        // reference does not outlive this call, and `blocks` is not
        // mutated through it.
        let block = unsafe { &*ptr.cast::<[u8; 128]>() };
        sha512_compress_block(state, block);
        // SAFETY: the next step is 128 bytes later, still inside `blocks`
        // or exactly one past the last whole block.
        ptr = unsafe { ptr.add(128) };
        n += 1;
    }
}

// FIPS 180-4 §4.2.3. On the ESP32-S3 ESP-IDF placement, internal DRAM rather
// than flash `.rodata`: `.iram1` code is expected not to touch flash while
// the cache is off. The unrolled body's cfg, except that
// `esp32s3-sha512-flash` leaves `K` in flash `.rodata` for the rolled loop.
//
// SAFETY: the attribute only selects the output section. The bytes are these
// constants, and ESP-IDF maps `.dram1` into internal DRAM.
#[cfg_attr(
    all(
        target_arch = "xtensa",
        target_os = "espidf",
        rind_esp32s3,
        not(feature = "esp32s3-sha512-flash"),
    ),
    unsafe(link_section = ".dram1.rodata")
)]
static K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

// Also compiled for the layout probe, which links its exports. A `tests`
// module, so cargo-mutants skips it under this compound `cfg`: see
// UPSTREAM.md, "cargo-mutants misses compound `cfg(test)`s".
#[cfg(any(test, rind_sha512_load_probe))]
mod tests {
    use super::sha512_compress_blocks;
    use super::unrolled::message_word;
    #[cfg(test)]
    use super::{rolled, unrolled};

    /// SHA-512's IV, FIPS 180-4 §5.3.5.
    const IV: [u64; 8] = [
        0x6a09e667f3bcc908,
        0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1,
        0x510e527fade682d1,
        0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b,
        0x5be0cd19137e2179,
    ];

    /// Compares every message word with `from_be_bytes`.
    ///
    /// Returns 0 when every word matches, including blocks at byte offsets 1
    /// and 3. Any other value is `0x0100_0000 | (start << 8) | byte` for the
    /// first mismatch. On Xtensa `message_word` is the `l32i` / `ssai` / `src`
    /// load, so `admin/esp32s3-sha512-layout` runs this under QEMU. Host tests
    /// take `from_be_bytes`.
    fn message_load_failures() -> u32 {
        // Uninitialized so the probe does not call `memset`. Every byte is
        // written before it is read.
        let mut raw = [const { core::mem::MaybeUninit::<u8>::uninit() }; 160];
        // SAFETY: `MaybeUninit<u8>` has the same layout as `u8`, and `raw`
        // has 160 elements. The loop writes each one.
        let base = raw.as_mut_ptr().cast::<u8>();
        let mut i = 0usize;
        while i < 160 {
            // SAFETY: `i` stays below 160.
            unsafe {
                *base.add(i) = i.wrapping_mul(17).wrapping_add(3) as u8;
            }
            i += 1;
        }
        // SAFETY: the first eight bytes were written by the loop above.
        unsafe {
            *base = 0x00;
            *base.add(1) = 0x01;
            *base.add(2) = 0x02;
            *base.add(3) = 0x03;
            *base.add(4) = 0x04;
            *base.add(5) = 0x05;
            *base.add(6) = 0x06;
            *base.add(7) = 0x07;
        }

        let fail = message_load_failures_at(base, 0);
        if fail != 0 {
            return fail;
        }
        let fail = message_load_failures_at(base, 1);
        if fail != 0 {
            return fail;
        }
        message_load_failures_at(base, 3)
    }

    // The block at byte `start` of the probe's buffer.
    fn message_load_failures_at(base: *const u8, start: usize) -> u32 {
        // SAFETY: `start` is 0, 1, or 3, and `base` points at 160 written
        // bytes, so the 128 bytes at `start` are in range.
        let block = unsafe { &*base.add(start).cast::<[u8; 128]>() };
        macro_rules! word {
            ($byte:literal) => {{
                let p = block.as_ptr();
                // SAFETY: `$byte` is 0, 8, ..., 120, so these eight bytes lie in `block`.
                let expect = u64::from_be_bytes(unsafe {
                    [
                        *p.add($byte),
                        *p.add($byte + 1),
                        *p.add($byte + 2),
                        *p.add($byte + 3),
                        *p.add($byte + 4),
                        *p.add($byte + 5),
                        *p.add($byte + 6),
                        *p.add($byte + 7),
                    ]
                });
                if message_word::<$byte>(block) != expect {
                    return 0x0100_0000 | ((start as u32) << 8) | $byte;
                }
            }};
        }
        word!(0);
        word!(8);
        word!(16);
        word!(24);
        word!(32);
        word!(40);
        word!(48);
        word!(56);
        word!(64);
        word!(72);
        word!(80);
        word!(88);
        word!(96);
        word!(104);
        word!(112);
        word!(120);
        0
    }

    /// SHA-512 of "abc", FIPS 180-4: the state after its one padded block.
    const ABC: [u64; 8] = [
        0xddaf35a193617aba,
        0xcc417349ae204131,
        0x12e6fa4e89a97ea2,
        0x0a9eeee64b55d39a,
        0x2192992a274fc1a8,
        0x36ba3c23a3feebbd,
        0x454d4423643ce80e,
        0x2a9ac94fa54ca49f,
    ];

    /// Compresses FIPS 180-4's padded "abc" block from the IV, at byte
    /// offsets 0 and 1, through the driver and so the body this target
    /// ships, and compares all eight words with the FIPS digest.
    ///
    /// Returns 0 when both match. Any other value is
    /// `0x0200_0000 | (start << 8) | word` for the first mismatch. On the
    /// ESP32-S3 ESP-IDF build that is the unrolled body in IRAM, its `K` in
    /// DRAM, and its `l32i` load, so `admin/esp32s3-sha512-layout` runs this
    /// under QEMU. Host tests take the same Rust with `from_be_bytes`.
    fn abc_failures() -> u32 {
        let fail = abc_failures_at(0);
        if fail != 0 {
            return fail;
        }
        abc_failures_at(1)
    }

    /// The padded "abc" block twice, at byte 0 and at byte 129, so the
    /// second copy starts one byte past a word boundary.
    #[repr(align(4))]
    struct AbcBlocks([u8; 257]);

    // A constant, not a buffer zeroed at run time, so the probe needs no
    // `memset` from the QEMU image, as `message_load_failures` needs none.
    static ABC_BLOCKS: AbcBlocks = {
        // FIPS 180-4 §5.1.2: "abc", the 0x80 terminator, zeros, and the
        // 128-bit length, 24.
        let mut b = [0u8; 257];
        let mut at = 0;
        while at <= 129 {
            b[at] = b'a';
            b[at + 1] = b'b';
            b[at + 2] = b'c';
            b[at + 3] = 0x80;
            b[at + 127] = 24;
            at += 129;
        }
        AbcBlocks(b)
    };

    fn abc_failures_at(start: usize) -> u32 {
        let at = start * 129;
        let mut state = IV;
        sha512_compress_blocks(&mut state, &ABC_BLOCKS.0[at..at + 128]);
        first_difference(&state, &ABC, start)
    }

    fn first_difference(got: &[u64; 8], want: &[u64; 8], start: usize) -> u32 {
        let mut i = 0;
        while i < 8 {
            if got[i] != want[i] {
                return 0x0200_0000 | ((start as u32) << 8) | i as u32;
            }
            i += 1;
        }
        0
    }

    /// Entry the layout probe links and runs. Not a rind API.
    #[cfg(rind_sha512_load_probe)]
    #[unsafe(no_mangle)]
    #[inline(never)]
    pub extern "C" fn sha512_load_probe() -> u32 {
        message_load_failures()
    }

    /// Entry the layout probe links and runs. Not a rind API.
    #[cfg(rind_sha512_load_probe)]
    #[unsafe(no_mangle)]
    #[inline(never)]
    pub extern "C" fn sha512_abc_probe() -> u32 {
        abc_failures()
    }

    #[cfg(test)]
    fn padded(message: &[u8]) -> Vec<u8> {
        let bits = (message.len() as u128).checked_mul(8).unwrap();
        let (blocks, rest) = crate::low::split_tail::<128, 16>(message);
        let mut padded = blocks.to_vec();
        let mut last = [[0u8; 128]; 2];
        padded.extend_from_slice(crate::low::pad(rest, bits.to_be_bytes(), &mut last));
        padded
    }

    #[cfg(test)]
    fn encode(state: [u64; 8]) -> [u8; 64] {
        let mut out = [0u8; 64];
        for (i, word) in state.iter().enumerate() {
            out[i * 8..(i + 1) * 8].copy_from_slice(&word.to_be_bytes());
        }
        out
    }

    /// One block compression, as each body has it.
    #[cfg(test)]
    type Body = fn(&mut [u64; 8], &[u8; 128]);

    /// Both bodies, whichever this target ships.
    #[cfg(test)]
    const BODIES: [(&str, Body); 2] = [
        ("rolled", rolled::sha512_compress_block),
        ("unrolled", unrolled::sha512_compress_block),
    ];

    #[cfg(test)]
    fn hash_with(body: Body, message: &[u8]) -> [u8; 64] {
        let padded = padded(message);
        let mut state = IV;
        // The block is the secret (a message, or an HMAC key block). Mark it
        // before these bodies, which 64-bit builds compile only in tests, so
        // ctgrind sees them. The state is public again before a comparison.
        crate::low::ct::secret_slice(&padded);
        for block in padded.as_chunks::<128>().0 {
            body(&mut state, block);
        }
        encode(crate::low::ct::into_public(state))
    }

    /// Through the driver, and so the body this target ships.
    #[cfg(test)]
    fn hash(message: &[u8]) -> [u8; 64] {
        let padded = padded(message);
        let mut state = IV;
        crate::low::ct::secret_slice(&padded);
        sha512_compress_blocks(&mut state, &padded);
        encode(crate::low::ct::into_public(state))
    }

    #[cfg(test)]
    fn digest_hex(message: &[u8], hex_digest: &str) {
        let expected = hex::decode(hex_digest).unwrap();
        assert_eq!(hash(message).as_slice(), expected.as_slice(), "driver");
        for (name, body) in BODIES {
            assert_eq!(
                hash_with(body, message).as_slice(),
                expected.as_slice(),
                "{name}"
            );
        }
    }

    /// The two bodies agree from chaining states no padded message reaches
    /// in one block, on blocks whose words take every high and low bit.
    #[test]
    fn bodies_agree() {
        let mut x = 0x9e37_79b9_7f4a_7c15u64;
        let mut next = || {
            // xorshift64: arbitrary, public, reproducible.
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            x
        };
        for _ in 0..64 {
            let mut state = [0u64; 8];
            state.iter_mut().for_each(|w| *w = next());
            let mut block = [0u8; 128];
            for word in block.as_chunks_mut::<8>().0 {
                *word = next().to_be_bytes();
            }
            crate::low::ct::secret_slice(&block);
            let mut rolled_state = state;
            let mut unrolled_state = state;
            rolled::sha512_compress_block(&mut rolled_state, &block);
            unrolled::sha512_compress_block(&mut unrolled_state, &block);
            assert_eq!(
                crate::low::ct::into_public(rolled_state),
                crate::low::ct::into_public(unrolled_state)
            );
        }
        // All-zero and all-one blocks and states, the carry extremes.
        for fill in [0u8, 0xff] {
            let block = [fill; 128];
            let mut rolled_state = [u64::from(fill) * 0x0101_0101_0101_0101; 8];
            let mut unrolled_state = rolled_state;
            rolled::sha512_compress_block(&mut rolled_state, &block);
            unrolled::sha512_compress_block(&mut unrolled_state, &block);
            assert_eq!(rolled_state, unrolled_state, "fill {fill:#x}");
        }
    }

    #[test]
    fn fips180_empty() {
        // FIPS 180-4, SHA-512 of the empty message.
        digest_hex(
            b"",
            "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
        );
    }

    #[test]
    fn fips180_abc() {
        // FIPS 180-4, SHA-512 of "abc".
        digest_hex(
            b"abc",
            "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
        );
    }

    /// A portable backend whose pointer is not 64 bits *is* this compression,
    /// so that comparison would call itself. Everywhere else it is HACL* or
    /// aws-lc.
    #[cfg(not(all(rind_backend = "portable", not(target_pointer_width = "64"))))]
    #[test]
    fn matches_backend_compression() {
        for len in [0usize, 1, 3, 55, 111, 112, 113, 127, 128, 239, 1000] {
            let message: Vec<u8> = (0..len).map(|i| (i * 17 + 3) as u8).collect();
            let bytes = padded(&message);
            let mut state = IV;
            crate::low::sha512_compress_blocks(&mut state, &bytes);
            assert_eq!(hash(&message), encode(state), "{len} bytes");
        }
    }

    /// Each message word matches `from_be_bytes`, including a block that is
    /// not word-aligned. On Xtensa that comparison is the `l32i` load;
    /// `admin/esp32s3-sha512-layout` is what runs it. This host build takes
    /// `from_be_bytes`.
    #[test]
    fn message_word_matches_from_be_bytes() {
        let fail = message_load_failures();
        assert_eq!(fail, 0, "message load mismatch {fail:#x}");
    }

    /// The probe's FIPS "abc" compression, at both offsets, through the
    /// driver. `admin/esp32s3-sha512-layout` runs the same code on QEMU.
    #[test]
    fn abc_probe_matches_fips180() {
        assert_eq!(abc_failures(), 0);
        // Its expected state is the digest `fips180_abc` checks.
        let mut digest = [0u8; 64];
        for (out, word) in digest.as_chunks_mut::<8>().0.iter_mut().zip(ABC) {
            *out = word.to_be_bytes();
        }
        assert_eq!(digest, hash(b"abc"));
    }

    /// A mismatch names its offset and the first word that differs.
    #[test]
    fn first_difference_names_the_word() {
        assert_eq!(first_difference(&ABC, &ABC, 1), 0);
        for i in 0..8 {
            let mut got = ABC;
            got[i] ^= 1 << 63;
            // A later word differs too, except when `i` is the last.
            got[7] ^= 1;
            assert_eq!(first_difference(&got, &ABC, 1), 0x0200_0100 | i as u32);
        }
    }

    #[test]
    fn fips180_two_blocks() {
        // FIPS 180-4, SHA-512 of the 112-byte letter sequence that pads
        // to two blocks.
        digest_hex(
            b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
            "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
        );
    }
}
