// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! A rolled SHA-512 compression, for portable targets whose pointer is not
//! 64 bits.
//!
//! The portable backend otherwise calls HACL*'s `sha512_update`, which is
//! fully unrolled. On Xtensa that function is about 47 KiB — several times
//! the ESP32-S3's 16 KiB instruction cache — so every block streams its
//! code from flash. On that board the rolled loop takes about 0.033×
//! main's unrolled HACL* body, about 30×. This implementation
//! follows [`sha256`](sha256.rs): one 16-word window and an 80-round loop,
//! which stays in a few kilobytes. On the ESP32-S3 under ESP-IDF that loop
//! is placed in IRAM (`.iram1.text`, literal pool included) and its `K`
//! table in internal DRAM. The layout check, at opt-level 3, s, and z,
//! verifies that this body adds no flash text and calls nothing.
//! The `esp32s3-sha512-flash` feature leaves the ordinary flash sections,
//! for an image whose IRAM is already full. The ESP32, the ESP32-S2,
//! `*-none-elf`, and every other target are unchanged. ESP-IDF Xtensa
//! SHA-256 is rind's own IRAM body in `sha256_iram`, so this placement
//! leaves libcrux-sha2's sections as that crate built them. The round
//! functions and the eighty `K` constants are FIPS 180-4 §4.1.3 and
//! §4.2.3. The unit tests check FIPS 180-4's SHA-512 vectors, mark the
//! block secret so ctgrind checks this loop, and, on every backend except
//! portable with a pointer that is not 64 bits, compare with the
//! compression the backend ships (HACL* or aws-lc). On 64-bit portable
//! targets, HACL*'s unrolled form is still used.

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

// Big-endian word at byte `BYTE`. `BYTE` is a literal offset.
#[cfg(target_arch = "xtensa")]
#[inline(always)]
fn be_u32<const BYTE: usize>(block: &[u8; 128]) -> u32 {
    let y;
    // SAFETY: the same `l32i` plus byte swap as `sha256_iram`'s message
    // load. `BYTE` is a multiple of 4 in `0..128`. ESP-IDF v5.5.1 sets
    // `XCHAL_UNALIGNED_LOAD_HW` to 1 and `XCHAL_UNALIGNED_LOAD_EXCEPTION`
    // to 0 on ESP32, ESP32-S2, and ESP32-S3, so `l32i` does not trap and
    // does not call a helper when `block` is not word-aligned. The sequence
    // writes SAR, `a14`, and `y`, and does not use the stack. esp rustc
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
            byte = const BYTE,
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
fn message_word<const BYTE: usize>(block: &[u8; 128]) -> u64 {
    let hi = be_u32::<BYTE>(block) as u64;
    let lo = be_u32::<{ BYTE + 4 }>(block) as u64;
    (hi << 32) | lo
}

#[cfg(not(target_arch = "xtensa"))]
#[inline(always)]
fn message_word<const BYTE: usize>(block: &[u8; 128]) -> u64 {
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

// ESP32-S3 ESP-IDF only (`xtensa-esp32s3-espidf`, and not the
// `esp32s3-sha512-flash` feature). ESP-IDF's `soc.lf` puts `.iram1` and
// `.iram1.*` in instruction RAM. The flash catch-all
// `*(.literal .literal.* .text .text.*)` is applied per input file, so a
// `.text.*` body here would sit in flash text ahead of later objects.
// The Xtensa backend names the literal pool `.iram1.text.literal`, and
// `l32r` reads that pool from IRAM. `K` is in `.dram1.rodata` (internal
// DRAM). The layout probe checks opt-level 3, s, and z: each loads nothing
// from flash and makes no call from this body. opt-level 0 is not a
// cache-off guarantee. The length check in `sha512_compress_blocks` stays
// in ordinary flash text. The ESP32, the ESP32-S2, and `*-none-elf` keep
// the ordinary
// text section. ESP-IDF Xtensa SHA-256 is `sha256_iram`, already in IRAM.
//
// SAFETY: the attribute only selects the output section. The instructions
// match the ordinary text placement, and ESP-IDF maps `.iram1` as executable.
#[inline(never)]
#[cfg_attr(
    all(
        target_arch = "xtensa",
        target_os = "espidf",
        target_feature = "esp32s3ops",
        not(feature = "esp32s3-sha512-flash"),
    ),
    unsafe(link_section = ".iram1.text")
)]
fn sha512_compress_block(state: &mut [u64; 8], block: &[u8; 128]) {
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
        w, block, kp, a, b, c, d, e, f, g, h, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15
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
        // inside `blocks`. The block may be unaligned. On Xtensa,
        // `message_word` loads it with `l32i`, which these cores perform
        // unaligned in hardware; other targets read it as bytes. The
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
// the cache is off. Same cfg as `sha512_compress_block`.
//
// SAFETY: the attribute only selects the output section. The bytes are these
// constants, and ESP-IDF maps `.dram1` into internal DRAM.
#[cfg_attr(
    all(
        target_arch = "xtensa",
        target_os = "espidf",
        target_feature = "esp32s3ops",
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

#[cfg(test)]
mod tests {
    use super::sha512_compress_blocks;

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

    fn padded(message: &[u8]) -> Vec<u8> {
        let bits = (message.len() as u128).checked_mul(8).unwrap();
        let (blocks, rest) = crate::low::split_tail::<128, 16>(message);
        let mut padded = blocks.to_vec();
        let mut last = [[0u8; 128]; 2];
        padded.extend_from_slice(crate::low::pad(rest, bits.to_be_bytes(), &mut last));
        padded
    }

    fn encode(state: [u64; 8]) -> [u8; 64] {
        let mut out = [0u8; 64];
        for (i, word) in state.iter().enumerate() {
            out[i * 8..(i + 1) * 8].copy_from_slice(&word.to_be_bytes());
        }
        out
    }

    fn hash(message: &[u8]) -> [u8; 64] {
        let padded = padded(message);
        let mut state = IV;
        // The block is the secret (a message, or an HMAC key block). Mark it
        // before this rolled loop, which 64-bit builds compile only in tests,
        // so ctgrind sees it. The state is public again before a comparison.
        crate::low::ct::secret_slice(&padded);
        sha512_compress_blocks(&mut state, &padded);
        encode(crate::low::ct::into_public(state))
    }

    fn digest_hex(message: &[u8], hex_digest: &str) {
        let expected = hex::decode(hex_digest).unwrap();
        assert_eq!(hash(message).as_slice(), expected.as_slice());
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
    /// not word-aligned. On Xtensa `message_word` is the `l32i` plus
    /// `ssai`/`src` assembly, so this is the run that executes it. Other
    /// targets take `from_be_bytes` and still instantiate every offset.
    #[test]
    fn message_word_matches_from_be_bytes() {
        let mut storage = [0u8; 160];
        for (i, byte) in storage.iter_mut().enumerate() {
            *byte = i.wrapping_mul(17).wrapping_add(3) as u8;
        }
        storage[..8].copy_from_slice(&[0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07]);

        fn check(block: &[u8; 128]) {
            macro_rules! word {
                ($byte:literal) => {{
                    let expect = u64::from_be_bytes(block[$byte..$byte + 8].try_into().unwrap());
                    assert_eq!(
                        super::message_word::<$byte>(block),
                        expect,
                        "byte {}",
                        $byte
                    );
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
        }

        let aligned: &[u8; 128] = storage[..128].try_into().unwrap();
        assert_eq!(super::message_word::<0>(aligned), 0x0001_0203_0405_0607);
        check(aligned);
        // `[u8; 128]` has alignment 1, so these references are not word-aligned.
        for start in [1usize, 3] {
            let block: &[u8; 128] = storage[start..start + 128].try_into().unwrap();
            check(block);
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
