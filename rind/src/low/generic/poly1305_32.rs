// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Poly1305 in five 26-bit limbs held in `u32`s, for the portable backend
//! on Xtensa (the ESP32-S3). Each limb product is one 32x32->64-bit multiply,
//! `mull` and `muluh` on Xtensa, where HACL*'s 26-bit limbs, which libcrux
//! keeps in `u64`s, take a full 64x64-bit multiply each and 64-bit carries.
//! Other targets build it only in tests, which check it against HACL*'s and
//! the 64-bit Poly1305; 32-bit ones keep HACL*'s.
//!
//! The radix and the carry chain are Andrew Moon's poly1305-donna-32 (public
//! domain or MIT), as the fork's 26-bit Poly1305 line (steelhead99x/rind#191)
//! has them; the code is rind's. Nothing proves it (steelhead99x/rind#281
//! plans the proof). Its correctness argument is the bounds below, which keep
//! every sum inside its type, and its tests: RFC 8439's and aws-lc's vectors,
//! every carry out of the final reduction, and agreement with HACL*'s verified
//! Poly1305 and the 64-bit one over random keys, messages and splits.
//!
//! It adds, multiplies, shifts and masks, and branches on no secret: the final
//! choice between `h` and `h - p` is a mask. Its time depends on no secret on
//! a core whose 32x32->64-bit multiply takes the same time for every operand,
//! as the portable backend assumes.

use super::blockwise::Blockwise;
use crate::low::{Zeroable, zeroise_value};

/// The low 26 bits.
const MASK: u32 = 0x3ff_ffff;

pub(crate) struct Poly1305 {
    /// The accumulator, 130 bits and a few more in five 26-bit limbs, least
    /// significant first.
    h: [u32; 5],

    /// The clamped first half of the key, in five 26-bit limbs.
    r: [u32; 5],

    /// The second half of the key, added to the result, in four 32-bit words.
    s: [u32; 4],

    /// Unprocessed input.
    bw: Blockwise<16>,
}

impl Poly1305 {
    pub(crate) fn new(key: &[u8; 32]) -> Self {
        // Clamp r by ANDing it with 0x0ffffffc0ffffffc0ffffffc0fffffff (RFC
        // 8439 section 2.5.1), splitting it into limbs as it is read: so
        // r[0], r[1], r[2] and r[3] < 2^26, and r[4] < 2^20.
        let r = [
            read32(key, 0) & 0x3ff_ffff,
            (read32(key, 3) >> 2) & 0x3ff_ff03,
            (read32(key, 6) >> 4) & 0x3ff_c0ff,
            (read32(key, 9) >> 6) & 0x3f0_3fff,
            (read32(key, 12) >> 8) & 0x00f_ffff,
        ];
        let s = [
            read32(key, 16),
            read32(key, 20),
            read32(key, 24),
            read32(key, 28),
        ];
        Self {
            h: [0; 5],
            r,
            s,
            bw: Blockwise::new(),
        }
    }

    pub(crate) fn add_bytes(&mut self, bytes: &[u8]) {
        let bytes = self.bw.add_leading(bytes);

        if let Some(block) = self.bw.take() {
            self.blocks(&block, 1 << 24);
        }

        let (full_blocks, remainder) = bytes.as_chunks::<16>();
        self.blocks(full_blocks.as_flattened(), 1 << 24);

        self.bw.add_trailing(remainder);
    }

    pub(crate) fn finish(mut self) -> [u8; 16] {
        // The short last block's 1 goes after its bytes, not at bit 128.
        let mut block = [0u8; 16];
        let tail = self.bw.peek_remaining().map(|tail| {
            block[..tail.len()].copy_from_slice(tail);
            block[tail.len()] = 0x01;
        });
        if tail.is_some() {
            self.blocks(&block, 0);
        }

        let [mut h0, mut h1, mut h2, mut h3, mut h4] = self.h;

        // Carry fully: each limb below 2^26, and h4's carry folded into h0
        // as 5, since 2^130 = 5 (mod p), as poly1305-donna-32 does. One pass
        // is enough. `blocks` leaves h0, h2, h3 and h4 under 2^26 and h1
        // under 2^26 + 2^6, so h1's carry is 0 or 1, and h4 carries only if
        // h1 did, leaving h1 under 2^6. h0 then exceeds 2^26 - 1 only by
        // that carry's 5, so its carry is 0 or 1, and 1 only when h1 is
        // under 2^6, so adding it leaves h1 under 2^26. `finish_carries_far`
        // takes every carry here.
        let mut c;
        c = h1 >> 26;
        h1 &= MASK;
        h2 = h2.wrapping_add(c);
        c = h2 >> 26;
        h2 &= MASK;
        h3 = h3.wrapping_add(c);
        c = h3 >> 26;
        h3 &= MASK;
        h4 = h4.wrapping_add(c);
        c = h4 >> 26;
        h4 &= MASK;
        h0 = h0.wrapping_add(c.wrapping_mul(5));
        c = h0 >> 26;
        h0 &= MASK;
        h1 = h1.wrapping_add(c);

        // g = h + 5 - 2^130, which is h - p, and is not negative exactly
        // when h >= p. Its sign is the top bit of g4, so the mask picks g
        // then and h otherwise. `black_box` keeps the compiler from turning
        // that select into a branch on h, which RISC-V, with no conditional
        // move, would emit.
        let mut g0 = h0.wrapping_add(5);
        c = g0 >> 26;
        g0 &= MASK;
        let mut g1 = h1.wrapping_add(c);
        c = g1 >> 26;
        g1 &= MASK;
        let mut g2 = h2.wrapping_add(c);
        c = g2 >> 26;
        g2 &= MASK;
        let mut g3 = h3.wrapping_add(c);
        c = g3 >> 26;
        g3 &= MASK;
        let g4 = h4.wrapping_add(c).wrapping_sub(1 << 26);

        let use_g = core::hint::black_box((g4 >> 31).wrapping_sub(1));
        let use_h = !use_g;
        h0 = (h0 & use_h) | (g0 & use_g);
        h1 = (h1 & use_h) | (g1 & use_g);
        h2 = (h2 & use_h) | (g2 & use_g);
        h3 = (h3 & use_h) | (g3 & use_g);
        h4 = (h4 & use_h) | (g4 & use_g);

        // Repack the low 128 bits into 32-bit words, and add s mod 2^128.
        let words = [
            h0 | (h1 << 26),
            (h1 >> 6) | (h2 << 20),
            (h2 >> 12) | (h3 << 14),
            (h3 >> 18) | (h4 << 8),
        ];
        add_s(words, self.s)
    }

    /// h = (h + block) * r for each 16-byte block of `bytes`, where `hibit`
    /// is 2^24 in the top limb, the 2^128 RFC 8439 sets above a whole block,
    /// or 0 for a padded last block, which carries its own 1.
    ///
    /// Blocks that start on a word load as words; others byte by byte, as
    /// Xtensa has no misaligned load. Where they start is public.
    fn blocks(&mut self, bytes: &[u8], hibit: u32) {
        // SAFETY: every bit pattern is a `u32`, so aligned bytes may be read
        // as words.
        let (head, words, tail) = unsafe { bytes.align_to::<u32>() };
        let mut st = Blocks::new(self, hibit);
        if head.is_empty() && tail.is_empty() {
            for w in words.as_chunks::<4>().0 {
                st.block(w.map(u32::from_le));
            }
        } else {
            for b in bytes.as_chunks::<16>().0 {
                st.block([read32(b, 0), read32(b, 4), read32(b, 8), read32(b, 12)]);
            }
        }
        self.h = st.h;
    }
}

/// `Poly1305::blocks`' working state, kept in registers across its loop.
struct Blocks {
    h: [u32; 5],
    r: [u32; 5],
    /// 5 * r[1..], for the products at or above 2^130.
    s: [u32; 4],
    hibit: u32,
}

impl Blocks {
    #[inline(always)]
    fn new(p: &Poly1305, hibit: u32) -> Self {
        let r = p.r;
        // 2^130 = 5 (mod p), so a product's part at or above 2^130 folds
        // back in multiplied by 5: s1..s4 < 5 * 2^26 < 2^29.
        Self {
            h: p.h,
            r,
            s: [1, 2, 3, 4].map(|i| r[i].wrapping_mul(5)),
            hibit,
        }
    }

    /// h = (h + m) * r for the block `m`, as four little-endian words.
    #[inline(always)]
    fn block(&mut self, m: [u32; 4]) {
        let [mut h0, mut h1, mut h2, mut h3, mut h4] = self.h;

        // On entry, h0, h2, h3 and h4 < 2^26 and h1 < 2^26 + 2^6 (from
        // the last block's carries, or 0), and each limb of the block is
        // under 2^26, or 2^25 for the top one, so each sum is under 2^27
        // but h1, which is under 2^27 + 2^6.
        // A debug build's overflow checks would branch on the secret, hence
        // wrapping arithmetic, here and below.
        h0 = h0.wrapping_add(m[0] & MASK);
        h1 = h1.wrapping_add(((m[0] >> 26) | (m[1] << 6)) & MASK);
        h2 = h2.wrapping_add(((m[1] >> 20) | (m[2] << 12)) & MASK);
        h3 = h3.wrapping_add(((m[2] >> 14) | (m[3] << 18)) & MASK);
        h4 = h4.wrapping_add((m[3] >> 8) | self.hibit);

        // The product, folded and carried; see `reduce`.
        [h0, h1, h2, h3, h4] = reduce([h0, h1, h2, h3, h4], self.r, self.s);

        self.h = [h0, h1, h2, h3, h4];
    }
}

/// `words` plus `s` mod 2^128, as the tag's bytes. Xtensa takes `add_s_split`;
/// host tests take `add_s_wide`, or the split form when they force it. The two
/// agree on every input, which a test checks.
#[inline(always)]
fn add_s(words: [u32; 4], s: [u32; 4]) -> [u8; 16] {
    #[cfg(target_arch = "xtensa")]
    return add_s_split(words, s);
    #[cfg(not(target_arch = "xtensa"))]
    return if tests::FORCE_SPLIT.with(|f| f.get()) {
        add_s_split(words, s)
    } else {
        add_s_wide(words, s)
    };
}

/// The sum with a `u64` carry, the plain form `add_s_split` is checked against.
#[cfg(not(target_arch = "xtensa"))]
#[inline(always)]
fn add_s_wide(words: [u32; 4], s: [u32; 4]) -> [u8; 16] {
    let mut tag = [0u8; 16];
    let mut carry = 0u64;
    for ((out, word), s) in tag.as_chunks_mut::<4>().0.iter_mut().zip(words).zip(s) {
        let sum = u64::from(word)
            .wrapping_add(u64::from(s))
            .wrapping_add(carry);
        *out = (sum as u32).to_le_bytes();
        carry = sum >> 32;
    }
    tag
}

/// The sum in 16-bit halves, so the carry is a shift of a `u32` sum: a `u64`
/// add is a branch on its carry on Xtensa.
#[cfg(any(target_arch = "xtensa", test))]
#[inline(always)]
fn add_s_split(words: [u32; 4], s: [u32; 4]) -> [u8; 16] {
    let mut tag = [0u8; 16];
    let mut carry = 0u32;
    for ((out, word), s) in tag.as_chunks_mut::<4>().0.iter_mut().zip(words).zip(s) {
        let lo = (word & 0xffff).wrapping_add(s & 0xffff).wrapping_add(carry);
        let hi = (word >> 16).wrapping_add(s >> 16).wrapping_add(lo >> 16);
        *out = ((lo & 0xffff) | (hi << 16)).to_le_bytes();
        carry = hi >> 16;
    }
    tag
}

/// h * r partially reduced: the limbs of `h` times `r`, with the products at
/// or above 2^130 folded back through `s` = 5 * r[1..], then carried so each
/// limb is under 2^26 but the second, which is under 2^26 + 2^6. Xtensa takes
/// `reduce_split`; host tests take `reduce_wide`, or the split form when they
/// force it. The two agree on every input within the bounds in
/// `Blocks::block`, which a test checks.
#[inline(always)]
fn reduce(h: [u32; 5], r: [u32; 5], s: [u32; 4]) -> [u32; 5] {
    #[cfg(target_arch = "xtensa")]
    return reduce_split(h, r, s);
    // A test can force the split form on the host, so the RFC 8439, aws-lc and
    // HACL* tests run it end to end.
    #[cfg(not(target_arch = "xtensa"))]
    return if tests::FORCE_SPLIT.with(|f| f.get()) {
        reduce_split(h, r, s)
    } else {
        reduce_wide(h, r, s)
    };
}

/// `reduce` over 64-bit sums: five 26-bit products' sums in `u64`s, then
/// the carry chain.
#[cfg(not(target_arch = "xtensa"))]
#[inline(always)]
fn reduce_wide(
    [mut h0, mut h1, mut h2, mut h3, mut h4]: [u32; 5],
    r: [u32; 5],
    s: [u32; 4],
) -> [u32; 5] {
    let [r0, r1, r2, r3, r4] = r;
    let [s1, s2, s3, s4] = s;
    // Schoolbook multiplication, with the products at or above 2^130
    // folded back through s. Each product is under
    // (2^27 + 2^6) * 5 * 2^26, so each sum of five is under 2^58.
    let h = [h0, h1, h2, h3, h4];
    let d0 = dot(h, [r0, s4, s3, s2, s1]);
    let d1 = dot(h, [r1, r0, s4, s3, s2]);
    let d2 = dot(h, [r2, r1, r0, s4, s3]);
    let d3 = dot(h, [r3, r2, r1, r0, s4]);
    let d4 = dot(h, [r4, r3, r2, r1, r0]);

    // Partially reduce: carry each limb into the next. Each carry is
    // the sum shifted down 26 bits, plus the carry before, so under
    // 2^32. d4 holds no product with s, so with d3's carry it is under
    // 2^27 * (2^20 + 4 * 2^26) + 2^32, its carry under 2^29 + 2^22, and
    // h0, under 2^26, plus 5 times that carry is under 2^32.
    let mut c;
    c = (d0 >> 26) as u32;
    h0 = d0 as u32 & MASK;
    let d1 = d1.wrapping_add(u64::from(c));
    c = (d1 >> 26) as u32;
    h1 = d1 as u32 & MASK;
    let d2 = d2.wrapping_add(u64::from(c));
    c = (d2 >> 26) as u32;
    h2 = d2 as u32 & MASK;
    let d3 = d3.wrapping_add(u64::from(c));
    c = (d3 >> 26) as u32;
    h3 = d3 as u32 & MASK;
    let d4 = d4.wrapping_add(u64::from(c));
    c = (d4 >> 26) as u32;
    h4 = d4 as u32 & MASK;
    h0 = h0.wrapping_add(c.wrapping_mul(5));
    c = h0 >> 26;
    h0 &= MASK;
    h1 = h1.wrapping_add(c);
    [h0, h1, h2, h3, h4]
}

/// `reduce` with every sum in `u32`s, for Xtensa, where LLVM adds two `u64`s
/// as an `add` and a conditional branch on the carry: a branch on secret
/// data, and a taken one costs cycles. Nothing here is wider than 32 bits
/// but the multiplies, `mull` and `muluh`.
///
/// Each product `h * r`, with `h` under 2^28 and `r` or `s` under 5 * 2^26 (about 2^28.3), is split at bit 28 into
/// `lo = h * r mod 2^28` and `hi = h * r >> 28`, from `h << 4` times `r`:
/// its low word is `16 * lo` and its high word is `hi`. A limb's sum is then
/// `a + 2^28 * b`, `a` the five `lo`s (under 5 * 2^28) and `b` the five `hi`s,
/// each in a `u32`. Its carry into the next limb is `(a >> 26) + 4 * b`, which
/// is under 2^32: `h` is under 2^27 + 2^6 and `r` and `s` under 5 * 2^26, so a
/// `hi` is under (2^27 + 2^6) * 5 * 2^26 / 2^28 < 1.7 * 10^8, `b` under
/// 8.4 * 10^8 and `4 * b` under 3.4 * 10^9. The carry in is split at bit 26
/// so its low part adds to `a` without overflow. Every limb and carry equals
/// `reduce_wide`'s.
#[cfg(any(target_arch = "xtensa", test))]
#[inline(always)]
fn reduce_split(h: [u32; 5], r: [u32; 5], s: [u32; 4]) -> [u32; 5] {
    let [r0, r1, r2, r3, r4] = r;
    let [s1, s2, s3, s4] = s;
    let h = h.map(|h| h << 4);
    // (low 28 bits of the product, the product shifted down 28 bits), summed.
    let split = |terms: [u32; 5]| {
        let (mut a, mut b) = (0u32, 0u32);
        for (h, r) in h.into_iter().zip(terms) {
            a = a.wrapping_add(h.wrapping_mul(r) >> 4);
            b = b.wrapping_add(mulhi(h, r));
        }
        (a, b)
    };
    let d = [
        split([r0, s4, s3, s2, s1]),
        split([r1, r0, s4, s3, s2]),
        split([r2, r1, r0, s4, s3]),
        split([r3, r2, r1, r0, s4]),
        split([r4, r3, r2, r1, r0]),
    ];
    let mut out = [0u32; 5];
    let mut c = 0u32;
    for (out, (a, b)) in out.iter_mut().zip(d) {
        let t = a.wrapping_add(c & MASK);
        *out = t & MASK;
        c = (t >> 26).wrapping_add(c >> 26).wrapping_add(b << 2);
    }
    // h4's carry folds into h0 as 5, as 2^130 = 5 (mod p); h0 is under 2^26
    // and 5 * c under 2^32.
    out[0] = out[0].wrapping_add(c.wrapping_mul(5));
    let c = out[0] >> 26;
    out[0] &= MASK;
    out[1] = out[1].wrapping_add(c);
    out
}

/// The high word of `a * b`, `muluh` on Xtensa.
#[cfg(any(target_arch = "xtensa", test))]
#[inline(always)]
fn mulhi(a: u32, b: u32) -> u32 {
    (u64::from(a).wrapping_mul(u64::from(b)) >> 32) as u32
}

/// The sum of the 64-bit products of `a`'s and `b`'s limbs, pairwise: each
/// each one 32x32->64-bit multiply.
#[cfg(not(target_arch = "xtensa"))]
#[inline(always)]
fn dot(a: [u32; 5], b: [u32; 5]) -> u64 {
    a.iter().zip(b).fold(0, |sum, (a, b)| {
        sum.wrapping_add(u64::from(*a).wrapping_mul(u64::from(b)))
    })
}

fn read32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

impl Drop for Poly1305 {
    fn drop(&mut self) {
        // The clamped `r` and the pad `s` are the key, `h` is a function of
        // it and the message, and `bw` holds message bytes: one wipe of the
        // whole value, as AGENTS.md has keyed state do.
        zeroise_value(self);
    }
}

impl Zeroable for Poly1305 {}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use core::cell::Cell;

    use super::*;

    thread_local! {
        /// Makes `reduce` take `reduce_split`, as Xtensa does.
        pub(super) static FORCE_SPLIT: Cell<bool> = const { Cell::new(false) };
    }

    // Every test above that checks a tag, with `reduce_split` doing the
    // reductions, as it does on Xtensa.
    #[test]
    fn through_split() {
        FORCE_SPLIT.with(|f| f.set(true));
        aws_lc();
        rfc8439();
        finish_carries_far();
        matches_hacl_and_generic();
        FORCE_SPLIT.with(|f| f.set(false));
    }

    use crate::low::ct;
    use crate::test::file_test;

    // aws-lc's vectors, of every length and carry, split so the buffering
    // of partial blocks runs too.
    #[test]
    fn aws_lc() {
        for test in file_test::tests("aws-lc/crypto/poly1305/poly1305_tests.txt") {
            let mut p = Poly1305::new(&test.bytes("Key").try_into().unwrap());
            let input = test.bytes("Input");
            let (head, tail) = input.split_at(input.len() / 3);
            p.add_bytes(head);
            p.add_bytes(tail);
            assert_eq!(p.finish(), &test.bytes("MAC")[..], "{test}");
        }
    }

    // RFC 8439 section 2.5.2, and appendix A.3's vectors #5 to #11, which
    // reach the final reduction's edges: an accumulator at or just past p,
    // s carrying out of the top word, and carries across every limb.
    #[test]
    fn rfc8439() {
        let mut key = [0u8; 32];
        hex_into(
            "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b",
            &mut key,
        );
        let mut p = Poly1305::new(&key);
        p.add_bytes(b"Cryptographic Forum Research Group");
        assert_eq!(p.finish(), hex16("a8061dc1305136c6c22b8baf0c0127a9"));

        let one = |r: &str, s: &str, msg: &str, tag: &str| {
            let mut key = [0u8; 32];
            hex_into(r, &mut key[..16]);
            hex_into(s, &mut key[16..]);
            let msg = hex(msg);
            let mut p = Poly1305::new(&key);
            p.add_bytes(&msg);
            assert_eq!(p.finish(), hex16(tag), "{r} {s} {msg:02x?}");
        };
        let zero = "00000000000000000000000000000000";
        let two = "02000000000000000000000000000000";
        let ones = "ffffffffffffffffffffffffffffffff";
        one(two, zero, ones, "03000000000000000000000000000000");
        one(two, ones, two, "03000000000000000000000000000000");
        one(
            "01000000000000000000000000000000",
            zero,
            "fffffffffffffffffffffffffffffffff0ffffffffffffffffffffffffffffff\
             11000000000000000000000000000000",
            "05000000000000000000000000000000",
        );
        one(
            "01000000000000000000000000000000",
            zero,
            "fffffffffffffffffffffffffffffffffbfefefefefefefefefefefefefefefe\
             01010101010101010101010101010101",
            zero,
        );
        one(
            two,
            zero,
            "fdffffffffffffffffffffffffffffff",
            "faffffffffffffffffffffffffffffff",
        );
        one(
            "01000000000000000400000000000000",
            zero,
            "e33594d7505e43b900000000000000003394d7505e4379cd0100000000000000\
             0000000000000000000000000000000001000000000000000000000000000000",
            "14000000000000005500000000000000",
        );
        one(
            "01000000000000000400000000000000",
            zero,
            "e33594d7505e43b900000000000000003394d7505e4379cd0100000000000000\
             00000000000000000000000000000000",
            "13000000000000000000000000000000",
        );
    }

    // Blocks that leave the accumulator as [2^26 - 5, 2^26, 2^26 - 1,
    // 2^26 - 1, 2^26 - 1] before `finish`, 2^130 + 2^26 - 5, so `finish`
    // carries out of every limb, folds h4's carry into h0 as 5, and carries
    // out of h0 into h1, and as [4, 2^26, 2^26 - 1, 2^26 - 1, 2^26 - 1],
    // whose fold carries no further. Each tag is (h mod p + s) mod 2^128,
    // with s zero and all ones, so adding s carries through every word too.
    // From steelhead99x/rind#191.
    #[test]
    fn finish_carries_far() {
        const M: u32 = MASK;
        let cases: [(&str, &str, [u32; 5], &str, &str); 2] = [
            (
                "00000008fcff0f000000000000000000",
                "24fcb28d4e41852590bd93a959856f84",
                [M - 4, M + 1, M, M, M],
                "00000004000000000000000000000000",
                "ffffff03000000000000000000000000",
            ),
            (
                "00000004000000000000000000000000",
                "feffffffffffffffffffcccc8c999999ffffffffffffffffffffffffff000000",
                [4, M + 1, M, M, M],
                "09000000000000000000000000000000",
                "08000000000000000000000000000000",
            ),
        ];
        for (r, msg, h, with_zero, with_ones) in cases {
            for (s, tag) in [("00", with_zero), ("ff", with_ones)] {
                let mut key = [0u8; 32];
                hex_into(r, &mut key[..16]);
                key[16..].fill(u8::from_str_radix(s, 16).unwrap());
                let msg = hex(msg);
                let mut p = Poly1305::new(&key);
                p.add_bytes(&msg);
                assert_eq!(p.h, h, "{r}");
                assert_eq!(p.finish(), hex16(tag), "{r} {s}");
            }
        }
    }

    // Against the 64-bit Poly1305 and, where the portable backend builds,
    // HACL*'s verified one, which other 32-bit targets run: every length
    // up to 300 bytes, random lengths up to 4 KiB, keys and messages of all
    // ones, which push the accumulator to its largest values before the
    // final reduction, and of all zeros. Each runs whole and in random
    // pieces, starting at each offset from a word, so both of `blocks`'
    // loads run. The key and message are secret, so under `admin/ctgrind`
    // this also checks this Poly1305 is constant time in both.
    #[test]
    fn matches_hacl_and_generic() {
        let mut rng = 0x1305_5eed_0f90_1730u64;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng
        };
        let mut cases: Vec<([u8; 32], Vec<u8>)> = Vec::new();
        for byte in [0xff, 0] {
            cases.push(([byte; 32], vec![byte; 4096 + 15]));
        }
        let long: Vec<u8> = (0..300).map(|_| next() as u8).collect();
        for len in 0..=long.len() {
            cases.push((core::array::from_fn(|_| next() as u8), long[..len].to_vec()));
        }
        for _ in 0..64 {
            let len = next() as usize % 4097;
            let msg = (0..len).map(|_| next() as u8).collect();
            cases.push((core::array::from_fn(|_| next() as u8), msg));
        }

        for (i, (key, msg)) in cases.iter().enumerate() {
            let mut want = crate::low::generic::poly1305::Poly1305::new(key);
            want.add_bytes(msg);
            let want = want.finish();

            #[cfg(rind_backend = "portable")]
            {
                let mut hacl = crate::low::portable::poly1305::Hacl::new(key);
                hacl.add_bytes(msg);
                assert_eq!(hacl.finish(), want, "HACL*");
            }

            // At `i % 4` bytes past a word.
            let mut buf = vec![0u8; msg.len() + 8];
            let start = buf.as_ptr().addr().wrapping_neg() % 4 + i % 4;
            let bytes = &mut buf[start..start + msg.len()];
            bytes.copy_from_slice(msg);
            ct::secret_slice(key);
            ct::secret_slice(bytes);

            let mut got = Poly1305::new(key);
            got.add_bytes(bytes);
            assert_eq!(ct::into_public(got.finish()), want, "{} bytes", msg.len());
            let mut got = Poly1305::new(key);
            let mut rest = &bytes[..];
            while !rest.is_empty() {
                let (piece, tail) = rest.split_at(next() as usize % (rest.len().min(70) + 1));
                got.add_bytes(piece);
                rest = tail;
            }
            let got = ct::into_public(got.finish());
            assert_eq!(got, want, "{} bytes in pieces", msg.len());
            ct::public_slice(key);
            ct::public_slice(bytes);
        }
    }

    // `add_s_split`, which Xtensa runs, against `add_s_wide`: edges (all ones,
    // carry through every word) and random words.
    #[test]
    fn add_s_split_matches_wide() {
        let mut rng = 0x1305_5eed_f00d_cafeu64;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng as u32
        };
        let edges = [0, 1, 0xffff, 0x1_0000, 0x7fff_ffff, 0x8000_0000, u32::MAX];
        for a in edges {
            for b in edges {
                let (w, s) = ([a, b, a, b], [b, a, b, a]);
                assert_eq!(add_s_split(w, s), add_s_wide(w, s), "{w:x?} {s:x?}");
                let (w, s) = ([u32::MAX; 4], [a, b, a, b]);
                assert_eq!(add_s_split(w, s), add_s_wide(w, s), "{w:x?} {s:x?}");
            }
        }
        for _ in 0..20_000 {
            let w = [(); 4].map(|()| next());
            let s = [(); 4].map(|()| next());
            assert_eq!(add_s_split(w, s), add_s_wide(w, s), "{w:x?} {s:x?}");
        }
    }

    // `reduce_split`, which Xtensa runs, against `reduce_wide` on states at
    // the edges of `Blocks::block`'s bounds (h under 2^27, h1 under
    // 2^27 + 2^6, r the largest a clamped key gives) and at random within
    // them: every limb must match, so the carries do.
    #[test]
    fn split_matches_wide() {
        let mut rng = 0x5eed_1305_cafe_f00du64;
        let mut next = move || {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            rng as u32
        };
        let top = [
            (1 << 27) - 1,
            (1 << 27) + 63,
            (1 << 27) - 1,
            (1 << 27) - 1,
            (1 << 26) + (1 << 25) - 1,
        ];
        let rmax = [
            MASK,
            MASK & 0x3ff_ff03,
            MASK & 0x3ff_c0ff,
            MASK & 0x3f0_3fff,
            0xf_ffff,
        ];
        let mut cases = vec![(top, rmax), ([0; 5], rmax), (top, [0; 5])];
        for i in 0..20_000 {
            let h = core::array::from_fn(|k| {
                let v = next() & (top[k] | (1 << 26));
                if i % 4 == 0 {
                    top[k] - (v & 7)
                } else {
                    v.min(top[k])
                }
            });
            let r: [u32; 5] = core::array::from_fn(|k| {
                let v = next() & rmax[k];
                if i % 3 == 0 {
                    (rmax[k] - (v & 3 & rmax[k])) & rmax[k]
                } else {
                    v
                }
            });
            cases.push((h, r));
        }
        for (h, r) in cases {
            let s = [1, 2, 3, 4].map(|i| r[i].wrapping_mul(5));
            assert_eq!(reduce_split(h, r, s), reduce_wide(h, r, s), "{h:x?} {r:x?}");
        }
    }

    fn hex(s: &str) -> Vec<u8> {
        hex::decode(s).unwrap()
    }

    fn hex_into(s: &str, out: &mut [u8]) {
        out.copy_from_slice(&hex(s));
    }

    fn hex16(s: &str) -> [u8; 16] {
        hex(s).try_into().unwrap()
    }
}
