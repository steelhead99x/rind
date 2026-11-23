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
        let mut tag = [0u8; 16];
        let mut carry = 0u64;
        for ((out, word), s) in tag.as_chunks_mut::<4>().0.iter_mut().zip(words).zip(self.s) {
            let sum = u64::from(word)
                .wrapping_add(u64::from(s))
                .wrapping_add(carry);
            *out = (sum as u32).to_le_bytes();
            carry = sum >> 32;
        }
        tag
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
        let [r0, r1, r2, r3, r4] = self.r;
        let [s1, s2, s3, s4] = self.s;
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

        self.h = [h0, h1, h2, h3, h4];
    }
}

/// The sum of the 64-bit products of `a`'s and `b`'s limbs, pairwise: each
/// one `mull` and one `muluh` on Xtensa.
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
    use super::*;
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
