// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Poly1305 in five 26-bit limbs, for the portable backend on 32-bit
//! targets. Each limb product is one 32x32->64-bit multiply, which a 32-bit
//! core does in one or two instructions, where `generic::poly1305`'s 64-bit
//! limbs take a library call for each 64x64->128-bit product, and HACL*'s
//! 26-bit limbs, which libcrux keeps in `u64`s, take 64-bit multiplies a
//! 32-bit compiler cannot always narrow.
//!
//! The radix and the carry chain are Andrew Moon's poly1305-donna-32 (public
//! domain or MIT); the code is rind's. Its correctness argument is the bounds
//! below, which keep every sum inside its type, and its tests: RFC 8439's and
//! aws-lc's vectors, and agreement with HACL*'s verified Poly1305 and
//! Graviola's 64-bit one over random keys, messages and splits.
//!
//! It adds, multiplies, shifts and masks, and branches on no secret: the final
//! choice between `h` and `h - p` is a mask. Its time depends on no secret on
//! a core whose 32x32->64-bit multiply takes the same time for every operand,
//! as the ESP32-S3's and Cortex-M4's do; a Cortex-M3's `umull` ends early on
//! small operands.

use super::blockwise::Blockwise;
use crate::low::ct;

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
        // r[0] < 2^26, r[1], r[2] and r[3] < 2^26, and r[4] < 2^20.
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
            self.blocks(&[block], 1 << 24);
        }

        let (full_blocks, remainder) = bytes.as_chunks::<16>();
        self.blocks(full_blocks, 1 << 24);

        self.bw.add_trailing(remainder);
    }

    pub(crate) fn finish(mut self) -> [u8; 16] {
        if let Some(tail) = self.bw.clone().peek_remaining() {
            // The short last block's 1 goes after its bytes, not at bit 128.
            let mut block = [0u8; 16];
            block[..tail.len()].copy_from_slice(tail);
            block[tail.len()] = 0x01;
            self.blocks(&[block], 0);
        }

        let [mut h0, mut h1, mut h2, mut h3, mut h4] = self.h;

        // Carry fully: each limb below 2^26, and h4's carry folded into h0
        // as 5, since 2^130 = 5 (mod p). The second carry from h0 can leave
        // h1 at 2^26, so the chain runs again to h4, which then exceeds
        // 2^26 - 1 only when h >= 2^130 > p, the case `g` below replaces.
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
        c = h1 >> 26;
        h1 &= MASK;
        h2 = h2.wrapping_add(c);
        c = h2 >> 26;
        h2 &= MASK;
        h3 = h3.wrapping_add(c);
        c = h3 >> 26;
        h3 &= MASK;
        h4 = h4.wrapping_add(c);

        // g = h + 5 - 2^130, which is h - p, and is not negative exactly
        // when h >= p. Its sign is the top bit of g4, so the mask picks g
        // then and h otherwise, without branching on h.
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

        let use_g = (g4 >> 31).wrapping_sub(1);
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
        for (i, (word, s)) in words.iter().zip(self.s).enumerate() {
            let sum = u64::from(*word)
                .wrapping_add(u64::from(s))
                .wrapping_add(carry);
            tag[i * 4..i * 4 + 4].copy_from_slice(&(sum as u32).to_le_bytes());
            carry = sum >> 32;
        }
        tag
    }

    /// h = (h + block) * r for each block, where `hibit` is 2^24 in the top
    /// limb, the 2^128 RFC 8439 sets above a whole block, or 0 for a padded
    /// last block, which carries its own 1.
    fn blocks(&mut self, blocks: &[[u8; 16]], hibit: u32) {
        let [r0, r1, r2, r3, r4] = self.r;
        // 2^130 = 5 (mod p), so a product's part at or above 2^130 folds
        // back in multiplied by 5: s1..s4 < 5 * 2^26 < 2^29.
        let (s1, s2, s3, s4) = (
            r1.wrapping_mul(5),
            r2.wrapping_mul(5),
            r3.wrapping_mul(5),
            r4.wrapping_mul(5),
        );
        let [mut h0, mut h1, mut h2, mut h3, mut h4] = self.h;

        for block in blocks {
            // On entry, h0, h2, h3 and h4 < 2^26 and h1 < 2^26 + 2^6 (from
            // the last block's carries, or 0), and each limb of the block is
            // under 2^26, or 2^25 for the top one, so each sum is under 2^27
            // but h1, which is under 2^27 + 2^6.
            h0 = h0.wrapping_add(read32(block, 0) & MASK);
            h1 = h1.wrapping_add((read32(block, 3) >> 2) & MASK);
            h2 = h2.wrapping_add((read32(block, 6) >> 4) & MASK);
            h3 = h3.wrapping_add((read32(block, 9) >> 6) & MASK);
            h4 = h4.wrapping_add((read32(block, 12) >> 8) | hibit);
            // A debug build's overflow checks would branch on the secret, as
            // these assertions would without declassifying, hence wrapping
            // arithmetic.
            debug_assert!(ct::into_public(h0 | h2 | h3 | h4) < 1 << 27);
            debug_assert!(ct::into_public(h1) < (1 << 27) + (1 << 6));

            // Schoolbook multiplication, with the products at or above 2^130
            // folded back through s. Each product is under
            // (2^27 + 2^6) * 5 * 2^26, so each sum of five is under 2^58.
            let d0 = mul(h0, r0)
                .wrapping_add(mul(h1, s4))
                .wrapping_add(mul(h2, s3))
                .wrapping_add(mul(h3, s2))
                .wrapping_add(mul(h4, s1));
            let d1 = mul(h0, r1)
                .wrapping_add(mul(h1, r0))
                .wrapping_add(mul(h2, s4))
                .wrapping_add(mul(h3, s3))
                .wrapping_add(mul(h4, s2));
            let d2 = mul(h0, r2)
                .wrapping_add(mul(h1, r1))
                .wrapping_add(mul(h2, r0))
                .wrapping_add(mul(h3, s4))
                .wrapping_add(mul(h4, s3));
            let d3 = mul(h0, r3)
                .wrapping_add(mul(h1, r2))
                .wrapping_add(mul(h2, r1))
                .wrapping_add(mul(h3, r0))
                .wrapping_add(mul(h4, s4));
            let mut d4 = mul(h0, r4)
                .wrapping_add(mul(h1, r3))
                .wrapping_add(mul(h2, r2))
                .wrapping_add(mul(h3, r1))
                .wrapping_add(mul(h4, r0));

            // Partially reduce: carry each limb into the next. Each carry
            // is the sum shifted down 26 bits, plus the carry before, so
            // under 2^32. d4 holds no product with s, so with d3's carry it
            // is under 2^27 * (2^20 + 4 * 2^26) + 2^32, its carry under
            // 2^29 + 2^22, and h0, under 2^26, plus 5 times that carry is
            // under 2^32.
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
            d4 = d4.wrapping_add(u64::from(c));
            c = (d4 >> 26) as u32;
            h4 = d4 as u32 & MASK;
            h0 = h0.wrapping_add(c.wrapping_mul(5));
            c = h0 >> 26;
            h0 &= MASK;
            h1 = h1.wrapping_add(c);
        }

        self.h = [h0, h1, h2, h3, h4];
    }
}

/// The 64-bit product of two 32-bit limbs: one `mull`/`muluh` pair on
/// Xtensa, one `umull` on Cortex-M.
#[inline(always)]
fn mul(a: u32, b: u32) -> u64 {
    u64::from(a).wrapping_mul(u64::from(b))
}

fn read32(bytes: &[u8], at: usize) -> u32 {
    u32::from_le_bytes(bytes[at..at + 4].try_into().unwrap())
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
    use crate::low::portable::poly1305::Hacl;
    use crate::test::file_test;

    // aws-lc's vectors, of every length and carry.
    #[test]
    fn aws_lc() {
        for test in file_test::tests("aws-lc/crypto/poly1305/poly1305_tests.txt") {
            let mut p = Poly1305::new(&test.bytes("Key").try_into().unwrap());
            let input = test.bytes("Input");
            // Split, so the buffering of partial blocks runs too.
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
        // #5
        one(two, zero, ones, "03000000000000000000000000000000");
        // #6
        one(two, ones, two, "03000000000000000000000000000000");
        // #7
        one(
            "01000000000000000000000000000000",
            zero,
            "fffffffffffffffffffffffffffffffff0ffffffffffffffffffffffffffffff\
             11000000000000000000000000000000",
            "05000000000000000000000000000000",
        );
        // #8
        one(
            "01000000000000000000000000000000",
            zero,
            "fffffffffffffffffffffffffffffffffbfefefefefefefefefefefefefefefe\
             01010101010101010101010101010101",
            zero,
        );
        // #9
        one(
            two,
            zero,
            "fdffffffffffffffffffffffffffffff",
            "faffffffffffffffffffffffffffffff",
        );
        // #10
        one(
            "01000000000000000400000000000000",
            zero,
            "e33594d7505e43b900000000000000003394d7505e4379cd01000000000000000000000000000000000000000000000001000000000000000000000000000000",
            "14000000000000005500000000000000",
        );
        // #11
        one(
            "01000000000000000400000000000000",
            zero,
            "e33594d7505e43b900000000000000003394d7505e4379cd010000000000000000000000000000000000000000000000",
            "13000000000000000000000000000000",
        );
    }

    // Each split of a message, so updates start partway into a block and
    // run past its end, gives the one-shot tag.
    #[test]
    fn split_updates() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8 * 7 + 1);
        let message: Vec<u8> = (0..80u8).map(|i| i.wrapping_mul(29)).collect();
        let mut p = Poly1305::new(&key);
        p.add_bytes(&message);
        let want = p.finish();
        for first in 0..=message.len() {
            for second in first..=message.len().min(first + 40) {
                let mut p = Poly1305::new(&key);
                p.add_bytes(&message[..first]);
                p.add_bytes(&message[first..second]);
                p.add_bytes(&message[second..]);
                assert_eq!(p.finish(), want, "{first}, {second}");
            }
        }
    }

    // Against Graviola's 64-bit Poly1305 and, where the portable backend
    // builds, HACL*'s verified one, which 32-bit targets ran before: random keys and messages of random lengths
    // up to 16 KiB, fed in random pieces, plus every length up to 300 bytes
    // and keys and messages of all ones, which push the accumulator to its
    // largest values before the final reduction, and of all zeros. The key
    // and message are secret, so under `admin/ctgrind` this also checks this
    // Poly1305 is constant time in both.
    #[test]
    fn matches_hacl_and_generic() {
        let mut rng = SplitMix(0x1305_5eed_0f90_1730);
        let mut cases: Vec<([u8; 32], Vec<u8>)> = Vec::new();
        for (key, byte) in [([0xff; 32], 0xff), ([0; 32], 0)] {
            cases.push((key, vec![byte; 16 * 1024 + 15]));
        }
        let long: Vec<u8> = (0..300).map(|_| rng.next() as u8).collect();
        for len in 0..=long.len() {
            cases.push((rng.key(), long[..len].to_vec()));
        }
        let seeds = if cfg!(debug_assertions) { 96 } else { 512 };
        for _ in 0..seeds {
            let len = rng.below(16 * 1024 + 1);
            let msg: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
            cases.push((rng.key(), msg));
        }

        for (key, msg) in &cases {
            ct::secret_slice(key);
            ct::secret_slice(msg);
            let mut want = crate::low::generic::poly1305::Poly1305::new(key);
            want.add_bytes(msg);
            let want = ct::into_public(want.finish());

            // HACL*'s builds only where the portable backend's dependencies
            // do.
            #[cfg(any(rind_backend = "arm", rind_backend = "portable"))]
            {
                let mut hacl = Hacl::new(key);
                hacl.add_bytes(msg);
                assert_eq!(ct::into_public(hacl.finish()), want, "HACL*");
            }

            // Whole, then in random pieces, some of them empty.
            let mut got = Poly1305::new(key);
            got.add_bytes(msg);
            assert_eq!(ct::into_public(got.finish()), want, "{} bytes", msg.len());
            let mut got = Poly1305::new(key);
            let mut rest = &msg[..];
            while !rest.is_empty() {
                let (piece, tail) = rest.split_at(rng.below(rest.len().min(70) + 1));
                got.add_bytes(piece);
                rest = tail;
            }
            assert_eq!(
                ct::into_public(got.finish()),
                want,
                "{} bytes in pieces",
                msg.len()
            );
        }
    }

    /// SplitMix64, for reproducible random cases.
    struct SplitMix(u64);

    impl SplitMix {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }

        fn key(&mut self) -> [u8; 32] {
            core::array::from_fn(|_| self.next() as u8)
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
