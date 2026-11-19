// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Poly1305 on armv7, in four 32-bit limbs and a small fifth.
//!
//! This is the radix of OpenSSL's `poly1305-armv4` integer path: the
//! accumulator is read and written as whole words, so a block needs no limb
//! split, and a block takes sixteen `umlal` and four small multiplies where
//! the five 26-bit limbs of `generic::poly1305_32` take twenty-five `umlal`.
//! The radix and the `5/4` folding of the high products are OpenSSL's, from
//! `poly1305-armv4.pl` (Andy Polyakov); the code is rind's, written in Rust
//! rather than ported line by line, and the arithmetic is below, with its
//! bounds.
//!
//! 32-bit Arm NEON intrinsics are unstable on the toolchain this crate builds
//! with, so this backend does not ship aws-lc's NEON Poly1305.
//!
//! # Representation and bounds
//!
//! The accumulator is `h = h0 + h1 2^32 + h2 2^64 + h3 2^96 + h4 2^128`. The
//! clamped key (RFC 8439 section 2.5.1) is `r0 < 2^28` and `r1, r2, r3 < 2^28`
//! with the low two bits clear, so `s_j = r_j + (r_j >> 2) = 5 r_j / 4` is
//! exact and under `1.25 * 2^28`. Since `2^130 = 5 (mod p)`, `2^128 = 5/4`, so
//! a product `h_i r_j 2^(32 (i + j))` with `i + j >= 4` and `j >= 1` becomes
//! `h_i s_j 2^(32 (i + j - 4))`. `h4 r0` is the only product left at `2^128`.
//!
//! * `h4 <= 4` between blocks, and `h4 <= 6` once a block and its 2^128 bit
//!   are added (a carry of at most 1 and the bit).
//! * Each of `d0..d3` sums at most four products of a word under `2^32` and a
//!   limb under `1.25 * 2^28`, plus `h4 s_j` under `6 * 1.25 * 2^28`, so each
//!   is under `5 * 2^60 + 2^31 < 2^63`, and the carry into the next is under
//!   `2^31`, so adding it cannot overflow a `u64`.
//! * `d4 = h4 r0 + carry < 6 * 2^28 + 2^31 < 2^32`. Its part at or above
//!   `2^130` returns as `5 * (d4 >> 2) < 5 * 2^30`, added into `h0` with a
//!   carry ripple, and `h4 = (d4 & 3) + carry <= 4`, where that ripple's carry
//!   out of `h3` is at most 1.
//! * `h < 5 * 2^128 < 2p` between blocks, so `finish` needs one conditional
//!   subtraction of `p`.
//!
//! The arithmetic is adds, multiplies, shifts, and masks. The final choice
//! between `h` and `h - p` is a mask. Its time depends on no secret on a core
//! whose 32x32->64-bit multiply takes the same time for every operand.

use crate::low::generic::blockwise::Blockwise;
use crate::low::{Zeroable, ct, zeroise_value};

pub(crate) struct Poly1305 {
    /// The accumulator: four words and `h4 <= 4`.
    h: [u32; 5],

    /// The clamped first half of the key, `r0..r3`.
    r: [u32; 4],

    /// The second half of the key, added to the result.
    s: [u32; 4],

    /// Unprocessed input.
    bw: Blockwise<16>,
}

impl Poly1305 {
    pub(crate) fn new(key: &[u8; 32]) -> Self {
        let word = |at: usize| u32::from_le_bytes(*key[at..].first_chunk::<4>().unwrap());
        Self {
            h: [0; 5],
            r: [
                word(0) & 0x0fff_ffff,
                word(4) & 0x0fff_fffc,
                word(8) & 0x0fff_fffc,
                word(12) & 0x0fff_fffc,
            ],
            s: [word(16), word(20), word(24), word(28)],
            bw: Blockwise::new(),
        }
    }

    pub(crate) fn add_bytes(&mut self, bytes: &[u8]) {
        let bytes = self.bw.add_leading(bytes);

        if let Some(block) = self.bw.take() {
            self.blocks(&[block], 1);
        }

        let (full_blocks, remainder) = bytes.as_chunks::<16>();
        self.blocks(full_blocks, 1);

        self.bw.add_trailing(remainder);
    }

    pub(crate) fn finish(mut self) -> [u8; 16] {
        // Copy the tail out before `blocks` borrows `self`. A full block was
        // already taken, so `tail` is shorter than 16 and the pad byte fits.
        let partial = self.bw.peek_remaining().map(|tail| {
            let mut block = [0u8; 16];
            block[..tail.len()].copy_from_slice(tail);
            block[tail.len()] = 0x01;
            block
        });
        if let Some(block) = partial {
            self.blocks(&[block], 0);
        }

        let [h0, h1, h2, h3, h4] = self.h;
        debug_assert!(ct::into_public(h4) <= 4);

        // g = h + 5, which is h - p + 2^130, and has bit 130 set exactly when
        // h >= p. h < 2p, so one subtraction is enough, and only the low 128
        // bits of the result are the tag. The mask picks g then, and h
        // otherwise, without branching on h.
        let g = (u64::from(h0) + 5, h1, h2, h3, h4);
        let a = g.0;
        let g0 = a as u32;
        let a = u64::from(g.1) + (a >> 32);
        let g1 = a as u32;
        let a = u64::from(g.2) + (a >> 32);
        let g2 = a as u32;
        let a = u64::from(g.3) + (a >> 32);
        let g3 = a as u32;
        let g4 = g.4 + (a >> 32) as u32;
        let use_g = (g4 >> 2).wrapping_neg();
        let words = [
            (h0 & !use_g) | (g0 & use_g),
            (h1 & !use_g) | (g1 & use_g),
            (h2 & !use_g) | (g2 & use_g),
            (h3 & !use_g) | (g3 & use_g),
        ];

        // Add s mod 2^128.
        let mut tag = [0u8; 16];
        let mut carry = 0u64;
        for (i, (word, s)) in words.iter().zip(self.s).enumerate() {
            let sum = u64::from(*word) + u64::from(s) + carry;
            tag[i * 4..i * 4 + 4].copy_from_slice(&(sum as u32).to_le_bytes());
            carry = sum >> 32;
        }
        tag
    }

    /// h = (h + block + hibit 2^128) * r for each block, where `hibit` is 1
    /// for a whole block and 0 for a padded last block, which carries its own
    /// 1.
    ///
    /// Never inlined, so a multiply scan can find this function by name. It
    /// runs once per update, over every block of it.
    #[inline(never)]
    fn blocks(&mut self, blocks: &[[u8; 16]], hibit: u32) {
        let [r0, r1, r2, r3] = self.r;
        // See the bounds above: s_j < 1.25 * 2^28.
        let (s1, s2, s3) = (r1 + (r1 >> 2), r2 + (r2 >> 2), r3 + (r3 >> 2));
        let [mut h0, mut h1, mut h2, mut h3, mut h4] = self.h;

        for block in blocks {
            let (words, _) = block.as_chunks::<4>();
            // h += block, a ripple of at most one carry from word to word.
            let a = u64::from(h0) + u64::from(u32::from_le_bytes(words[0]));
            let a1 = u64::from(h1) + u64::from(u32::from_le_bytes(words[1])) + (a >> 32);
            let a2 = u64::from(h2) + u64::from(u32::from_le_bytes(words[2])) + (a1 >> 32);
            let a3 = u64::from(h3) + u64::from(u32::from_le_bytes(words[3])) + (a2 >> 32);
            (h0, h1, h2, h3) = (a as u32, a1 as u32, a2 as u32, a3 as u32);
            // At most 4 + 1 + 1. A debug build's overflow checks would branch
            // on the secret, hence wrapping arithmetic and no assertions on
            // the words.
            h4 = h4.wrapping_add((a3 >> 32) as u32).wrapping_add(hibit);
            debug_assert!(ct::into_public(h4) <= 6);

            // Schoolbook multiplication on 32-bit words, the products at or
            // above 2^128 folded back through s.
            let (m0, m1, m2, m3) = (h0, h1, h2, h3);
            let mut d = mul(m0, r0);
            d = d.wrapping_add(mul(m1, s3));
            d = d.wrapping_add(mul(m2, s2));
            d = d.wrapping_add(mul(m3, s1));
            h0 = d as u32;
            d >>= 32;
            d = d.wrapping_add(mul(m0, r1));
            d = d.wrapping_add(mul(m1, r0));
            d = d.wrapping_add(mul(m2, s3));
            d = d.wrapping_add(mul(m3, s2));
            d = d.wrapping_add(mul(h4, s1));
            h1 = d as u32;
            d >>= 32;
            d = d.wrapping_add(mul(m0, r2));
            d = d.wrapping_add(mul(m1, r1));
            d = d.wrapping_add(mul(m2, r0));
            d = d.wrapping_add(mul(m3, s3));
            d = d.wrapping_add(mul(h4, s2));
            h2 = d as u32;
            d >>= 32;
            d = d.wrapping_add(mul(m0, r3));
            d = d.wrapping_add(mul(m1, r2));
            d = d.wrapping_add(mul(m2, r1));
            d = d.wrapping_add(mul(m3, r0));
            d = d.wrapping_add(mul(h4, s3));
            h3 = d as u32;
            debug_assert!(ct::into_public(d) < 1 << 63);
            let d4 = h4.wrapping_mul(r0).wrapping_add((d >> 32) as u32);
            // h4 r0 < 6 * 2^28 and the carry < 2^31, so d4 < 2^32.
            debug_assert!(ct::into_public(u64::from(h4) * u64::from(r0)) < 3 << 29);
            debug_assert!(ct::into_public(d >> 32) < 1 << 31);

            // Fold d4's part at or above 2^130 back in as 5 times it.
            h4 = d4 & 3;
            let t = u64::from(d4 >> 2).wrapping_mul(5);
            let a = u64::from(h0).wrapping_add(t);
            h0 = a as u32;
            let a = u64::from(h1).wrapping_add(a >> 32);
            h1 = a as u32;
            let a = u64::from(h2).wrapping_add(a >> 32);
            h2 = a as u32;
            let a = u64::from(h3).wrapping_add(a >> 32);
            h3 = a as u32;
            h4 = h4.wrapping_add((a >> 32) as u32);
        }

        self.h = [h0, h1, h2, h3, h4];
    }
}

impl Drop for Poly1305 {
    fn drop(&mut self) {
        // The clamped `r`, the pad `s`, and the accumulator are the key.
        zeroise_value(self);
    }
}

impl Zeroable for Poly1305 {}

/// The 64-bit product of two 32-bit words.
#[inline(always)]
fn mul(a: u32, b: u32) -> u64 {
    u64::from(a).wrapping_mul(u64::from(b))
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::generic::poly1305_32::Poly1305 as Limbs26;
    // The `unsafe` aws-lc call lives in a sibling file of `poly1305_32`, as
    // `low::tests::no_debug_assert_beside_unsafe` requires.
    #[cfg(not(any(miri, target_family = "wasm")))]
    use crate::low::generic::poly1305_32::aws;
    use crate::test::file_test;

    fn tag(key: &[u8; 32], pieces: &[&[u8]]) -> [u8; 16] {
        let mut p = Poly1305::new(key);
        for piece in pieces {
            p.add_bytes(piece);
        }
        p.finish()
    }

    // aws-lc's vectors, of every length and carry.
    #[test]
    fn aws_lc_vectors() {
        for test in file_test::tests("aws-lc/crypto/poly1305/poly1305_tests.txt") {
            let key: [u8; 32] = test.bytes("Key").try_into().unwrap();
            let input = test.bytes("Input");
            let (head, tail) = input.split_at(input.len() / 3);
            assert_eq!(tag(&key, &[head, tail]), &test.bytes("MAC")[..], "{test}");
        }
    }

    // RFC 8439 section 2.5.2, and appendix A.3's vectors #5 to #11, which
    // reach the final reduction's edges.
    #[test]
    fn rfc8439() {
        let key: [u8; 32] = hex("85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")
            .try_into()
            .unwrap();
        assert_eq!(
            tag(&key, &[b"Cryptographic Forum Research Group"]),
            &hex("a8061dc1305136c6c22b8baf0c0127a9")[..]
        );

        let zero = "00000000000000000000000000000000";
        let two = "02000000000000000000000000000000";
        let ones = "ffffffffffffffffffffffffffffffff";
        let one = |r: &str, s: &str, msg: &str, want: &str| {
            let key: [u8; 32] = hex(&format!("{r}{s}")).try_into().unwrap();
            assert_eq!(tag(&key, &[&hex(msg)]), &hex(want)[..], "{r} {s} {msg}");
        };
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
            "e33594d7505e43b900000000000000003394d7505e4379cd01000000000000000000000000000000000000000000000001000000000000000000000000000000",
            "14000000000000005500000000000000",
        );
        one(
            "01000000000000000400000000000000",
            zero,
            "e33594d7505e43b900000000000000003394d7505e4379cd010000000000000000000000000000000000000000000000",
            "13000000000000000000000000000000",
        );
    }

    // Against the 26-bit limbs: all-ones and zero keys and messages (the
    // largest carries), every length up to 300, random messages fed whole and
    // in pieces, and keys with r at its clamped maximum, so every product is
    // at its bound. The key and message are secret, so under `admin/ctgrind`
    // this also checks this Poly1305 is constant time in both.
    #[test]
    fn matches_26_bit_limbs() {
        let mut rng = SplitMix(0x1305_a4a7_0f90_1730);
        let max_r: [u8; 16] = [
            0xff, 0xff, 0xff, 0x0f, 0xfc, 0xff, 0xff, 0x0f, 0xfc, 0xff, 0xff, 0x0f, 0xfc, 0xff,
            0xff, 0x0f,
        ];
        let mut cases: Vec<([u8; 32], Vec<u8>)> = Vec::new();
        for byte in [0xffu8, 0] {
            for key in [[byte; 32], {
                let mut k = [0xff; 32];
                k[..16].copy_from_slice(&max_r);
                k
            }] {
                cases.push((key, vec![byte; 1024]));
            }
        }
        let long: Vec<u8> = (0..300).map(|_| rng.next() as u8).collect();
        for len in 0..=long.len() {
            cases.push((rng.key(), long[..len].to_vec()));
        }
        let seeds = if cfg!(debug_assertions) { 4 } else { 32 };
        for _ in 0..seeds {
            let len = (rng.next() % 1025) as usize;
            let msg: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
            let mut key = rng.key();
            if rng.next() & 1 == 1 {
                key[..16].copy_from_slice(&max_r);
            }
            cases.push((key, msg));
        }
        for (key, msg) in &cases {
            ct::secret_slice(key);
            ct::secret_slice(msg);
            let mut want = Limbs26::new(key);
            want.add_bytes(msg);
            let want = ct::into_public(want.finish());
            assert_eq!(
                ct::into_public(tag(key, &[msg])),
                want,
                "{} bytes",
                msg.len()
            );
            let mut got = Poly1305::new(key);
            let mut rest = &msg[..];
            while !rest.is_empty() {
                let n = 1 + (rng.next() as usize) % rest.len().min(70);
                let (piece, tail) = rest.split_at(n);
                got.add_bytes(piece);
                rest = tail;
            }
            assert_eq!(
                ct::into_public(got.finish()),
                want,
                "{} in pieces",
                msg.len()
            );
        }
    }

    // Messages of mostly 0xff bytes under a maximal r, whose accumulator and
    // products sit near the bounds in the module comment, against the 26-bit
    // limbs.
    #[test]
    fn near_the_bounds() {
        let mut rng = SplitMix(0x0ff0_b0b0_1305_0001);
        let cases = if cfg!(debug_assertions) { 200 } else { 4000 };
        for _ in 0..cases {
            let mut key = rng.key();
            key[..16].fill(0xff);
            let len = (rng.next() % 100) as usize;
            let msg: Vec<u8> = (0..len)
                .map(|_| {
                    if rng.next().is_multiple_of(4) {
                        rng.next() as u8
                    } else {
                        0xff
                    }
                })
                .collect();
            let mut want = Limbs26::new(&key);
            want.add_bytes(&msg);
            assert_eq!(tag(&key, &[&msg]), want.finish(), "{key:02x?} {msg:02x?}");
        }
    }

    // The accumulator at its largest. `r` all ones (clamped) and a message of
    // 0xff bytes keep every limb near 2^32, and a carry out of d3 is large.
    // The tag is checked against the 26-bit limbs and, below, aws-lc.
    #[cfg(not(any(miri, target_family = "wasm")))]
    #[test]
    fn matches_aws_lc() {
        for len in [0usize, 1, 15, 16, 17, 31, 32, 33, 64, 200, 1024] {
            let key: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(9).wrapping_add(1));
            let msg: Vec<u8> = (0..len).map(|i| (i * 17 + 3) as u8).collect();
            assert_eq!(tag(&key, &[&msg]), aws::tag(&key, &msg), "{len}");
            assert_eq!(
                tag(&[0xff; 32], &[&msg]),
                aws::tag(&[0xff; 32], &msg),
                "ones {len}"
            );
        }
    }

    struct SplitMix(u64);

    impl SplitMix {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn key(&mut self) -> [u8; 32] {
            core::array::from_fn(|_| self.next() as u8)
        }
    }

    fn hex(s: &str) -> Vec<u8> {
        hex::decode(s).unwrap()
    }
}
