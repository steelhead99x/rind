// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
// Originally from cifra, but later adopting the 64x64
// multiplication layout from aws-lc.

use super::blockwise::Blockwise;
use crate::low::ct;

pub(crate) struct Poly1305 {
    /// Current accumulator, 131 bits split into limbs of 64, 64, and 3 bits
    h: [u64; 3],

    /// First half of key: block multiplier
    r: [u64; 2],

    /// Second half of key: added to result
    s: [u64; 2],

    /// Unprocessed input
    bw: Blockwise<16>,

    /// r's powers for x86_64's SSE2 lanes, once a run long enough needs them.
    #[cfg(rind_backend = "x86_64")]
    powers: Option<crate::low::x86_64::poly1305_sse2::Powers>,
}

impl Poly1305 {
    pub(crate) fn new(key: &[u8; 32]) -> Self {
        let h = [0; 3];
        // Clamp r by ANDing it with 0x0ffffffc0ffffffc0ffffffc0fffffff (RFC 8439 section 2.5.1)
        let r = [
            read64(&key[0..8]) & 0x0ffffffc0fffffff,
            read64(&key[8..16]) & 0x0ffffffc0ffffffc,
        ];
        let s = [read64(&key[16..24]), read64(&key[24..32])];
        Self {
            h,
            r,
            s,
            bw: Blockwise::new(),
            #[cfg(rind_backend = "x86_64")]
            powers: None,
        }
    }

    pub(crate) fn add_bytes(&mut self, bytes: &[u8]) {
        let bytes = self.bw.add_leading(bytes);

        if let Some(block) = self.bw.take() {
            self.process_whole_block(&block);
        }

        let (full_blocks, remainder) = bytes.as_chunks::<16>();
        #[cfg(rind_backend = "x86_64")]
        let full_blocks = crate::low::x86_64::poly1305_sse2::blocks(
            &mut self.h,
            &self.r,
            &mut self.powers,
            full_blocks,
        );
        for block in full_blocks {
            self.process_whole_block(block);
        }

        self.bw.add_trailing(remainder);
    }

    pub(crate) fn finish(mut self) -> [u8; 16] {
        if let Some(block) = self.bw.clone().peek_remaining() {
            self.process_last_block(block);
        }

        full_reduce(&mut self.h);

        // add s with carry
        let prev = self.h[0];
        self.h[0] = self.h[0].wrapping_add(self.s[0]);
        let carry = (self.h[0] < prev) as u64;
        self.h[1] = self.h[1].wrapping_add(self.s[1]).wrapping_add(carry);

        let mut r = [0u8; 16];
        r[0..8].copy_from_slice(&self.h[0].to_le_bytes());
        r[8..16].copy_from_slice(&self.h[1].to_le_bytes());
        r
    }

    fn process_whole_block(&mut self, inp: &[u8; 16]) {
        let block = [read64(&inp[0..8]), read64(&inp[8..16]), 0x01];
        self.process_block(&block);
    }

    fn process_last_block(&mut self, inp: &[u8]) {
        let mut bytes = [0u8; 16];
        bytes[..inp.len()].copy_from_slice(inp);
        bytes[inp.len()] = 0x01;

        let block = [read64(&bytes[0..8]), read64(&bytes[8..16]), 0];
        self.process_block(&block);
    }

    fn process_block(&mut self, block: &[u64; 3]) {
        add(&mut self.h, block);
        mul(&mut self.h, &self.r);
    }
}

fn read64(bytes: &[u8]) -> u64 {
    u64::from_le_bytes(bytes.try_into().unwrap())
}

fn add(h: &mut [u64; 3], x: &[u64; 3]) {
    // Add h += x, with carry. The generated code is a little less efficient
    // than hand-written assembly, but this is portable.
    // FIXME: try u64::carrying_add once the MSRV >= 1.91
    let carry: bool;
    (h[0], carry) = h[0].overflowing_add(x[0]);
    let (carry1, carry2): (bool, bool);
    (h[1], carry1) = h[1].overflowing_add(carry as u64);
    (h[1], carry2) = h[1].overflowing_add(x[1]);
    h[2] = h[2].wrapping_add((carry1 | carry2) as u64);
    h[2] = h[2].wrapping_add(x[2]);
}

fn mul(h: &mut [u64; 3], r: &[u64; 2]) {
    fn mul64(a: u64, b: u64) -> (u64, u64) {
        let product = (a as u128) * (b as u128);
        (product as u64, (product >> 64) as u64)
    }

    // Multiply t = r * h
    // The following implementation depends on these invariants to ensure that
    // certain 64-bit addition and multiplication results fit in a u64:
    //  * h uses at most 131 bits, and thus h[2] uses at most 3 bits
    //  * r[0] uses at most 60 bits
    //  * r[1] uses at most 60 bits
    // Hence wrapping arithmetic: a debug build's overflow check would branch on
    // the secret, as would these assertions without declassifying.
    debug_assert!(ct::into_public(h[2]) < 1 << 3);
    debug_assert!(ct::into_public(r[0]) < 1 << 60);
    debug_assert!(ct::into_public(r[1]) < 1 << 60);

    //         h[2] h[1] h[0]
    // x                 r[0]
    // ----------------------
    //               d1   d0
    //          d3   d2
    //          d4
    // ----------------------
    //          e2   e1   e0
    let (d0, d1) = mul64(r[0], h[0]);
    let (d2, d3) = mul64(r[0], h[1]);
    let d4 = r[0].wrapping_mul(h[2]);
    let e0 = d0;
    let (e1, carry) = d1.overflowing_add(d2);
    let e2 = d3.wrapping_add(d4).wrapping_add(carry as u64);

    //         h[2] h[1] h[0]
    // x            r[1]
    // ----------------------
    //          d1   d0
    //     d3   d2
    //     d4
    // ----------------------
    //     s5   e4   e3
    let (d0, d1) = mul64(r[1], h[0]);
    let (d2, d3) = mul64(r[1], h[1]);
    let d4 = r[1].wrapping_mul(h[2]);
    let e3 = d0;
    let (e4, carry) = d1.overflowing_add(d2);
    let e5 = d3.wrapping_add(d4).wrapping_add(carry as u64);

    //          e2   e1   e0
    // +   e5   e4   e3
    // ----------------------
    //     f3   f2   f1   f0
    let f0 = e0;
    let (f1, carry) = e1.overflowing_add(e3);
    let (f2, carry1) = e2.overflowing_add(carry as u64);
    let (f2, carry2) = f2.overflowing_add(e4);
    let f3 = e5.wrapping_add((carry1 | carry2) as u64);
    debug_assert!(ct::into_public(f3) < 1u64 << 63);

    // Partially reduce the result so it fits within 131 bits
    let (carry1, carry2): (bool, bool);
    (h[0], carry1) = f0.overflowing_add(f2 & !0x03);
    (h[0], carry2) = h[0].overflowing_add((f3 << 62) | (f2 >> 2));
    let carry3: bool;
    (h[1], carry3) = f1.overflowing_add(
        f3.wrapping_add(f3 >> 2)
            .wrapping_add(carry1 as u64)
            .wrapping_add(carry2 as u64),
    );
    h[2] = (f2 & 0x03).wrapping_add(carry3 as u64);
}

fn full_reduce(h: &mut [u64; 3]) {
    let (g0, carry0) = h[0].overflowing_sub(0u64.wrapping_sub(5));
    let (g1, carry1a) = h[1].overflowing_sub(carry0 as u64);
    let (g1, carry1b) = g1.overflowing_sub(0u64.wrapping_sub(1));
    let (g2, carry2a) = h[2].overflowing_sub((carry1a as u64).wrapping_add(carry1b as u64));
    let (_, carry2b) = g2.overflowing_sub(3);

    // Through `black_box`, as `ct_copy` takes its mask, or LLVM can turn the
    // select below into a branch on the secret, as it did once `finish`
    // inlined into `tests::lanes_match_scalar`.
    let positive_mask = core::hint::black_box((carry2a | carry2b) as u64).wrapping_sub(1);
    let negative_mask = !positive_mask;
    h[0] = (h[0] & negative_mask) | (g0 & positive_mask);
    h[1] = (h[1] & negative_mask) | (g1 & positive_mask);
    // `finish` reads only the low 128 bits, so `h[2]` is left as it is.
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::file_test;

    // aws-lc's vectors, of every length and carry. The fused assembly that
    // x86_64 and aarch64 run with ChaCha20 meets them through the AEAD files.
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

    /// The tag from `process_whole_block` alone, without x86_64's lanes.
    fn scalar(key: &[u8; 32], message: &[u8]) -> [u8; 16] {
        let mut p = Poly1305::new(key);
        let (blocks, tail) = message.as_chunks::<16>();
        for block in blocks {
            p.process_whole_block(block);
        }
        if !tail.is_empty() {
            p.process_last_block(tail);
        }
        p.finish()
    }

    // x86_64 hashes runs of whole blocks in two SSE2 lanes. Every length
    // through several of their four-block passes, on each side of the
    // shortest run they take, gives the scalar blocks' tag, starting from
    // each offset into a block, so a scalar accumulator enters the lanes, and
    // under keys and messages of all-ones limbs, whose sums carry most, as
    // well as random ones. `admin/ctgrind` keeps the key and the message
    // secret, and runs this on the CPU tiers that hash this way.
    #[test]
    fn lanes_match_scalar() {
        let mut rng = super::super::splitmix::Rng(1305);
        let mut bytes = |n: usize| (0..n).map(|_| rng.next() as u8).collect::<Vec<u8>>();
        let keys = [[0xff; 32], [0; 32], bytes(32).try_into().unwrap()];
        let messages = [vec![0xff; 50 * 16], bytes(50 * 16)];
        for key in &keys {
            for message in &messages {
                for len in 0..=message.len() {
                    let message = &message[..len];
                    let want = scalar(key, message);
                    for split in [0, 1, 15, 16, 17, 33, 49, 129] {
                        let split = split.min(len);
                        ct::secret_slice(key);
                        ct::secret_slice(message);
                        let mut p = Poly1305::new(key);
                        p.add_bytes(&message[..split]);
                        p.add_bytes(&message[split..]);
                        let got = ct::into_public(p.finish());
                        ct::public_slice(key);
                        ct::public_slice(message);
                        assert_eq!(got, want, "{len} bytes split at {split}");
                    }
                }
            }
        }
    }

    #[test]
    fn test_vectors() {
        // From draft-agl-tls-chacha20poly1305-04 section 7
        let key = &[
            0x74, 0x68, 0x69, 0x73, 0x20, 0x69, 0x73, 0x20, 0x33, 0x32, 0x2d, 0x62, 0x79, 0x74,
            0x65, 0x20, 0x6b, 0x65, 0x79, 0x20, 0x66, 0x6f, 0x72, 0x20, 0x50, 0x6f, 0x6c, 0x79,
            0x31, 0x33, 0x30, 0x35,
        ];

        let mut p = Poly1305::new(key);
        p.add_bytes(&[0u8; 32]);
        assert_eq!(
            p.finish(),
            [
                0x49, 0xec, 0x78, 0x09, 0x0e, 0x48, 0x1e, 0xc6, 0xc2, 0x6b, 0x33, 0xb9, 0x1c, 0xcc,
                0x03, 0x07
            ]
        );

        let mut p = Poly1305::new(key);
        p.add_bytes(&[
            0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x21,
        ]);
        assert_eq!(
            p.finish(),
            [
                0xa6, 0xf7, 0x45, 0x00, 0x8f, 0x81, 0xc9, 0x16, 0xa2, 0x0d, 0xcc, 0x74, 0xee, 0xf2,
                0xb2, 0xf0
            ]
        );

        // From RFC 8439 appendix A.3 test vector #1
        let key = &[0; 32];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[0; 64]);
        assert_eq!(p.finish(), [0; 16]);

        // From RFC 8439 appendix A.3 test vector #5
        let key = &[
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[0xff; 16]);
        assert_eq!(
            p.finish(),
            [
                0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00
            ]
        );

        // From RFC 8439 appendix A.3 test vector #6
        let key = &[
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff,
        ];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00,
        ]);
        assert_eq!(
            p.finish(),
            [
                0x03, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00
            ]
        );

        // From RFC 8439 appendix A.3 test vector #7
        let key = &[
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xf0, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xff, 0xff, 0x11, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]);
        assert_eq!(
            p.finish(),
            [
                0x05, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00
            ]
        );

        // From RFC 8439 appendix A.3 test vector #8
        let key = &[
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[
            0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff, 0xfb, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe, 0xfe,
            0xfe, 0xfe, 0xfe, 0xfe, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
            0x01, 0x01, 0x01, 0x01, 0x01, 0x01,
        ]);
        assert_eq!(p.finish(), [0; 16]);

        // From RFC 8439 appendix A.3 test vector #9
        let key = &[
            0x02, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[
            0xfd, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
            0xff, 0xff,
        ]);
        assert_eq!(
            p.finish(),
            [
                0xfa, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff
            ]
        );

        // From RFC 8439 appendix A.3 test vector #10
        let key = &[
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[
            0xE3, 0x35, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x33, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0x79, 0xCD, 0x01, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]);
        assert_eq!(
            p.finish(),
            [
                0x14, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x55, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00
            ]
        );

        // From RFC 8439 appendix A.3 test vector #11
        let key = &[
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x04, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00,
        ];
        let mut p = Poly1305::new(key);
        p.add_bytes(&[
            0xE3, 0x35, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0xB9, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x33, 0x94, 0xD7, 0x50, 0x5E, 0x43, 0x79, 0xCD, 0x01, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
            0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
        ]);
        assert_eq!(
            p.finish(),
            [
                0x13, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
                0x00, 0x00
            ]
        );
    }
}
