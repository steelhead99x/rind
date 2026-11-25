// Copyright (C) 1995-1998 Eric Young (eay@cryptsoft.com) All rights reserved.
// SPDX-License-Identifier: Apache-2.0

//! SHA-256's block function: aws-lc's `sha256_block_data_order_nohw`, from
//! `crypto/fipsmodule/sha/sha256.c` at commit
//! 5ed12cce0fd4453f2f63300d44325ed14f845d6f, in Rust. The portable backend
//! runs it everywhere but ESP-IDF Xtensa; armv7 and x86_64 tests check their
//! assembly against it.
//!
//! As in aws-lc, the first sixteen rounds read the block and the other
//! forty-eight run in a loop, unrolled so the eight working variables
//! rename instead of moving, over a sixteen-word window of the message
//! schedule. Each pass runs sixteen rounds, as aws-lc's SHA-512 does; its
//! SHA-256 runs eight. Ch and Maj are the three-operation forms
//! `((f ^ g) & e) ^ g` and `((a ^ b) & (b ^ c)) ^ b`, whose `a ^ b` the next
//! round reuses as its `b ^ c`. Every operation is an add, rotate, shift, or
//! bitwise op, and every index is a round number, so nothing branches on or
//! indexes by the state or the block. It is not formally verified: its
//! correctness rests on its use in OpenSSL, BoringSSL, and aws-lc, and on
//! rind's tests of it against FIPS 180-4, Wycheproof, and aws-lc-rs.

use super::sha256_k::K;

/// One round on the schedule word `$w`, the working variables named in
/// their current order.
macro_rules! round {
    ($w:expr, $k:expr, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident) => {{
        let s1 = $e.rotate_right(6) ^ $e.rotate_right(11) ^ $e.rotate_right(25);
        let ch = (($f ^ $g) & $e) ^ $g;
        let t1 = $w
            .wrapping_add($h)
            .wrapping_add(s1)
            .wrapping_add(ch)
            .wrapping_add($k);
        let s0 = $a.rotate_right(2) ^ $a.rotate_right(13) ^ $a.rotate_right(22);
        let maj = (($a ^ $b) & ($b ^ $c)) ^ $b;
        $d = $d.wrapping_add(t1);
        $h = s0.wrapping_add(maj).wrapping_add(t1);
    }};
}

/// Compresses whole 64-byte `blocks` into `state`.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    let (blocks, _) = blocks.as_chunks::<64>();
    for block in blocks {
        let (words, _) = block.as_chunks::<4>();
        let mut x: [u32; 16] = core::array::from_fn(|j| u32::from_be_bytes(words[j]));
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;

        macro_rules! first {
            ($j:literal, $($v:ident),*) => {
                round!(x[$j], K[$j], $($v),*)
            };
        }
        sixteen!(first, a, b, c, d, e, f, g, h);

        // A loop rather than three copies, as in aws-lc: unrolling all
        // sixty-four rounds measured no faster.
        let mut i = 16;
        while i < 64 {
            // W[t] = σ1(W[t-2]) + W[t-7] + σ0(W[t-15]) + W[t-16], FIPS 180-4
            // §6.2.2, with each index taken mod 16 in the window.
            macro_rules! rest {
                ($j:literal, $($v:ident),*) => {{
                    let w1 = x[($j + 1) & 15];
                    let w14 = x[($j + 14) & 15];
                    let s0 = w1.rotate_right(7) ^ w1.rotate_right(18) ^ (w1 >> 3);
                    let s1 = w14.rotate_right(17) ^ w14.rotate_right(19) ^ (w14 >> 10);
                    let w = x[$j]
                        .wrapping_add(s0)
                        .wrapping_add(s1)
                        .wrapping_add(x[($j + 9) & 15]);
                    x[$j] = w;
                    round!(w, K[i + $j], $($v),*)
                }};
            }
            sixteen!(rest, a, b, c, d, e, f, g, h);
            i += 16;
        }

        for (s, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *s = s.wrapping_add(v);
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::sha256_compress_blocks;
    use crate::low::ct;

    /// SHA-256's IV, FIPS 180-4 §5.3.3.
    const IV: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    /// The digest of a secret `message`, padded as `sha256_finish` pads it.
    fn hash(message: &[u8]) -> [u8; 32] {
        let message = message.to_vec();
        ct::secret_slice(&message);
        let bits = (message.len() as u64).checked_mul(8).unwrap();
        let (blocks, rest) = crate::low::split_tail::<64, 8>(&message);
        let mut state = IV;
        sha256_compress_blocks(&mut state, blocks);
        let mut last = [[0u8; 64]; 2];
        sha256_compress_blocks(
            &mut state,
            crate::low::pad(rest, bits.to_be_bytes(), &mut last),
        );
        crate::low::sha256_digest(&ct::into_public(state))
    }

    #[test]
    fn fips180() {
        // FIPS 180-4 SHA-256: the empty message, "abc", and the 56-byte
        // message whose padding fills a second block.
        let cases: [(&[u8], &str); 3] = [
            (
                b"",
                "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
            ),
            (
                b"abc",
                "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
            ),
            (
                b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
                "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
            ),
        ];
        for (message, hex_digest) in cases {
            let expected = hex::decode(hex_digest).unwrap();
            assert_eq!(hash(message).as_slice(), expected.as_slice());
        }
    }

    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    fn matches_aws_lc() {
        // Both padding boundaries and runs of several blocks, on a secret
        // message, against aws-lc's SHA-256.
        let message: [u8; 1200] = core::array::from_fn(|i| i.wrapping_mul(197) as u8);
        for len in [
            0, 1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 1200,
        ] {
            let input = &message[..len];
            let want = aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA256, input);
            assert_eq!(hash(input).as_slice(), want.as_ref(), "{len}");
        }
    }

    #[test]
    fn keyed_states() {
        // Arbitrary secret chaining states, as HMAC's keyed states are, and
        // all-zero and all-one states and blocks, against the backend's own
        // compression one block at a time. A run's split must not matter.
        for case in 0..16u32 {
            let state: [u32; 8] = core::array::from_fn(|i| match case {
                0 => 0,
                1 => u32::MAX,
                _ => case.wrapping_mul(0x9e37_79b9).rotate_left(i as u32 * 3) ^ i as u32,
            });
            let blocks: [u8; 64 * 5] = core::array::from_fn(|i| match case {
                0 => 0,
                1 => 0xff,
                _ => (i as u32).wrapping_mul(197).wrapping_add(case) as u8,
            });
            ct::secret_slice(&state);
            ct::secret_slice(&blocks);
            let mut whole = state;
            sha256_compress_blocks(&mut whole, &blocks);
            let mut split = state;
            for block in blocks.chunks(64) {
                sha256_compress_blocks(&mut split, block);
            }
            let mut backend = state;
            crate::low::sha256_compress_blocks(&mut backend, &blocks);
            let whole = ct::into_public(whole);
            assert_eq!(whole, ct::into_public(split), "{case}");
            assert_eq!(whole, ct::into_public(backend), "{case}");
        }
    }
}
