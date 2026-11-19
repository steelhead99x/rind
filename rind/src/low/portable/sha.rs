// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 and SHA-256 on rind's portable code in `generic`, as armv7 runs
//! SHA-1 without the crypto extension. On ESP-IDF Xtensa, SHA-256 is rind's
//! own FIPS 180-4 compression in `sha256_iram`: sixteen rounds unrolled, the
//! schedule body run three times, placed in internal RAM. Nothing proves
//! that body. A fully rolled SHA-256 was slower in IRAM on an ESP32-S3,
//! which is why it is unrolled by sixteen. Measured there at `3aaa3c6a`,
//! long SHA-256 takes about 0.76× the time of the previous HACL* body placed
//! in IRAM and about 0.65–0.74× main. The sha2 image's block symbol is
//! 4,412 bytes and `.iram0.text` is 4,516 bytes above main. A standalone
//! object probe of the same tree is smaller (4,256-byte block, 4,357 bytes
//! of IRAM sections) and is not that firmware image. Other portable targets
//! ship `generic::sha256` and do not link the IRAM body. Xtensa does not
//! link `generic::sha256` beside it: a second compressor made long hashes
//! slower on that chip. Host tests
//! compile the IRAM body and call it directly, on the Rust `rotate_right`
//! and `from_be_bytes` fallbacks rather than the Xtensa asm. SHA-384/512
//! unrolls `generic::sha512` when the pointer is 64 bits and rolls it when
//! the pointer is 32 bits. The unrolled form is about 47 KiB on a 32-bit
//! pointer and misses a 16 KiB instruction cache. The measured ratio against
//! aws-lc's C is the portable SHA-2 decision in `benchmarks/gaps.toml`.

pub(crate) use crate::low::generic::sha1::sha1_compress_blocks;
pub(crate) use crate::low::generic::sha512::sha512_compress_blocks;

// The IRAM body is what ESP-IDF Xtensa ships. Other builds compile it only
// for the tests below, which call it by name. `sha256_compress_blocks` does
// not, so a portable `cargo test` still runs `generic::sha256`, and
// ctgrind's portable job checks that body.
#[cfg(any(all(target_arch = "xtensa", target_os = "espidf"), test))]
#[path = "sha256_iram.rs"]
mod iram;

// The IRAM body is what ESP-IDF Xtensa ships. Other builds compile it only
// for the tests below, which call it by name, so their `cargo test` and
// ctgrind still run the HACL* SHA-256 they ship.
#[cfg(any(all(target_arch = "xtensa", target_os = "espidf"), test))]
#[path = "sha256_iram.rs"]
mod iram;

/// Compresses whole 64-byte `blocks` into `state`.
///
/// `generic::sha256` on every portable target except ESP-IDF Xtensa, which
/// runs the 16-round body in `sha256_iram` from internal RAM. Xtensa does
/// not also link `generic::sha256`: on an ESP32-S3 a second compressor made
/// long hashes slower. Nothing proves the IRAM body. The predicate is the
/// target, not `test`: a host test of this function runs `generic::sha256`.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    #[cfg(all(target_arch = "xtensa", target_os = "espidf"))]
    {
        iram::sha256_update_nblocks(state, blocks);
    }
    #[cfg(not(all(target_arch = "xtensa", target_os = "espidf")))]
    {
        crate::low::generic::sha256::sha256_compress_blocks(state, blocks);
    }
}

/// Compresses `message`, padded and closed by the big-endian bit `length`.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha1_compress_blocks(state, blocks);
    let mut last = [[0u8; 64]; 2];
    sha1_compress_blocks(state, crate::low::pad(rest, length, &mut last));
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
#[inline]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
    sha256_compress_blocks(&mut h, blocks);
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(&mut h, crate::low::pad(rest, length, &mut last));
    crate::low::sha256_digest(&h)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;

    /// SHA-256's IV, FIPS 180-4 §5.3.3.
    const IV: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    /// The IRAM body, with the same padding `sha256_finish` uses. Host tests
    /// call this by name. Off Xtensa, `sha256_finish` runs `generic::sha256`.
    fn iram_digest(message: &[u8]) -> [u8; 32] {
        let bits = (message.len() as u64).checked_mul(8).unwrap();
        let mut state = IV;
        let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
        iram::sha256_update_nblocks(&mut state, blocks);
        let mut last = [[0u8; 64]; 2];
        iram::sha256_update_nblocks(
            &mut state,
            crate::low::pad(rest, bits.to_be_bytes(), &mut last),
        );
        crate::low::sha256_digest(&state)
    }

    /// Whole blocks as they fill, then the same padding. A chunk that spans
    /// a block boundary is what `Context::update` does on the target.
    fn iram_digest_chunked(message: &[u8], chunk: usize) -> [u8; 32] {
        let mut pending = [0u8; 64];
        let mut filled = 0usize;
        let mut state = IV;
        for piece in message.chunks(chunk.max(1)) {
            let mut rest = piece;
            while !rest.is_empty() {
                let take = (64 - filled).min(rest.len());
                pending[filled..filled + take].copy_from_slice(&rest[..take]);
                filled += take;
                rest = &rest[take..];
                if filled == 64 {
                    iram::sha256_update_nblocks(&mut state, &pending);
                    filled = 0;
                }
            }
        }
        let bits = (message.len() as u64).checked_mul(8).unwrap();
        let mut last = [[0u8; 64]; 2];
        iram::sha256_update_nblocks(
            &mut state,
            crate::low::pad(&pending[..filled], bits.to_be_bytes(), &mut last),
        );
        crate::low::sha256_digest(&state)
    }

    #[test]
    fn fips180_sha256() {
        // FIPS 180-4 SHA-256: the empty message, "abc", and the 56-byte
        // message whose padding fills a second block. The message is secret
        // so ctgrind checks this IRAM body. Host builds compile it only in
        // tests and do not ship it in place of `generic::sha256`.
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
            let secret = message.to_vec();
            ct::secret_slice(&secret);
            let got = ct::into_public(iram_digest(&secret));
            let expected = hex::decode(hex_digest).unwrap();
            assert_eq!(got.as_slice(), expected.as_slice(), "{}", secret.len());
        }
    }

    #[test]
    fn iram_compression_matches_references() {
        // Arbitrary chaining states cover HMAC's keyed states as well as a
        // fresh digest. Empty and split block runs check the IRAM driver.
        for case in 0..64u32 {
            let mut state = core::array::from_fn(|i| {
                case.wrapping_mul(0x9e37_79b9)
                    .rotate_left(i as u32 * 3)
                    .wrapping_add(i as u32)
            });
            if case < 2 {
                state.fill(if case == 0 { 0 } else { u32::MAX });
            }
            let blocks: [u8; 64 * 17] = core::array::from_fn(|i| match case {
                0 => 0,
                1 => 0xff,
                _ => (i as u32).wrapping_mul(197).wrapping_add(case) as u8,
            });
            ct::secret_slice(&state);
            ct::secret_slice(&blocks);
            for count in [0, 1, 2, 3, 8, 17] {
                let input = &blocks[..count * 64];
                let mut got = state;
                iram::sha256_update_nblocks(&mut got, input);

                let mut split = state;
                for block in input.chunks(64) {
                    iram::sha256_update_nblocks(&mut split, block);
                }
                let mut generic = state;
                crate::low::generic::sha256::sha256_compress_blocks(&mut generic, input);
                let got = ct::into_public(got);
                assert_eq!(got, ct::into_public(split), "split {case}, {count}");
                assert_eq!(got, ct::into_public(generic), "generic {case}, {count}");
            }
        }
    }

    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    fn iram_digest_matches_aws_lc() {
        // Both padding boundaries and updates across them go through the
        // IRAM body, with a secret message. Off Xtensa the production
        // finish stays on `generic::sha256`, so this calls the IRAM driver
        // by name.
        let message: [u8; 1200] = core::array::from_fn(|i| i.wrapping_mul(197) as u8);
        ct::secret_slice(&message);
        for len in [
            0, 1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 1200,
        ] {
            let input = &message[..len];
            let want =
                ct::into_public(aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA256, input));
            let got = ct::into_public(iram_digest(input));
            assert_eq!(got.as_ref(), want.as_ref(), "one shot, {len}");
            for chunk in [1, 16, 64, 65] {
                let got = ct::into_public(iram_digest_chunked(input, chunk));
                assert_eq!(got.as_ref(), want.as_ref(), "{len}, chunks of {chunk}");
            }
        }
    }
}
