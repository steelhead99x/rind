// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 on rind's portable code in `generic`, as armv7 runs it without the
//! crypto extension, and the SHA-2 family on aws-lc's C block functions in
//! Rust, `generic::sha256` and `generic::sha512`. On x86_64 those took
//! 0.83-0.93 of aws-lc's own C's time for SHA-256 and 0.94-1.00 for SHA-512
//! from 32 B to 16 KB, where HACL*'s verified `Hacl_Hash_SHA2`, which this
//! ran before, took 0.92-0.99 and 1.25-1.33 on an Intel core and up to 1.17
//! and 1.22 on GitHub's runners.
//!
//! Two exceptions are for small instruction caches. On 32-bit
//! microcontrollers (ESP-IDF or no OS), SHA-384/512 is the rolled loop in
//! `generic::sha512_rolled`, whose code 32-bit codegen keeps to a few
//! kilobytes. On ESP-IDF Xtensa, SHA-256 is rind's own unproven compression
//! in `sha256_iram`, run from internal RAM, at about 0.65-0.74 of HACL*'s
//! time from flash on a Seeed XIAO ESP32-S3 from 1200 B to 16 KB. Host tests
//! call that body by name, on its Rust fallbacks.

pub(crate) use crate::low::generic::sha1::sha1_compress_blocks;

// The IRAM body is what ESP-IDF Xtensa ships. Other builds compile it only
// for the tests below, which call it by name.
#[cfg(any(all(target_arch = "xtensa", target_os = "espidf"), test))]
#[path = "sha256_iram.rs"]
mod iram;

/// Compresses whole 64-byte `blocks` into `state`.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    #[cfg(all(target_arch = "xtensa", target_os = "espidf"))]
    {
        assert!(blocks.len().is_multiple_of(64));
        iram::sha256_update_nblocks(state, blocks);
    }
    #[cfg(not(all(target_arch = "xtensa", target_os = "espidf")))]
    crate::low::generic::sha256::sha256_compress_blocks(state, blocks);
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

/// Compresses whole 128-byte `blocks` into `state`.
pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    // The rolled loop on 32-bit microcontrollers, as the module comment
    // says. The pointer width, not `rind_limb`, is the switch: the code size
    // is a property of the 32-bit codegen.
    #[cfg(all(
        not(target_pointer_width = "64"),
        any(target_os = "espidf", target_os = "none")
    ))]
    crate::low::generic::sha512_rolled::sha512_compress_blocks(state, blocks);
    #[cfg(not(all(
        not(target_pointer_width = "64"),
        any(target_os = "espidf", target_os = "none")
    )))]
    crate::low::generic::sha512::sha512_compress_blocks(state, blocks);
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
    /// call this rather than `sha256_finish`, which runs `generic::sha256`
    /// off Xtensa.
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
        // tests and ship `generic::sha256` in its place.
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
                // RustCrypto's shares no code with either rind body. Miri
                // and wasm builds have no `sha2`.
                #[cfg(not(any(miri, target_family = "wasm")))]
                {
                    let mut rustcrypto = ct::into_public(state);
                    let public_blocks = ct::into_public(blocks);
                    sha2::block_api::compress256(
                        &mut rustcrypto,
                        public_blocks[..count * 64].as_chunks::<64>().0,
                    );
                    assert_eq!(got, rustcrypto, "RustCrypto {case}, {count}");
                }
            }
        }
    }

    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    fn iram_digest_matches_aws_lc() {
        // Both padding boundaries and updates across them go through the
        // IRAM body, with a secret message. Off Xtensa the production
        // finish runs `generic::sha256`, so this calls the IRAM driver by
        // name.
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
