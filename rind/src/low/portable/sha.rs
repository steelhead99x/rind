// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 on rind's portable code in `generic`, as armv7 runs it without the
//! crypto extension, and SHA-256 on HACL*'s verified `Hacl_Hash_SHA2`, as
//! libcrux-sha2 ships it, except on ESP-IDF Xtensa. HACL*'s SHA-256 took
//! 0.67-0.93 of `generic`'s time at 16 KB on x86_64. SHA-384/512 is that
//! HACL* body on 64-bit targets and the rolled loop in `generic::sha512` on
//! 32-bit targets, where the unrolled body is about 47 KiB and misses a
//! 16 KiB instruction cache. On ESP-IDF Xtensa, SHA-256 is rind's own
//! FIPS 180-4 compression in `sha256_iram`: sixteen rounds unrolled, the
//! schedule body run three times, placed in internal RAM. It is not HACL*
//! and nothing proves it. A fully rolled SHA-256 was slower than HACL* in
//! IRAM on an ESP32-S3, which is why this body is unrolled by sixteen.
//! This head has not been timed on a board. Other portable targets keep
//! HACL* at every length: a second body beside that ~12 KiB function made
//! long hashes slower on that chip.

/// ESP-IDF Xtensa runs the IRAM body. Host tests compile it too.
macro_rules! iram_sha256 {
    ($($item:item)*) => {
        $(
            #[cfg(any(all(target_arch = "xtensa", target_os = "espidf"), test))]
            $item
        )*
    };
}

/// Every other build keeps HACL* through libcrux-sha2.
macro_rules! hacl_sha256 {
    ($($item:item)*) => {
        $(
            #[cfg(not(any(all(target_arch = "xtensa", target_os = "espidf"), test)))]
            $item
        )*
    };
}

hacl_sha256! {
    use libcrux_sha2::hacl::sha256_update_nblocks;
}
#[cfg(target_pointer_width = "64")]
use libcrux_sha2::hacl::sha512_update_nblocks;

pub(crate) use crate::low::generic::sha1::sha1_compress_blocks;

/// HACL* takes a 32-bit length, so longer input goes in pieces of whole
/// blocks below it.
#[cfg_attr(all(target_arch = "xtensa", target_os = "espidf"), allow(dead_code))]
#[cfg(any(target_pointer_width = "64", not(test)))]
const PIECE: usize = 1 << 31;

/// Compresses whole 64-byte `blocks` into `state`.
///
/// One loop of HACL*'s `sha256_update_nblocks` on every pointer width,
/// except ESP-IDF Xtensa, which runs the 16-round body in `sha256_iram`
/// from internal RAM. 32-bit portable does not keep a second compressor
/// beside HACL*: on an ESP32-S3 that second body made long hashes slower.
/// Xtensa replaces HACL* for SHA-256 instead of adding one. The HACL*
/// proof does not cover the replacement.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    sha256_compress_blocks_inner(state, blocks);
}

// Portable host tests run the ESP-IDF body too, including the digest and
// HMAC vectors and their secret-input checks. The predicate lives in
// `iram_sha256` / `hacl_sha256` so the target cannot drift between the
// import, the module, and the two bodies.
iram_sha256! {
    fn sha256_compress_blocks_inner(state: &mut [u32; 8], blocks: &[u8]) {
        iram::sha256_update_nblocks(state, blocks);
    }
}

hacl_sha256! {
    fn sha256_compress_blocks_inner(state: &mut [u32; 8], blocks: &[u8]) {
        for piece in blocks.chunks(PIECE) {
            sha256_update_nblocks(piece.len() as u32, piece, state);
        }
    }
}

iram_sha256! {
    #[path = "sha256_iram.rs"]
    mod iram;
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
    assert!(blocks.len().is_multiple_of(128));
    // HACL*'s `sha512_update` is fully unrolled (~47 KiB on Xtensa), which
    // is several times a 16 KiB instruction cache. On 32-bit targets use
    // the rolled compression in `generic::sha512` instead. 64-bit portable
    // keeps HACL*, which is faster when the code stays cached.
    #[cfg(target_pointer_width = "32")]
    {
        // ESP32-S3 ESP-IDF places `sha512_compress_block` in `.iram1.text`
        // unless `esp32s3-sha512-flash` is set. Other 32-bit targets compile
        // the same call in ordinary text. SHA-256 on that target is
        // `sha256_iram`.
        crate::low::generic::sha512::sha512_compress_blocks(state, blocks);
    }
    #[cfg(target_pointer_width = "64")]
    {
        for piece in blocks.chunks(PIECE) {
            sha512_update_nblocks(piece.len() as u32, piece, state);
        }
    }
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

    fn fips_digest(message: &[u8]) -> [u8; 32] {
        let bits = (message.len() as u64).checked_mul(8).unwrap();
        sha256_finish(&IV, message, bits.to_be_bytes())
    }

    #[test]
    fn fips180_sha256() {
        // FIPS 180-4 SHA-256: the empty message, "abc", and the 56-byte
        // message whose padding fills a second block. The message is secret
        // so ctgrind checks this IRAM body, which host builds compile only
        // in tests.
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
        for (message, hex) in cases {
            let secret = message.to_vec();
            ct::secret_slice(&secret);
            let got = ct::into_public(fips_digest(&secret));
            let mut expected = [0u8; 32];
            for (byte, pair) in expected.iter_mut().zip(hex.as_bytes().chunks(2)) {
                *byte = u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap();
            }
            assert_eq!(got, expected, "{}", secret.len());
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
                sha256_compress_blocks(&mut got, input);

                let mut split = state;
                for block in input.chunks(64) {
                    sha256_compress_blocks(&mut split, block);
                }
                let mut generic = state;
                crate::low::generic::sha256::sha256_compress_blocks(&mut generic, input);
                let mut hacl = state;
                libcrux_sha2::hacl::sha256_update_nblocks(input.len() as u32, input, &mut hacl);
                let got = ct::into_public(got);
                assert_eq!(got, ct::into_public(split), "split {case}, {count}");
                assert_eq!(got, ct::into_public(generic), "generic {case}, {count}");
                assert_eq!(got, ct::into_public(hacl), "HACL* {case}, {count}");
            }
        }
    }

    #[test]
    #[cfg(not(any(miri, target_family = "wasm")))]
    fn iram_digest_matches_aws_lc() {
        // Both padding boundaries and updates across them go through the
        // production compression/finish entry points, with a secret message.
        let message: [u8; 1200] = core::array::from_fn(|i| i.wrapping_mul(197) as u8);
        ct::secret_slice(&message);
        for len in [
            0, 1, 31, 32, 55, 56, 63, 64, 65, 119, 120, 127, 128, 129, 1200,
        ] {
            let input = &message[..len];
            let want =
                ct::into_public(aws_lc_rs::digest::digest(&aws_lc_rs::digest::SHA256, input));
            let got = ct::into_public(crate::digest::digest(&crate::digest::SHA256, input));
            assert_eq!(got.as_ref(), want.as_ref(), "one shot, {len}");
            for chunk in [1, 16, 64, 65] {
                let mut context = crate::digest::Context::new(&crate::digest::SHA256);
                for piece in input.chunks(chunk) {
                    context.update(piece);
                }
                let got = ct::into_public(context.finish());
                assert_eq!(got.as_ref(), want.as_ref(), "{len}, chunks of {chunk}");
            }
        }
    }
}
