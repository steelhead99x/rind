// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-1 on rind's portable code in `generic`, as armv7 runs it without the
//! crypto extension, and SHA-256 on HACL*'s verified `Hacl_Hash_SHA2`, as
//! libcrux-sha2 ships it. HACL*'s SHA-256 took 0.67-0.93 of `generic`'s time
//! at 16 KB on x86_64. SHA-384/512 is that HACL* body on 64-bit targets and
//! the rolled loop in `generic::sha512` on 32-bit targets, where the unrolled
//! body is about 47 KiB and misses a 16 KiB instruction cache. A message of
//! at most 55 bytes, one padded block, finishes through the same rolled slot
//! on targets that build the native slot. Longer SHA-256 stays on HACL*: a
//! second compressor on every block made long hashes slower on an ESP32-S3.

use libcrux_sha2::hacl::sha256_update_nblocks;
#[cfg(target_pointer_width = "64")]
use libcrux_sha2::hacl::sha512_update_nblocks;

pub(crate) use crate::low::generic::sha1::sha1_compress_blocks;

/// HACL* takes a 32-bit length, so longer input goes in pieces of whole
/// blocks below it.
const PIECE: usize = 1 << 31;

/// Compresses whole 64-byte `blocks` into `state`.
///
/// One loop of HACL*'s `sha256_update_nblocks` on every pointer width.
/// 32-bit portable does not keep a rolled compressor beside it: on an
/// ESP32-S3 that second body made long hashes slower.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    for piece in blocks.chunks(PIECE) {
        sha256_update_nblocks(piece.len() as u32, piece, state);
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
    // One padded block fits a message of at most 55 bytes. The rolled
    // compressor for that block lives in the same slot as SHA-512, so a
    // short hash does not enter HACL*'s 12 KiB body. The length is public.
    #[cfg(sha512_asm_slot)]
    if message.len() <= 55 {
        let mut out = [0u8; 32];
        // SAFETY: `state` is eight words, `message` is `message.len()` bytes,
        // `length` is eight bytes, and `out` is 32 bytes. The length is at
        // most 55, which the slot requires.
        unsafe {
            rind_sha256_finish_one(
                state.as_ptr(),
                message.as_ptr(),
                message.len(),
                length.as_ptr(),
                out.as_mut_ptr(),
            );
        }
        return out;
    }

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
        crate::low::generic::sha512::sha512_compress_blocks(state, blocks);
    }
    #[cfg(target_pointer_width = "64")]
    {
        for piece in blocks.chunks(PIECE) {
            sha512_update_nblocks(piece.len() as u32, piece, state);
        }
    }
}

// SAFETY: `rind_sha256_finish_one` is the slot object from `build.rs`. It
// reads eight state words, `len` message bytes, eight length bytes, and
// writes 32 bytes at `out`.
#[cfg(sha512_asm_slot)]
unsafe extern "C" {
    #[link_name = concat!(env!("RIND_SLOT_PREFIX"), "_sha256_finish_one")]
    fn rind_sha256_finish_one(
        state: *const u32,
        message: *const u8,
        len: usize,
        length: *const u8,
        out: *mut u8,
    );
}

#[cfg(test)]
mod tests {
    use super::{sha256_compress_blocks, sha256_finish};

    /// SHA-256's IV, FIPS 180-4 §5.3.2.
    const IV: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];

    fn pattern(len: usize) -> Vec<u8> {
        (0..len).map(|i| (i * 17 + 3) as u8).collect()
    }

    fn expect(message: &[u8], hex: &str) {
        let bits = (message.len() as u64).wrapping_mul(8);
        let got = sha256_finish(&IV, message, bits.to_be_bytes());
        let mut expected = [0u8; 32];
        for i in 0..32 {
            expected[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).unwrap();
        }
        assert_eq!(got, expected);
    }

    #[test]
    fn sha256_finish_known_answers() {
        // Empty and "abc" are FIPS 180-4. 32 and 55 bytes fit one padded
        // block; 56 and 64 need two, so they stay on the long path.
        expect(
            b"",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        );
        expect(
            b"abc",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        );
        expect(
            &pattern(32),
            "ba6cd1a2ce6f9e35b43c2b1df39404331d3c3bbececef613d02fcfacec8a0dee",
        );
        expect(
            &pattern(55),
            "c40dbcd18dfdb34a5c52a791f09286986b5e9d61f867278c03adda227684e897",
        );
        expect(
            &pattern(56),
            "ca6c4804e2170c368f94d2da606adf4552eb0b1d35bc2ad1dc12887627a028eb",
        );
        expect(
            &pattern(64),
            "30a1b375b49e0f1d5e00b6868bbfd471cbe5387806456cc11fd153c689bfe747",
        );
    }

    #[test]
    fn sha256_finish_one_block_after_chaining() {
        // The first block is the long compressor. The 32-byte tail is one
        // padded block, so a native-slot build finishes it in the rolled slot,
        // with a chaining value that is not the IV.
        let message = pattern(96);
        let mut state = IV;
        sha256_compress_blocks(&mut state, &message[..64]);
        let got = sha256_finish(&state, &message[64..], (96u64 * 8).to_be_bytes());
        expect_bytes(
            &got,
            "02cd3e5ef77d48fd6003ea52baaac00466c30879d0b47192ff992d047f78ac4e",
        );
    }

    fn expect_bytes(got: &[u8; 32], hex: &str) {
        let mut expected = [0u8; 32];
        for i in 0..32 {
            expected[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).unwrap();
        }
        assert_eq!(got, &expected);
    }
}
