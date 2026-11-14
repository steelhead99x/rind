// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! A rolled SHA-512 compression, for 32-bit portable targets.
//!
//! The portable backend otherwise calls HACL*'s `sha512_update`, which is
//! fully unrolled. On Xtensa that function is about 47 KiB — several times
//! the ESP32-S3's 16 KiB instruction cache — so every block streams its
//! code from flash, about 33× rind's compact loop. This implementation
//! follows [`sha256`](sha256.rs): one 16-word window and an 80-round loop.
//! On 32-bit portable targets that loop is assembled into
//! `.text.rind_rolled_slot`, padded to a multiple of 2048 bytes so the
//! following code keeps its instruction-cache set. The round functions and
//! the eighty `K` constants are FIPS 180-4 §4.1.3 and §4.2.3. The unit tests
//! check FIPS 180-4's SHA-512 vectors and, on every backend except 32-bit
//! portable, the same compression the backend ships (HACL* or aws-lc).
//! On 64-bit portable targets, HACL*'s unrolled form is still used.

#[cfg(all(sha512_asm_slot, target_arch = "x86"))]
core::arch::global_asm!(
    include_str!(concat!(env!("OUT_DIR"), "/sha512_slot.s")),
    options(att_syntax)
);
#[cfg(all(sha512_asm_slot, not(target_arch = "x86")))]
core::arch::global_asm!(include_str!(concat!(env!("OUT_DIR"), "/sha512_slot.s")));

/// Compresses whole 128-byte `blocks` into `state`, through the padded slot.
#[cfg(sha512_asm_slot)]
pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    // SAFETY: `state` is eight words and `blocks` is `blocks.len()` bytes,
    // a multiple of the block. The slot reads nothing past that.
    unsafe {
        rind_sha512_compress_blocks(state.as_mut_ptr(), blocks.as_ptr(), blocks.len());
    }
}

// SAFETY: `rind_sha512_compress_blocks` is the slot object from `build.rs`.
// It reads `len` bytes at `blocks` and eight `u64`s at `state`.
#[cfg(sha512_asm_slot)]
unsafe extern "C" {
    fn rind_sha512_compress_blocks(state: *mut u64, blocks: *const u8, len: usize);
}

#[cfg(not(sha512_asm_slot))]
include!("sha512_block.rs");

#[cfg(test)]
mod tests {
    use super::sha512_compress_blocks;

    /// SHA-512's IV, FIPS 180-4 §5.3.5.
    const IV: [u64; 8] = [
        0x6a09e667f3bcc908,
        0xbb67ae8584caa73b,
        0x3c6ef372fe94f82b,
        0xa54ff53a5f1d36f1,
        0x510e527fade682d1,
        0x9b05688c2b3e6c1f,
        0x1f83d9abfb41bd6b,
        0x5be0cd19137e2179,
    ];

    fn padded(message: &[u8]) -> Vec<u8> {
        let bits = (message.len() as u128).checked_mul(8).unwrap();
        let mut padded = message.to_vec();
        padded.push(0x80);
        // SHA-512's length field is 16 bytes; pad so the total is a
        // multiple of 128 and the length sits in the last 16.
        while padded.len() % 128 != 112 {
            padded.push(0);
        }
        padded.extend_from_slice(&bits.to_be_bytes());
        padded
    }

    fn encode(state: [u64; 8]) -> [u8; 64] {
        let mut out = [0u8; 64];
        for (i, word) in state.iter().enumerate() {
            out[i * 8..(i + 1) * 8].copy_from_slice(&word.to_be_bytes());
        }
        out
    }

    fn hash(message: &[u8]) -> [u8; 64] {
        let padded = padded(message);
        let mut state = IV;
        sha512_compress_blocks(&mut state, &padded);
        encode(state)
    }

    fn digest_hex(message: &[u8], hex: &str) {
        assert_eq!(hex.len(), 128, "hex length");
        let mut expected = [0u8; 64];
        for i in 0..64 {
            expected[i] = u8::from_str_radix(&hex[i * 2..i * 2 + 2], 16).unwrap();
        }
        assert_eq!(hash(message), expected);
    }

    #[test]
    fn fips180_empty() {
        // FIPS 180-4, SHA-512 of the empty message.
        digest_hex(
            b"",
            "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e",
        );
    }

    #[test]
    fn fips180_abc() {
        // FIPS 180-4, SHA-512 of "abc".
        digest_hex(
            b"abc",
            "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f",
        );
    }

    /// The 32-bit portable backend *is* this compression, so that
    /// comparison would call itself. Everywhere else it is HACL* or aws-lc.
    #[cfg(not(all(rind_backend = "portable", target_pointer_width = "32")))]
    #[test]
    fn matches_backend_compression() {
        for len in [0usize, 1, 3, 55, 111, 112, 113, 127, 128, 239, 1000] {
            let message: Vec<u8> = (0..len).map(|i| (i * 17 + 3) as u8).collect();
            let bytes = padded(&message);
            let mut state = IV;
            crate::low::sha512_compress_blocks(&mut state, &bytes);
            assert_eq!(hash(&message), encode(state), "{len} bytes");
        }
    }

    #[test]
    fn fips180_two_blocks() {
        // FIPS 180-4, SHA-512 of the 112-byte letter sequence that pads
        // to two blocks.
        digest_hex(
            b"abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
            "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909",
        );
    }
}
