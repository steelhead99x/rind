// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! A rolled SHA-512 compression, for 32-bit portable microcontrollers.
//!
//! The portable backend otherwise runs [`sha512`](sha512.rs), whose two
//! unrolled sixteen-round bodies cost more of a small instruction cache than
//! this; HACL*'s fully unrolled body, about 47 KiB in 32-bit codegen, took
//! about 30 times this loop's time on an ESP32-S3, streaming its code from
//! flash. This follows Graviola's portable SHA-256: one 16-word window and
//! an 80-round loop, a few kilobytes. The round functions are FIPS 180-4
//! §4.1.3. Every test build compiles it, so ctgrind checks it on a host.
//!
//! Its sums go through [`Sum64`](sum64.rs), which on Xtensa adds in `u32`
//! lanes: LLVM adds a plain `u64` there with a branch on the carry.

use super::sha512::K;
use super::sum64::Sum64;

macro_rules! CH {
    ($x:expr, $y:expr, $z:expr) => {
        ($x & $y) ^ (!$x & $z)
    };
}

macro_rules! MAJ {
    ($x:expr, $y:expr, $z:expr) => {
        ($x & $y) ^ ($x & $z) ^ ($y & $z)
    };
}

// Σ0, Σ1, σ0, σ1 of FIPS 180-4 §4.1.3.
macro_rules! BSIG0 {
    ($x:expr) => {
        $x.rotate_right(28) ^ $x.rotate_right(34) ^ $x.rotate_right(39)
    };
}

macro_rules! BSIG1 {
    ($x:expr) => {
        $x.rotate_right(14) ^ $x.rotate_right(18) ^ $x.rotate_right(41)
    };
}

macro_rules! SSIG0 {
    ($x:expr) => {
        $x.rotate_right(1) ^ $x.rotate_right(8) ^ ($x >> 7)
    };
}

macro_rules! SSIG1 {
    ($x:expr) => {
        $x.rotate_right(19) ^ $x.rotate_right(61) ^ ($x >> 6)
    };
}

#[inline(never)]
fn sha512_compress_block(state: &mut [u64; 8], block: &[u8; 128]) {
    // Sixteen big-endian words. The caller already holds a whole block, so
    // the conversion is once, ahead of the round loop, and the loop does
    // not carry a `try_into` panic path.
    let (words, rest) = block.as_chunks::<8>();
    debug_assert!(rest.is_empty());
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    // A 16-word window into the whole W array, as in Graviola's SHA-256.
    let mut w: [u64; 16] = [0; 16];

    for t in 0..80 {
        // W[0..16] comes from the block; W[16..80] is
        //
        // W[t] = SSIG1(W[t - 2]) + W[t - 7] + SSIG0(W[t - 15]) + W[t - 16]
        //
        // with every index reduced mod 16 into the window.
        let w_t = if t < 16 {
            let w_t = u64::from_be_bytes(words[t]);
            w[t] = w_t;
            w_t
        } else {
            let w_t = Sum64::of(SSIG1!(w[(t - 2) % 16]))
                .add(w[(t - 7) % 16])
                .add(SSIG0!(w[(t - 15) % 16]))
                .add(w[(t - 16) % 16])
                .value();
            w[t % 16] = w_t;
            w_t
        };

        // T1, unfolded, is shared by `e` and `a`; T2 is Σ0(a) + Maj(a, b, c).
        let t1 = Sum64::of(h)
            .add(BSIG1!(e))
            .add(CH!(e, f, g))
            .add(K[t])
            .add(w_t);
        let new_a = t1.add(BSIG0!(a)).add(MAJ!(a, b, c)).value();
        h = g;
        g = f;
        f = e;
        e = t1.add(d).value();
        d = c;
        c = b;
        b = a;
        a = new_a;
    }

    state[0] = Sum64::of(state[0]).add(a).value();
    state[1] = Sum64::of(state[1]).add(b).value();
    state[2] = Sum64::of(state[2]).add(c).value();
    state[3] = Sum64::of(state[3]).add(d).value();
    state[4] = Sum64::of(state[4]).add(e).value();
    state[5] = Sum64::of(state[5]).add(f).value();
    state[6] = Sum64::of(state[6]).add(g).value();
    state[7] = Sum64::of(state[7]).add(h).value();
}

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));

    let (chunks, _) = blocks.as_chunks::<128>();
    for block in chunks {
        sha512_compress_block(state, block);
    }
}

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
        let (blocks, rest) = crate::low::split_tail::<128, 16>(message);
        let mut padded = blocks.to_vec();
        let mut last = [[0u8; 128]; 2];
        padded.extend_from_slice(crate::low::pad(rest, bits.to_be_bytes(), &mut last));
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
        // The block is the secret (a message, or an HMAC key block). Mark it
        // before this rolled loop, which 64-bit builds compile only in tests,
        // so ctgrind sees it. The state is public again before a comparison.
        crate::low::ct::secret_slice(&padded);
        sha512_compress_blocks(&mut state, &padded);
        encode(crate::low::ct::into_public(state))
    }

    fn digest_hex(message: &[u8], hex_digest: &str) {
        let expected = hex::decode(hex_digest).unwrap();
        assert_eq!(hash(message).as_slice(), expected.as_slice());
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

    /// Where the backend ships this compression, the comparison would call
    /// itself. Everywhere else it is the unrolled port or assembly.
    #[cfg(not(all(
        rind_backend = "portable",
        not(target_pointer_width = "64"),
        any(target_os = "espidf", target_os = "none")
    )))]
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
