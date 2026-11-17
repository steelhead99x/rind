// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-512 compression. A 64-bit pointer unrolls all eighty rounds. A 32-bit
//! pointer rolls them: that unrolled body is about 47 KiB, several times the
//! ESP32-S3's 16 KiB instruction cache, so every block would stream its code
//! from flash. On that board the loop takes about 0.033× the unrolled body's
//! time. It follows [`sha256`](sha256.rs): one 16-word window. The round
//! functions and the eighty `K` constants are FIPS 180-4 §4.1.3 and §4.2.3.
//! The unit tests check FIPS 180-4's SHA-512 vectors, mark the block secret
//! so ctgrind checks this body, and, on every backend except portable,
//! compare with the compression that backend ships.

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

/// One block, eighty rounds unrolled. A 32-bit build keeps the loop below
/// this function: the unrolled body is about 47 KiB there.
#[cfg(target_pointer_width = "64")]
#[inline(never)]
fn sha512_compress_block(state: &mut [u64; 8], block: &[u8; 128]) {
    let (words, rest) = block.as_chunks::<8>();
    debug_assert!(rest.is_empty());
    let mut w = [0u64; 16];
    for (slot, word) in w.iter_mut().zip(words) {
        *slot = u64::from_be_bytes(*word);
    }
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    macro_rules! round {
        ($i:literal, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident) => {
            let w_t = message_word(&mut w, $i);
            let t1 = $h
                .wrapping_add(BSIG1!($e))
                .wrapping_add(CH!($e, $f, $g))
                .wrapping_add(K[$i])
                .wrapping_add(w_t);
            let t2 = BSIG0!($a).wrapping_add(MAJ!($a, $b, $c));
            $h = $g;
            $g = $f;
            $f = $e;
            $e = $d.wrapping_add(t1);
            $d = $c;
            $c = $b;
            $b = $a;
            $a = t1.wrapping_add(t2);
        };
    }

    round!(0, a, b, c, d, e, f, g, h);
    round!(1, a, b, c, d, e, f, g, h);
    round!(2, a, b, c, d, e, f, g, h);
    round!(3, a, b, c, d, e, f, g, h);
    round!(4, a, b, c, d, e, f, g, h);
    round!(5, a, b, c, d, e, f, g, h);
    round!(6, a, b, c, d, e, f, g, h);
    round!(7, a, b, c, d, e, f, g, h);
    round!(8, a, b, c, d, e, f, g, h);
    round!(9, a, b, c, d, e, f, g, h);
    round!(10, a, b, c, d, e, f, g, h);
    round!(11, a, b, c, d, e, f, g, h);
    round!(12, a, b, c, d, e, f, g, h);
    round!(13, a, b, c, d, e, f, g, h);
    round!(14, a, b, c, d, e, f, g, h);
    round!(15, a, b, c, d, e, f, g, h);
    round!(16, a, b, c, d, e, f, g, h);
    round!(17, a, b, c, d, e, f, g, h);
    round!(18, a, b, c, d, e, f, g, h);
    round!(19, a, b, c, d, e, f, g, h);
    round!(20, a, b, c, d, e, f, g, h);
    round!(21, a, b, c, d, e, f, g, h);
    round!(22, a, b, c, d, e, f, g, h);
    round!(23, a, b, c, d, e, f, g, h);
    round!(24, a, b, c, d, e, f, g, h);
    round!(25, a, b, c, d, e, f, g, h);
    round!(26, a, b, c, d, e, f, g, h);
    round!(27, a, b, c, d, e, f, g, h);
    round!(28, a, b, c, d, e, f, g, h);
    round!(29, a, b, c, d, e, f, g, h);
    round!(30, a, b, c, d, e, f, g, h);
    round!(31, a, b, c, d, e, f, g, h);
    round!(32, a, b, c, d, e, f, g, h);
    round!(33, a, b, c, d, e, f, g, h);
    round!(34, a, b, c, d, e, f, g, h);
    round!(35, a, b, c, d, e, f, g, h);
    round!(36, a, b, c, d, e, f, g, h);
    round!(37, a, b, c, d, e, f, g, h);
    round!(38, a, b, c, d, e, f, g, h);
    round!(39, a, b, c, d, e, f, g, h);
    round!(40, a, b, c, d, e, f, g, h);
    round!(41, a, b, c, d, e, f, g, h);
    round!(42, a, b, c, d, e, f, g, h);
    round!(43, a, b, c, d, e, f, g, h);
    round!(44, a, b, c, d, e, f, g, h);
    round!(45, a, b, c, d, e, f, g, h);
    round!(46, a, b, c, d, e, f, g, h);
    round!(47, a, b, c, d, e, f, g, h);
    round!(48, a, b, c, d, e, f, g, h);
    round!(49, a, b, c, d, e, f, g, h);
    round!(50, a, b, c, d, e, f, g, h);
    round!(51, a, b, c, d, e, f, g, h);
    round!(52, a, b, c, d, e, f, g, h);
    round!(53, a, b, c, d, e, f, g, h);
    round!(54, a, b, c, d, e, f, g, h);
    round!(55, a, b, c, d, e, f, g, h);
    round!(56, a, b, c, d, e, f, g, h);
    round!(57, a, b, c, d, e, f, g, h);
    round!(58, a, b, c, d, e, f, g, h);
    round!(59, a, b, c, d, e, f, g, h);
    round!(60, a, b, c, d, e, f, g, h);
    round!(61, a, b, c, d, e, f, g, h);
    round!(62, a, b, c, d, e, f, g, h);
    round!(63, a, b, c, d, e, f, g, h);
    round!(64, a, b, c, d, e, f, g, h);
    round!(65, a, b, c, d, e, f, g, h);
    round!(66, a, b, c, d, e, f, g, h);
    round!(67, a, b, c, d, e, f, g, h);
    round!(68, a, b, c, d, e, f, g, h);
    round!(69, a, b, c, d, e, f, g, h);
    round!(70, a, b, c, d, e, f, g, h);
    round!(71, a, b, c, d, e, f, g, h);
    round!(72, a, b, c, d, e, f, g, h);
    round!(73, a, b, c, d, e, f, g, h);
    round!(74, a, b, c, d, e, f, g, h);
    round!(75, a, b, c, d, e, f, g, h);
    round!(76, a, b, c, d, e, f, g, h);
    round!(77, a, b, c, d, e, f, g, h);
    round!(78, a, b, c, d, e, f, g, h);
    round!(79, a, b, c, d, e, f, g, h);

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

/// `W[t]` from the 16-word window. Rounds 78 and 79 do not store: nothing
/// later reads those words, and a store there is an unused assignment.
#[cfg(target_pointer_width = "64")]
#[inline(always)]
fn message_word(w: &mut [u64; 16], t: usize) -> u64 {
    if t < 16 {
        w[t]
    } else {
        let w_t = SSIG1!(w[(t + 14) & 15])
            .wrapping_add(w[(t + 9) & 15])
            .wrapping_add(SSIG0!(w[(t + 1) & 15]))
            .wrapping_add(w[t & 15]);
        if t < 78 {
            w[t & 15] = w_t;
        }
        w_t
    }
}

#[cfg(not(target_pointer_width = "64"))]
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

    // A 16-word window into the whole W array, as in sha256.rs.
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
            let w_t = SSIG1!(w[(t - 2) % 16])
                .wrapping_add(w[(t - 7) % 16])
                .wrapping_add(SSIG0!(w[(t - 15) % 16]))
                .wrapping_add(w[(t - 16) % 16]);
            w[t % 16] = w_t;
            w_t
        };

        let t1 = h
            .wrapping_add(BSIG1!(e))
            .wrapping_add(CH!(e, f, g))
            .wrapping_add(K[t])
            .wrapping_add(w_t);
        let t2 = BSIG0!(a).wrapping_add(MAJ!(a, b, c));
        h = g;
        g = f;
        f = e;
        e = d.wrapping_add(t1);
        d = c;
        c = b;
        b = a;
        a = t1.wrapping_add(t2);
    }

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));

    let (chunks, _) = blocks.as_chunks::<128>();
    for block in chunks {
        sha512_compress_block(state, block);
    }
}

// FIPS 180-4 §4.2.3. aarch64's SHA-512 instructions add these two at a time.
pub(crate) static K: [u64; 80] = [
    0x428a2f98d728ae22,
    0x7137449123ef65cd,
    0xb5c0fbcfec4d3b2f,
    0xe9b5dba58189dbbc,
    0x3956c25bf348b538,
    0x59f111f1b605d019,
    0x923f82a4af194f9b,
    0xab1c5ed5da6d8118,
    0xd807aa98a3030242,
    0x12835b0145706fbe,
    0x243185be4ee4b28c,
    0x550c7dc3d5ffb4e2,
    0x72be5d74f27b896f,
    0x80deb1fe3b1696b1,
    0x9bdc06a725c71235,
    0xc19bf174cf692694,
    0xe49b69c19ef14ad2,
    0xefbe4786384f25e3,
    0x0fc19dc68b8cd5b5,
    0x240ca1cc77ac9c65,
    0x2de92c6f592b0275,
    0x4a7484aa6ea6e483,
    0x5cb0a9dcbd41fbd4,
    0x76f988da831153b5,
    0x983e5152ee66dfab,
    0xa831c66d2db43210,
    0xb00327c898fb213f,
    0xbf597fc7beef0ee4,
    0xc6e00bf33da88fc2,
    0xd5a79147930aa725,
    0x06ca6351e003826f,
    0x142929670a0e6e70,
    0x27b70a8546d22ffc,
    0x2e1b21385c26c926,
    0x4d2c6dfc5ac42aed,
    0x53380d139d95b3df,
    0x650a73548baf63de,
    0x766a0abb3c77b2a8,
    0x81c2c92e47edaee6,
    0x92722c851482353b,
    0xa2bfe8a14cf10364,
    0xa81a664bbc423001,
    0xc24b8b70d0f89791,
    0xc76c51a30654be30,
    0xd192e819d6ef5218,
    0xd69906245565a910,
    0xf40e35855771202a,
    0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8,
    0x1e376c085141ab53,
    0x2748774cdf8eeb99,
    0x34b0bcb5e19b48a8,
    0x391c0cb3c5c95a63,
    0x4ed8aa4ae3418acb,
    0x5b9cca4f7763e373,
    0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc,
    0x78a5636f43172f60,
    0x84c87814a1f0ab72,
    0x8cc702081a6439ec,
    0x90befffa23631e28,
    0xa4506cebde82bde9,
    0xbef9a3f7b2c67915,
    0xc67178f2e372532b,
    0xca273eceea26619c,
    0xd186b8c721c0c207,
    0xeada7dd6cde0eb1e,
    0xf57d4f7fee6ed178,
    0x06f067aa72176fba,
    0x0a637dc5a2c898a6,
    0x113f9804bef90dae,
    0x1b710b35131c471b,
    0x28db77f523047d84,
    0x32caab7b40c72493,
    0x3c9ebe0a15c9bebc,
    0x431d67c49c100d4c,
    0x4cc5d4becb3e42b6,
    0x597f299cfc657e2a,
    0x5fcb6fab3ad6faec,
    0x6c44198c4a475817,
];

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
        // before this body so ctgrind sees it. The state is public again
        // before a comparison.
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

    /// The portable backend is this compression, and so are x86_64 and armv7,
    /// so there the comparison calls itself. On aarch64 it compares the
    /// crypto-extension body, when the CPU has it, with this one.
    #[cfg(not(rind_backend = "portable"))]
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
