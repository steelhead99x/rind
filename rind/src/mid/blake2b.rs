// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Unkeyed BLAKE2b (RFC 7693), for Argon2.
//!
//! Written from RFC 7693's specification and checked against its appendix
//! A vector, the BLAKE2 reference's KAT, and Argon2's vectors. Argon2 spends
//! nearly all its time filling memory, so this plain version costs it
//! nothing measurable.

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

const SIGMA: [[usize; 16]; 12] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
];

const BLOCK_LEN: usize = 128;

/// The most a BLAKE2b hash outputs.
pub(crate) const MAX_OUT_LEN: usize = 64;

#[derive(Clone)]
pub(crate) struct Blake2b {
    h: [u64; 8],
    // Bytes compressed so far; RFC 7693's 128-bit `t`.
    t: u128,
    buf: [u8; BLOCK_LEN],
    used: usize,
    out_len: usize,
}

impl Blake2b {
    /// Starts a hash of `out_len` bytes, which must be 1 through 64.
    pub(crate) fn new(out_len: usize) -> Self {
        assert!((1..=MAX_OUT_LEN).contains(&out_len));
        let mut h = IV;
        h[0] ^= 0x0101_0000 ^ out_len as u64;
        Self {
            h,
            t: 0,
            buf: [0; BLOCK_LEN],
            used: 0,
            out_len,
        }
    }

    pub(crate) fn update(&mut self, mut data: &[u8]) {
        // The last block is compressed differently, so a full buffer waits
        // until more data shows it is not the last.
        while !data.is_empty() {
            if self.used == BLOCK_LEN {
                self.t += BLOCK_LEN as u128;
                compress(&mut self.h, &self.buf, self.t, false);
                self.used = 0;
            }
            let take = (BLOCK_LEN - self.used).min(data.len());
            self.buf[self.used..self.used + take].copy_from_slice(&data[..take]);
            self.used += take;
            data = &data[take..];
        }
    }

    /// Writes the hash to `out`, which must be the length given to `new`.
    pub(crate) fn finish(mut self, out: &mut [u8]) {
        assert_eq!(out.len(), self.out_len);
        self.t += self.used as u128;
        self.buf[self.used..].fill(0);
        compress(&mut self.h, &self.buf, self.t, true);
        for (out, h) in out.chunks_mut(8).zip(self.h) {
            out.copy_from_slice(&h.to_le_bytes()[..out.len()]);
        }
    }
}

// RFC 7693's F.
fn compress(h: &mut [u64; 8], block: &[u8; BLOCK_LEN], t: u128, last: bool) {
    let mut m = [0u64; 16];
    for (m, bytes) in m.iter_mut().zip(block.as_chunks::<8>().0) {
        *m = u64::from_le_bytes(*bytes);
    }

    let mut v = [0u64; 16];
    v[..8].copy_from_slice(h);
    v[8..].copy_from_slice(&IV);
    v[12] ^= t as u64;
    v[13] ^= (t >> 64) as u64;
    if last {
        v[14] = !v[14];
    }

    for s in &SIGMA {
        g(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
        g(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
        g(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
        g(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
        g(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
        g(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
        g(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
        g(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
    }

    for i in 0..8 {
        h[i] ^= v[i] ^ v[i + 8];
    }
}

#[inline(always)]
fn g(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn hash(out_len: usize, chunks: &[&[u8]]) -> Vec<u8> {
        let mut ctx = Blake2b::new(out_len);
        for chunk in chunks {
            ctx.update(chunk);
        }
        let mut out = vec![0; out_len];
        ctx.finish(&mut out);
        out
    }

    #[test]
    fn rfc7693_appendix_a() {
        assert_eq!(
            hex::encode(hash(64, &[b"abc"])),
            "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1\
             7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"
        );
    }

    #[test]
    fn empty_and_short_outputs() {
        // From the BLAKE2 reference's `b2sum -l 512` and `-l 256`.
        assert_eq!(
            hex::encode(hash(64, &[])),
            "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419\
             d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"
        );
        assert_eq!(
            hex::encode(hash(32, &[])),
            "0e5751c026e543b2e8ab2eb06099daa1d1e5df47778f7787faab45cdf12fe3a8"
        );
    }

    #[test]
    fn chunking() {
        // Every split of messages around the block boundary, including one
        // exactly a block long, whose block must be compressed as the last.
        // Expected digests from Python's `hashlib.blake2b(bytes(range(len)))`.
        let message: Vec<u8> = (0..=255u8).collect();
        for (len, expected) in [
            (
                127,
                "b6292669ccd38d5f01caae96ba272c76a879a45743afa0725d83b9ebb26665b731f1848c52f11972b6644f554c064fa90780dbbbf3a89d4fc31f67df3e5857ef",
            ),
            (
                128,
                "2319e3789c47e2daa5fe807f61bec2a1a6537fa03f19ff32e87eecbfd64b7e0e8ccff439ac333b040f19b0c4ddd11a61e24ac1fe0f10a039806c5dcc0da3d115",
            ),
            (
                129,
                "f59711d44a031d5f97a9413c065d1e614c417ede998590325f49bad2fd444d3e4418be19aec4e11449ac1a57207898bc57d76a1bcf3566292c20c683a5c4648f",
            ),
            (
                255,
                "5b21c5fd8868367612474fa2e70e9cfa2201ffeee8fafab5797ad58fefa17c9b5b107da4a3db6320baaf2c8617d5a51df914ae88da3867c2d41f0cc14fa67928",
            ),
            (
                256,
                "1ecc896f34d3f9cac484c73f75f6a5fb58ee6784be41b35f46067b9c65c63a6794d3d744112c653f73dd7deb6666204c5a9bfa5b46081fc10fdbe7884fa5cbf8",
            ),
        ] {
            for split in 0..=len {
                let digest = hash(64, &[&message[..split], &message[split..len]]);
                assert_eq!(hex::encode(digest), expected);
            }
        }
    }

    #[test]
    fn matches_rustcrypto() {
        // RustCrypto's blake2 crate, as aws-lc-rs has no BLAKE2b, takes its
        // output length at compile time.
        fn oracle(out_len: usize, message: &[u8]) -> Vec<u8> {
            use blake2::Digest;
            use blake2::digest::consts::*;
            macro_rules! by_len {
                ($($n:literal $u:ident),*) => {
                    match out_len {
                        $($n => blake2::Blake2b::<$u>::digest(message).to_vec(),)*
                        _ => unreachable!(),
                    }
                };
            }
            by_len!(1 U1, 2 U2, 3 U3, 4 U4, 5 U5, 6 U6, 7 U7, 8 U8, 9 U9, 10 U10, 11 U11, 12 U12, 13 U13, 14 U14, 15 U15, 16 U16, 17 U17, 18 U18, 19 U19, 20 U20, 21 U21, 22 U22, 23 U23, 24 U24, 25 U25, 26 U26, 27 U27, 28 U28, 29 U29, 30 U30, 31 U31, 32 U32, 33 U33, 34 U34, 35 U35, 36 U36, 37 U37, 38 U38, 39 U39, 40 U40, 41 U41, 42 U42, 43 U43, 44 U44, 45 U45, 46 U46, 47 U47, 48 U48, 49 U49, 50 U50, 51 U51, 52 U52, 53 U53, 54 U54, 55 U55, 56 U56, 57 U57, 58 U58, 59 U59, 60 U60, 61 U61, 62 U62, 63 U63, 64 U64)
        }

        // Every output length, over messages up to two blocks and one byte,
        // each fed whole and split around the first block's boundary.
        let message: Vec<u8> = (0..257u32).map(|i| (i * 7 + 3) as u8).collect();
        for out_len in 1..=MAX_OUT_LEN {
            for len in 0..=message.len() {
                let message = &message[..len];
                let expected = oracle(out_len, message);
                for split in [0, 1, 127, 128, 129, len] {
                    let split = split.min(len);
                    let (a, b) = message.split_at(split);
                    assert_eq!(hash(out_len, &[a, b]), expected, "{out_len} {len} {split}");
                }
            }
        }
    }
}
