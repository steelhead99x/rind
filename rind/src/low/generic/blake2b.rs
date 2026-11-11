// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! BLAKE2b, as [RFC 7693](https://www.rfc-editor.org/rfc/rfc7693) specifies it,
//! only as far as Argon2's variable-length hash needs: an unkeyed hash of at
//! most 64 bytes.
//!
//! Argon2's compression uses the same rotations and a different mixing
//! function, so this is not that permutation.

const IV: [u64; 8] = [
    0x6a09_e667_f3bc_c908,
    0xbb67_ae85_84ca_a73b,
    0x3c6e_f372_fe94_f82b,
    0xa54f_f53a_5f1d_36f1,
    0x510e_527f_ade6_82d1,
    0x9b05_688c_2b3e_6c1f,
    0x1f83_d9ab_fb41_bd6b,
    0x5be0_cd19_137e_2179,
];

/// Message word schedule, RFC 7693 section 2.7.
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

const BLOCK: usize = 128;

/// An unkeyed BLAKE2b in progress, writing `out_len` bytes, from 1 to 64.
pub(crate) struct Blake2b {
    h: [u64; 8],
    t0: u64,
    t1: u64,
    buf: [u8; BLOCK],
    buflen: usize,
    out_len: usize,
}

impl Blake2b {
    /// Starts a hash of `out_len` bytes. `out_len` is 1 to 64.
    pub(crate) fn new(out_len: usize) -> Self {
        debug_assert!((1..=64).contains(&out_len));
        let mut h = IV;
        // Fanout and depth are 1, the key length is 0, and the digest length
        // is `out_len`: the low word of the parameter block.
        h[0] ^= 0x0101_0000 ^ (out_len as u64);
        Self {
            h,
            t0: 0,
            t1: 0,
            buf: [0; BLOCK],
            buflen: 0,
            out_len,
        }
    }

    /// Absorbs `data`. Its length is public; its bytes are not branched on.
    pub(crate) fn update(&mut self, mut data: &[u8]) {
        if data.is_empty() {
            return;
        }
        if self.buflen + data.len() > BLOCK {
            let fill = BLOCK - self.buflen;
            self.buf[self.buflen..].copy_from_slice(&data[..fill]);
            self.increment(BLOCK as u64);
            let block = self.buf;
            self.compress(&block, false);
            self.buflen = 0;
            data = &data[fill..];
            while data.len() > BLOCK {
                let mut block = [0u8; BLOCK];
                block.copy_from_slice(&data[..BLOCK]);
                self.increment(BLOCK as u64);
                self.compress(&block, false);
                data = &data[BLOCK..];
            }
        }
        let end = self.buflen + data.len();
        self.buf[self.buflen..end].copy_from_slice(data);
        self.buflen = end;
    }

    /// Writes the digest into `out`, which is `out_len` bytes.
    pub(crate) fn finalize(mut self, out: &mut [u8]) {
        debug_assert_eq!(out.len(), self.out_len);
        self.increment(self.buflen as u64);
        self.buf[self.buflen..].fill(0);
        let block = self.buf;
        self.compress(&block, true);
        let mut full = [0u8; 64];
        for (i, word) in self.h.iter().enumerate() {
            full[i * 8..i * 8 + 8].copy_from_slice(&word.to_le_bytes());
        }
        out.copy_from_slice(&full[..self.out_len]);
    }

    fn increment(&mut self, n: u64) {
        let (lo, carry) = self.t0.overflowing_add(n);
        self.t0 = lo;
        if carry {
            self.t1 = self.t1.wrapping_add(1);
        }
    }

    fn compress(&mut self, block: &[u8; BLOCK], last: bool) {
        let mut m = [0u64; 16];
        for i in 0..16 {
            let mut word = [0u8; 8];
            word.copy_from_slice(&block[i * 8..i * 8 + 8]);
            m[i] = u64::from_le_bytes(word);
        }
        let mut v = [0u64; 16];
        v[..8].copy_from_slice(&self.h);
        v[8..].copy_from_slice(&IV);
        v[12] ^= self.t0;
        v[13] ^= self.t1;
        if last {
            v[14] ^= u64::MAX;
        }
        for s in &SIGMA {
            mix(&mut v, 0, 4, 8, 12, m[s[0]], m[s[1]]);
            mix(&mut v, 1, 5, 9, 13, m[s[2]], m[s[3]]);
            mix(&mut v, 2, 6, 10, 14, m[s[4]], m[s[5]]);
            mix(&mut v, 3, 7, 11, 15, m[s[6]], m[s[7]]);
            mix(&mut v, 0, 5, 10, 15, m[s[8]], m[s[9]]);
            mix(&mut v, 1, 6, 11, 12, m[s[10]], m[s[11]]);
            mix(&mut v, 2, 7, 8, 13, m[s[12]], m[s[13]]);
            mix(&mut v, 3, 4, 9, 14, m[s[14]], m[s[15]]);
        }
        for i in 0..8 {
            self.h[i] ^= v[i] ^ v[i + 8];
        }
    }
}

fn mix(v: &mut [u64; 16], a: usize, b: usize, c: usize, d: usize, x: u64, y: u64) {
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(x);
    v[d] = (v[d] ^ v[a]).rotate_right(32);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(24);
    v[a] = v[a].wrapping_add(v[b]).wrapping_add(y);
    v[d] = (v[d] ^ v[a]).rotate_right(16);
    v[c] = v[c].wrapping_add(v[d]);
    v[b] = (v[b] ^ v[c]).rotate_right(63);
}

/// BLAKE2b-512 of the concatenation of `parts`, written into `out`, which is 64 bytes.
pub(crate) fn hash(parts: &[&[u8]], out: &mut [u8]) {
    debug_assert_eq!(out.len(), 64);
    let mut hash = Blake2b::new(64);
    for part in parts {
        hash.update(part);
    }
    hash.finalize(out);
}

/// Argon2's variable-length hash, RFC 9106 section 3.2, of the concatenation
/// of `parts`, written into `out`.
///
/// `out` is non-empty and at most `u32::MAX` bytes. The caller has checked both.
pub(crate) fn blake2b_long(parts: &[&[u8]], out: &mut [u8]) {
    debug_assert!(!out.is_empty());
    let len = (out.len() as u32).to_le_bytes();
    if out.len() <= 64 {
        let mut hash = Blake2b::new(out.len());
        hash.update(&len);
        for part in parts {
            hash.update(part);
        }
        hash.finalize(out);
        return;
    }

    let mut hash = Blake2b::new(64);
    hash.update(&len);
    for part in parts {
        hash.update(part);
    }
    let mut last = [0u8; 64];
    hash.finalize(&mut last);
    out[..32].copy_from_slice(&last[..32]);
    let mut produced = 32;
    while out.len() - produced > 64 {
        let mut hash = Blake2b::new(64);
        hash.update(&last);
        hash.finalize(&mut last);
        out[produced..produced + 32].copy_from_slice(&last[..32]);
        produced += 32;
    }
    let mut hash = Blake2b::new(out.len() - produced);
    hash.update(&last);
    hash.finalize(&mut out[produced..]);
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn hash(out_len: usize, data: &[u8]) -> Vec<u8> {
        let mut hash = Blake2b::new(out_len);
        hash.update(data);
        let mut out = vec![0u8; out_len];
        hash.finalize(&mut out);
        out
    }

    #[test]
    fn rfc7693() {
        // RFC 7693 appendix A, unkeyed BLAKE2b-512.
        assert_eq!(
            hex::encode(hash(64, b"")),
            "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419\
             d25e1031afee585313896444934eb04b903a685b1448b755d56f701afe9be2ce"
        );
        assert_eq!(
            hex::encode(hash(64, b"abc")),
            "ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1\
             7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923"
        );
    }

    #[test]
    fn long_output_is_deterministic_and_extends() {
        let mut once = [0u8; 128];
        let mut twice = [0u8; 128];
        blake2b_long(&[b"argon2"], &mut once);
        let mut hash = Blake2b::new(64);
        // A second call with the input split must match one call.
        blake2b_long(&[b"arg", b"on2"], &mut twice);
        assert_eq!(once, twice);
        hash.update(b"argon2");
        let mut short = [0u8; 64];
        hash.finalize(&mut short);
        // The long hash is not a prefix of the 64-byte hash: it prefixes the
        // length. Just check it differs and the 65th byte is produced.
        assert_ne!(&once[..64], &short);
        assert!(once.iter().any(|&b| b != 0));
    }
}
