// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256's compression as aws-lc's `sha256_block_data_order_nohw` runs it:
//! sixteen straight rounds over the block, then the other 48 in three passes
//! of sixteen rounds that rename the working variables by position, so no
//! round moves a register. aws-lc's own loop takes eight rounds a pass; sixteen
//! make the message-schedule indices constants, which measured faster here.
//! The round functions and constants are FIPS 180-4 §4.1.2 and §4.2.2.

use super::sha256_k::K;

macro_rules! round {
    ($k:expr, $t1:ident, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident) => {
        $t1 = $t1
            .wrapping_add($h)
            .wrapping_add($e.rotate_right(6) ^ $e.rotate_right(11) ^ $e.rotate_right(25))
            .wrapping_add(($e & $f) ^ (!$e & $g))
            .wrapping_add($k);
        $h = ($a.rotate_right(2) ^ $a.rotate_right(13) ^ $a.rotate_right(22))
            .wrapping_add(($a & $b) ^ ($a & $c) ^ ($b & $c));
        $d = $d.wrapping_add($t1);
        $h = $h.wrapping_add($t1);
    };
}

macro_rules! load {
    ($i:expr, $x:ident, $words:ident, $t1:ident, $($r:ident),*) => {
        $t1 = u32::from_be_bytes($words[$i]);
        $x[$i] = $t1;
        round!(K[$i], $t1, $($r),*);
    };
}

macro_rules! expand {
    ($j:expr, $k:expr, $x:ident, $t1:ident, $($r:ident),*) => {
        let s0 = $x[($j + 1) & 15];
        let s0 = s0.rotate_right(7) ^ s0.rotate_right(18) ^ (s0 >> 3);
        let s1 = $x[($j + 14) & 15];
        let s1 = s1.rotate_right(17) ^ s1.rotate_right(19) ^ (s1 >> 10);
        $t1 = $x[$j & 15].wrapping_add(s0).wrapping_add(s1).wrapping_add($x[($j + 9) & 15]);
        $x[$j & 15] = $t1;
        round!($k, $t1, $($r),*);
    };
}

fn sha256_compress_block(state: &mut [u32; 8], block: &[u8; 64]) {
    let (words, _) = block.as_chunks::<4>();
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    let mut x = [0u32; 16];
    let mut t1: u32;
    load!(0, x, words, t1, a, b, c, d, e, f, g, h);
    load!(1, x, words, t1, h, a, b, c, d, e, f, g);
    load!(2, x, words, t1, g, h, a, b, c, d, e, f);
    load!(3, x, words, t1, f, g, h, a, b, c, d, e);
    load!(4, x, words, t1, e, f, g, h, a, b, c, d);
    load!(5, x, words, t1, d, e, f, g, h, a, b, c);
    load!(6, x, words, t1, c, d, e, f, g, h, a, b);
    load!(7, x, words, t1, b, c, d, e, f, g, h, a);
    load!(8, x, words, t1, a, b, c, d, e, f, g, h);
    load!(9, x, words, t1, h, a, b, c, d, e, f, g);
    load!(10, x, words, t1, g, h, a, b, c, d, e, f);
    load!(11, x, words, t1, f, g, h, a, b, c, d, e);
    load!(12, x, words, t1, e, f, g, h, a, b, c, d);
    load!(13, x, words, t1, d, e, f, g, h, a, b, c);
    load!(14, x, words, t1, c, d, e, f, g, h, a, b);
    load!(15, x, words, t1, b, c, d, e, f, g, h, a);
    for ks in K[16..].as_chunks::<16>().0 {
        expand!(0, ks[0], x, t1, a, b, c, d, e, f, g, h);
        expand!(1, ks[1], x, t1, h, a, b, c, d, e, f, g);
        expand!(2, ks[2], x, t1, g, h, a, b, c, d, e, f);
        expand!(3, ks[3], x, t1, f, g, h, a, b, c, d, e);
        expand!(4, ks[4], x, t1, e, f, g, h, a, b, c, d);
        expand!(5, ks[5], x, t1, d, e, f, g, h, a, b, c);
        expand!(6, ks[6], x, t1, c, d, e, f, g, h, a, b);
        expand!(7, ks[7], x, t1, b, c, d, e, f, g, h, a);
        expand!(8, ks[8], x, t1, a, b, c, d, e, f, g, h);
        expand!(9, ks[9], x, t1, h, a, b, c, d, e, f, g);
        expand!(10, ks[10], x, t1, g, h, a, b, c, d, e, f);
        expand!(11, ks[11], x, t1, f, g, h, a, b, c, d, e);
        expand!(12, ks[12], x, t1, e, f, g, h, a, b, c, d);
        expand!(13, ks[13], x, t1, d, e, f, g, h, a, b, c);
        expand!(14, ks[14], x, t1, c, d, e, f, g, h, a, b);
        expand!(15, ks[15], x, t1, b, c, d, e, f, g, h, a);
    }

    for (s, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *s = s.wrapping_add(v);
    }
}

/// Compresses whole 64-byte `blocks` into `state`.
pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));
    let (chunks, _) = blocks.as_chunks::<64>();
    for block in chunks {
        sha256_compress_block(state, block);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::sha256_compress_blocks;

    /// FIPS 180-4's "abc": one padded block from SHA-256's IV.
    #[test]
    fn fips180_abc() {
        let mut state = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let mut block = [0u8; 64];
        block[..3].copy_from_slice(b"abc");
        block[3] = 0x80;
        block[63] = 24;
        sha256_compress_blocks(&mut state, &block);
        assert_eq!(
            state,
            [
                0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61,
                0xf20015ad
            ]
        );
    }

    /// FIPS 180-4's two-block message, "abcdbcde...nopq", whose padding fills
    /// a second block, and a rolled reference over arbitrary chaining states.
    #[test]
    fn two_blocks_and_reference() {
        let iv: [u32; 8] = [
            0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
            0x5be0cd19,
        ];
        let mut blocks = [0u8; 128];
        blocks[..56].copy_from_slice(b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq");
        blocks[56] = 0x80;
        blocks[126..].copy_from_slice(&(448u16).to_be_bytes());
        let mut state = iv;
        sha256_compress_blocks(&mut state, &blocks);
        assert_eq!(
            state,
            [
                0x248d6a61, 0xd20638b8, 0xe5c02693, 0x0c3e6039, 0xa33ce459, 0x64ff2167, 0xf6ecedd4,
                0x19db06c1
            ]
        );

        for case in 0..16u32 {
            let start: [u32; 8] = core::array::from_fn(|i| {
                case.wrapping_mul(0x9e37_79b9)
                    .rotate_left(i as u32 * 5)
                    .wrapping_add(i as u32)
            });
            let data: [u8; 64 * 3] =
                core::array::from_fn(|i| (i as u32).wrapping_mul(197).wrapping_add(case) as u8);
            for count in [0, 1, 3] {
                let mut got = start;
                sha256_compress_blocks(&mut got, &data[..count * 64]);
                let mut want = start;
                for block in data[..count * 64].chunks(64) {
                    rolled(&mut want, block);
                }
                assert_eq!(got, want, "{case}, {count}");
            }
        }
    }

    /// FIPS 180-4 §6.2.2 as written: the 64-word schedule, then 64 rounds.
    fn rolled(state: &mut [u32; 8], block: &[u8]) {
        let mut w = [0u32; 64];
        for (i, word) in block.chunks(4).enumerate() {
            w[i] = u32::from_be_bytes(word.try_into().unwrap());
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
        for i in 0..64 {
            let t1 = h
                .wrapping_add(e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25))
                .wrapping_add((e & f) ^ (!e & g))
                .wrapping_add(super::K[i])
                .wrapping_add(w[i]);
            let t2 = (a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22))
                .wrapping_add((a & b) ^ (a & c) ^ (b & c));
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (s, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
            *s = s.wrapping_add(v);
        }
    }
}
