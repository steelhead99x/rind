// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-512's compression as aws-lc's `sha512_block_data_order_nohw` runs it:
//! sixteen straight rounds over the block, then the other 64 in four passes
//! of sixteen rounds that rename the working variables by position, so no round
//! moves a register. The round functions and constants are FIPS 180-4
//! §4.1.3 and §4.2.3.

use super::sha512_k::K;

macro_rules! round {
    ($k:expr, $t1:ident, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident) => {
        $t1 = $t1
            .wrapping_add($h)
            .wrapping_add($e.rotate_right(14) ^ $e.rotate_right(18) ^ $e.rotate_right(41))
            .wrapping_add(($e & $f) ^ (!$e & $g))
            .wrapping_add($k);
        $h = ($a.rotate_right(28) ^ $a.rotate_right(34) ^ $a.rotate_right(39))
            .wrapping_add(($a & $b) ^ ($a & $c) ^ ($b & $c));
        $d = $d.wrapping_add($t1);
        $h = $h.wrapping_add($t1);
    };
}

macro_rules! load {
    ($i:expr, $x:ident, $words:ident, $t1:ident, $($r:ident),*) => {
        $t1 = u64::from_be_bytes($words[$i]);
        $x[$i] = $t1;
        round!(K[$i], $t1, $($r),*);
    };
}

macro_rules! expand {
    ($j:expr, $ks:ident, $x:ident, $t1:ident, $($r:ident),*) => {
        let s0 = $x[($j + 1) & 15];
        let s0 = s0.rotate_right(1) ^ s0.rotate_right(8) ^ (s0 >> 7);
        let s1 = $x[($j + 14) & 15];
        let s1 = s1.rotate_right(19) ^ s1.rotate_right(61) ^ (s1 >> 6);
        $t1 = $x[$j & 15].wrapping_add(s0).wrapping_add(s1).wrapping_add($x[($j + 9) & 15]);
        $x[$j & 15] = $t1;
        round!($ks[$j], $t1, $($r),*);
    };
}

fn sha512_compress_block(state: &mut [u64; 8], block: &[u8; 128]) {
    let (words, _) = block.as_chunks::<8>();
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;
    let mut x = [0u64; 16];
    let mut t1: u64;

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
        expand!(0, ks, x, t1, a, b, c, d, e, f, g, h);
        expand!(1, ks, x, t1, h, a, b, c, d, e, f, g);
        expand!(2, ks, x, t1, g, h, a, b, c, d, e, f);
        expand!(3, ks, x, t1, f, g, h, a, b, c, d, e);
        expand!(4, ks, x, t1, e, f, g, h, a, b, c, d);
        expand!(5, ks, x, t1, d, e, f, g, h, a, b, c);
        expand!(6, ks, x, t1, c, d, e, f, g, h, a, b);
        expand!(7, ks, x, t1, b, c, d, e, f, g, h, a);
        expand!(8, ks, x, t1, a, b, c, d, e, f, g, h);
        expand!(9, ks, x, t1, h, a, b, c, d, e, f, g);
        expand!(10, ks, x, t1, g, h, a, b, c, d, e, f);
        expand!(11, ks, x, t1, f, g, h, a, b, c, d, e);
        expand!(12, ks, x, t1, e, f, g, h, a, b, c, d);
        expand!(13, ks, x, t1, d, e, f, g, h, a, b, c);
        expand!(14, ks, x, t1, c, d, e, f, g, h, a, b);
        expand!(15, ks, x, t1, b, c, d, e, f, g, h, a);
    }

    for (s, v) in state.iter_mut().zip([a, b, c, d, e, f, g, h]) {
        *s = s.wrapping_add(v);
    }
}

/// Compresses whole 128-byte `blocks` into `state`.
pub(crate) fn sha512_compress_blocks(state: &mut [u64; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(128));
    let (chunks, _) = blocks.as_chunks::<128>();
    for block in chunks {
        sha512_compress_block(state, block);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::sha512_compress_blocks;

    /// The unrolled compression matches the rolled one on arbitrary chaining
    /// states and block counts, which covers HMAC's keyed states as well as a
    /// fresh digest. FIPS 180-4's vectors check the rolled loop.
    #[test]
    fn matches_rolled_loop() {
        for case in 0..32u64 {
            let state: [u64; 8] = core::array::from_fn(|i| {
                case.wrapping_mul(0x9e37_79b9_7f4a_7c15)
                    .rotate_left(i as u32 * 7)
                    .wrapping_add(i as u64)
            });
            let blocks: [u8; 128 * 9] = core::array::from_fn(|i| match case {
                0 => 0,
                1 => 0xff,
                _ => (i as u64).wrapping_mul(197).wrapping_add(case) as u8,
            });
            for count in [0, 1, 2, 9] {
                let input = &blocks[..count * 128];
                let mut got = state;
                sha512_compress_blocks(&mut got, input);
                let mut want = state;
                crate::low::generic::sha512::sha512_compress_blocks(&mut want, input);
                assert_eq!(got, want, "{case}, {count}");
            }
        }
    }
}
