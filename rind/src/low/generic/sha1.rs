// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

macro_rules! CH {
    ($x:expr, $y:expr, $z:expr) => {
        $z ^ ($x & ($y ^ $z))
    };
}

macro_rules! PARITY {
    ($x:expr, $y:expr, $z:expr) => {
        $x ^ $y ^ $z
    };
}

macro_rules! MAJ {
    ($x:expr, $y:expr, $z:expr) => {
        ($x & $y) | ($z & ($x | $y))
    };
}

fn sha1_compress_block(state: &mut [u32; 5], block: &[u8; 64]) {
    // This is a 16-word window into the whole W array.
    let mut w = [0u32; 16];
    let (words, _) = block.as_chunks::<4>();
    for (w, word) in w.iter_mut().zip(words) {
        *w = u32::from_be_bytes(*word);
    }

    // W[t] = ROTL1(W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16]),
    // with all W indices reduced mod 16 into our window.
    macro_rules! w {
        ($t:expr) => {{
            let t = $t;
            if t >= 16 {
                w[t & 15] = (w[(t + 13) & 15] ^ w[(t + 8) & 15] ^ w[(t + 2) & 15] ^ w[t & 15])
                    .rotate_left(1);
            }
            w[t & 15]
        }};
    }

    let [mut a, mut b, mut c, mut d, mut e] = *state;

    // Five rounds from `$t`.  Rather than shifting a..e along after every
    // round, each round renames them, so the names line up again after five.
    macro_rules! rounds5 {
        ($f:ident, $k:literal, $t:expr) => {
            let t = $t;
            e = e
                .wrapping_add(a.rotate_left(5))
                .wrapping_add($f!(b, c, d))
                .wrapping_add($k)
                .wrapping_add(w!(t));
            b = b.rotate_left(30);
            d = d
                .wrapping_add(e.rotate_left(5))
                .wrapping_add($f!(a, b, c))
                .wrapping_add($k)
                .wrapping_add(w!(t + 1));
            a = a.rotate_left(30);
            c = c
                .wrapping_add(d.rotate_left(5))
                .wrapping_add($f!(e, a, b))
                .wrapping_add($k)
                .wrapping_add(w!(t + 2));
            e = e.rotate_left(30);
            b = b
                .wrapping_add(c.rotate_left(5))
                .wrapping_add($f!(d, e, a))
                .wrapping_add($k)
                .wrapping_add(w!(t + 3));
            d = d.rotate_left(30);
            a = a
                .wrapping_add(b.rotate_left(5))
                .wrapping_add($f!(c, d, e))
                .wrapping_add($k)
                .wrapping_add(w!(t + 4));
            c = c.rotate_left(30);
        };
    }

    // Every round is written out, so each schedule index is a constant and
    // the window's words stay in registers or fixed stack slots, as in
    // aws-lc's `sha1_block_data_order_nohw`; a loop over `t` would index it
    // at run time.
    rounds5!(CH, 0x5a827999, 0);
    rounds5!(CH, 0x5a827999, 5);
    rounds5!(CH, 0x5a827999, 10);
    rounds5!(CH, 0x5a827999, 15);
    rounds5!(PARITY, 0x6ed9eba1, 20);
    rounds5!(PARITY, 0x6ed9eba1, 25);
    rounds5!(PARITY, 0x6ed9eba1, 30);
    rounds5!(PARITY, 0x6ed9eba1, 35);
    rounds5!(MAJ, 0x8f1bbcdc, 40);
    rounds5!(MAJ, 0x8f1bbcdc, 45);
    rounds5!(MAJ, 0x8f1bbcdc, 50);
    rounds5!(MAJ, 0x8f1bbcdc, 55);
    rounds5!(PARITY, 0xca62c1d6, 60);
    rounds5!(PARITY, 0xca62c1d6, 65);
    rounds5!(PARITY, 0xca62c1d6, 70);
    rounds5!(PARITY, 0xca62c1d6, 75);

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
}

pub(crate) fn sha1_compress_blocks(state: &mut [u32; 5], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));

    let (chunks, _) = blocks.as_chunks::<64>();
    for block in chunks {
        sha1_compress_block(state, block);
    }
}

// Miri and wasm builds have no `sha1` dev-dependency (rind/Cargo.toml).
#[cfg(all(test, not(any(miri, target_family = "wasm"))))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::collection::vec;
    use proptest::prelude::*;

    use super::*;

    proptest! {
        // RustCrypto's compression shares no code with this one. An arbitrary
        // starting state reaches inputs a hash from the standard IV never
        // does, and up to five blocks carry each block's state into the next.
        #[test]
        fn matches_rustcrypto(
            state in any::<[u32; 5]>(),
            blocks in (0..=5usize).prop_flat_map(|n| vec(any::<u8>(), n * 64)),
        ) {
            let mut want = state;
            sha1::block_api::compress(&mut want, blocks.as_chunks::<64>().0);
            let mut got = state;
            sha1_compress_blocks(&mut got, &blocks);
            prop_assert_eq!(got, want);
        }
    }
}
