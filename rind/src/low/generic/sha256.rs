// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::sha256_k::K;

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

macro_rules! BSIG0 {
    ($x:expr) => {
        $x.rotate_right(2) ^ $x.rotate_right(13) ^ $x.rotate_right(22)
    };
}

macro_rules! BSIG1 {
    ($x:expr) => {
        $x.rotate_right(6) ^ $x.rotate_right(11) ^ $x.rotate_right(25)
    };
}

macro_rules! SSIG0 {
    ($x:expr) => {
        $x.rotate_right(7) ^ $x.rotate_right(18) ^ ($x >> 3)
    };
}

macro_rules! SSIG1 {
    ($x:expr) => {
        $x.rotate_right(17) ^ $x.rotate_right(19) ^ ($x >> 10)
    };
}

// A 32-bit Arm core has too few registers to rotate the eight working
// variables each round, and a round that names them afresh moves none (see
// `round!`): on a Cortex-A7 that is 1.3x faster than the loop below. Other
// targets keep the loop, whose code is a fraction of the size.
/// One round with the eight working variables renamed instead of rotated, so
/// a round moves no register: the next round names `$h` as its `a`.
#[cfg(target_arch = "arm")]
macro_rules! round {
    ($a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $k:expr, $w:expr) => {
        let t1 = $h
            .wrapping_add(BSIG1!($e))
            .wrapping_add(CH!($e, $f, $g))
            .wrapping_add($k)
            .wrapping_add($w);
        $d = $d.wrapping_add(t1);
        $h = t1.wrapping_add(BSIG0!($a).wrapping_add(MAJ!($a, $b, $c)));
    };
}

/// `W[t]` in place of `W[t - 16]`, from the 16-word window `w`, for `i` = `t`
/// mod 16.
#[cfg(target_arch = "arm")]
macro_rules! extend {
    ($w:ident, $i:literal) => {
        $w[$i] = SSIG1!($w[($i + 14) % 16])
            .wrapping_add($w[($i + 9) % 16])
            .wrapping_add(SSIG0!($w[($i + 1) % 16]))
            .wrapping_add($w[$i]);
    };
}

/// Sixteen rounds over `w`, `k` being the first of their sixteen constants.
/// With `$schedule`, each word of `w` is first extended by sixteen, just ahead
/// of the round that reads it, so the schedule's loads and shifts fill the
/// round's idle issue slots: a separate pass over `w` measured 8% slower on a
/// Cortex-A7.
#[cfg(target_arch = "arm")]
macro_rules! sixteen {
    ($schedule:literal, $a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $w:ident, $k:expr) => {
        if $schedule {
            extend!($w, 0);
        }
        round!($a, $b, $c, $d, $e, $f, $g, $h, K[$k + 0], $w[0]);
        if $schedule {
            extend!($w, 1);
        }
        round!($h, $a, $b, $c, $d, $e, $f, $g, K[$k + 1], $w[1]);
        if $schedule {
            extend!($w, 2);
        }
        round!($g, $h, $a, $b, $c, $d, $e, $f, K[$k + 2], $w[2]);
        if $schedule {
            extend!($w, 3);
        }
        round!($f, $g, $h, $a, $b, $c, $d, $e, K[$k + 3], $w[3]);
        if $schedule {
            extend!($w, 4);
        }
        round!($e, $f, $g, $h, $a, $b, $c, $d, K[$k + 4], $w[4]);
        if $schedule {
            extend!($w, 5);
        }
        round!($d, $e, $f, $g, $h, $a, $b, $c, K[$k + 5], $w[5]);
        if $schedule {
            extend!($w, 6);
        }
        round!($c, $d, $e, $f, $g, $h, $a, $b, K[$k + 6], $w[6]);
        if $schedule {
            extend!($w, 7);
        }
        round!($b, $c, $d, $e, $f, $g, $h, $a, K[$k + 7], $w[7]);
        if $schedule {
            extend!($w, 8);
        }
        round!($a, $b, $c, $d, $e, $f, $g, $h, K[$k + 8], $w[8]);
        if $schedule {
            extend!($w, 9);
        }
        round!($h, $a, $b, $c, $d, $e, $f, $g, K[$k + 9], $w[9]);
        if $schedule {
            extend!($w, 10);
        }
        round!($g, $h, $a, $b, $c, $d, $e, $f, K[$k + 10], $w[10]);
        if $schedule {
            extend!($w, 11);
        }
        round!($f, $g, $h, $a, $b, $c, $d, $e, K[$k + 11], $w[11]);
        if $schedule {
            extend!($w, 12);
        }
        round!($e, $f, $g, $h, $a, $b, $c, $d, K[$k + 12], $w[12]);
        if $schedule {
            extend!($w, 13);
        }
        round!($d, $e, $f, $g, $h, $a, $b, $c, K[$k + 13], $w[13]);
        if $schedule {
            extend!($w, 14);
        }
        round!($c, $d, $e, $f, $g, $h, $a, $b, K[$k + 14], $w[14]);
        if $schedule {
            extend!($w, 15);
        }
        round!($b, $c, $d, $e, $f, $g, $h, $a, K[$k + 15], $w[15]);
    };
}

#[cfg(target_arch = "arm")]
fn sha256_compress_block(state: &mut [u32; 8], block: &[u8; 64]) {
    let (words, rest) = block.as_chunks::<4>();
    debug_assert!(rest.is_empty());
    let mut w = [0u32; 16];
    for (slot, word) in w.iter_mut().zip(words) {
        *slot = u32::from_be_bytes(*word);
    }
    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = *state;

    sixteen!(false, a, b, c, d, e, f, g, h, w, 0);
    sixteen!(true, a, b, c, d, e, f, g, h, w, 16);
    sixteen!(true, a, b, c, d, e, f, g, h, w, 32);
    sixteen!(true, a, b, c, d, e, f, g, h, w, 48);

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
    state[5] = state[5].wrapping_add(f);
    state[6] = state[6].wrapping_add(g);
    state[7] = state[7].wrapping_add(h);
}

#[cfg(not(target_arch = "arm"))]
fn sha256_compress_block(state: &mut [u32; 8], block: &[u8]) {
    let mut a = state[0];
    let mut b = state[1];
    let mut c = state[2];
    let mut d = state[3];
    let mut e = state[4];
    let mut f = state[5];
    let mut g = state[6];
    let mut h = state[7];

    // This is a 16-word window into the whole W array.
    let mut w: [u32; 16] = [0; 16];

    for t in 0..64 {
        // For W[0..16] we process the input into W.
        // For W[16..64] we compute the next W value:
        //
        // W[t] = SSIG1(W[t - 2]) + W[t - 7] + SSIG0(W[t - 15]) + W[t - 16];
        //
        // But all W indices are reduced mod 16 into our window.
        let w_t = if t < 16 {
            let w_t = u32::from_be_bytes(block[t * 4..(t + 1) * 4].try_into().unwrap());
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

pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    assert!(blocks.len().is_multiple_of(64));

    let (chunks, _) = blocks.as_chunks::<64>();
    for block in chunks {
        sha256_compress_block(state, block);
    }
}
