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
