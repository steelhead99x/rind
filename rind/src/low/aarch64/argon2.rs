// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on NEON.
//!
//! The permutation is the NEON `fill_block` libsodium ships in
//! `blamka-round-neon.h` and `argon2-fill-block-neon.c`, a port of the Argon2
//! reference implementation's SSSE3 fill (copyright 2015 Daniel Dinu, Dmitry
//! Khovratovich, Jean-Philippe Aumasson, and Samuel Neves; CC0-1.0). The lane
//! shuffles are that code's, so a block it returns matches the scalar one.
//!
//! aarch64 requires NEON. [`crate::low::cpu::check`] refuses a CPU without it,
//! naming `neon`, before a public call reaches here. This function does not
//! run the portable permutation in its place.

use core::arch::aarch64::*;

use crate::low::argon2::Block;

/// `G(prev, reference)`, the NEON permutation.
pub(crate) fn compress(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    // SAFETY: this backend requires NEON, and the blocks are 1024 bytes each,
    // which the loads and stores stay inside.
    unsafe { compress_neon(next, prev, reference, with_xor) };
}

#[target_feature(enable = "neon")]
unsafe fn compress_neon(next: &mut Block, prev: &Block, reference: &Block, with_xor: bool) {
    // SAFETY: `prev` is 1024 bytes, as `load` requires.
    let mut state = unsafe { load(prev) };
    let mut xy = [core::mem::MaybeUninit::<uint64x2_t>::uninit(); 64];
    // SAFETY: each block is 1024 bytes, sixty-four 16-byte lanes. Every `xy`
    // lane is written before it is read.
    unsafe {
        for i in 0..64 {
            state[i] = veorq_u64(state[i], vld1q_u64(reference.0.as_ptr().add(i * 2)));
            xy[i].write(if with_xor {
                veorq_u64(state[i], vld1q_u64(next.0.as_ptr().add(i * 2)))
            } else {
                state[i]
            });
        }
        let xy =
            core::mem::transmute::<[core::mem::MaybeUninit<uint64x2_t>; 64], [uint64x2_t; 64]>(xy);
        for i in 0..8 {
            round(
                &mut state,
                8 * i,
                8 * i + 1,
                8 * i + 2,
                8 * i + 3,
                8 * i + 4,
                8 * i + 5,
                8 * i + 6,
                8 * i + 7,
            );
        }
        for i in 0..8 {
            round(
                &mut state,
                i,
                8 + i,
                16 + i,
                24 + i,
                32 + i,
                40 + i,
                48 + i,
                56 + i,
            );
        }
        for i in 0..64 {
            state[i] = veorq_u64(state[i], xy[i]);
            vst1q_u64(next.0.as_mut_ptr().add(i * 2), state[i]);
        }
    }
}

#[target_feature(enable = "neon")]
unsafe fn load(block: &Block) -> [uint64x2_t; 64] {
    let mut state = [core::mem::MaybeUninit::<uint64x2_t>::uninit(); 64];
    // SAFETY: `block` is 1024 bytes, and every lane is written before the
    // array is read as initialized.
    unsafe {
        for (i, lane) in state.iter_mut().enumerate() {
            lane.write(vld1q_u64(block.0.as_ptr().add(i * 2)));
        }
        core::mem::transmute(state)
    }
}

#[target_feature(enable = "neon")]
fn blamka(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
    let z = vmull_u32(vmovn_u64(x), vmovn_u64(y));
    vaddq_u64(vaddq_u64(x, y), vaddq_u64(z, z))
}

#[target_feature(enable = "neon")]
fn rotr32(x: uint64x2_t) -> uint64x2_t {
    vreinterpretq_u64_u32(vrev64q_u32(vreinterpretq_u32_u64(x)))
}

#[target_feature(enable = "neon")]
fn rotr24(x: uint64x2_t) -> uint64x2_t {
    const TABLE: [u8; 16] = [3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10];
    // SAFETY: `TABLE` is 16 bytes.
    let table = unsafe { vld1q_u8(TABLE.as_ptr()) };
    vreinterpretq_u64_u8(vqtbl1q_u8(vreinterpretq_u8_u64(x), table))
}

#[target_feature(enable = "neon")]
fn rotr16(x: uint64x2_t) -> uint64x2_t {
    const TABLE: [u8; 16] = [2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9];
    // SAFETY: `TABLE` is 16 bytes.
    let table = unsafe { vld1q_u8(TABLE.as_ptr()) };
    vreinterpretq_u64_u8(vqtbl1q_u8(vreinterpretq_u8_u64(x), table))
}

#[target_feature(enable = "neon")]
fn rotr63(x: uint64x2_t) -> uint64x2_t {
    veorq_u64(vshrq_n_u64::<63>(x), vaddq_u64(x, x))
}

#[target_feature(enable = "neon")]
fn g1(
    a0: &mut uint64x2_t,
    b0: &mut uint64x2_t,
    c0: &mut uint64x2_t,
    d0: &mut uint64x2_t,
    a1: &mut uint64x2_t,
    b1: &mut uint64x2_t,
    c1: &mut uint64x2_t,
    d1: &mut uint64x2_t,
) {
    *a0 = blamka(*a0, *b0);
    *a1 = blamka(*a1, *b1);
    *d0 = rotr32(veorq_u64(*d0, *a0));
    *d1 = rotr32(veorq_u64(*d1, *a1));
    *c0 = blamka(*c0, *d0);
    *c1 = blamka(*c1, *d1);
    *b0 = rotr24(veorq_u64(*b0, *c0));
    *b1 = rotr24(veorq_u64(*b1, *c1));
}

#[target_feature(enable = "neon")]
fn g2(
    a0: &mut uint64x2_t,
    b0: &mut uint64x2_t,
    c0: &mut uint64x2_t,
    d0: &mut uint64x2_t,
    a1: &mut uint64x2_t,
    b1: &mut uint64x2_t,
    c1: &mut uint64x2_t,
    d1: &mut uint64x2_t,
) {
    *a0 = blamka(*a0, *b0);
    *a1 = blamka(*a1, *b1);
    *d0 = rotr16(veorq_u64(*d0, *a0));
    *d1 = rotr16(veorq_u64(*d1, *a1));
    *c0 = blamka(*c0, *d0);
    *c1 = blamka(*c1, *d1);
    *b0 = rotr63(veorq_u64(*b0, *c0));
    *b1 = rotr63(veorq_u64(*b1, *c1));
}

/// `vext` by 8 bytes, the NEON form of the reference's SSSE3 `alignr`.
#[target_feature(enable = "neon")]
fn diagonalize(
    b0: &mut uint64x2_t,
    b1: &mut uint64x2_t,
    c0: &mut uint64x2_t,
    c1: &mut uint64x2_t,
    d0: &mut uint64x2_t,
    d1: &mut uint64x2_t,
) {
    let t0 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*b0),
        vreinterpretq_u8_u64(*b1),
    ));
    let t1 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*b1),
        vreinterpretq_u8_u64(*b0),
    ));
    *b0 = t0;
    *b1 = t1;
    core::mem::swap(c0, c1);
    let t0 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*d0),
        vreinterpretq_u8_u64(*d1),
    ));
    let t1 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*d1),
        vreinterpretq_u8_u64(*d0),
    ));
    *d0 = t1;
    *d1 = t0;
}

#[target_feature(enable = "neon")]
fn undiagonalize(
    b0: &mut uint64x2_t,
    b1: &mut uint64x2_t,
    c0: &mut uint64x2_t,
    c1: &mut uint64x2_t,
    d0: &mut uint64x2_t,
    d1: &mut uint64x2_t,
) {
    let t0 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*b1),
        vreinterpretq_u8_u64(*b0),
    ));
    let t1 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*b0),
        vreinterpretq_u8_u64(*b1),
    ));
    *b0 = t0;
    *b1 = t1;
    core::mem::swap(c0, c1);
    let t0 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*d1),
        vreinterpretq_u8_u64(*d0),
    ));
    let t1 = vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(*d0),
        vreinterpretq_u8_u64(*d1),
    ));
    *d0 = t1;
    *d1 = t0;
}

/// One `BLAKE2_ROUND`. The indexes are `(A0, A1, B0, B1, C0, C1, D0, D1)`.
#[target_feature(enable = "neon")]
fn round(
    state: &mut [uint64x2_t; 64],
    a0i: usize,
    a1i: usize,
    b0i: usize,
    b1i: usize,
    c0i: usize,
    c1i: usize,
    d0i: usize,
    d1i: usize,
) {
    let (mut a0, mut a1, mut b0, mut b1, mut c0, mut c1, mut d0, mut d1) = (
        state[a0i], state[a1i], state[b0i], state[b1i], state[c0i], state[c1i], state[d0i],
        state[d1i],
    );
    g1(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    g2(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    diagonalize(&mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1);
    g1(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    g2(
        &mut a0, &mut b0, &mut c0, &mut d0, &mut a1, &mut b1, &mut c1, &mut d1,
    );
    undiagonalize(&mut b0, &mut b1, &mut c0, &mut c1, &mut d0, &mut d1);
    state[a0i] = a0;
    state[a1i] = a1;
    state[b0i] = b0;
    state[b1i] = b1;
    state[c0i] = c0;
    state[c1i] = c1;
    state[d0i] = d0;
    state[d1i] = d1;
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::argon2::compress as compress_scalar;

    #[test]
    fn neon_matches_scalar() {
        let mut prev = Block::zero();
        let mut reference = Block::zero();
        let mut next = Block::zero();
        for seed in [0x9E37_79B9_7F4A_7C15, 1] {
            for i in 0..128 {
                prev.0[i] = (i as u64).wrapping_mul(seed);
                reference.0[i] = (i as u64).wrapping_mul(seed ^ 0x1234_5678_9ABC_DEF0) ^ 0x00FF;
                next.0[i] = 0xFFFF_0000_FFFF_0000 ^ seed.wrapping_add(i as u64);
            }
            for with_xor in [false, true] {
                let mut scalar = next;
                let mut wide = next;
                compress_scalar(&mut scalar, &prev, &reference, with_xor);
                // SAFETY: aarch64 requires NEON, and the blocks are 1024 bytes.
                unsafe { compress_neon(&mut wide, &prev, &reference, with_xor) };
                assert_eq!(scalar.0, wide.0, "seed={seed:#x} with_xor={with_xor}");
            }
        }
    }

    // Valgrind on aarch64 runs NEON. `admin/ct-qemu` traces this permutation
    // where a host's valgrind cannot execute the binary. The loads and stores
    // cover the whole block, whichever words it holds.
    #[test]
    #[ignore = "admin/ct-qemu runs it under qemu"]
    fn ct_qemu_argon2() {
        use crate::low::aarch64::ct_qemu;

        let seed = ct_qemu::seed();
        let mut prev = Block::zero();
        let mut reference = Block::zero();
        let mut next = Block::zero();
        for i in 0..128 {
            prev.0[i] = seed.wrapping_mul(i as u64 + 1);
            reference.0[i] = seed.rotate_left(17).wrapping_mul(i as u64 + 3);
            next.0[i] = seed.wrapping_add(i as u64);
        }
        let word = ct_qemu::traced(|| {
            let mut wide = next;
            // SAFETY: aarch64 requires NEON, and the blocks are 1024 bytes.
            unsafe { compress_neon(&mut wide, &prev, &reference, true) };
            wide.0[0]
        });
        core::hint::black_box(word);
    }
}
