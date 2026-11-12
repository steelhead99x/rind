// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Argon2's compression function on NEON.
//!
//! The permutation is the NEON `fill_block` libsodium ships in
//! `blamka-round-neon.h` and `argon2-fill-block-neon.c`, a port of the Argon2
//! reference implementation's SSSE3 fill (copyright 2015 Daniel Dinu, Dmitry
//! Khovratovich, Jean-Philippe Aumasson, and Samuel Neves; CC0-1.0). The lane
//! shuffles are that code's, so a block it returns matches the scalar one.
//!
//! Four changes from that code, none of which moves a lane:
//!
//! - BlaMka narrows both halves of a pair with one `uzp1`, where the reference
//!   narrows each half alone. The SHA3 build then accumulates the product into
//!   each input with `umlal` and `umlal2`; the plain NEON build doubles a
//!   `umull`, which measured faster on a Cortex-A76 (no SHA3) and slower on an
//!   Apple M1 Pro.
//! - The column rounds read `prev ^ reference` straight from the blocks and the
//!   row rounds XOR and store `next` as they finish, so the 1 KiB state is not
//!   loaded or stored in passes of its own.
//! - With SHA3, `xar` does each round's XOR and rotation in one instruction.
//! - Each pass runs two of its eight rounds at once, step by step. One round
//!   is a single dependency chain two vectors wide: on a Cortex-A76 the
//!   one-round fill spent about two thirds of its cycles stalled in the back
//!   end, and two rounds at once took a third fewer cycles per block.
//!
//! aarch64 requires NEON. [`crate::low::cpu::check`] refuses a CPU without it,
//! naming `neon`, before a public call reaches here. This function does not
//! run the portable permutation in its place.

use core::arch::aarch64::*;

use super::cpu::HaveSha3;
use crate::low::argon2::Block;

/// The permutation for this CPU. Chosen once per derivation.
#[derive(Clone, Copy)]
pub(crate) enum Fill {
    Sha3,
    Neon,
}

impl Fill {
    /// SHA3's `xar`, then plain NEON. A CPU without SHA3 does not run it.
    pub(crate) fn select() -> Self {
        if HaveSha3::check().is_some() {
            Self::Sha3
        } else {
            Self::Neon
        }
    }
}

/// `G(prev, reference)` with a permutation [`Fill::select`] already chose.
pub(crate) fn compress(
    fill: Fill,
    next: &mut Block,
    prev: &Block,
    reference: &Block,
    with_xor: bool,
) {
    match fill {
        // SAFETY: `Fill::Sha3` is proof of SHA3, aarch64 requires NEON, and
        // the blocks are 1024 bytes each, which the loads and stores stay inside.
        Fill::Sha3 => unsafe { sha3::compress(next, prev, reference, with_xor) },
        // SAFETY: this backend requires NEON, and the blocks are 1024 bytes.
        Fill::Neon => unsafe { neon::compress(next, prev, reference, with_xor) },
    }
}

/// `x + y + 2 * (x mod 2^32) * (y mod 2^32)` for two pairs of lanes at once,
/// with `umull` and adds. The plain NEON fill's form: on a Cortex-A76 the fill
/// took 4% to 5% longer with [`blamka2_umlal`].
#[target_feature(enable = "neon")]
fn blamka2_umull(
    x0: uint64x2_t,
    x1: uint64x2_t,
    y0: uint64x2_t,
    y1: uint64x2_t,
) -> (uint64x2_t, uint64x2_t) {
    // The low words of `x0` then `x1`, and the same for `y`.
    let x = vuzp1q_u32(vreinterpretq_u32_u64(x0), vreinterpretq_u32_u64(x1));
    let y = vuzp1q_u32(vreinterpretq_u32_u64(y0), vreinterpretq_u32_u64(y1));
    let z0 = vmull_u32(vget_low_u32(x), vget_low_u32(y));
    let z1 = vmull_high_u32(x, y);
    (
        vaddq_u64(vaddq_u64(x0, y0), vaddq_u64(z0, z0)),
        vaddq_u64(vaddq_u64(x1, y1), vaddq_u64(z1, z1)),
    )
}

/// As [`blamka2_umull`], with `umlal`: the SHA3 fill's form. On an Apple M1 Pro
/// it took about 13% less time per block.
#[target_feature(enable = "neon")]
fn blamka2_umlal(
    x0: uint64x2_t,
    x1: uint64x2_t,
    y0: uint64x2_t,
    y1: uint64x2_t,
) -> (uint64x2_t, uint64x2_t) {
    // The low words of `x0` then `x1`, and the same for `y`.
    let x = vuzp1q_u32(vreinterpretq_u32_u64(x0), vreinterpretq_u32_u64(x1));
    let y = vuzp1q_u32(vreinterpretq_u32_u64(y0), vreinterpretq_u32_u64(y1));
    // `(x + xy) + (y + xy)`: one `umlal` into each input and an add, so the
    // product is two instructions deep rather than `umull`, a doubling and two
    // adds. Written in assembly because LLVM folds two `vmlal`s of one product
    // back into `umull` and adds.
    // One block, not four: LLVM's inliner charges each `asm!` as a call, and
    // four of them per BlaMka left the round out of line.
    let (mut a0, mut b0, mut a1, mut b1) = (x0, y0, x1, y1);
    // SAFETY: `umlal` and `umlal2` only read and write the named vector
    // registers; aarch64 requires NEON. Fixed latency, no data-dependent timing.
    unsafe {
        core::arch::asm!(
            "umlal {a0:v}.2d, {x:v}.2s, {y:v}.2s",
            "umlal {b0:v}.2d, {x:v}.2s, {y:v}.2s",
            "umlal2 {a1:v}.2d, {x:v}.4s, {y:v}.4s",
            "umlal2 {b1:v}.2d, {x:v}.4s, {y:v}.4s",
            a0 = inout(vreg) a0, b0 = inout(vreg) b0,
            a1 = inout(vreg) a1, b1 = inout(vreg) b1,
            x = in(vreg) x, y = in(vreg) y,
            options(pure, nomem, nostack, preserves_flags)
        );
    }
    (vaddq_u64(a0, b0), vaddq_u64(a1, b1))
}

/// `vext` by 8 bytes, the NEON form of the reference's SSSE3 `alignr`.
#[target_feature(enable = "neon")]
fn ext(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
    vreinterpretq_u64_u8(vextq_u8::<8>(
        vreinterpretq_u8_u64(x),
        vreinterpretq_u8_u64(y),
    ))
}

/// The `(B0, B1, C0, C1, D0, D1)` shuffle between a round's halves.
#[target_feature(enable = "neon")]
fn diagonalize(v: &mut [uint64x2_t; 8]) {
    let [_, _, b0, b1, c0, c1, d0, d1] = *v;
    v[2] = ext(b0, b1);
    v[3] = ext(b1, b0);
    v[4] = c1;
    v[5] = c0;
    v[6] = ext(d1, d0);
    v[7] = ext(d0, d1);
}

#[target_feature(enable = "neon")]
fn undiagonalize(v: &mut [uint64x2_t; 8]) {
    let [_, _, b0, b1, c0, c1, d0, d1] = *v;
    v[2] = ext(b1, b0);
    v[3] = ext(b0, b1);
    v[4] = c1;
    v[5] = c0;
    v[6] = ext(d0, d1);
    v[7] = ext(d1, d0);
}

/// Two `BLAKE2_ROUND`s, each on `(A0, A1, B0, B1, C0, C1, D0, D1)`, step by
/// step, with the fill's `g1` and `g2`. A macro, not a function: LLVM would
/// leave a function called from both passes out of line, and pass the 16
/// vectors through the stack.
macro_rules! round {
    ($v:ident) => {
        g1(&mut $v);
        g2(&mut $v);
        diagonalize(&mut $v[0]);
        diagonalize(&mut $v[1]);
        g1(&mut $v);
        g2(&mut $v);
        undiagonalize(&mut $v[0]);
        undiagonalize(&mut $v[1]);
    };
}

/// The fill, built once per instruction set. The caller's module supplies
/// `xor_rotr32`, `xor_rotr24`, `xor_rotr16` and `xor_rotr63`, each
/// `(x ^ y).rotate_right(n)` on both lanes, and `blamka2`.
macro_rules! fill {
    ($features:literal) => {
        use core::arch::aarch64::*;
        use core::mem::MaybeUninit;

        use super::{diagonalize, undiagonalize};
        use crate::low::argon2::Block;

        /// # Safety
        /// The CPU must have every feature this function enables.
        #[target_feature(enable = $features)]
        pub(super) unsafe fn compress(
            next: &mut Block,
            prev: &Block,
            reference: &Block,
            with_xor: bool,
        ) {
            let mut state = [MaybeUninit::<uint64x2_t>::uninit(); 64];
            let mut xy = [MaybeUninit::<uint64x2_t>::uninit(); 64];
            // SAFETY: each block is 1024 bytes, sixty-four 16-byte lanes, and
            // every index below is under 64. The column rounds write each
            // `state` and `xy` lane before the row rounds read it, and they
            // read `next` before the row rounds overwrite it.
            unsafe {
                // Two independent rounds at a time: one round's G steps form a
                // single dependency chain, which a narrow core waits on.
                for col in (0..8).step_by(2) {
                    let mut v = [[vdupq_n_u64(0); 8]; 2];
                    for (j, half) in v.iter_mut().enumerate() {
                        for (k, lane) in half.iter_mut().enumerate() {
                            let i = 8 * (col + j) + k;
                            let r = veorq_u64(
                                vld1q_u64(prev.0.as_ptr().add(2 * i)),
                                vld1q_u64(reference.0.as_ptr().add(2 * i)),
                            );
                            xy[i].write(if with_xor {
                                veorq_u64(r, vld1q_u64(next.0.as_ptr().add(2 * i)))
                            } else {
                                r
                            });
                            *lane = r;
                        }
                    }
                    round!(v);
                    for (j, half) in v.into_iter().enumerate() {
                        for (k, lane) in half.into_iter().enumerate() {
                            state[8 * (col + j) + k].write(lane);
                        }
                    }
                }
                for row in (0..8).step_by(2) {
                    let mut v = [[vdupq_n_u64(0); 8]; 2];
                    for (j, half) in v.iter_mut().enumerate() {
                        for (k, lane) in half.iter_mut().enumerate() {
                            *lane = state[row + j + 8 * k].assume_init();
                        }
                    }
                    round!(v);
                    for (j, half) in v.into_iter().enumerate() {
                        for (k, lane) in half.into_iter().enumerate() {
                            let i = row + j + 8 * k;
                            let out = veorq_u64(lane, xy[i].assume_init());
                            vst1q_u64(next.0.as_mut_ptr().add(2 * i), out);
                        }
                    }
                }
            }
        }

        #[target_feature(enable = $features)]
        fn g1(v: &mut [[uint64x2_t; 8]; 2]) {
            let [
                [a0, a1, b0, b1, c0, c1, d0, d1],
                [e0, e1, f0, f1, g0, g1, h0, h1],
            ] = *v;
            let (a0, a1) = blamka2(a0, a1, b0, b1);
            let (e0, e1) = blamka2(e0, e1, f0, f1);
            let d0 = xor_rotr32(d0, a0);
            let h0 = xor_rotr32(h0, e0);
            let d1 = xor_rotr32(d1, a1);
            let h1 = xor_rotr32(h1, e1);
            let (c0, c1) = blamka2(c0, c1, d0, d1);
            let (g0, g1) = blamka2(g0, g1, h0, h1);
            let b0 = xor_rotr24(b0, c0);
            let f0 = xor_rotr24(f0, g0);
            let b1 = xor_rotr24(b1, c1);
            let f1 = xor_rotr24(f1, g1);
            *v = [
                [a0, a1, b0, b1, c0, c1, d0, d1],
                [e0, e1, f0, f1, g0, g1, h0, h1],
            ];
        }

        #[target_feature(enable = $features)]
        fn g2(v: &mut [[uint64x2_t; 8]; 2]) {
            let [
                [a0, a1, b0, b1, c0, c1, d0, d1],
                [e0, e1, f0, f1, g0, g1, h0, h1],
            ] = *v;
            let (a0, a1) = blamka2(a0, a1, b0, b1);
            let (e0, e1) = blamka2(e0, e1, f0, f1);
            let d0 = xor_rotr16(d0, a0);
            let h0 = xor_rotr16(h0, e0);
            let d1 = xor_rotr16(d1, a1);
            let h1 = xor_rotr16(h1, e1);
            let (c0, c1) = blamka2(c0, c1, d0, d1);
            let (g0, g1) = blamka2(g0, g1, h0, h1);
            let b0 = xor_rotr63(b0, c0);
            let f0 = xor_rotr63(f0, g0);
            let b1 = xor_rotr63(b1, c1);
            let f1 = xor_rotr63(f1, g1);
            *v = [
                [a0, a1, b0, b1, c0, c1, d0, d1],
                [e0, e1, f0, f1, g0, g1, h0, h1],
            ];
        }
    };
}

/// Plain NEON: the rotations by 32, 24 and 16 are lane shuffles.
mod neon {
    use super::blamka2_umull as blamka2;

    fill!("neon");

    #[target_feature(enable = "neon")]
    fn xor_rotr32(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        vreinterpretq_u64_u32(vrev64q_u32(vreinterpretq_u32_u64(veorq_u64(x, y))))
    }

    #[target_feature(enable = "neon")]
    fn xor_rotr24(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        const TABLE: [u8; 16] = [3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10];
        // SAFETY: `TABLE` is 16 bytes.
        let table = unsafe { vld1q_u8(TABLE.as_ptr()) };
        vreinterpretq_u64_u8(vqtbl1q_u8(vreinterpretq_u8_u64(veorq_u64(x, y)), table))
    }

    #[target_feature(enable = "neon")]
    fn xor_rotr16(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        const TABLE: [u8; 16] = [2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9];
        // SAFETY: `TABLE` is 16 bytes.
        let table = unsafe { vld1q_u8(TABLE.as_ptr()) };
        vreinterpretq_u64_u8(vqtbl1q_u8(vreinterpretq_u8_u64(veorq_u64(x, y)), table))
    }

    #[target_feature(enable = "neon")]
    fn xor_rotr63(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        let z = veorq_u64(x, y);
        veorq_u64(vshrq_n_u64::<63>(z), vaddq_u64(z, z))
    }
}

/// SHA3's `xar`: one instruction for each XOR and rotation.
mod sha3 {
    use super::blamka2_umlal as blamka2;

    fill!("neon,sha3");

    #[target_feature(enable = "neon,sha3")]
    fn xor_rotr32(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        vxarq_u64::<32>(x, y)
    }

    #[target_feature(enable = "neon,sha3")]
    fn xor_rotr24(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        vxarq_u64::<24>(x, y)
    }

    #[target_feature(enable = "neon,sha3")]
    fn xor_rotr16(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        vxarq_u64::<16>(x, y)
    }

    #[target_feature(enable = "neon,sha3")]
    fn xor_rotr63(x: uint64x2_t, y: uint64x2_t) -> uint64x2_t {
        vxarq_u64::<63>(x, y)
    }
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
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..64 {
            seed = seed
                .wrapping_mul(0x6C62_272E_07BB_0142)
                .wrapping_add(0x9E37);
            for i in 0..128 {
                prev.0[i] = (i as u64).wrapping_mul(seed);
                reference.0[i] = (i as u64).wrapping_mul(seed ^ 0x1234_5678_9ABC_DEF0) ^ 0x00FF;
                next.0[i] = 0xFFFF_0000_FFFF_0000 ^ seed.wrapping_add(i as u64);
            }
            for with_xor in [false, true] {
                let mut scalar = next;
                compress_scalar(&mut scalar, &prev, &reference, with_xor);
                let mut wide = next;
                // SAFETY: aarch64 requires NEON, and the blocks are 1024 bytes.
                unsafe { neon::compress(&mut wide, &prev, &reference, with_xor) };
                assert_eq!(scalar.0, wide.0, "neon seed={seed:#x} with_xor={with_xor}");
                if HaveSha3::check().is_some() {
                    let mut wide = next;
                    // SAFETY: checked for SHA3 just above; the blocks are 1024 bytes.
                    unsafe { sha3::compress(&mut wide, &prev, &reference, with_xor) };
                    assert_eq!(scalar.0, wide.0, "sha3 seed={seed:#x} with_xor={with_xor}");
                }
                let mut selected = next;
                compress(Fill::select(), &mut selected, &prev, &reference, with_xor);
                assert_eq!(
                    scalar.0, selected.0,
                    "selected seed={seed:#x} with_xor={with_xor}"
                );
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
            unsafe { neon::compress(&mut wide, &prev, &reference, true) };
            if HaveSha3::check().is_some() {
                // SAFETY: checked for SHA3 just above; the blocks are 1024 bytes.
                unsafe { sha3::compress(&mut wide, &prev, &reference, true) };
            }
            wide.0[0]
        });
        core::hint::black_box(word);
    }
}
