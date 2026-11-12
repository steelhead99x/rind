// Copyright (c) 2014, Google Inc.
// SPDX-License-Identifier: ISC
//
// Poly1305 with NEON: aws-lc's `crypto/poly1305/poly1305_arm.c` at commit
// 91c93a8eb860e51482a871a8772cb9b1b310baea, in Rust, around the assembly
// `admin/import-aws-lc` imports beside it. Both come from the public
// domain neon2 version in SUPERCOP by D. J. Bernstein and Peter Schwabe,
// which computes two interleaved Poly1305 lanes in 26-bit limbs.
//
// Neither is formally verified: their correctness rests on their use and
// testing in BoringSSL and aws-lc, and on rind's tests of them against
// HACL*'s verified Poly1305, Wycheproof, and aws-lc-rs.

use super::cpu::HaveNeon;

/// Two field elements in 26-bit limbs, interleaved: lane 0 in the even words
/// and lane 1 in the odd ones. The last two words only pad it to 16 bytes,
/// which the assembly's aligned loads need.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
struct Fe1305x2 {
    v: [u32; 12],
}

static ZERO: Fe1305x2 = Fe1305x2 { v: [0; 12] };

unsafe extern "C" {
    /// `r = x * y + c`, per lane, modulo 2^130 - 5.
    #[link_name = aws_lc_symbol!("openssl_poly1305_neon2_addmulmod")]
    fn openssl_poly1305_neon2_addmulmod(
        r: *mut Fe1305x2,
        x: *const Fe1305x2,
        y: *const Fe1305x2,
        c: *const Fe1305x2,
    );

    /// Absorbs 32-byte pairs of blocks while more than 32 bytes remain, and
    /// returns how many remain.
    #[link_name = aws_lc_symbol!("openssl_poly1305_neon2_blocks")]
    fn openssl_poly1305_neon2_blocks(
        h: *mut Fe1305x2,
        precomp: *const [Fe1305x2; 2],
        input: *const u8,
        len: usize,
    ) -> usize;
}

// As in `aesv8_armx`: ARM mode with NEON, then the target's `.fpu` again.
core::arch::global_asm!(
    ".text",
    ".fpu neon",
    ".code 32",
    include_str!("aws_lc/poly1305_arm_asm.s"),
    ".fpu vfpv3",
    openssl_poly1305_neon2_blocks = sym openssl_poly1305_neon2_blocks,
    openssl_poly1305_neon2_addmulmod = sym openssl_poly1305_neon2_addmulmod,
);

fn addmulmod(r: *mut Fe1305x2, x: *const Fe1305x2, y: *const Fe1305x2, c: &Fe1305x2) {
    // SAFETY: every argument points to a live, aligned `Fe1305x2`, which the
    // routine allows `r` to share with `x`. Only a `HaveNeon` token builds the
    // state they come from.
    unsafe { asm_call!(unsafe extern "C" openssl_poly1305_neon2_addmulmod(r, x, y, c)) }
}

fn freeze(r: &mut Fe1305x2) {
    let mut x0 = r.v[0];
    let mut x1 = r.v[2];
    let mut x2 = r.v[4];
    let mut x3 = r.v[6];
    let mut x4 = r.v[8];

    for _ in 0..3 {
        x1 = x1.wrapping_add(x0 >> 26);
        x0 &= 0x3ffffff;
        x2 = x2.wrapping_add(x1 >> 26);
        x1 &= 0x3ffffff;
        x3 = x3.wrapping_add(x2 >> 26);
        x2 &= 0x3ffffff;
        x4 = x4.wrapping_add(x3 >> 26);
        x3 &= 0x3ffffff;
        x0 = x0.wrapping_add(5u32.wrapping_mul(x4 >> 26));
        x4 &= 0x3ffffff;
    }

    let mut y0 = x0.wrapping_add(5);
    let mut y1 = x1.wrapping_add(y0 >> 26);
    y0 &= 0x3ffffff;
    let mut y2 = x2.wrapping_add(y1 >> 26);
    y1 &= 0x3ffffff;
    let mut y3 = x3.wrapping_add(y2 >> 26);
    y2 &= 0x3ffffff;
    let mut y4 = x4.wrapping_add(y3 >> 26);
    y3 &= 0x3ffffff;
    let swap = 0u32.wrapping_sub(y4 >> 26);
    y4 &= 0x3ffffff;

    y0 ^= x0;
    y1 ^= x1;
    y2 ^= x2;
    y3 ^= x3;
    y4 ^= x4;

    y0 &= swap;
    y1 &= swap;
    y2 &= swap;
    y3 &= swap;
    y4 &= swap;

    y0 ^= x0;
    y1 ^= x1;
    y2 ^= x2;
    y3 ^= x3;
    y4 ^= x4;

    r.v[0] = y0;
    r.v[2] = y1;
    r.v[4] = y2;
    r.v[6] = y3;
    r.v[8] = y4;
}

fn load32(t: &[u8]) -> u32 {
    u32::from_le_bytes([t[0], t[1], t[2], t[3]])
}

fn fe1305x2_tobytearray(r: &mut [u8; 16], x: &Fe1305x2) {
    let mut x0 = x.v[0];
    let mut x1 = x.v[2];
    let mut x2 = x.v[4];
    let mut x3 = x.v[6];
    let mut x4 = x.v[8];

    x1 = x1.wrapping_add(x0 >> 26);
    x0 &= 0x3ffffff;
    x2 = x2.wrapping_add(x1 >> 26);
    x1 &= 0x3ffffff;
    x3 = x3.wrapping_add(x2 >> 26);
    x2 &= 0x3ffffff;
    x4 = x4.wrapping_add(x3 >> 26);
    x3 &= 0x3ffffff;

    r[0..4].copy_from_slice(&x0.wrapping_add(x1 << 26).to_le_bytes());
    r[4..8].copy_from_slice(&(x1 >> 6).wrapping_add(x2 << 20).to_le_bytes());
    r[8..12].copy_from_slice(&(x2 >> 12).wrapping_add(x3 << 14).to_le_bytes());
    r[12..16].copy_from_slice(&(x3 >> 18).wrapping_add(x4 << 8).to_le_bytes());
}

/// Loads up to two blocks from `x`, at most 32 bytes, each with its final 1
/// bit; lane 1 is zero when `x` has 16 bytes or fewer.
fn fe1305x2_frombytearray(r: &mut Fe1305x2, x: &[u8]) {
    let (first, second) = x.split_at(x.len().min(16));
    load_lane(r, 0, first);
    if second.is_empty() {
        for i in [1, 3, 5, 7, 9] {
            r.v[i] = 0;
        }
    } else {
        load_lane(r, 1, second);
    }
}

/// Loads `block`, at most 16 bytes, and its final 1 bit into `lane`.
fn load_lane(r: &mut Fe1305x2, lane: usize, block: &[u8]) {
    let mut t = [0u8; 17];
    t[..block.len()].copy_from_slice(block);
    t[block.len()] = 1;

    r.v[lane] = 0x3ffffff & load32(&t[0..]);
    r.v[lane + 2] = 0x3ffffff & (load32(&t[3..]) >> 2);
    r.v[lane + 4] = 0x3ffffff & (load32(&t[6..]) >> 4);
    r.v[lane + 6] = 0x3ffffff & (load32(&t[9..]) >> 6);
    r.v[lane + 8] = load32(&t[13..]);
}

pub(crate) struct Poly1305Neon {
    r: Fe1305x2,
    h: Fe1305x2,
    c: Fe1305x2,
    /// r^2 and r^4, in both lanes.
    precomp: [Fe1305x2; 2],
    buf: [u8; 32],
    buf_used: usize,
    key: [u8; 16],
}

impl Poly1305Neon {
    pub(crate) fn new(key: &[u8; 32], _: HaveNeon) -> Self {
        let mut r = Fe1305x2 { v: [0; 12] };
        r.v[0] = 0x3ffffff & load32(&key[0..]);
        r.v[2] = 0x3ffff03 & (load32(&key[3..]) >> 2);
        r.v[4] = 0x3ffc0ff & (load32(&key[6..]) >> 4);
        r.v[6] = 0x3f03fff & (load32(&key[9..]) >> 6);
        r.v[8] = 0x00fffff & (load32(&key[12..]) >> 8);
        for i in [0, 2, 4, 6, 8] {
            r.v[i + 1] = r.v[i];
        }

        let mut st = Self {
            r,
            h: ZERO,
            c: ZERO,
            precomp: [ZERO; 2],
            buf: [0; 32],
            buf_used: 0,
            key: core::array::from_fn(|i| key[16 + i]),
        };
        let precomp = st.precomp.as_mut_ptr();
        addmulmod(precomp, &st.r, &st.r, &ZERO);
        // SAFETY: `precomp` has two elements.
        addmulmod(unsafe { precomp.add(1) }, precomp, precomp, &ZERO);
        st
    }

    pub(crate) fn add_bytes(&mut self, mut input: &[u8]) {
        if self.buf_used != 0 {
            let todo = (self.buf.len() - self.buf_used).min(input.len());
            let (head, rest) = input.split_at(todo);
            self.buf[self.buf_used..self.buf_used + todo].copy_from_slice(head);
            self.buf_used += todo;
            input = rest;

            if self.buf_used == self.buf.len() && !input.is_empty() {
                let h: *mut Fe1305x2 = &mut self.h;
                addmulmod(h, h, &self.precomp[0], &ZERO);
                fe1305x2_frombytearray(&mut self.c, &self.buf);
                for i in 0..10 {
                    self.h.v[i] = self.h.v[i].wrapping_add(self.c.v[i]);
                }
                self.buf_used = 0;
            }
        }

        while input.len() > 32 {
            let len = input.len().min(1 << 20);
            // SAFETY: `input` has `len` readable bytes, `self.h` is aligned,
            // and only a `HaveNeon` token builds `self`.
            let left = unsafe {
                asm_call!(unsafe extern "C" openssl_poly1305_neon2_blocks(&mut self.h, &self.precomp, input.as_ptr(), len))
            };
            input = &input[len - left..];
        }

        if !input.is_empty() {
            self.buf[..input.len()].copy_from_slice(input);
            self.buf_used = input.len();
        }
    }

    pub(crate) fn finish(mut self) -> [u8; 16] {
        let h: *mut Fe1305x2 = &mut self.h;
        addmulmod(h, h, &self.precomp[0], &ZERO);

        if self.buf_used > 16 {
            fe1305x2_frombytearray(&mut self.c, &self.buf[..self.buf_used]);
            for i in [1, 3, 5, 7, 9] {
                self.precomp[0].v[i] = self.r.v[i];
            }
            addmulmod(h, h, &self.precomp[0], &self.c);
        } else if self.buf_used > 0 {
            fe1305x2_frombytearray(&mut self.c, &self.buf[..self.buf_used]);
            self.r.v[1] = 1;
            for i in [3, 5, 7, 9] {
                self.r.v[i] = 0;
            }
            addmulmod(h, h, &self.r, &self.c);
        }

        for i in [0, 2, 4, 6, 8] {
            self.h.v[i] = self.h.v[i].wrapping_add(self.h.v[i + 1]);
        }
        freeze(&mut self.h);

        fe1305x2_frombytearray(&mut self.c, &self.key);
        self.c.v[8] ^= 1 << 24;

        for i in [0, 2, 4, 6, 8] {
            self.h.v[i] = self.h.v[i].wrapping_add(self.c.v[i]);
        }
        let mut mac = [0u8; 16];
        fe1305x2_tobytearray(&mut mac, &self.h);
        mac
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    /// Lane 0 of `freeze`'s result, from lane 0's 26-bit limbs.
    fn frozen(limbs: [u32; 5]) -> [u32; 5] {
        let mut fe = Fe1305x2 { v: [0; 12] };
        for (i, limb) in limbs.into_iter().enumerate() {
            fe.v[2 * i] = limb;
        }
        freeze(&mut fe);
        [fe.v[0], fe.v[2], fe.v[4], fe.v[6], fe.v[8]]
    }

    // Random inputs leave `h` in `[p, 2^130)` with probability about 2^-128,
    // so only these reach the subtraction of `p`.
    #[test]
    fn freeze_reduces_below_p() {
        const MAX: u32 = 0x3ffffff;
        // p is 0, and 2^130 - 1 is 4.
        assert_eq!(frozen([MAX - 4, MAX, MAX, MAX, MAX]), [0; 5]);
        assert_eq!(frozen([MAX, MAX, MAX, MAX, MAX]), [4, 0, 0, 0, 0]);
        // p - 1 stays.
        assert_eq!(
            frozen([MAX - 5, MAX, MAX, MAX, MAX]),
            [MAX - 5, MAX, MAX, MAX, MAX]
        );
        // Carries out of each limb, and 2^130 as 5.
        assert_eq!(frozen([MAX + 1, MAX, MAX, MAX, 0]), [0, 0, 0, 0, 1]);
        assert_eq!(frozen([0, 0, 0, 0, MAX + 1]), [5, 0, 0, 0, 0]);
    }
}
