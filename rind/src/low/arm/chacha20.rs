// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20 on armv7. The state words are RFC 8439 §2.3: the constants, the
//! key, the block counter, and the nonce, each little-endian. QUIC header
//! protection's lone block and HChaCha20 run HACL*'s rounds in
//! `generic::chacha20`. The keystream runs the rounds below, which are the
//! same quarter-rounds laid out for an in-order core.
//!
//! 32-bit Arm NEON intrinsics are unstable on the toolchain this crate builds
//! with, so this backend does not ship a NEON keystream.
//!
//! # The schedule
//!
//! A Cortex-A7 issues one register-register instruction or one load or store
//! a cycle, and an instruction that shifts an operand needs that operand a
//! cycle early. `add a, a, b, ror #25` straight after the `eor` that made `b`
//! waits a cycle, and a quarter-round is eight such instructions each fed by
//! the last, so one alone stalls three times. Two quarter-rounds interleaved
//! never stall. ChaCha20 has sixteen words and the core fourteen registers,
//! so some words live in memory, and every load and store is a cycle too.
//!
//! Written plainly, the compiler orders one quarter-round after another,
//! which stalls, lets the last steps of one drift past the first of the
//! next, which keeps more words alive than there are registers, and reloads
//! what it then spills: about 104 instructions and 20 stalls a double round.
//! [`xor_blocks`] fixes all three by hand, the way `chacha-armv4` does:
//!
//! - Thirteen words stay in registers. The third row is in memory but for
//!   the two words the running pair of quarter-rounds uses, and `x13` and
//!   `x15` share a register. [`Slots`] reads and writes them volatile, so
//!   the compiler moves a word exactly where the schedule says and keeps
//!   the fourteenth register for the trip count.
//! - The second and fourth rows are held rotated, so a rotation is always
//!   the shifted operand of the next instruction and never one of its own.
//! - [`steps!`] makes each step a basic block. The compiler orders
//!   instructions within a block only, so the blocks' order is the
//!   instructions' order: two quarter-rounds, step by step.
//!
//! That is 76 instructions a double round and no stalls. On a Raspberry Pi
//! 2B it took 0.75 of the time of the plain rounds at 16 KB.

use core::ptr::{read_volatile, write_volatile};

const CONSTANTS: [u32; 4] = [0x61707865, 0x3320646e, 0x79622d32, 0x6b206574];

fn chacha20_init(ctx: &mut [u32; 16], key: &[u8; 32], nonce: &[u8; 12], counter: u32) {
    ctx[0..4].copy_from_slice(&CONSTANTS);
    for (i, word) in key.as_chunks::<4>().0.iter().enumerate() {
        ctx[4 + i] = u32::from_le_bytes(*word);
    }
    ctx[12] = counter;
    for (i, word) in nonce.as_chunks::<4>().0.iter().enumerate() {
        ctx[13 + i] = u32::from_le_bytes(*word);
    }
}

pub(crate) struct ChaCha20 {
    ctx: [u32; 16],
}

impl ChaCha20 {
    /// `nonce` is the little-endian block counter followed by the 96-bit nonce.
    pub(crate) fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        let mut ctx = [0u32; 16];
        // `nonce` is 16 bytes: a 32-bit counter, then 12 nonce bytes.
        let counter = u32::from_le_bytes(*nonce.first_chunk::<4>().unwrap());
        let n: &[u8; 12] = nonce.last_chunk::<12>().unwrap();
        chacha20_init(&mut ctx, key, n, counter);
        Self { ctx }
    }

    /// XORs the keystream into `buffer`, starting at the current block, then
    /// moves the counter past every block it touched.
    pub(crate) fn cipher(&mut self, buffer: &mut [u8]) {
        let (blocks, tail) = buffer.as_chunks_mut::<64>();
        xor_blocks(&mut self.ctx, blocks);
        if !tail.is_empty() {
            // A partial block goes through the same rounds in a block of its
            // own, so there is one copy of them.
            let mut last = [[0u8; 64]];
            last[0][..tail.len()].copy_from_slice(tail);
            xor_blocks(&mut self.ctx, &mut last);
            tail.copy_from_slice(&last[0][..tail.len()]);
        }
    }
}

/// The words [`xor_blocks`] keeps in memory: the third row, `x13` and `x15`,
/// and the trip count. Every access is volatile, so each is one load or one
/// store where the schedule puts it, and the compiler can neither keep a
/// word in a register across them nor move it to a slot of its own.
struct Slots([u32; 7]);

/// The third row, `x8` to `x11`, at slots 0 to 3.
const C: usize = 0;
/// `x13`, while `x15` has the register.
const X13: usize = 4;
/// `x15`, while `x13` has the register.
const X15: usize = 5;
/// How many passes of the rounds are left.
const TRIPS: usize = 6;

impl Slots {
    #[inline(always)]
    fn get(&self, i: usize) -> u32 {
        // SAFETY: a reference is valid for a read of its type.
        unsafe { read_volatile(&self.0[i]) }
    }

    #[inline(always)]
    fn set(&mut self, i: usize, v: u32) {
        // SAFETY: a mutable reference is valid for a write of its type.
        unsafe { write_volatile(&mut self.0[i], v) }
    }
}

/// Runs each `{ step }` in turn, with every step a basic block of its own.
///
/// The compiler picks the order of the instructions in a basic block, and
/// for two independent chains it picks one chain then the other. It cannot
/// move an instruction to another block, so a block per step leaves it only
/// the order within a step, which does not matter.
///
/// A step becomes a block by having a second way in. `$trips` is a count of
/// at most 16 on every path that runs. Were it more, the dispatch below would
/// jump to the step whose number it is, as Duff's device enters a loop
/// part-way: no path takes that jump, and the compiler cannot tell, because
/// `$opaque` is a volatile load. The steps that run pay one compare and one
/// branch a pass for it.
///
/// Each step has two such entries. With one, the compiler's partial
/// redundancy elimination computes a rotation on that entry's edge so that
/// the step need not, which turns a shifted operand into a `ror` of its own.
/// It does that for a single missing predecessor only.
macro_rules! steps {
    ($trips:expr, $opaque:expr; {$($first:tt)*} $($n:literal $label:lifetime {$($step:tt)*})*) => {
        steps!(@nest {
            if $trips > 16 {
                $( if $opaque == $n { break $label; } )*
                $( if $opaque == $n + 64 { break $label; } )*
            }
            $($first)*
        }; $($label {$($step)*})*)
    };
    (@nest {$($done:tt)*};) => { $($done)* };
    (@nest {$($done:tt)*}; $label:lifetime {$($step:tt)*} $($rest:tt)*) => {
        steps!(@nest { $label: { $($done)* } $($step)* }; $($rest)*)
    };
}

/// `a += b; d ^= a` for two quarter-rounds, `(a, b, c, d)` and
/// `(e, f, g, h)`, with `b` held rotated right by `$rb` and `d` by `$rd`. `d`
/// comes out rotated right by the rotation RFC 8439 applies next, 16 or 8.
/// Between quarter-rounds `b` is rotated right by 7 and `d` by 8, the
/// rotations RFC 8439 ends on, left undone.
macro_rules! add_xor_ad {
    ($rb:literal, $rd:literal; $a:ident, $b:ident, $d:ident; $e:ident, $f:ident, $h:ident) => {
        $a = $a.wrapping_add($b.rotate_left($rb));
        $d = $d.rotate_left($rd) ^ $a;
        $e = $e.wrapping_add($f.rotate_left($rb));
        $h = $h.rotate_left($rd) ^ $e;
    };
}

/// `c += d; b ^= c` for the same two quarter-rounds. `b` comes out rotated
/// right by the rotation RFC 8439 applies next, 12 or 7.
macro_rules! add_xor_cb {
    ($rb:literal, $rd:literal; $b:ident, $c:ident, $d:ident; $f:ident, $g:ident, $h:ident) => {
        $c = $c.wrapping_add($d.rotate_left($rd));
        $b = $b.rotate_left($rb) ^ $c;
        $g = $g.wrapping_add($h.rotate_left($rd));
        $f = $f.rotate_left($rb) ^ $g;
    };
}

/// XORs one keystream block into each of `blocks`, from the state `input`,
/// and leaves `input`'s counter past them.
#[inline(never)]
fn xor_blocks(input: &mut [u32; 16], blocks: &mut [[u8; 64]]) {
    // The second row rotated right by 7 and the nonce by 8, as the rounds
    // hold them.
    let row_b = [
        input[4].rotate_right(7),
        input[5].rotate_right(7),
        input[6].rotate_right(7),
        input[7].rotate_right(7),
    ];
    let nonce = [
        input[13].rotate_right(8),
        input[14].rotate_right(8),
        input[15].rotate_right(8),
    ];
    for block in blocks.iter_mut() {
        let mut slots = Slots([0; 7]);
        let [mut x0, mut x1, mut x2, mut x3] = [input[0], input[1], input[2], input[3]];
        let [mut x4, mut x5, mut x6, mut x7] = row_b;
        // `p` and `q` are the two words of the third row in registers: `x8`
        // and `x9` here, and at the end of every pass.
        let mut p = input[8];
        let mut q = input[9];
        slots.set(C + 2, input[10]);
        slots.set(C + 3, input[11]);
        let mut x12 = input[12].rotate_right(8);
        // `t` is `x13` or `x15`: `x13` here, and at the end of every pass.
        let mut t = nonce[0];
        let mut x14 = nonce[1];
        slots.set(X15, nonce[2]);
        // Five passes of two double rounds.
        slots.set(TRIPS, 5);
        let mut trips = slots.get(TRIPS);
        loop {
            steps!(trips, slots.get(TRIPS);
                // The column round: (x0, x4, x8, x12) with (x1, x5, x9, x13),
                // then (x2, x6, x10, x14) with (x3, x7, x11, x15).
                { add_xor_ad!(7, 8; x0, x4, x12; x1, x5, t); }
                17 'a1 { add_xor_cb!(7, 16; x4, p, x12; x5, q, t); }
                18 'a2 { add_xor_ad!(12, 16; x0, x4, x12; x1, x5, t); }
                19 'a3 { add_xor_cb!(12, 8; x4, p, x12; x5, q, t); }
                20 'a4 {
                    slots.set(C, p);
                    slots.set(C + 1, q);
                    slots.set(X13, t);
                    p = slots.get(C + 2);
                    q = slots.get(C + 3);
                    t = slots.get(X15);
                }
                21 'a5 { add_xor_ad!(7, 8; x2, x6, x14; x3, x7, t); }
                22 'a6 { add_xor_cb!(7, 16; x6, p, x14; x7, q, t); }
                23 'a7 { add_xor_ad!(12, 16; x2, x6, x14; x3, x7, t); }
                24 'a8 { add_xor_cb!(12, 8; x6, p, x14; x7, q, t); }
                // The diagonal round: (x1, x6, x11, x12) with
                // (x0, x5, x10, x15), which use the words in registers, then
                // (x3, x4, x9, x14) with (x2, x7, x8, x13).
                25 'a9 { add_xor_ad!(7, 8; x1, x6, x12; x0, x5, t); }
                26 'a10 { add_xor_cb!(7, 16; x6, q, x12; x5, p, t); }
                27 'a11 { add_xor_ad!(12, 16; x1, x6, x12; x0, x5, t); }
                28 'a12 { add_xor_cb!(12, 8; x6, q, x12; x5, p, t); }
                29 'a13 {
                    slots.set(C + 2, p);
                    slots.set(C + 3, q);
                    slots.set(X15, t);
                    p = slots.get(C);
                    q = slots.get(C + 1);
                    t = slots.get(X13);
                }
                30 'a14 { add_xor_ad!(7, 8; x3, x4, x14; x2, x7, t); }
                31 'a15 { add_xor_cb!(7, 16; x4, q, x14; x7, p, t); }
                32 'a16 { add_xor_ad!(12, 16; x3, x4, x14; x2, x7, t); }
                33 'a17 { add_xor_cb!(12, 8; x4, q, x14; x7, p, t); }
                // The same double round again.
                34 'b0 { add_xor_ad!(7, 8; x0, x4, x12; x1, x5, t); }
                35 'b1 { add_xor_cb!(7, 16; x4, p, x12; x5, q, t); }
                36 'b2 { add_xor_ad!(12, 16; x0, x4, x12; x1, x5, t); }
                37 'b3 { add_xor_cb!(12, 8; x4, p, x12; x5, q, t); }
                38 'b4 {
                    slots.set(C, p);
                    slots.set(C + 1, q);
                    slots.set(X13, t);
                    p = slots.get(C + 2);
                    q = slots.get(C + 3);
                    t = slots.get(X15);
                }
                39 'b5 { add_xor_ad!(7, 8; x2, x6, x14; x3, x7, t); }
                40 'b6 { add_xor_cb!(7, 16; x6, p, x14; x7, q, t); }
                41 'b7 { add_xor_ad!(12, 16; x2, x6, x14; x3, x7, t); }
                42 'b8 { add_xor_cb!(12, 8; x6, p, x14; x7, q, t); }
                43 'b9 { add_xor_ad!(7, 8; x1, x6, x12; x0, x5, t); }
                44 'b10 { add_xor_cb!(7, 16; x6, q, x12; x5, p, t); }
                45 'b11 { add_xor_ad!(12, 16; x1, x6, x12; x0, x5, t); }
                46 'b12 { add_xor_cb!(12, 8; x6, q, x12; x5, p, t); }
                47 'b13 {
                    slots.set(C + 2, p);
                    slots.set(C + 3, q);
                    slots.set(X15, t);
                    p = slots.get(C);
                    q = slots.get(C + 1);
                    t = slots.get(X13);
                }
                48 'b14 { add_xor_ad!(7, 8; x3, x4, x14; x2, x7, t); }
                49 'b15 { add_xor_cb!(7, 16; x4, q, x14; x7, p, t); }
                50 'b16 { add_xor_ad!(12, 16; x3, x4, x14; x2, x7, t); }
                51 'b17 { add_xor_cb!(12, 8; x4, q, x14; x7, p, t); }
            );
            trips = slots.get(TRIPS).wrapping_sub(1);
            slots.set(TRIPS, trips);
            if trips == 0 {
                break;
            }
        }
        // Add the input, undoing the rotations the rows are held in, and XOR
        // the block, a word at a time straight into it.
        let (words, _) = block.as_chunks_mut::<4>();
        macro_rules! out {
            ($i:literal, $x:expr) => {
                words[$i] =
                    (u32::from_le_bytes(words[$i]) ^ $x.wrapping_add(input[$i])).to_le_bytes();
            };
        }
        out!(0, x0);
        out!(1, x1);
        out!(2, x2);
        out!(3, x3);
        out!(4, x4.rotate_left(7));
        out!(5, x5.rotate_left(7));
        out!(6, x6.rotate_left(7));
        out!(7, x7.rotate_left(7));
        out!(8, p);
        out!(9, q);
        out!(12, x12.rotate_left(8));
        out!(13, t.rotate_left(8));
        out!(14, x14.rotate_left(8));
        out!(10, slots.get(C + 2));
        out!(11, slots.get(C + 3));
        out!(15, slots.get(X15).rotate_left(8));
        input[12] = input[12].wrapping_add(1);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::generic::chacha20;

    struct SplitMix(u64);

    impl SplitMix {
        fn next(&mut self) -> u64 {
            self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
            let mut z = self.0;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
            z ^ (z >> 31)
        }

        fn fill(&mut self, out: &mut [u8]) {
            for b in out {
                *b = self.next() as u8;
            }
        }
    }

    // HACL*'s rounds, one call for the whole buffer.
    fn reference(key: &[u8; 32], nonce: &[u8; 16], buffer: &mut [u8]) {
        let state = ChaCha20::new(key, nonce);
        let key: &[u32; 8] = state.ctx[4..12].try_into().unwrap();
        let counter_nonce: &[u32; 4] = state.ctx[12..16].try_into().unwrap();
        chacha20::cipher(key, counter_nonce, buffer);
    }

    // RFC 8439 section 2.4.2.
    #[test]
    fn rfc8439_sunscreen() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let nonce = [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00,
            0x00, 0x00,
        ];
        let mut text = *b"Ladies and Gentlemen of the class of '99: If I could offer you \
only one tip for the future, sunscreen would be it.";
        ChaCha20::new(&key, &nonce).cipher(&mut text);
        assert_eq!(
            text,
            [
                0x6e, 0x2e, 0x35, 0x9a, 0x25, 0x68, 0xf9, 0x80, 0x41, 0xba, 0x07, 0x28, 0xdd, 0x0d,
                0x69, 0x81, 0xe9, 0x7e, 0x7a, 0xec, 0x1d, 0x43, 0x60, 0xc2, 0x0a, 0x27, 0xaf, 0xcc,
                0xfd, 0x9f, 0xae, 0x0b, 0xf9, 0x1b, 0x65, 0xc5, 0x52, 0x47, 0x33, 0xab, 0x8f, 0x59,
                0x3d, 0xab, 0xcd, 0x62, 0xb3, 0x57, 0x16, 0x39, 0xd6, 0x24, 0xe6, 0x51, 0x52, 0xab,
                0x8f, 0x53, 0x0c, 0x35, 0x9f, 0x08, 0x61, 0xd8, 0x07, 0xca, 0x0d, 0xbf, 0x50, 0x0d,
                0x6a, 0x61, 0x56, 0xa3, 0x8e, 0x08, 0x8a, 0x22, 0xb6, 0x5e, 0x52, 0xbc, 0x51, 0x4d,
                0x16, 0xcc, 0xf8, 0x06, 0x81, 0x8c, 0xe9, 0x1a, 0xb7, 0x79, 0x37, 0x36, 0x5a, 0xf9,
                0x0b, 0xbf, 0x74, 0xa3, 0x5b, 0xe6, 0xb4, 0x0b, 0x8e, 0xed, 0xf2, 0x78, 0x5e, 0x42,
                0x87, 0x4d,
            ]
        );
    }

    // Every length to five blocks, and a longer one, against HACL*'s rounds.
    // The key is secret, so under `admin/ctgrind` this also checks that the
    // schedule's branches and addresses do not depend on it.
    #[test]
    fn matches_hacl_rounds() {
        let mut rng = SplitMix(0x0c4a_c4a2_0a57_ab1e);
        for len in (0..=320).chain([1000, 4099]) {
            let mut key = [0u8; 32];
            let mut nonce = [0u8; 16];
            rng.fill(&mut key);
            rng.fill(&mut nonce);
            let mut want = vec![0u8; len];
            rng.fill(&mut want);
            let mut got = want.clone();
            reference(&key, &nonce, &mut want);
            ct::secret_slice(&key);
            ChaCha20::new(&key, &nonce).cipher(&mut got);
            assert_eq!(ct::into_public(got), want, "{len}");
        }
    }

    // A buffer in pieces: each call starts a block, as the AEAD's do, so the
    // pieces but the last are whole blocks.
    #[test]
    fn pieces_match_one_call() {
        let mut rng = SplitMix(0x5eed_0f00_c4ac_4a20);
        for _ in 0..200 {
            let mut key = [0u8; 32];
            let mut nonce = [0u8; 16];
            rng.fill(&mut key);
            rng.fill(&mut nonce);
            let len = (rng.next() % 1500) as usize;
            let mut want = vec![0u8; len];
            rng.fill(&mut want);
            let mut got = want.clone();
            reference(&key, &nonce, &mut want);
            let mut state = ChaCha20::new(&key, &nonce);
            let mut rest = &mut got[..];
            while !rest.is_empty() {
                let blocks = 1 + (rng.next() % 5) as usize;
                let (head, tail) = rest.split_at_mut((64 * blocks).min(rest.len()));
                state.cipher(head);
                rest = tail;
            }
            assert_eq!(got, want, "{len}");
        }
    }

    // The block counter wraps to zero, as RFC 8439's 32-bit counter does in
    // HACL*'s rounds.
    #[test]
    fn counter_wraps() {
        let key = [0x42u8; 32];
        let mut nonce = [7u8; 16];
        nonce[..4].copy_from_slice(&0xffff_fffeu32.to_le_bytes());
        let mut want = [0x5au8; 300];
        let mut got = want;
        reference(&key, &nonce, &mut want);
        let mut state = ChaCha20::new(&key, &nonce);
        state.cipher(&mut got);
        assert_eq!(got, want);
        assert_eq!(state.ctx[12], 3);
    }

    // RFC 8439 §2.3.2's initial state.
    #[test]
    fn state_matches_rfc8439() {
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        // Block counter 1, then the 96-bit nonce 00000009 0000004a 00000000.
        let nonce = [
            0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00,
            0x00, 0x00,
        ];
        let state = ChaCha20::new(&key, &nonce);
        assert_eq!(
            state.ctx,
            [
                0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0x03020100, 0x07060504, 0x0b0a0908,
                0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x00000001, 0x09000000,
                0x4a000000, 0x00000000,
            ]
        );
    }
}
