// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20 on HACL*'s verified rounds in `generic::chacha20`, one block at a
//! time, as x86_64 runs it without SSSE3.
//!
//! On 32-bit targets the keystream goes from registers straight into the
//! buffer a word at a time, never through a 64-byte array. On the ESP32-C6
//! (riscv32imac, which has no fast misaligned loads) that array cost a fifth
//! of each block's instructions: stored a byte at a time, then loaded back
//! to XOR a byte at a time.

#[cfg(not(target_pointer_width = "32"))]
use crate::low::generic::chacha20;
#[cfg(any(target_pointer_width = "32", test))]
use crate::low::generic::chacha20::SIGMA;
#[cfg(all(any(target_pointer_width = "32", test), not(target_arch = "xtensa")))]
use crate::low::generic::chacha20::rounds;

pub(crate) struct ChaCha20 {
    key: [u32; 8],
    /// The block counter, then the 96-bit nonce.
    counter_nonce: [u32; 4],
}

impl ChaCha20 {
    /// `nonce` is the little-endian block counter followed by the 96-bit nonce.
    pub(crate) fn new(key: &[u8; 32], nonce: &[u8; 16]) -> Self {
        Self {
            key: words(key),
            counter_nonce: words(nonce),
        }
    }

    /// XORs the keystream into `buffer`, starting at the current block, then
    /// moves the counter past every block it touched.
    pub(crate) fn cipher(&mut self, buffer: &mut [u8]) {
        #[cfg(target_pointer_width = "32")]
        cipher32(&self.key, &self.counter_nonce, buffer);
        #[cfg(not(target_pointer_width = "32"))]
        chacha20::cipher(&self.key, &self.counter_nonce, buffer);
        self.counter_nonce[0] =
            self.counter_nonce[0].wrapping_add(buffer.len().div_ceil(64) as u32);
    }
}

/// Rotates four words right by `R`.
///
/// On Xtensa one `ssai` and four `src`, where LLVM's backend emits the shift
/// pair and `or` a rotate: 960 of a block's 2,200 instructions were rotates.
/// Elsewhere (host tests) the same function in Rust, so `rounds4`'s schedule
/// runs under test; only this asm block is checked by the board alone.
#[cfg(target_arch = "xtensa")]
#[inline(always)]
fn rotr4<const R: u32>([w0, w1, w2, w3]: [u32; 4]) -> [u32; 4] {
    let (y0, y1, y2, y3);
    // SAFETY: `ssai` and `src` are base Xtensa instructions; `R` is one of
    // 16, 20, 24, 25 (the call sites), in `ssai`'s 0..32 range. The block
    // writes only SAR and its four operands, which are `inout`, each its own
    // register read and written in place (`lateout` would let an output
    // share an input's register before every input was read), loads and
    // stores nothing, and reads SAR only after its own `ssai`.
    unsafe {
        core::arch::asm!(
            "ssai {r}",
            "src {a}, {a}, {a}",
            "src {b}, {b}, {b}",
            "src {c}, {c}, {c}",
            "src {d}, {d}, {d}",
            r = const R,
            a = inout(reg) w0 => y0,
            b = inout(reg) w1 => y1,
            c = inout(reg) w2 => y2,
            d = inout(reg) w3 => y3,
            out("sar") _,
            options(nomem, nostack),
        );
    }
    [y0, y1, y2, y3]
}

#[cfg(all(test, not(target_arch = "xtensa")))]
#[inline(always)]
fn rotr4<const R: u32>(w: [u32; 4]) -> [u32; 4] {
    w.map(|w| w.rotate_right(R))
}

/// ChaCha20's twenty rounds as Xtensa runs them: four quarter rounds at once,
/// step by step, so each rotate distance is shared by the four. Same
/// arithmetic as `generic::chacha20::rounds` (a test checks it against them);
/// the Xtensa form is not proven.
///
/// Every operation is an add, an xor, or a fixed rotate: no branch or index
/// depends on the state, and `ssai`'s distance is an immediate, not data.
#[cfg(any(target_arch = "xtensa", test))]
#[inline(never)]
fn rounds4(st: &mut [u32; 16]) {
    #[inline(always)]
    fn round(x: &mut [u32; 16], a: [usize; 4], b: [usize; 4], c: [usize; 4], d: [usize; 4]) {
        let mut va = a.map(|i| x[i]);
        let mut vb = b.map(|i| x[i]);
        let mut vc = c.map(|i| x[i]);
        let mut vd = d.map(|i| x[i]);
        for i in 0..4 {
            va[i] = va[i].wrapping_add(vb[i]);
            vd[i] ^= va[i];
        }
        vd = rotr4::<16>(vd);
        for i in 0..4 {
            vc[i] = vc[i].wrapping_add(vd[i]);
            vb[i] ^= vc[i];
        }
        vb = rotr4::<20>(vb);
        for i in 0..4 {
            va[i] = va[i].wrapping_add(vb[i]);
            vd[i] ^= va[i];
        }
        vd = rotr4::<24>(vd);
        for i in 0..4 {
            vc[i] = vc[i].wrapping_add(vd[i]);
            vb[i] ^= vc[i];
        }
        vb = rotr4::<25>(vb);
        for i in 0..4 {
            x[a[i]] = va[i];
            x[b[i]] = vb[i];
            x[c[i]] = vc[i];
            x[d[i]] = vd[i];
        }
    }
    let mut x = *st;
    for _ in 0..10 {
        round(&mut x, [0, 1, 2, 3], [4, 5, 6, 7], [8, 9, 10, 11], [12, 13, 14, 15]);
        round(&mut x, [0, 1, 2, 3], [5, 6, 7, 4], [10, 11, 8, 9], [15, 12, 13, 14]);
    }
    *st = x;
}

/// The keystream block for the state `input`, as words.
#[cfg(any(target_pointer_width = "32", test))]
#[inline(always)]
fn keystream(input: &[u32; 16]) -> [u32; 16] {
    let mut st = *input;
    #[cfg(target_arch = "xtensa")]
    rounds4(&mut st);
    #[cfg(not(target_arch = "xtensa"))]
    rounds(&mut st);
    for (s, i) in st.iter_mut().zip(input) {
        *s = s.wrapping_add(*i);
    }
    st
}

/// `generic::chacha20::cipher`: XORs the keystream for `key` and
/// `counter_nonce` into `buffer`.
///
/// A whole block's words are read and written whole. Where the buffer does
/// not start on a word, each word takes the keystream's bytes across two of
/// its words, shifted by the misalignment, which is public. One keystream
/// call site keeps one copy of the unrolled rounds in the instruction cache.
#[cfg(any(target_pointer_width = "32", test))]
fn cipher32(key: &[u32; 8], counter_nonce: &[u32; 4], buffer: &mut [u8]) {
    let mut input = [0u32; 16];
    input[..4].copy_from_slice(&SIGMA);
    input[4..12].copy_from_slice(key);
    input[12..].copy_from_slice(counter_nonce);

    for chunk in buffer.chunks_mut(64) {
        let ks = keystream(&input);
        input[12] = input[12].wrapping_add(1);
        // SAFETY: every bit pattern is a `u32`, so aligned bytes may be read
        // and written as words.
        let (head, words, tail) = unsafe { chunk.align_to_mut::<u32>() };
        let at = head.len();
        if let Ok(words) = <&mut [u32; 16]>::try_from(&mut *words) {
            for (w, k) in words.iter_mut().zip(ks) {
                *w = (u32::from_le(*w) ^ k).to_le();
            }
        } else if let (Ok(words), 1..4) = (<&mut [u32; 15]>::try_from(&mut *words), at) {
            // The keystream from byte `at`, a word at a time; the bytes
            // before it from the first word, and the bytes after from
            // the last.
            let (lo, hi) = (8 * at as u32, 32 - 8 * at as u32);
            for (i, w) in words.iter_mut().enumerate() {
                *w = (u32::from_le(*w) ^ (ks[i] >> lo | ks[i + 1] << hi)).to_le();
            }
            for (i, b) in head.iter_mut().enumerate() {
                *b ^= (ks[0] >> (8 * i)) as u8;
            }
            for (i, b) in (at..).zip(tail) {
                *b ^= (ks[15] >> (8 * i)) as u8;
            }
        } else {
            // A short last block, or `align_to_mut` leaving more in `head`,
            // as it may under Miri.
            xor_any(head, words, tail, &{ ks });
        }
    }
}

/// XORs the keystream `ks` into `head`, then `words`, then `tail`, which are
/// one run of at most 64 bytes.
#[cfg(any(target_pointer_width = "32", test))]
#[inline(never)]
fn xor_any(head: &mut [u8], words: &mut [u32], tail: &mut [u8], ks: &[u32; 16]) {
    let byte = |i: usize| (ks[i / 4] >> (8 * (i % 4))) as u8;
    for (i, b) in head.iter_mut().enumerate() {
        *b ^= byte(i);
    }
    let at = head.len();
    for (i, w) in words.iter_mut().enumerate() {
        let mut b = w.to_ne_bytes();
        for (j, b) in b.iter_mut().enumerate() {
            *b ^= byte(at + 4 * i + j);
        }
        *w = u32::from_ne_bytes(b);
    }
    let at = at + 4 * words.len();
    for (i, b) in tail.iter_mut().enumerate() {
        *b ^= byte(at + i);
    }
}

/// `bytes` as little-endian words.
fn words<const B: usize, const W: usize>(bytes: &[u8; B]) -> [u32; W] {
    const { assert!(B == 4 * W) };
    let mut words = [0; W];
    for (w, b) in words.iter_mut().zip(bytes.as_chunks::<4>().0) {
        *w = u32::from_le_bytes(*b);
    }
    words
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;
    use crate::low::generic::chacha20::cipher;

    // `rounds4`, the schedule Xtensa runs with `rotr4` in Rust, against the
    // proven generic rounds: RFC 8439 section 2.3.2's block and random states.
    #[test]
    fn rounds4_matches_generic() {
        let mut st: [u32; 16] = core::array::from_fn(|i| 0x6170_7865u32.wrapping_mul(i as u32 + 1));
        for _ in 0..1000 {
            let mut want = st;
            crate::low::generic::chacha20::rounds(&mut want);
            let mut got = st;
            rounds4(&mut got);
            assert_eq!(got, want);
            st = core::array::from_fn(|i| want[i].rotate_left(i as u32).wrapping_add(st[(i + 5) % 16]));
        }
        let key: [u8; 32] = core::array::from_fn(|i| i as u8);
        let nonce = [1, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0x4a, 0, 0, 0, 0];
        let input = {
            let mut input = [0u32; 16];
            input[..4].copy_from_slice(&SIGMA);
            input[4..12].copy_from_slice(&words::<32, 8>(&key));
            input[12..].copy_from_slice(&words::<16, 4>(&nonce));
            input
        };
        let mut a = input;
        rounds4(&mut a);
        let mut b = input;
        crate::low::generic::chacha20::rounds(&mut b);
        assert_eq!(a, b);
    }

    // `cipher32` against `generic::chacha20::cipher`, the proven loop: every
    // length up to 300 bytes, starting at each offset from a word, so the
    // aligned, misaligned, and short-block paths all run, from a counter
    // that wraps partway. The key and data are secret, so under
    // `admin/ctgrind` this also checks this path is constant time in both.
    #[test]
    fn matches_generic() {
        let key: [u8; 32] = core::array::from_fn(|i| (i as u8).wrapping_mul(0x9d) ^ 0x5a);
        let mut nonce = [0u8; 16];
        nonce[..4].copy_from_slice(&(u32::MAX - 2).to_le_bytes());
        nonce[4..].copy_from_slice(b"rind nonce!!");
        let data: Vec<u8> = (0..300u32).map(|i| (i * 31 + 7) as u8).collect();
        for len in 0..=data.len() {
            let mut want = data[..len].to_vec();
            cipher(&words(&key), &words(&nonce), &mut want);
            for offset in 0..4 {
                let mut buf = vec![0u8; len + 8];
                let start = buf.as_ptr().addr().wrapping_neg() % 4 + offset;
                let got = &mut buf[start..start + len];
                got.copy_from_slice(&data[..len]);
                ct::secret_slice(&key);
                ct::secret_slice(got);
                cipher32(&words(&key), &words(&nonce), got);
                ct::public_slice(&key);
                ct::public_slice(got);
                assert_eq!(got, &want[..], "{len} bytes at offset {offset}");
            }
        }
    }
}
