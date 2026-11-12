// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ChaCha20 on HACL*'s verified rounds in `generic::chacha20`, one block at a
//! time, as x86_64 runs it without SSSE3.

use crate::low::generic::chacha20;

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
        chacha20::cipher(&self.key, &self.counter_nonce, buffer);
        self.counter_nonce[0] =
            self.counter_nonce[0].wrapping_add(buffer.len().div_ceil(64) as u32);
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
    use crate::low::generic::chacha20;

    fn key_and_nonce() -> ([u8; 32], [u8; 16]) {
        (
            core::array::from_fn(|i| i as u8),
            core::array::from_fn(|i| (i as u8).wrapping_mul(3)),
        )
    }

    /// Little-endian words, written out so a change in [`words`] cannot hide
    /// by being used on both sides.
    fn le_words<const B: usize, const W: usize>(bytes: &[u8; B]) -> [u32; W] {
        const { assert!(B == 4 * W) };
        let mut out = [0; W];
        for (w, b) in out.iter_mut().zip(bytes.as_chunks::<4>().0) {
            *w = u32::from_le_bytes(*b);
        }
        out
    }

    #[test]
    fn matches_one_block_at_a_time() {
        let (key, nonce) = key_and_nonce();
        let mut via_struct = [0x5a; 130];
        ChaCha20::new(&key, &nonce).cipher(&mut via_struct);

        let mut via_generic = [0x5a; 130];
        chacha20::cipher(&le_words(&key), &le_words(&nonce), &mut via_generic);
        assert_eq!(via_struct, via_generic);
    }

    #[test]
    fn second_call_continues_the_counter() {
        let (key, nonce) = key_and_nonce();
        let mut split = ChaCha20::new(&key, &nonce);
        let mut first = [0x11; 64];
        let mut second = [0x22; 66];
        split.cipher(&mut first);
        split.cipher(&mut second);

        let mut whole = [0x11; 130];
        whole[64..].fill(0x22);
        ChaCha20::new(&key, &nonce).cipher(&mut whole);
        assert_eq!(&first, &whole[..64]);
        assert_eq!(&second, &whole[64..]);
    }

    /// A partial block still consumes that block: the next call starts at the
    /// following one, which `div_ceil` counts and truncating division does not.
    #[test]
    fn partial_block_consumes_it() {
        let (key, nonce) = key_and_nonce();
        let mut continued = ChaCha20::new(&key, &nonce);
        continued.cipher(&mut [0u8; 100]);
        let mut next = [0u8; 16];
        continued.cipher(&mut next);

        let mut later = nonce;
        let counter = u32::from_le_bytes(later[..4].try_into().unwrap()).wrapping_add(2);
        later[..4].copy_from_slice(&counter.to_le_bytes());
        let mut expected = [0u8; 16];
        ChaCha20::new(&key, &later).cipher(&mut expected);
        assert_eq!(next, expected);
    }

    #[test]
    fn empty_does_not_advance() {
        let (key, nonce) = key_and_nonce();
        let mut after_empty = ChaCha20::new(&key, &nonce);
        after_empty.cipher(&mut []);
        let mut buf = [0x7e; 70];
        after_empty.cipher(&mut buf);

        let mut once = [0x7e; 70];
        ChaCha20::new(&key, &nonce).cipher(&mut once);
        assert_eq!(buf, once);
    }
}
