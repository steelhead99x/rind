// Copyright (c) 2016-2022 INRIA, CMU and Microsoft Corporation
// Copyright (c) 2022-2023 HACL* Contributors
// Copyright 2023 Cryspen Sarl
// SPDX-License-Identifier: Apache-2.0
//
// ChaCha20's rounds, from HACL*'s verified `Hacl_Chacha20` as
// libcrux-chacha20poly1305 0.0.10 ships it (`src/hacl/chacha20.rs`), for
// HChaCha20 and QUIC header protection on every backend, for the portable
// backend's ChaCha20, and for x86_64's: one block, up to 128 bytes without
// AVX2, and every length without SSSE3. They run in general-purpose registers, as aws-lc's integer routines
// do: a single block packed into vector registers is one serial chain, which
// Zen 5's two-cycle vector latency makes twice as slow.
//
// `proofs/` proves `chacha20_block` against RFC 8439 and `hchacha20` against
// draft-irtf-cfrg-xchacha-03, these rounds included.

#[inline]
fn quarter_round(st: &mut [u32], a: u32, b: u32, c: u32, d: u32) {
    let sta: u32 = st[a as usize];
    let stb: u32 = st[b as usize];
    let std: u32 = st[d as usize];
    let sta1: u32 = sta.wrapping_add(stb);
    let std1: u32 = std ^ sta1;
    let std2: u32 = std1.wrapping_shl(16u32) | std1.wrapping_shr(16u32);
    st[a as usize] = sta1;
    st[d as usize] = std2;
    let sta0: u32 = st[c as usize];
    let stb0: u32 = st[d as usize];
    let std0: u32 = st[b as usize];
    let sta10: u32 = sta0.wrapping_add(stb0);
    let std10: u32 = std0 ^ sta10;
    let std20: u32 = std10.wrapping_shl(12u32) | std10.wrapping_shr(20u32);
    st[c as usize] = sta10;
    st[b as usize] = std20;
    let sta2: u32 = st[a as usize];
    let stb1: u32 = st[b as usize];
    let std3: u32 = st[d as usize];
    let sta11: u32 = sta2.wrapping_add(stb1);
    let std11: u32 = std3 ^ sta11;
    let std21: u32 = std11.wrapping_shl(8u32) | std11.wrapping_shr(24u32);
    st[a as usize] = sta11;
    st[d as usize] = std21;
    let sta3: u32 = st[c as usize];
    let stb2: u32 = st[d as usize];
    let std4: u32 = st[b as usize];
    let sta12: u32 = sta3.wrapping_add(stb2);
    let std12: u32 = std4 ^ sta12;
    let std22: u32 = std12.wrapping_shl(7u32) | std12.wrapping_shr(25u32);
    st[c as usize] = sta12;
    st[b as usize] = std22
}

#[inline]
fn double_round(st: &mut [u32]) {
    quarter_round(st, 0u32, 4u32, 8u32, 12u32);
    quarter_round(st, 1u32, 5u32, 9u32, 13u32);
    quarter_round(st, 2u32, 6u32, 10u32, 14u32);
    quarter_round(st, 3u32, 7u32, 11u32, 15u32);
    quarter_round(st, 0u32, 5u32, 10u32, 15u32);
    quarter_round(st, 1u32, 6u32, 11u32, 12u32);
    quarter_round(st, 2u32, 7u32, 8u32, 13u32);
    quarter_round(st, 3u32, 4u32, 9u32, 14u32)
}

#[inline]
fn rounds(st: &mut [u32]) {
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st);
    double_round(st)
}

/// ChaCha20's constant, "expand 32-byte k" as little-endian words.
const SIGMA: [u32; 4] = [0x6170_7865, 0x3320_646e, 0x7962_2d32, 0x6b20_6574];

/// ChaCha20's state for `key` and `nonce`: the constant, then the key and the
/// nonce as little-endian words.
//
// Indexes rather than splitting into chunks, which Aeneas cannot translate,
// so `proofs/` can prove `chacha20_block`.
#[inline]
fn state(key: &[u8; 32], nonce: &[u8; 16]) -> [u32; 16] {
    let mut st = [0u32; 16];
    st[..4].copy_from_slice(&SIGMA);
    for i in 0..8 {
        st[4 + i] =
            u32::from_le_bytes([key[4 * i], key[4 * i + 1], key[4 * i + 2], key[4 * i + 3]]);
    }
    for i in 0..4 {
        st[12 + i] = u32::from_le_bytes([
            nonce[4 * i],
            nonce[4 * i + 1],
            nonce[4 * i + 2],
            nonce[4 * i + 3],
        ]);
    }
    st
}

/// HChaCha20 of `key` and `nonce`, for XChaCha20's subkey: the ChaCha20
/// rounds without the final addition, keeping words 0-3 and 12-15, as
/// draft-irtf-cfrg-xchacha-03 specifies.
//
// Indexes, as `state` does, so `proofs/` can prove it.
pub(crate) fn hchacha20(key: &[u8; 32], nonce: &[u8; 16]) -> [u8; 32] {
    let mut st = state(key, nonce);
    rounds(&mut st);
    let mut out = [0u8; 32];
    for i in 0..8 {
        let w = if i < 4 { st[i] } else { st[i + 8] };
        out[4 * i..4 * (i + 1)].copy_from_slice(&w.to_le_bytes());
    }
    out
}

/// ChaCha20's keystream block for `key` and `counter_nonce`, the
/// little-endian block counter then the 96-bit nonce (RFC 8439 section 2.3).
#[inline]
pub(crate) fn chacha20_block(key: &[u8; 32], counter_nonce: &[u8; 16]) -> [u8; 64] {
    let input = state(key, counter_nonce);
    let mut st = input;
    rounds(&mut st);
    let mut out = [0u8; 64];
    for i in 0..16 {
        out[4 * i..4 * (i + 1)].copy_from_slice(&st[i].wrapping_add(input[i]).to_le_bytes());
    }
    out
}

/// XORs the ChaCha20 keystream for `key` and `counter_nonce`, the block
/// counter then the 96-bit nonce, into `buffer`, one block at a time.
#[cfg(any(rind_backend = "x86_64", rind_backend = "portable"))]
pub(crate) fn cipher(key: &[u32; 8], counter_nonce: &[u32; 4], buffer: &mut [u8]) {
    let mut input = [0u32; 16];
    for (i, b) in input.iter_mut().zip(b"expand 32-byte k".as_chunks::<4>().0) {
        *i = u32::from_le_bytes(*b);
    }
    input[4..12].copy_from_slice(key);
    input[12..].copy_from_slice(counter_nonce);

    for block in buffer.chunks_mut(64) {
        let mut st = input;
        rounds(&mut st);
        for (s, i) in st.iter_mut().zip(input) {
            *s = s.wrapping_add(i);
        }
        let (words, tail) = block.as_chunks_mut::<4>();
        for (w, k) in words.iter_mut().zip(st) {
            *w = (u32::from_le_bytes(*w) ^ k).to_le_bytes();
        }
        if let Some(k) = st.get(words.len()) {
            for (b, k) in tail.iter_mut().zip(k.to_le_bytes()) {
                *b ^= k;
            }
        }
        input[12] = input[12].wrapping_add(1);
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn hchacha_test_vectors() {
        // From draft-irtf-cfrg-xchacha-03

        let key = [
            0x00, 0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d,
            0x0e, 0x0f, 0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b,
            0x1c, 0x1d, 0x1e, 0x1f,
        ];
        let nonce = [
            0x00, 0x00, 0x00, 0x09, 0x00, 0x00, 0x00, 0x4a, 0x00, 0x00, 0x00, 0x00, 0x31, 0x41,
            0x59, 0x27, 0xfe, 0xdc, 0xba, 0x98, 0x76, 0x54, 0x32, 0x10,
        ];

        assert_eq!(
            hchacha20(&key, nonce[..16].try_into().unwrap()),
            [
                0x82, 0x41, 0x3b, 0x42, 0x27, 0xb2, 0x7b, 0xfe, 0xd3, 0x0e, 0x42, 0x50, 0x8a, 0x87,
                0x7d, 0x73, 0xa0, 0xf9, 0xe4, 0xd5, 0x8a, 0x74, 0xa8, 0x53, 0xc1, 0x2e, 0xc4, 0x13,
                0x26, 0xd3, 0xec, 0xdc,
            ]
        );
    }
}
