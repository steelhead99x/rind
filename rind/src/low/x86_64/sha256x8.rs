// Ported from the SPHINCS+ team's sha2-avx2 `sha256avx.c`, written by
// Joost Rijneveld and others, which is in the public domain.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! SHA-256's compression function over eight independent chaining values at
//! once, one per 32-bit lane of an AVX2 register.

use core::arch::x86_64::*;

use super::cpu::{HaveAvx2, HaveSha256};
use crate::low::{pad, sha256_digest, split_tail};

/// Eight SHA-256 hashes at once, each continuing chaining value `state` over
/// one of `messages`, which are of equal length, padded and closed by
/// `length`. `messages` holds one to eight; the digests past them are
/// unspecified.
///
/// The SHA extensions run each in turn, faster than AVX2 runs all eight at
/// once; without them, AVX2 runs eight at once, four times faster than one
/// at a time.
pub(crate) fn sha256_finish_x8(
    state: &[u32; 8],
    messages: &[&[u8]],
    length: [u8; 8],
) -> [[u8; 32]; 8] {
    match (HaveSha256::check(), HaveAvx2::check()) {
        (None, Some(token)) if messages.len() > 1 => finish_avx2(state, messages, length, token),
        _ => crate::low::generic::sha256x8::sha256_finish_x8(state, messages, length),
    }
}

fn finish_avx2(
    state: &[u32; 8],
    messages: &[&[u8]],
    length: [u8; 8],
    token: HaveAvx2,
) -> [[u8; 32]; 8] {
    // Unused lanes hash the last message again.
    let lane = |j: usize| messages[Ord::min(j, messages.len() - 1)];
    let len = messages[0].len();
    assert!(messages.iter().all(|m| m.len() == len));

    let mut states = [*state; 8];
    let (whole, _) = split_tail::<64, 8>(messages[0]);
    for start in (0..whole.len()).step_by(64) {
        let blocks = core::array::from_fn(|j| lane(j)[start..start + 64].try_into().unwrap());
        sha256_compress_x8_avx2(&mut states, &blocks, token);
    }
    let mut last = [[[0u8; 64]; 2]; 8];
    let mut tails = 0;
    for (j, last) in last.iter_mut().enumerate() {
        tails = pad(&lane(j)[whole.len()..], length, last).len() / 64;
    }
    for block in 0..tails {
        let blocks = last.map(|lane| lane[block]);
        sha256_compress_x8_avx2(&mut states, &blocks, token);
    }
    states.map(|h| sha256_digest(&h))
}

/// Compresses one block into each of eight SHA-256 chaining values with
/// AVX2.
fn sha256_compress_x8_avx2(states: &mut [[u32; 8]; 8], blocks: &[[u8; 64]; 8], _token: HaveAvx2) {
    // SAFETY: `_token` proves the caller checked AVX2.
    unsafe { compress(states, blocks) }
}

#[target_feature(enable = "avx,avx2")]
fn compress(states: &mut [[u32; 8]; 8], blocks: &[[u8; 64]; 8]) {
    let bswap = _mm256_set_epi8(
        12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11, 4, 5,
        6, 7, 0, 1, 2, 3,
    );

    let mut init = [_mm256_setzero_si256(); 8];
    let mut w = [_mm256_setzero_si256(); 16];
    for j in 0..8 {
        // SAFETY: each state is 32 readable bytes, and each block 64.
        unsafe {
            init[j] = _mm256_loadu_si256(states[j].as_ptr().cast());
            w[j] = _mm256_shuffle_epi8(_mm256_loadu_si256(blocks[j].as_ptr().cast()), bswap);
            w[j + 8] =
                _mm256_shuffle_epi8(_mm256_loadu_si256(blocks[j][32..].as_ptr().cast()), bswap);
        }
    }
    // Lane `j` of word `i` is block `j`'s word `i`, and likewise the state.
    transpose(&mut init);
    let (low, high) = w.split_at_mut(8);
    transpose(low.try_into().unwrap());
    transpose(high.try_into().unwrap());

    let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = init;

    macro_rules! round {
        ($a:ident, $b:ident, $c:ident, $d:ident, $e:ident, $f:ident, $g:ident, $h:ident, $i:expr) => {
            let i = $i;
            if i >= 16 {
                w[i & 15] = add(
                    add(small_sigma1(w[(i - 2) & 15]), w[(i - 7) & 15]),
                    add(small_sigma0(w[(i - 15) & 15]), w[i & 15]),
                );
            }
            let t0 = add(
                add(add($h, big_sigma1($e)), ch($e, $f, $g)),
                add(_mm256_set1_epi32(K[i] as i32), w[i & 15]),
            );
            $d = add($d, t0);
            $h = add(t0, add(big_sigma0($a), maj($a, $b, $c)));
        };
    }

    for i in (0..64).step_by(8) {
        round!(a, b, c, d, e, f, g, h, i);
        round!(h, a, b, c, d, e, f, g, i + 1);
        round!(g, h, a, b, c, d, e, f, i + 2);
        round!(f, g, h, a, b, c, d, e, i + 3);
        round!(e, f, g, h, a, b, c, d, i + 4);
        round!(d, e, f, g, h, a, b, c, i + 5);
        round!(c, d, e, f, g, h, a, b, i + 6);
        round!(b, c, d, e, f, g, h, a, i + 7);
    }

    let mut out = [a, b, c, d, e, f, g, h];
    for (out, init) in out.iter_mut().zip(init) {
        *out = add(*out, init);
    }
    transpose(&mut out);
    for j in 0..8 {
        // SAFETY: each state is 32 writable bytes.
        unsafe { _mm256_storeu_si256(states[j].as_mut_ptr().cast(), out[j]) };
    }
}

/// Transposes eight vectors of eight 32-bit words.
#[target_feature(enable = "avx,avx2")]
fn transpose(s: &mut [__m256i; 8]) {
    let t0 = [
        _mm256_unpacklo_epi32(s[0], s[1]),
        _mm256_unpackhi_epi32(s[0], s[1]),
        _mm256_unpacklo_epi32(s[2], s[3]),
        _mm256_unpackhi_epi32(s[2], s[3]),
        _mm256_unpacklo_epi32(s[4], s[5]),
        _mm256_unpackhi_epi32(s[4], s[5]),
        _mm256_unpacklo_epi32(s[6], s[7]),
        _mm256_unpackhi_epi32(s[6], s[7]),
    ];
    let t1 = [
        _mm256_unpacklo_epi64(t0[0], t0[2]),
        _mm256_unpackhi_epi64(t0[0], t0[2]),
        _mm256_unpacklo_epi64(t0[1], t0[3]),
        _mm256_unpackhi_epi64(t0[1], t0[3]),
        _mm256_unpacklo_epi64(t0[4], t0[6]),
        _mm256_unpackhi_epi64(t0[4], t0[6]),
        _mm256_unpacklo_epi64(t0[5], t0[7]),
        _mm256_unpackhi_epi64(t0[5], t0[7]),
    ];
    for i in 0..4 {
        s[i] = _mm256_permute2x128_si256::<0x20>(t1[i], t1[i + 4]);
        s[i + 4] = _mm256_permute2x128_si256::<0x31>(t1[i], t1[i + 4]);
    }
}

#[target_feature(enable = "avx,avx2")]
fn add(a: __m256i, b: __m256i) -> __m256i {
    _mm256_add_epi32(a, b)
}

#[target_feature(enable = "avx,avx2")]
fn rotr<const R: i32, const L: i32>(x: __m256i) -> __m256i {
    _mm256_or_si256(_mm256_srli_epi32::<R>(x), _mm256_slli_epi32::<L>(x))
}

#[target_feature(enable = "avx,avx2")]
fn big_sigma0(x: __m256i) -> __m256i {
    _mm256_xor_si256(
        _mm256_xor_si256(rotr::<2, 30>(x), rotr::<13, 19>(x)),
        rotr::<22, 10>(x),
    )
}

#[target_feature(enable = "avx,avx2")]
fn big_sigma1(x: __m256i) -> __m256i {
    _mm256_xor_si256(
        _mm256_xor_si256(rotr::<6, 26>(x), rotr::<11, 21>(x)),
        rotr::<25, 7>(x),
    )
}

#[target_feature(enable = "avx,avx2")]
fn small_sigma0(x: __m256i) -> __m256i {
    _mm256_xor_si256(
        _mm256_xor_si256(rotr::<7, 25>(x), rotr::<18, 14>(x)),
        _mm256_srli_epi32::<3>(x),
    )
}

#[target_feature(enable = "avx,avx2")]
fn small_sigma1(x: __m256i) -> __m256i {
    _mm256_xor_si256(
        _mm256_xor_si256(rotr::<17, 15>(x), rotr::<19, 13>(x)),
        _mm256_srli_epi32::<10>(x),
    )
}

#[target_feature(enable = "avx,avx2")]
fn ch(e: __m256i, f: __m256i, g: __m256i) -> __m256i {
    _mm256_xor_si256(_mm256_and_si256(e, f), _mm256_andnot_si256(e, g))
}

#[target_feature(enable = "avx,avx2")]
fn maj(a: __m256i, b: __m256i, c: __m256i) -> __m256i {
    _mm256_or_si256(
        _mm256_and_si256(a, b),
        _mm256_and_si256(c, _mm256_or_si256(a, b)),
    )
}

const K: [u32; 64] = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
];

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    // The SHA extensions, where present, hide the AVX2 path from every
    // other test, so it is checked against them directly.
    #[test]
    fn avx2_matches_serial() {
        let Some(token) = HaveAvx2::check() else {
            return;
        };
        let _entry = crate::low::Entry::new_secret();
        let state = core::array::from_fn(|i| (i as u32).wrapping_mul(0x9e3779b9));
        let messages: [[u8; 200]; 8] =
            core::array::from_fn(|j| core::array::from_fn(|i| (j * 64 + i * 7) as u8));
        for len in [0, 1, 54, 55, 56, 63, 64, 65, 119, 120, 128, 200] {
            for lanes in 1..=8 {
                let messages: Vec<&[u8]> = messages[..lanes].iter().map(|m| &m[..len]).collect();
                let length = ((64 + len as u64) * 8).to_be_bytes();
                let want =
                    crate::low::generic::sha256x8::sha256_finish_x8(&state, &messages, length);
                let got = finish_avx2(&state, &messages, length, token);
                assert_eq!(got[..lanes], want[..lanes], "{len} bytes, {lanes} lanes");
            }
        }
    }
}
