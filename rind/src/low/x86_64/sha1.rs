// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::arch::x86_64::*;

pub(in crate::low) fn sha1_compress_blocks_shaext(
    state: &mut [u32; 5],
    blocks: &[u8],
    _token: super::cpu::HaveSha1,
) {
    assert!(blocks.len().is_multiple_of(64));
    // SAFETY: `_token` proves the caller checked the `sha`, `ssse3`, and
    // `sse4.1` features
    unsafe { sha1(state, blocks) }
}

/// Compresses `message`, padded and closed by `length`.
///
/// The last block is padded in registers, so no load of it waits on a store
/// that cannot forward.
pub(in crate::low) fn sha1_compress_padded_shaext(
    state: &mut [u32; 5],
    message: &[u8],
    length: [u8; 8],
    _token: super::cpu::HaveSha1,
) {
    // SAFETY: `_token` proves the caller checked the `sha`, `ssse3`, and
    // `sse4.1` features
    unsafe { sha1_finish(state, message, length) }
}

/// Four rounds: `$e` gains the next message words, `$e_next` saves `$abcd`
/// to seed the following four.
macro_rules! rounds4 {
    ($abcd:ident, $e:ident, $e_next:ident, $msg:ident, $func:literal) => {
        $e = _mm_sha1nexte_epu32($e, $msg);
        $e_next = $abcd;
        $abcd = _mm_sha1rnds4_epu32::<$func>($abcd, $e);
    };
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn sha1(state: &mut [u32; 5], blocks: &[u8]) {
    let mut abcde = load_state(state);
    let (blocks, _) = blocks.as_chunks::<64>();
    for block in blocks {
        compress_block(&mut abcde, load_block(block));
    }
    store_state(state, abcde);
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn sha1_finish(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    let mut abcde = load_state(state);
    let (blocks, tail) = message.as_chunks::<64>();
    for block in blocks {
        compress_block(&mut abcde, load_block(block));
    }
    let (last, next) = super::sha_tail::padded_tail(tail, length);
    compress_block(&mut abcde, last);
    if let Some(next) = next {
        compress_block(&mut abcde, next);
    }
    store_state(state, abcde);
}

/// `state` as the SHA extensions hold it: ABCD with A in the top lane, and
/// E in the top lane of the other.
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn load_state(state: &[u32; 5]) -> (__m128i, __m128i) {
    // SAFETY: `state` is 5 32-bit words, so the first 4 are readable
    let abcd = unsafe { _mm_loadu_si128(state[0..4].as_ptr().cast()) };
    (
        _mm_shuffle_epi32(abcd, 0b00_01_10_11),
        _mm_set_epi32(state[4] as i32, 0, 0, 0),
    )
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn store_state(state: &mut [u32; 5], (abcd, e): (__m128i, __m128i)) {
    let abcd = _mm_shuffle_epi32(abcd, 0b00_01_10_11);
    // SAFETY: `state` is 5 32-bit words, so the first 4 are writable
    unsafe { _mm_storeu_si128(state[0..4].as_mut_ptr().cast(), abcd) };
    state[4] = _mm_extract_epi32::<3>(e) as u32;
}

#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn load_block(block: &[u8; 64]) -> [__m128i; 4] {
    // SAFETY: `block` is 64 bytes and readable
    unsafe {
        [
            _mm_loadu_si128(block[0..].as_ptr().cast()),
            _mm_loadu_si128(block[16..].as_ptr().cast()),
            _mm_loadu_si128(block[32..].as_ptr().cast()),
            _mm_loadu_si128(block[48..].as_ptr().cast()),
        ]
    }
}

/// Compresses the block whose bytes `msg` holds into ABCD and E.
//
// The message schedule is interleaved with the rounds as in Intel's
// "Intel SHA Extensions" paper (2013): for each group `g` of four rounds,
// `sha1msg2` finishes W for group g+1, `sha1msg1` starts W for g+3, and the
// xor folds W[t-8] into W for g+2.
#[target_feature(enable = "sha,sse2,ssse3,sse4.1")]
fn compress_block(state: &mut (__m128i, __m128i), msg: [__m128i; 4]) {
    let (abcd_prev, e0_prev) = *state;
    let (mut abcd, mut e0) = *state;
    // Reverses all 16 bytes: big-endian words, with W[0] in the top lane.
    let byte_reverse = _mm_set_epi64x(0x0001020304050607, 0x08090a0b0c0d0e0f);
    let mut msg0 = _mm_shuffle_epi8(msg[0], byte_reverse);
    let mut msg1 = _mm_shuffle_epi8(msg[1], byte_reverse);
    let mut msg2 = _mm_shuffle_epi8(msg[2], byte_reverse);
    let mut msg3 = _mm_shuffle_epi8(msg[3], byte_reverse);

    // Rounds 0-3: the first group adds `e` directly, since it is not
    // derived from a previous `abcd`.
    e0 = _mm_add_epi32(e0, msg0);
    let mut e1 = abcd;
    abcd = _mm_sha1rnds4_epu32::<0>(abcd, e0);

    // Rounds 4-7
    rounds4!(abcd, e1, e0, msg1, 0);
    msg0 = _mm_sha1msg1_epu32(msg0, msg1);

    // Rounds 8-11
    rounds4!(abcd, e0, e1, msg2, 0);
    msg1 = _mm_sha1msg1_epu32(msg1, msg2);
    msg0 = _mm_xor_si128(msg0, msg2);

    // Rounds 12-15
    msg0 = _mm_sha1msg2_epu32(msg0, msg3);
    rounds4!(abcd, e1, e0, msg3, 0);
    msg2 = _mm_sha1msg1_epu32(msg2, msg3);
    msg1 = _mm_xor_si128(msg1, msg3);

    // Rounds 16-19
    msg1 = _mm_sha1msg2_epu32(msg1, msg0);
    rounds4!(abcd, e0, e1, msg0, 0);
    msg3 = _mm_sha1msg1_epu32(msg3, msg0);
    msg2 = _mm_xor_si128(msg2, msg0);

    // Rounds 20-23
    msg2 = _mm_sha1msg2_epu32(msg2, msg1);
    rounds4!(abcd, e1, e0, msg1, 1);
    msg0 = _mm_sha1msg1_epu32(msg0, msg1);
    msg3 = _mm_xor_si128(msg3, msg1);

    // Rounds 24-27
    msg3 = _mm_sha1msg2_epu32(msg3, msg2);
    rounds4!(abcd, e0, e1, msg2, 1);
    msg1 = _mm_sha1msg1_epu32(msg1, msg2);
    msg0 = _mm_xor_si128(msg0, msg2);

    // Rounds 28-31
    msg0 = _mm_sha1msg2_epu32(msg0, msg3);
    rounds4!(abcd, e1, e0, msg3, 1);
    msg2 = _mm_sha1msg1_epu32(msg2, msg3);
    msg1 = _mm_xor_si128(msg1, msg3);

    // Rounds 32-35
    msg1 = _mm_sha1msg2_epu32(msg1, msg0);
    rounds4!(abcd, e0, e1, msg0, 1);
    msg3 = _mm_sha1msg1_epu32(msg3, msg0);
    msg2 = _mm_xor_si128(msg2, msg0);

    // Rounds 36-39
    msg2 = _mm_sha1msg2_epu32(msg2, msg1);
    rounds4!(abcd, e1, e0, msg1, 1);
    msg0 = _mm_sha1msg1_epu32(msg0, msg1);
    msg3 = _mm_xor_si128(msg3, msg1);

    // Rounds 40-43
    msg3 = _mm_sha1msg2_epu32(msg3, msg2);
    rounds4!(abcd, e0, e1, msg2, 2);
    msg1 = _mm_sha1msg1_epu32(msg1, msg2);
    msg0 = _mm_xor_si128(msg0, msg2);

    // Rounds 44-47
    msg0 = _mm_sha1msg2_epu32(msg0, msg3);
    rounds4!(abcd, e1, e0, msg3, 2);
    msg2 = _mm_sha1msg1_epu32(msg2, msg3);
    msg1 = _mm_xor_si128(msg1, msg3);

    // Rounds 48-51
    msg1 = _mm_sha1msg2_epu32(msg1, msg0);
    rounds4!(abcd, e0, e1, msg0, 2);
    msg3 = _mm_sha1msg1_epu32(msg3, msg0);
    msg2 = _mm_xor_si128(msg2, msg0);

    // Rounds 52-55
    msg2 = _mm_sha1msg2_epu32(msg2, msg1);
    rounds4!(abcd, e1, e0, msg1, 2);
    msg0 = _mm_sha1msg1_epu32(msg0, msg1);
    msg3 = _mm_xor_si128(msg3, msg1);

    // Rounds 56-59
    msg3 = _mm_sha1msg2_epu32(msg3, msg2);
    rounds4!(abcd, e0, e1, msg2, 2);
    msg1 = _mm_sha1msg1_epu32(msg1, msg2);
    msg0 = _mm_xor_si128(msg0, msg2);

    // Rounds 60-63
    msg0 = _mm_sha1msg2_epu32(msg0, msg3);
    rounds4!(abcd, e1, e0, msg3, 3);
    msg2 = _mm_sha1msg1_epu32(msg2, msg3);
    msg1 = _mm_xor_si128(msg1, msg3);

    // Rounds 64-67
    msg1 = _mm_sha1msg2_epu32(msg1, msg0);
    rounds4!(abcd, e0, e1, msg0, 3);
    msg3 = _mm_sha1msg1_epu32(msg3, msg0);
    msg2 = _mm_xor_si128(msg2, msg0);

    // Rounds 68-71
    msg2 = _mm_sha1msg2_epu32(msg2, msg1);
    rounds4!(abcd, e1, e0, msg1, 3);
    msg3 = _mm_xor_si128(msg3, msg1);

    // Rounds 72-75
    msg3 = _mm_sha1msg2_epu32(msg3, msg2);
    rounds4!(abcd, e0, e1, msg2, 3);

    // Rounds 76-79
    rounds4!(abcd, e1, e0, msg3, 3);

    e0 = _mm_sha1nexte_epu32(e0, e0_prev);
    *state = (_mm_add_epi32(abcd, abcd_prev), e0);
}

/// SHA-1 without the SHA extensions, structured as aws-lc's
/// `sha1_block_data_order_avx2`: AVX2 computes the message schedule of two
/// blocks at once, one per 128-bit lane, while scalar code runs the rounds of
/// the pair before.
pub(in crate::low) fn sha1_compress_blocks_avx2(
    state: &mut [u32; 5],
    blocks: &[u8],
    _token: super::cpu::HaveAvx2,
) {
    assert!(blocks.len().is_multiple_of(64));
    // SAFETY: `_token` proves the `avx2` and `bmi2` cpu features
    unsafe { sha1_avx2(state, blocks) }
}

#[target_feature(enable = "avx,avx2,bmi2")]
fn sha1_avx2(state: &mut [u32; 5], blocks: &[u8]) {
    let (blocks, _) = blocks.as_chunks::<64>();
    let (pairs, last) = blocks.as_chunks::<2>();

    // The blocks whose schedule fills `wk` for pair `i`. An odd last block
    // fills both lanes, and only its first runs.
    let input = |i: usize| match pairs.get(i) {
        Some([first, second]) => Some((first, second)),
        None if i == pairs.len() => last.first().map(|last| (last, last)),
        None => None,
    };

    let Some((first, second)) = input(0) else {
        return;
    };
    let (mut wk, mut wk_next) = (&mut [[0u32; 8]; 20], &mut [[0u32; 8]; 20]);
    let mut expander = Expander::new(wk, first, second);
    // Unrolled, so each step's group is a constant and `w` stays in registers.
    macro_rules! steps {
        ($($g:literal)*) => {
            $(expander.step($g);)*
        };
    }
    steps!(0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19);

    // Each pair's rounds compute the next pair's schedule, a group every
    // eight rounds, so the vector work overlaps the serial scalar rounds.
    for i in 0..pairs.len() {
        let mut next = input(i + 1).map(|(first, second)| Expander::new(wk_next, first, second));
        rounds::<0>(state, wk, |g| {
            if let Some(next) = &mut next
                && g % 2 == 1
            {
                next.step(g / 2);
            }
        });
        rounds::<4>(state, wk, |g| {
            if let Some(next) = &mut next
                && g % 2 == 1
            {
                next.step(10 + g / 2);
            }
        });
        core::mem::swap(&mut wk, &mut wk_next);
    }
    if !last.is_empty() {
        rounds::<0>(state, wk, |_| {});
    }
}

/// W[t] + K[t] for rounds `4g..4g + 4` of two blocks: the first block's in
/// words `0..4` of group `g`, the second's in `4..8`.
type Schedule = [[u32; 8]; 20];

/// Computes a pair's [`Schedule`] one group of four rounds at a time.
struct Expander<'a> {
    wk: &'a mut Schedule,
    first: &'a [u8; 64],
    second: &'a [u8; 64],
    /// W[4g..4g + 4] for each group `g` computed so far.
    w: [__m256i; 20],
}

impl<'a> Expander<'a> {
    #[inline]
    #[target_feature(enable = "avx,avx2")]
    fn new(wk: &'a mut Schedule, first: &'a [u8; 64], second: &'a [u8; 64]) -> Self {
        Self {
            wk,
            first,
            second,
            w: [_mm256_setzero_si256(); 20],
        }
    }

    /// Computes group `g`, after groups `0..g`. Every AVX2 op used here works
    /// within its 128-bit lane, so the two blocks never mix.
    #[inline]
    #[target_feature(enable = "avx,avx2")]
    fn step(&mut self, g: usize) {
        let w = &mut self.w;
        if g < 4 {
            // W[0..16] are the message's big-endian words.
            let byte_reverse = _mm256_set_epi64x(
                0x0c0d0e0f_08090a0b,
                0x04050607_00010203,
                0x0c0d0e0f_08090a0b,
                0x04050607_00010203,
            );
            // SAFETY: both blocks are 64 bytes, so bytes `16g..16g + 16` are readable
            let (lo, hi) = unsafe {
                (
                    _mm_loadu_si128(self.first[16 * g..].as_ptr().cast()),
                    _mm_loadu_si128(self.second[16 * g..].as_ptr().cast()),
                )
            };
            let words = _mm256_inserti128_si256::<1>(_mm256_castsi128_si256(lo), hi);
            w[g] = _mm256_shuffle_epi8(words, byte_reverse);
        } else if g < 8 {
            // W[t] = ROTL1(W[t-3] ^ W[t-8] ^ W[t-14] ^ W[t-16]) (FIPS 180-4,
            // 6.1.2). W[t+3] needs W[t] from this same group, so its W[t-3]
            // term starts as zero and is folded in after:
            // ROTL1(x ^ W[t]) = ROTL1(x) ^ ROTL2(x_0), where x_0 is lane 0's
            // value before rotating.
            let x = _mm256_xor_si256(
                _mm256_xor_si256(_mm256_srli_si256::<4>(w[g - 1]), w[g - 2]),
                _mm256_xor_si256(_mm256_alignr_epi8::<8>(w[g - 3], w[g - 4]), w[g - 4]),
            );
            let fix = _mm256_slli_si256::<12>(x);
            w[g] = _mm256_xor_si256(rotl::<1, 31>(x), rotl::<2, 30>(fix));
        } else {
            // From t = 32 the recurrence, applied to each of its own terms,
            // cancels to W[t] = ROTL2(W[t-6] ^ W[t-16] ^ W[t-28] ^ W[t-32]),
            // since W[t-11], W[t-17], W[t-19], W[t-22], W[t-24] and W[t-30]
            // each appear twice. Its nearest term is six back, so the four
            // lanes are independent. This is the schedule of Intel's
            // "Improving the Performance of the Secure Hash Algorithm (SHA-1)"
            // (Locktyukhin, 2010), which aws-lc also uses.
            let x = _mm256_xor_si256(
                _mm256_xor_si256(_mm256_alignr_epi8::<8>(w[g - 1], w[g - 2]), w[g - 4]),
                _mm256_xor_si256(w[g - 7], w[g - 8]),
            );
            w[g] = rotl::<2, 30>(x);
        }
        let k = _mm256_set1_epi32(K[g / 5] as i32);
        // SAFETY: `wk[g]` is 8 32-bit words, so 32 bytes are writable
        unsafe { _mm256_storeu_si256(self.wk[g].as_mut_ptr().cast(), _mm256_add_epi32(w[g], k)) };
    }
}

/// Rotates each 32-bit word left by `L`, where `R` is `32 - L`.
#[inline]
#[target_feature(enable = "avx,avx2")]
fn rotl<const L: i32, const R: i32>(x: __m256i) -> __m256i {
    _mm256_or_si256(_mm256_slli_epi32::<L>(x), _mm256_srli_epi32::<R>(x))
}

const K: [u32; 4] = [0x5a827999, 0x6ed9eba1, 0x8f1bbcdc, 0xca62c1d6];

/// The 80 rounds of FIPS 180-4, 6.1.2, for the block in words
/// `LANE..LANE + 4` of each group of `wk`, calling `then(g)` after group `g`.
#[inline]
fn rounds<const LANE: usize>(state: &mut [u32; 5], wk: &Schedule, mut then: impl FnMut(usize)) {
    let [mut a, mut b, mut c, mut d, mut e] = *state;

    // Round `$t`, with `$f` as f(b, c, d).
    macro_rules! round {
        ($f:ident, $t:literal) => {
            e = e
                .wrapping_add(a.rotate_left(5))
                .wrapping_add($f(b, c, d))
                .wrapping_add(wk[$t / 4][LANE + $t % 4]);
            (a, b, c, d, e) = (e, a, b.rotate_left(30), c, d);
            if $t % 4 == 3 {
                then($t / 4);
            }
        };
    }
    macro_rules! rounds {
        ($f:ident: $($t:literal)*) => {
            $(round!($f, $t);)*
        };
    }

    rounds!(ch: 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19);
    rounds!(parity: 20 21 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39);
    rounds!(maj: 40 41 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59);
    rounds!(parity: 60 61 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79);

    state[0] = state[0].wrapping_add(a);
    state[1] = state[1].wrapping_add(b);
    state[2] = state[2].wrapping_add(c);
    state[3] = state[3].wrapping_add(d);
    state[4] = state[4].wrapping_add(e);
}

#[inline(always)]
fn ch(b: u32, c: u32, d: u32) -> u32 {
    d ^ (b & (c ^ d))
}

#[inline(always)]
fn parity(b: u32, c: u32, d: u32) -> u32 {
    b ^ c ^ d
}

/// b where b and c agree, else d.
#[inline(always)]
fn maj(b: u32, c: u32, d: u32) -> u32 {
    ((b ^ c) & (c ^ d)) ^ c
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::low::x86_64::cpu::{HaveAvx2, HaveSha1};
    use crate::low::{ct, generic};

    const START: [u32; 5] = [0x67452301, 0xefcdab89, 0x98badcfe, 0x10325476, 0xc3d2e1f0];

    // The SHA extensions and AVX2 hide each other from every other test, so
    // each the CPU can run is checked against the portable code directly.
    #[test]
    fn paths_match_generic() {
        let blocks: Vec<u8> = (0..5 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        ct::secret_slice(&blocks);
        for n in 0..=5 {
            let blocks = &blocks[..n * 64];
            let mut wanted = START;
            generic::sha1::sha1_compress_blocks(&mut wanted, blocks);
            let wanted = ct::into_public(wanted);

            if let Some(token) = HaveSha1::check() {
                let mut got = START;
                sha1_compress_blocks_shaext(&mut got, blocks, token);
                assert_eq!(ct::into_public(got), wanted, "shaext, {n} blocks");
            }
            if let Some(token) = HaveAvx2::check() {
                let mut got = START;
                sha1_compress_blocks_avx2(&mut got, blocks, token);
                assert_eq!(ct::into_public(got), wanted, "avx2, {n} blocks");
            }
        }
    }

    // Every length up to three blocks, so every place the padding can fall
    // after zero to two whole blocks, with bytes past the message that must
    // not count.
    #[test]
    fn padded_matches_generic() {
        let Some(token) = HaveSha1::check() else {
            return;
        };
        let bytes: Vec<u8> = (0..4 * 64u32)
            .map(|i| (i.wrapping_mul(0x9e3779b9) >> 24) as u8)
            .collect();
        let length = 0x0102030405060708u64.to_be_bytes();
        for len in 0..=3 * 64 {
            let message = &bytes[..len];
            let (blocks, rest) = crate::low::split_tail::<64, 8>(message);
            let mut wanted = START;
            generic::sha1::sha1_compress_blocks(&mut wanted, blocks);
            let mut padded = [[0u8; 64]; 2];
            let padded = crate::low::pad(rest, length, &mut padded);
            generic::sha1::sha1_compress_blocks(&mut wanted, padded);
            let mut got = START;
            sha1_compress_padded_shaext(&mut got, message, length, token);
            assert_eq!(got, wanted, "{len} bytes");
        }
    }
}
