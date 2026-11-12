// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The last block of a SHA-1 message, padded in registers.
//!
//! Padding in memory writes the 0x80 and the length with stores narrower
//! than the routines' 16-byte loads of them, which cannot forward, so the
//! loads wait for the stores to retire: on Zen 3, half of a 32-byte SHA-1.

use core::arch::x86_64::*;

/// The lanes of the padded last block of a message whose bytes past its
/// whole blocks are `tail`, under 64 bytes, closed by `length`, and those of
/// the block after it when the padding does not fit. A longer `tail` hashes
/// wrongly but reads only its own bytes, so it goes unchecked: a check here
/// slowed a one-block SHA-256 by a seventh.
///
/// Reads `tail` where it is, a whole lane at a time and the rest in loads of
/// 8, 4, 2, and 1 bytes from the lane's start, so each load is likely to lie
/// within one store its writer made, and forward from it.
// Inline, so the lanes stay in registers rather than return through memory.
#[inline(always)]
pub(super) fn padded_tail(tail: &[u8], length: [u8; 8]) -> ([__m128i; 4], Option<[__m128i; 4]>) {
    let lane = |at: usize| {
        if at + 16 <= tail.len() {
            // SAFETY: bytes `at..at + 16` of `tail` are readable
            unsafe { _mm_loadu_si128(tail[at..].as_ptr().cast()) }
        } else if at <= tail.len() {
            ended(&tail[at..])
        } else {
            // SAFETY: SSE2 is part of x86_64
            unsafe { _mm_setzero_si128() }
        }
    };
    let mut last = [lane(0), lane(16), lane(32), lane(48)];

    // SAFETY: SSE2 is part of x86_64
    unsafe {
        // The length's bytes, as the block's last eight.
        let length = _mm_set_epi64x(i64::from_le_bytes(length), 0);
        if tail.len() + 1 + 8 <= 64 {
            last[3] = _mm_or_si128(last[3], length);
            (last, None)
        } else {
            let zero = _mm_setzero_si128();
            (last, Some([zero, zero, zero, length]))
        }
    }
}

/// `part`, under 16 bytes, then the 0x80 that ends a message, as a lane.
#[inline(always)]
fn ended(part: &[u8]) -> __m128i {
    let (first, rest) = match part.split_first_chunk::<8>() {
        Some((first, rest)) => (Some(u64::from_le_bytes(*first)), rest),
        None => (None, part),
    };
    let mut word = 0x80 << (8 * rest.len());
    let mut at = 0;
    if rest.len() & 4 != 0 {
        word |= u64::from(u32::from_le_bytes(rest[..4].try_into().unwrap()));
        at = 4;
    }
    if rest.len() & 2 != 0 {
        word |= u64::from(u16::from_le_bytes(rest[at..at + 2].try_into().unwrap())) << (8 * at);
        at += 2;
    }
    if rest.len() & 1 != 0 {
        word |= u64::from(rest[at]) << (8 * at);
    }
    // SAFETY: SSE2 is part of x86_64
    unsafe {
        match first {
            Some(first) => _mm_set_epi64x(word as i64, first as i64),
            None => _mm_set_epi64x(0, word as i64),
        }
    }
}
