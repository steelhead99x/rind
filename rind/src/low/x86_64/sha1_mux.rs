// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::sync::atomic::AtomicU8;

use crate::low::x86_64;
use crate::low::x86_64::cpu::{HaveAvx, HaveAvx2, HaveSha1, HaveSsse3, cached_tag, is_intel};
use crate::low::{pad, split_tail};

/// The SHA-1 routine this CPU runs, with the proof it may.
#[derive(Clone, Copy)]
enum Path {
    Shaext(HaveSha1),
    Avx2(HaveAvx2),
    Avx(HaveAvx),
    Ssse3(HaveSsse3),
    Nohw,
}

pub(crate) fn sha1_compress_blocks(state: &mut [u32; 5], blocks: &[u8]) {
    match path() {
        Path::Shaext(token) => x86_64::sha1::sha1_compress_blocks_shaext(state, blocks, token),
        Path::Avx2(token) => x86_64::sha1::sha1_compress_blocks_avx2(state, blocks, token),
        Path::Avx(token) => x86_64::sha1::sha1_compress_blocks_avx(state, blocks, token),
        Path::Ssse3(token) => x86_64::sha1::sha1_compress_blocks_ssse3(state, blocks, token),
        Path::Nohw => x86_64::sha1::sha1_compress_blocks_nohw(state, blocks),
    }
}

/// Compresses the end of `message`, padded and closed by `length`.
// Out of line, so `Sha1State::finish_with` stays small enough to inline and
// write the digest where its caller keeps it. Out of line itself, it returns
// the digest through memory, and its caller's copy into a `Digest` loads
// across its stores, which misses store forwarding.
#[inline(never)]
pub(crate) fn sha1_compress_padded(state: &mut [u32; 5], message: &[u8], length: [u8; 8]) {
    match path() {
        Path::Shaext(token) => {
            x86_64::sha1::sha1_compress_padded_shaext(state, message, length, token)
        }
        _ => {
            let (blocks, rest) = split_tail::<64, 8>(message);
            if !blocks.is_empty() {
                sha1_compress_blocks(state, blocks);
            }
            let mut last = [[0u8; 64]; 2];
            sha1_compress_blocks(state, pad(rest, length, &mut last));
        }
    }
}

fn path() -> Path {
    // Picked once, rather than testing up to four features on every compression.
    // An atomic, not `OnceLock`: this file also builds for `x86_64-unknown-none`.
    static PATH: AtomicU8 = AtomicU8::new(0);
    match cached_tag(&PATH, || match pick() {
        Path::Shaext(_) => 1,
        Path::Avx2(_) => 2,
        Path::Avx(_) => 3,
        Path::Ssse3(_) => 4,
        Path::Nohw => 5,
    }) {
        1 => Path::Shaext(HaveSha1::cached()),
        2 => Path::Avx2(HaveAvx2::cached()),
        3 => Path::Avx(HaveAvx::cached()),
        4 => Path::Ssse3(HaveSsse3::cached()),
        _ => Path::Nohw,
    }
}

fn pick() -> Path {
    if let Some(token) = HaveSha1::check() {
        Path::Shaext(token)
    } else if let Some(token) = HaveAvx2::check() {
        Path::Avx2(token)
    } else if let Some(token) = HaveAvx::check().filter(|_| is_intel()) {
        Path::Avx(token)
    } else if let Some(token) = HaveSsse3::check() {
        Path::Ssse3(token)
    } else {
        Path::Nohw
    }
}
