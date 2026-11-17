// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use std::sync::OnceLock;

use crate::low::generic;
use crate::low::x86_64;
use crate::low::x86_64::cpu::{HaveAvx2, HaveSha1};
use crate::low::{pad, split_tail};

/// The SHA-1 routine this CPU runs, with the proof it may.
#[derive(Clone, Copy)]
enum Path {
    Shaext(HaveSha1),
    Avx2(HaveAvx2),
    Generic,
}

pub(crate) fn sha1_compress_blocks(state: &mut [u32; 5], blocks: &[u8]) {
    match path() {
        Path::Shaext(token) => x86_64::sha1::sha1_compress_blocks_shaext(state, blocks, token),
        Path::Avx2(token) => x86_64::sha1::sha1_compress_blocks_avx2(state, blocks, token),
        Path::Generic => generic::sha1::sha1_compress_blocks(state, blocks),
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
    static PATH: OnceLock<Path> = OnceLock::new();
    *PATH.get_or_init(pick)
}

fn pick() -> Path {
    if let Some(token) = HaveSha1::check() {
        Path::Shaext(token)
    } else if let Some(token) = HaveAvx2::check() {
        Path::Avx2(token)
    } else {
        Path::Generic
    }
}
