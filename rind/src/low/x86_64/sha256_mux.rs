// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use std::sync::OnceLock;

use crate::low::generic;
use crate::low::x86_64;
use crate::low::x86_64::cpu::HaveSha256;
use crate::low::{pad, sha256_digest, split_tail};

/// The SHA-256 routine this CPU runs, with the proof it may.
#[derive(Clone, Copy)]
enum Path {
    Shaext(HaveSha256),
    Generic,
}

pub(crate) fn sha256_compress_blocks(state: &mut [u32; 8], blocks: &[u8]) {
    match path() {
        Path::Shaext(token) => x86_64::sha256::sha256_compress_blocks_shaext(state, blocks, token),
        Path::Generic => generic::sha256::sha256_compress_blocks(state, blocks),
    }
}

/// The digest of `state` followed by `message`, padded and closed by `length`.
// Out of line, so `finish_with` stays small enough to inline.
#[inline(never)]
pub(crate) fn sha256_finish(state: &[u32; 8], message: &[u8], length: [u8; 8]) -> [u8; 32] {
    let mut h = *state;
    sha256_compress_padded(&mut h, message, length);
    sha256_digest(&h)
}

/// Compresses the end of `message`, padded and closed by `length`.
fn sha256_compress_padded(state: &mut [u32; 8], message: &[u8], length: [u8; 8]) {
    let (blocks, rest) = split_tail::<64, 8>(message);
    if !blocks.is_empty() {
        sha256_compress_blocks(state, blocks);
    }
    let mut last = [[0u8; 64]; 2];
    sha256_compress_blocks(state, pad(rest, length, &mut last));
}

fn path() -> Path {
    // Picked once, rather than testing the feature on every compression.
    static PATH: OnceLock<Path> = OnceLock::new();
    *PATH.get_or_init(pick)
}

fn pick() -> Path {
    match HaveSha256::check() {
        Some(token) => Path::Shaext(token),
        None => Path::Generic,
    }
}
