// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! `expand_message_xmd` (RFC 9380, section 5.3.1) over rind's SHA-2.
//!
//! A domain separation tag longer than 255 bytes is replaced first, as section
//! 5.3.3 requires: `H("H2C-OVERSIZE-DST-" || DST)`. The tag is not truncated.
//! An empty tag is refused: section 3.1 requires a nonzero length, and hashing
//! it would turn the refusal into a different tag.

use crate::low::Entry;
use crate::mid::sha2::{Sha256Context, Sha384Context, Sha512Context};

/// Why `expand_message_xmd` refused its inputs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExpandError {
    /// The domain separation tag was empty.
    EmptyDst,
    /// The requested length was above 65535 bytes, or needed more than 255 hash blocks.
    OutputLength,
}

const OVERSIZE_DST_PREFIX: &[u8] = b"H2C-OVERSIZE-DST-";
const ZEROS: [u8; 128] = [0u8; 128];

trait XmdHash {
    const BLOCK: usize;
    const OUT: usize;

    fn hash(parts: &[&[u8]]) -> [u8; 64];
}

struct Sha256;
struct Sha384;
struct Sha512;

impl XmdHash for Sha256 {
    const BLOCK: usize = Sha256Context::BLOCK_SZ;
    const OUT: usize = Sha256Context::OUTPUT_SZ;

    fn hash(parts: &[&[u8]]) -> [u8; 64] {
        let _entry = Entry::new_secret();
        let mut ctx = Sha256Context::new();
        for part in parts {
            ctx.update(part);
        }
        let digest = ctx.finish();
        let mut out = [0u8; 64];
        out[..Self::OUT].copy_from_slice(&digest);
        out
    }
}

impl XmdHash for Sha384 {
    const BLOCK: usize = Sha512Context::BLOCK_SZ;
    const OUT: usize = Sha384Context::OUTPUT_SZ;

    fn hash(parts: &[&[u8]]) -> [u8; 64] {
        let _entry = Entry::new_secret();
        let mut ctx = Sha384Context::new();
        for part in parts {
            ctx.update(part);
        }
        let digest = ctx.finish();
        let mut out = [0u8; 64];
        out[..Self::OUT].copy_from_slice(&digest);
        out
    }
}

impl XmdHash for Sha512 {
    const BLOCK: usize = Sha512Context::BLOCK_SZ;
    const OUT: usize = Sha512Context::OUTPUT_SZ;

    fn hash(parts: &[&[u8]]) -> [u8; 64] {
        let _entry = Entry::new_secret();
        let mut ctx = Sha512Context::new();
        for part in parts {
            ctx.update(part);
        }
        ctx.finish()
    }
}

/// `expand_message_xmd` with SHA-256. `out.len()` is `len_in_bytes`.
pub(in crate::mid) fn expand_sha256(
    msg: &[u8],
    dst: &[u8],
    out: &mut [u8],
) -> Result<(), ExpandError> {
    expand::<Sha256>(msg, dst, out)
}

/// `expand_message_xmd` with SHA-384. `out.len()` is `len_in_bytes`.
pub(in crate::mid) fn expand_sha384(
    msg: &[u8],
    dst: &[u8],
    out: &mut [u8],
) -> Result<(), ExpandError> {
    expand::<Sha384>(msg, dst, out)
}

/// `expand_message_xmd` with SHA-512. `out.len()` is `len_in_bytes`.
pub(in crate::mid) fn expand_sha512(
    msg: &[u8],
    dst: &[u8],
    out: &mut [u8],
) -> Result<(), ExpandError> {
    expand::<Sha512>(msg, dst, out)
}

fn expand<H: XmdHash>(msg: &[u8], dst: &[u8], out: &mut [u8]) -> Result<(), ExpandError> {
    if dst.is_empty() {
        return Err(ExpandError::EmptyDst);
    }
    let len = out.len();
    if len > 65535 {
        return Err(ExpandError::OutputLength);
    }
    // A loop, not a division: SHA-384's 48-byte output is not a power of two,
    // and a division's time can depend on its operands.
    let ell = block_count(len, H::OUT);
    if ell > 255 {
        return Err(ExpandError::OutputLength);
    }
    // A zero length is an empty substring of the blocks the RFC still hashes
    // and then discards. The returned bytes are empty either way.
    if len == 0 {
        return Ok(());
    }

    // Section 5.3.3 replaces a tag the primitive would abort on. The length
    // is public, so the branch does not depend on a secret.
    let hashed;
    let dst = if dst.len() > 255 {
        hashed = H::hash(&[OVERSIZE_DST_PREFIX, dst]);
        &hashed[..H::OUT]
    } else {
        dst
    };
    let dst_len = u8::try_from(dst.len()).expect("DST is at most one hash output");
    let lib = u16::try_from(len).expect("len fits in two bytes");
    let lib = lib.to_be_bytes();
    // l_i_b_str || I2OSP(0, 1), the counter of b_0.
    let lib_and_zero = [lib[0], lib[1], 0];

    let b0 = H::hash(&[&ZEROS[..H::BLOCK], msg, &lib_and_zero, dst, &[dst_len]]);
    let mut prev = H::hash(&[&b0[..H::OUT], &[1], dst, &[dst_len]]);
    let mut at = write_block(out, 0, &prev[..H::OUT]);
    for i in 2..=ell {
        let mut mixed = [0u8; 64];
        for j in 0..H::OUT {
            mixed[j] = b0[j] ^ prev[j];
        }
        let counter = u8::try_from(i).expect("ell is at most 255");
        prev = H::hash(&[&mixed[..H::OUT], &[counter], dst, &[dst_len]]);
        at += write_block(out, at, &prev[..H::OUT]);
    }
    debug_assert_eq!(at, len);
    Ok(())
}

fn block_count(len: usize, block: usize) -> usize {
    let mut count = 0;
    let mut covered = 0;
    while covered < len {
        covered += block;
        count += 1;
    }
    count
}

fn write_block(out: &mut [u8], at: usize, block: &[u8]) -> usize {
    let n = block.len().min(out.len() - at);
    out[at..at + n].copy_from_slice(&block[..n]);
    n
}
