// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! `poly1305_32`'s aligned word load, in a file of its own: that file's debug
//! checks may not sit beside `unsafe` (`low::tests`).

/// `bytes` as words, when it starts on a word and is whole words: Xtensa has
/// no misaligned load, so a block loads as words only then. Where `bytes`
/// starts is public.
#[inline(always)]
pub(super) fn aligned(bytes: &[u8]) -> Option<&[u32]> {
    // SAFETY: every bit pattern is a `u32`, so aligned bytes may be read as
    // words.
    let (head, words, tail) = unsafe { bytes.align_to::<u32>() };
    (head.is_empty() && tail.is_empty()).then_some(words)
}
