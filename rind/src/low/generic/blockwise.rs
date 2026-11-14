// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

#[derive(Clone)]
pub(crate) struct Blockwise<const N: usize> {
    buffer: [u8; N],
    used: usize,
}

impl<const N: usize> Blockwise<N> {
    pub(crate) const fn new() -> Self {
        Self {
            buffer: [0u8; N],
            used: 0,
        }
    }

    /// Stores one byte when the buffer has room. Returns false when the
    /// buffer already holds a whole block, so the caller runs [`Self::update`].
    ///
    /// SHA-256's one-byte update uses this. A store stays in the caller;
    /// the general path calls memcpy.
    #[inline(always)]
    pub(crate) fn absorb_byte(&mut self, byte: u8) -> bool {
        if self.used < N {
            self.buffer[self.used] = byte;
            self.used += 1;
            true
        } else {
            false
        }
    }

    /// Copies 16 bytes when they fit. Returns false when they don't.
    ///
    /// The length is the public input length. SHA-256's 16-byte update uses
    /// this so the copy is a fixed 16, which stays inline.
    #[inline(always)]
    pub(crate) fn absorb_sixteen(&mut self, bytes: &[u8]) -> bool {
        let used = self.used;
        if bytes.len() == 16 && used + 16 <= N {
            // SAFETY: `used + 16 <= N`, so the bytes land in the buffer, and
            // `bytes` has 16 bytes. The length is public.
            unsafe {
                core::ptr::copy_nonoverlapping(
                    bytes.as_ptr(),
                    self.buffer.as_mut_ptr().add(used),
                    16,
                );
            }
            self.used = used + 16;
            true
        } else {
            false
        }
    }

    /// Adds `bytes`, passing each run of whole blocks to `state` in order and
    /// holding the rest: what is short of a whole block, or the last whole
    /// block until more follows, so a hash can compress it with its padding
    /// in one call.
    pub(crate) fn update(&mut self, bytes: &[u8], state: &mut impl UpdateBlocks) {
        let used = self.used;
        // A short update, such as a one-byte one, only copies. Storing
        // `used` first, and leaving blocks to another function, lets it
        // save no registers and tail-call the copy.
        if bytes.len() <= N - used {
            self.used = used + bytes.len();
            self.buffer[used..used + bytes.len()].copy_from_slice(bytes);
        } else {
            self.complete_blocks(bytes, state);
        }
    }

    /// As [`Self::update`], for `bytes` longer than the room left.
    #[inline(never)]
    fn complete_blocks(&mut self, mut bytes: &[u8], state: &mut impl UpdateBlocks) {
        let used = self.used;
        if used > 0 {
            let (head, rest) = bytes.split_at(N - used);
            self.buffer[used..].copy_from_slice(head);
            state.update_blocks(&self.buffer);
            bytes = rest;
        }

        // Holds the last 1 to N bytes.
        let (whole, rest) = bytes.split_at((bytes.len() - 1) / N * N);
        if !whole.is_empty() {
            state.update_blocks(whole);
        }
        self.buffer[..rest.len()].copy_from_slice(rest);
        self.used = rest.len();
    }

    // Only Poly1305 uses it.
    #[cfg(any(
        rind_backend = "x86_64",
        all(rind_backend = "portable", target_pointer_width = "64"),
        all(rind_backend = "aarch64", test)
    ))]
    pub(crate) fn add_leading<'a>(&mut self, bytes: &'a [u8]) -> &'a [u8] {
        if self.used == 0 {
            return bytes;
        }

        let space = N - self.used;
        let take = core::cmp::min(bytes.len(), space);
        let (taken, returned) = bytes.split_at(take);
        self.buffer[self.used..self.used + take].copy_from_slice(taken);
        self.used += take;
        returned
    }

    // Only Poly1305 uses it.
    #[cfg(any(
        rind_backend = "x86_64",
        all(rind_backend = "portable", target_pointer_width = "64"),
        all(rind_backend = "aarch64", test)
    ))]
    pub(crate) fn take(&mut self) -> Option<[u8; N]> {
        if self.used == N {
            self.used = 0;
            Some(self.buffer)
        } else {
            None
        }
    }

    // Only Poly1305's tail reads it.
    #[cfg(any(
        rind_backend = "x86_64",
        all(rind_backend = "portable", target_pointer_width = "64"),
        all(rind_backend = "aarch64", test)
    ))]
    pub(crate) fn peek_remaining(&self) -> Option<&[u8]> {
        if self.used > 0 {
            Some(&self.buffer[..self.used])
        } else {
            None
        }
    }

    /// The bytes [`Self::update`] holds, up to one whole block.
    pub(crate) fn buffered(&self) -> &[u8] {
        &self.buffer[..self.used]
    }

    // Only Poly1305 uses it.
    #[cfg(any(
        rind_backend = "x86_64",
        all(rind_backend = "portable", target_pointer_width = "64"),
        all(rind_backend = "aarch64", test)
    ))]
    pub(crate) fn add_trailing(&mut self, trailing: &[u8]) {
        self.buffer[..trailing.len()].copy_from_slice(trailing);
        self.used += trailing.len();
    }
}

/// A hash's chaining value, which [`Blockwise::update`] passes whole blocks.
///
/// A trait rather than a closure, which Aeneas cannot translate when it
/// borrows the state mutably, so `proofs/` can prove SHA-512.
pub(crate) trait UpdateBlocks {
    /// Adds `blocks`, a whole number of blocks, to the hash computation.
    fn update_blocks(&mut self, blocks: &[u8]);
}

/// Splits the end of `message`, for a Merkle-Damgard hash of `N`-byte blocks
/// closed by an `L`-byte length: the whole blocks to compress first, then the
/// rest, under two blocks, for [`pad`]. Where the padding fits after the
/// message's last whole block, the rest takes that block too, so one call
/// compresses both, and the routine's entry and exit and the chaining value's
/// trip through memory come once fewer.
pub(crate) fn split_tail<const N: usize, const L: usize>(message: &[u8]) -> (&[u8], &[u8]) {
    let tail = message.len() % N;
    let start = if tail + 1 + L <= N && message.len() >= N {
        message.len() - tail - N
    } else {
        message.len() - tail
    };
    message.split_at(start)
}

/// `rest`, under two blocks, padded in `last`, which must be zeroed.
pub(crate) fn pad<'l, const N: usize, const L: usize>(
    rest: &[u8],
    length: [u8; L],
    last: &'l mut [[u8; N]; 2],
) -> &'l [u8] {
    let padded = if rest.len() % N + 1 + L <= N {
        rest.len() / N * N + N
    } else {
        rest.len() / N * N + 2 * N
    };
    let last = &mut last.as_flattened_mut()[..padded];
    last[..rest.len()].copy_from_slice(rest);
    last[rest.len()] = 0x80;
    last[padded - L..].copy_from_slice(&length);
    last
}

/// SHA-256's digest of its chaining value `h`: each word, big-endian.
// Indexes rather than zipping `as_chunks_mut`, which Aeneas cannot translate,
// so `proofs/` can prove the encoding. Inline, so the digest is written where
// its caller keeps it, rather than returned through memory a copy then loads.
#[inline(always)]
pub(crate) fn sha256_digest(h: &[u32; 8]) -> [u8; 32] {
    let mut r = [0u8; 32];
    for (i, word) in h.iter().enumerate() {
        r[i * 4..(i + 1) * 4].copy_from_slice(&word.to_be_bytes());
    }
    r
}
