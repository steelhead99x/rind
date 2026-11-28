//! What the bench targets share: the inputs their rows take, and the DIT
//! guard rind's rows hold.
//!
//! A benchmark's name is its file, then its modules, its function, and its
//! argument, as swole names it: `rind-bench/benches/sha2.rs::sha256::rind[32B]`.
//! `admin/bench-report` and the weekly bench read each as an ID, the path after
//! the file with `/` for `::` and `-` for `_`, then the argument:
//! `sha256/rind/32B`. So a module is an operation, or a part of one, and a
//! function a library, unless a row's ID puts it elsewhere.

#![allow(dead_code)]

use std::fmt;
use std::ops::{Deref, DerefMut};

/// A message length, shown as its rows show it, such as `1350B`.
#[derive(Clone, Copy, Debug)]
pub struct Size {
    pub len: usize,
    name: &'static str,
}

impl Size {
    pub const fn new(len: usize, name: &'static str) -> Self {
        Self { len, name }
    }

    /// A zeroed buffer of this length.
    pub fn zeros(self) -> Vec<u8> {
        vec![0; self.len]
    }
}

impl fmt::Display for Size {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name)
    }
}

/// Message sizes for ciphers and AEADs: a short token, QUIC datagrams at and
/// near the common 1200- and 1350-byte MTUs, and a full TLS record.
pub const SIZES: [Size; 4] = [
    Size::new(32, "32B"),
    Size::new(1200, "1200B"),
    Size::new(1350, "1350B"),
    Size::new(16384, "16KB"),
];

/// [`SIZES`], plus one hash block and a file-sized input, for hashes and MACs.
pub const HASH_SIZES: [Size; 6] = [
    Size::new(32, "32B"),
    Size::new(64, "64B"),
    Size::new(1200, "1200B"),
    Size::new(1350, "1350B"),
    Size::new(8192, "8KB"),
    Size::new(16384, "16KB"),
];

/// One AEAD row: a message length and the AAD it is sealed under.
#[derive(Clone, Copy, Debug)]
pub struct Aead {
    pub size: Size,
    pub aad: &'static [u8],
}

impl Aead {
    pub const fn new(len: usize, name: &'static str, aad: &'static [u8]) -> Self {
        Self {
            size: Size::new(len, name),
            aad,
        }
    }

    pub fn len(self) -> usize {
        self.size.len
    }
}

impl fmt::Display for Aead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.size.fmt(f)
    }
}

/// A TLS record's AAD length, which the sized rows seal under.
pub const AAD: &[u8] = &[0; 32];

/// QUIC's short-header AAD length.
pub const QUIC_AAD: &[u8] = &[0; 13];

/// The AEAD benches' rows: each of [`SIZES`] under a 32 B AAD, then lengths
/// between the 64 B and 1200 B the other rows time, where rind's AEADs switch
/// kernels, under QUIC's 13 B short-header AAD, so a threshold set wrong for
/// a CPU shows only here.
pub const AEAD_ROWS: [Aead; 7] = [
    Aead::new(32, "32B", AAD),
    Aead::new(1200, "1200B", AAD),
    Aead::new(1350, "1350B", AAD),
    Aead::new(16384, "16KB", AAD),
    Aead::new(128, "quic-128B", QUIC_AAD),
    Aead::new(256, "quic-256B", QUIC_AAD),
    Aead::new(512, "quic-512B", QUIC_AAD),
];

/// The [`AEAD_ROWS`] a `dit_per_call` module times: a short token and a QUIC
/// packet, where the toggle is the largest and a typical share of a call.
pub const DIT_PER_CALL_AEAD_ROWS: [Aead; 2] = [AEAD_ROWS[0], AEAD_ROWS[2]];

/// rind's input, built with a [`rind::cpu::Dit`] guard its calls run under:
/// on a CPU with DIT, the report times rind as a caller holding it across its
/// calls, as MoQ does. Elsewhere the guard does nothing.
///
/// rind's rows are timed again without it, in a `dit_per_call` module on
/// aarch64 alone, the one architecture with DIT, so the report shows what a
/// caller holding no guard pays for rind setting DIT around each call. Where
/// the OS reports no DIT, as on GitHub's arm64 runners, they match the held
/// rows.
pub struct Dit<T> {
    input: T,
    _guard: rind::cpu::Dit,
}

impl<T> Dit<T> {
    /// Holds DIT on this thread, which runs the benchmark's calls, until the
    /// input drops.
    pub fn hold(input: T) -> Self {
        Self {
            _guard: rind::cpu::Dit::hold(),
            input,
        }
    }
}

/// The setup of a rind row with no input of its own: only the guard.
pub fn dit() -> Dit<()> {
    Dit::hold(())
}

impl<T> Deref for Dit<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.input
    }
}

impl<T> DerefMut for Dit<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.input
    }
}

/// Times `call`, `iterations` times, inside `verified_garbage::dit::scope`,
/// which holds DIT across the calls as [`Dit`] does for rind's rows: a
/// `verified_garbage_dit_held` row, beside a `verified_garbage` row whose call
/// verified-garbage sets DIT around itself on an aarch64 CPU with DIT, as it
/// does for its MACs, AEADs, and ciphers. Its unkeyed hashes never set DIT, so
/// they take no pair. Where the CPU has no DIT the two rows time the same.
#[cfg(target_arch = "aarch64")]
pub fn vg_dit_held<O>(
    iterations: swole::Iterations,
    mut call: impl FnMut() -> O,
) -> std::time::Duration {
    verified_garbage::dit::scope(|| {
        let start = std::time::Instant::now();
        for _ in iterations {
            std::hint::black_box(call());
        }
        start.elapsed()
    })
}
