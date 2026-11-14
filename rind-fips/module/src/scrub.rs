// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Zeroization of what a service leaves on the stack: every SSP that lives
//! only inside a call, such as an ECDSA nonce, an expanded AES key, or
//! HMAC's padded key blocks, and every copy a move leaves behind.
//!
//! A service runs in a frame of its own, below its entry point's, and
//! returns only codes and handles; the entry point then zeroes the stack
//! below itself as deep as the service can reach. The break build checks
//! that depth on every call (see [`scrubbed`]).
//!
//! A service's self-tests run before its scrubbed region: their inputs are
//! public, and their frames, deeper than most services', would otherwise set
//! its depth.

use core::mem::MaybeUninit;

/// How deep a service's stack reaches, rounded up to a size the break
/// build has checked it stays within.
#[derive(Clone, Copy)]
pub(crate) enum Depth {
    /// Hashing, MACs, KDFs, and the AES modes.
    Small,
    /// Elliptic curves, the DRBG, and parsing keys.
    Medium,
    /// RSA, ML-KEM, and ML-DSA.
    Large,
}

impl Depth {
    const fn bytes(self) -> usize {
        match self {
            Self::Small => 8 << 10,
            Self::Medium => 32 << 10,
            Self::Large => 160 << 10,
        }
    }
}

/// Runs `service` in a frame of its own, then zeroes `depth` of the stack
/// below the caller's frame.
///
/// The break build checks each call: it paints the stack below before the
/// service runs, finds the lowest byte the service wrote, and aborts if
/// that lies below what the zeroing covered.
#[inline(always)]
pub(crate) fn scrubbed<R>(depth: Depth, service: impl FnOnce() -> R) -> R {
    #[cfg(rind_fips_break)]
    let painted = stack::<{ PAINTED / 8 }>(Op::Paint);
    let result = run(service);
    #[cfg(rind_fips_break)]
    let lowest = lowest_written(painted);
    let zeroed = match depth {
        Depth::Small => stack::<{ Depth::Small.bytes() / 8 }>(Op::Zero),
        Depth::Medium => stack::<{ Depth::Medium.bytes() / 8 }>(Op::Zero),
        Depth::Large => stack::<{ Depth::Large.bytes() / 8 }>(Op::Zero),
    };
    #[cfg(rind_fips_break)]
    if lowest < zeroed {
        std::eprintln!(
            "rind-fips: a service wrote {} bytes of stack below the {} it zeroes",
            zeroed - lowest,
            depth.bytes()
        );
        std::process::abort();
    }
    #[cfg(not(rind_fips_break))]
    let _ = zeroed;
    result
}

#[inline(never)]
fn run<R>(service: impl FnOnce() -> R) -> R {
    service()
}

/// How much stack the break build paints below the caller: more than any
/// [`Depth`], so a service that outgrows its tier shows.
#[cfg(rind_fips_break)]
const PAINTED: usize = 256 << 10;

#[cfg(rind_fips_break)]
const PAINT: u64 = 0xa5a5_a5a5_a5a5_a5a5;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Op {
    Zero,
    #[cfg(rind_fips_break)]
    Paint,
}

/// Zeroes or paints the `WORDS` 8-byte words of stack below the caller,
/// returning their lowest address. Called from one place for each size, so
/// its frame lands where the service's did.
#[inline(never)]
fn stack<const WORDS: usize>(op: Op) -> usize {
    let mut frame = MaybeUninit::<[u64; WORDS]>::uninit();
    let words = frame.as_mut_ptr().cast::<u64>();
    let byte = match op {
        Op::Zero => 0,
        #[cfg(rind_fips_break)]
        Op::Paint => PAINT as u8,
    };
    // SAFETY: `frame` is `WORDS` writable words.
    unsafe { core::ptr::write_bytes(words.cast::<u8>(), byte, WORDS * 8) };
    // Keeps the compiler from dropping the writes as dead.
    // SAFETY: an empty instruction sequence, which may read `words`.
    unsafe {
        core::arch::asm!("/* {0} */", in(reg) words, options(nostack, readonly, preserves_flags));
    }
    words as usize
}

/// The lowest address the service wrote within the `PAINTED` bytes from
/// `bottom`: stacks grow down, so the first word up from the bottom that is
/// not paint.
///
/// It reads those bytes in place from a small frame above them, since a
/// large frame's stack probes would write over the paint.
#[cfg(rind_fips_break)]
#[inline(never)]
fn lowest_written(bottom: usize) -> usize {
    let untouched = (0..PAINTED / 8)
        .take_while(|&i| dead_word(bottom + 8 * i) == PAINT)
        .count();
    bottom + 8 * untouched
}

/// The word at `address`, in stack no live frame holds. Rust has no
/// defined way to reach memory whose allocation has ended, so the load and
/// its address arithmetic are assembly, which the compiler cannot elide.
#[cfg(rind_fips_break)]
fn dead_word(address: usize) -> u64 {
    let word: u64;
    // SAFETY: `address` is word-aligned stack that `stack` painted, so it
    // is mapped, and the load writes nothing.
    unsafe {
        #[cfg(target_arch = "x86_64")]
        core::arch::asm!(
            "mov {word}, qword ptr [{address}]",
            address = in(reg) address,
            word = lateout(reg) word,
            options(nostack, readonly, preserves_flags),
        );
        #[cfg(target_arch = "aarch64")]
        core::arch::asm!(
            "ldr {word}, [{address}]",
            address = in(reg) address,
            word = lateout(reg) word,
            options(nostack, readonly, preserves_flags),
        );
    }
    word
}
