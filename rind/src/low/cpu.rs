// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::cell::Cell;
use core::marker::PhantomData;

/// Reports whether rind runs AES on CPU instructions, as aws-lc's `EVP_has_aes_hardware` does.
///
/// Where it doesn't, ChaCha20-Poly1305 is faster than AES-GCM, so a protocol
/// that negotiates between them should prefer it.
#[must_use]
pub fn has_aes_hardware() -> bool {
    #[cfg(any(rind_backend = "arm", rind_backend = "aarch64"))]
    return super::HaveCryptoExt::check().is_some();
    #[cfg(rind_backend = "x86_64")]
    return super::x86_64::cpu::HaveAesHardware::check().is_some();
    #[cfg(rind_backend = "portable")]
    return false;
}

/// Holds data-independent timing (DIT) on for this thread until dropped.
///
/// On Apple's platforms, every rind call that handles a secret runs with DIT,
/// turning it on at entry and back off on return. On Apple's M1 that costs
/// about 55 ns a call, a fifth of sealing a 1350-byte QUIC packet, so
/// holding a guard across a batch of calls pays it once instead, for calls
/// made directly or through an adapter such as rind-rustls. Everywhere else
/// rind sets no DIT, and the guard does nothing.
///
/// Everything the thread runs while a guard is held runs with DIT, rind's
/// code or not. DIT stays on until the thread's last guard drops, in
/// whatever order they drop, and then turns off only if the first guard
/// found it off.
///
/// ```
/// use rind::aead::{AES_128_GCM, Key, Nonce};
///
/// let key = Key::new(&AES_128_GCM, &[0x42; 16]).unwrap();
/// let mut packets = [[0u8; 1200]; 4];
///
/// let _dit = rind::cpu::Dit::hold();
/// for (number, packet) in packets.iter_mut().enumerate() {
///     let mut nonce = [0u8; 12];
///     nonce[4..].copy_from_slice(&(number as u64).to_be_bytes());
///     let nonce = Nonce::assume_unique_for_key(nonce);
///     key.seal_in_place_separate_tag(nonce, b"header", packet)
///         .unwrap();
/// }
/// ```
///
/// DIT belongs to a thread, so the guard can't leave the one that made it,
/// nor live across an `.await` in a task a multi-threaded runtime may move:
///
/// ```compile_fail,E0277
/// let dit = rind::cpu::Dit::hold();
/// std::thread::spawn(move || drop(dit));
/// ```
#[must_use = "DIT turns back off when the guard drops"]
#[derive(Debug)]
pub struct Dit {
    // Neither `Send` nor `Sync`: dropping it on another thread would count
    // against that thread's guards.
    _thread: PhantomData<*const ()>,
}

impl Dit {
    /// Turns DIT on for this thread, if rind sets it here, until the guard drops.
    pub fn hold() -> Self {
        let (guards, cpu_state) = DIT_GUARDS.get();
        let cpu_state = if guards == 0 {
            super::enter_cpu_state()
        } else {
            cpu_state
        };
        // Saturating, here and in `drop`: past `usize::MAX` guards the count
        // is inexact and DIT may turn off early, which costs speed but never
        // safety, since every rind call sets DIT itself.
        DIT_GUARDS.set((guards.saturating_add(1), cpu_state));
        Self {
            _thread: PhantomData,
        }
    }
}

impl Drop for Dit {
    fn drop(&mut self) {
        let (guards, cpu_state) = DIT_GUARDS.get();
        DIT_GUARDS.set((guards.saturating_sub(1), cpu_state));
        if guards == 1 {
            super::leave_cpu_state(cpu_state);
        }
    }
}

std::thread_local! {
    // This thread's live guards, and what the first one's `enter_cpu_state`
    // returned, for the last one to drop to restore.
    static DIT_GUARDS: Cell<(usize, u32)> = const { Cell::new((0, 0)) };
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    #[cfg(not(rind_backend = "portable"))]
    use crate::low::AesKey;

    /// The flag agrees with the AES keys run, whichever features are denied.
    #[test]
    fn has_aes_hardware_matches_keys() {
        #[cfg(not(rind_backend = "portable"))]
        let hardware = matches!(AesKey::new(&[0; 16]), AesKey::Hw(_));
        #[cfg(rind_backend = "portable")]
        let hardware = false;
        assert_eq!(super::has_aes_hardware(), hardware);
    }
}
