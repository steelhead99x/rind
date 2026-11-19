//! Constant-time checks for the secret paths this crate adds over rind, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. The wrappers copy no key: each passes
//! the bytes it is given to rind, which marks and wipes what it keeps.

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

#[test]
fn hmac_key() {
    use digest::{KeyInit, Mac};
    use rind_digest::{hmac::Hmac, sha2::Sha256};
    // Longer than a block, which HMAC hashes first, and shorter.
    for len in [20usize, 64, 100] {
        let key = vec![0x0b; len];
        secret(&key[..]);
        let mut mac = <Hmac<Sha256> as KeyInit>::new_from_slice(&key).unwrap();
        Mac::update(&mut mac, b"public message");
        let tag = mac.finalize().into_bytes();
        public(&tag);
        assert_eq!(tag.len(), 32);
    }
}
