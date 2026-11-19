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
fn aead_keys() {
    use aead::{Aead, KeyInit, array::Array};
    use rind_aead::{
        aes_gcm::{Aes128Gcm, Aes256Gcm},
        chacha20poly1305::ChaCha20Poly1305,
    };
    fn seal_open<A: Aead + KeyInit>(key_len: usize) {
        let key = vec![0x42u8; key_len];
        secret(&key[..]);
        let aead = A::new_from_slice(&key).unwrap();
        let nonce = Array::try_from([7u8; 12].as_slice()).unwrap();
        let sealed = aead.encrypt(&nonce, b"public message".as_slice()).unwrap();
        // The ciphertext and tag are public by design.
        public(&sealed[..]);
        let opened = aead.decrypt(&nonce, sealed.as_slice()).unwrap();
        public(&opened[..]);
        assert_eq!(opened, b"public message");
    }
    seal_open::<Aes128Gcm>(16);
    seal_open::<Aes256Gcm>(32);
    seal_open::<ChaCha20Poly1305>(32);
}
