//! Constant-time checks for the secret paths this crate adds over rind, run
//! under valgrind by `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. The wrappers copy no key: each passes
//! the bytes it is given to rind, which marks and wipes what it keeps. RSA is
//! not here: its secret path is `rsa`'s own encoder, not this crate's.
#![cfg(all(feature = "digest-0_11", feature = "aead-0_6", feature = "signature-3"))]

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
    use rind_rustcrypto::{hmac::Hmac, sha2::Sha256};
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

#[test]
fn aead_keys() {
    use aead::{Aead, KeyInit, array::Array};
    use rind_rustcrypto::{
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

#[test]
fn ed25519_seed() {
    use signature::{Signer, Verifier};
    let seed = [0x9du8; 32];
    secret(&seed);
    let key = rind_rustcrypto::ed25519::SigningKey::from_bytes(&seed);
    let signature = key.try_sign(b"public message").unwrap();
    public(&signature.to_bytes()[..]);
    key.verifying_key()
        .verify(b"public message", &signature)
        .unwrap();
}

macro_rules! ecdsa {
    ($test:ident, $module:ident, $len:expr) => {
        #[test]
        fn $test() {
            use rind_rustcrypto::$module::ecdsa::{DerSignature, Signature, SigningKey};
            use signature::{Signer, Verifier};
            let mut scalar = [0x11u8; $len];
            scalar[0] = 0;
            secret(&scalar);
            let key = SigningKey::from_slice(&scalar).unwrap();
            let fixed: Signature = key.try_sign(b"public message").unwrap();
            let der: DerSignature = key.try_sign(b"public message").unwrap();
            public(&fixed.to_bytes()[..]);
            public(der.as_bytes());
            key.verifying_key()
                .verify(b"public message", &fixed)
                .unwrap();
        }
    };
}

ecdsa!(ecdsa_p256_scalar, p256, 32);
ecdsa!(ecdsa_p384_scalar, p384, 48);
ecdsa!(ecdsa_p521_scalar, p521, 66);

#[test]
fn ml_dsa_seed() {
    use ml_dsa::{MlDsa44, MlDsa65, MlDsa87, Seed, Signature};
    use rind_rustcrypto::ml_dsa::{Params, SigningKey};
    use signature::{Signer, Verifier};
    fn sign<P: Params>() {
        let seed = Seed::try_from([0x5au8; 32].as_slice()).unwrap();
        secret(&seed[..]);
        let key = SigningKey::<P>::from_seed(&seed);
        let signature: Signature<P> = key.try_sign(b"public message").unwrap();
        let encoded = signature.encode();
        public(encoded.as_slice());
        key.verifying_key()
            .verify(b"public message", &signature)
            .unwrap();
    }
    sign::<MlDsa44>();
    sign::<MlDsa65>();
    sign::<MlDsa87>();
}
