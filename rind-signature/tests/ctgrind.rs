//! Constant-time checks for the secret paths this crate adds over rind, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. The wrappers copy no key: each passes
//! the bytes it is given to rind, which marks and wipes what it keeps.
//! RSA's import is this crate's own: it reads an `rsa::PrivateKey`'s private
//! integers, which the test marks secret in place, at their full width into
//! rind's component loader.

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
fn ed25519_seed() {
    use signature::{Signer, Verifier};
    let seed = [0x9du8; 32];
    secret(&seed);
    let key = rind_signature::ed25519::SigningKey::from_bytes(&seed);
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
            use rind_signature::$module::ecdsa::{DerSignature, Signature, SigningKey};
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
    use rind_signature::ml_dsa::{Params, SigningKey};
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

/// Both RSA signing keys import an `rsa` key whose private integers are
/// secret: the private exponent, the primes, and the CRT values `rsa`
/// precomputed. Only the modulus and public exponent are public.
#[test]
fn rsa_private_key() {
    use rsa::pkcs8::DecodePrivateKey;
    use rsa::traits::PrivateKeyParts;
    use signature::{SignatureEncoding, Signer, Verifier};
    type Hash = rind_digest::sha2::Sha256;

    let key = rsa::PrivateKey::from_pkcs8_der(include_bytes!("data/rsa2048.pkcs8.der")).unwrap();
    secret(key.d().as_words());
    for prime in key.primes() {
        secret(prime.as_ref().as_words());
    }
    secret(key.dp().unwrap().as_words());
    secret(key.dq().unwrap().as_words());
    secret(key.qinv().unwrap().as_montgomery().as_words());

    let pkcs1 = rind_signature::rsa::pkcs1v15::SigningKey::<Hash>::try_new(key.clone()).unwrap();
    let signature = pkcs1.try_sign(b"public message").unwrap();
    public(&signature.to_bytes()[..]);
    pkcs1
        .verifying_key()
        .verify(b"public message", &signature)
        .unwrap();

    let pss = rind_signature::rsa::pss::SigningKey::<Hash>::try_new(key).unwrap();
    let signature = pss.try_sign(b"public message").unwrap();
    public(&signature.to_bytes()[..]);
    pss.verifying_key()
        .verify(b"public message", &signature)
        .unwrap();
}
