#![no_main]

//! rind-dart's C ABI, call by call, against the same calls on rind: a
//! sequence of calls on live handles, each with arbitrary algorithm ids,
//! sources, export kinds, key bytes, and buffer lengths, from zero (passed as
//! a null pointer) up, with output buffers too short, exact, or long. Each
//! call must return the status and bytes rind's own call gives, or `Misuse`
//! where the binding's contract refuses the arguments; AddressSanitizer
//! catches a read or write outside a buffer, LeakSanitizer a handle the
//! binding leaks, and a panic aborts across the C ABI.
//!
//! Within the ABI's contract (`rind-dart/src/lib.rs`): every pointer is valid
//! for its length and every handle live and of its type, as the Dart side
//! guarantees. RSA keys are never generated, which takes seconds; they load
//! from rind's test keys.

use std::num::NonZeroU32;
use std::ptr;

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::ecdsa::KeyPair as EcdsaKeyPair;
use rind::ed25519::KeyPair as Ed25519KeyPair;
use rind::rsa::KeyPair as RsaKeyPair;
use rind::{Error, aead, agreement, cipher, digest, ecdsa, ed25519, hkdf, hmac, kem, pbkdf2, rsa};
use rind_dart::*;

mod edit;
mod fixtures;

use fixtures::Material;

const MISUSE: isize = -10;

fn code(error: Error) -> isize {
    match error {
        Error::WrongLength => -1,
        Error::KeyRejected(_) => -2,
        Error::BadSignature => -3,
        Error::DecryptFailed => -4,
        Error::RngFailed => -5,
        Error::NotEqual => -6,
        Error::Unsupported => -8,
        _ => -7,
    }
}

/// The status a call returning `result` gives, with `ok` on success.
fn status<T>(result: &Result<T, Error>, ok: isize) -> isize {
    match result {
        Ok(_) => ok,
        Err(error) => code(*error),
    }
}

fn input(bytes: &[u8]) -> *const u8 {
    if bytes.is_empty() {
        ptr::null()
    } else {
        bytes.as_ptr()
    }
}

fn output(bytes: &mut [u8]) -> *mut u8 {
    if bytes.is_empty() {
        ptr::null_mut()
    } else {
        bytes.as_mut_ptr()
    }
}

/// Checks a call that writes `expected`, or fails, into `out`: it returns
/// the length written, or `Misuse` when `out` is too short.
fn check_write<B: AsRef<[u8]>>(got: isize, out: &[u8], expected: Result<B, isize>) {
    match expected.as_ref().map(AsRef::as_ref) {
        Err(&status) => assert_eq!(got, status),
        Ok(bytes) if out.len() < bytes.len() => assert_eq!(got, MISUSE),
        Ok(bytes) => {
            assert_eq!(got, bytes.len() as isize);
            assert_eq!(&out[..bytes.len()], bytes);
        }
    }
}

/// Handles of one type, each beside rind's twin of its value.
struct Slots<T, W> {
    items: Vec<(*mut T, W)>,
    free: unsafe extern "C" fn(*mut T),
}

impl<T, W> Slots<T, W> {
    fn new(free: unsafe extern "C" fn(*mut T)) -> Self {
        Self {
            items: Vec::new(),
            free,
        }
    }

    /// Keeps a handle the binding stored, or frees it when the slots are
    /// full.
    fn keep(&mut self, handle: *mut T, twin: W) {
        assert!(!handle.is_null());
        if self.items.len() < 4 {
            self.items.push((handle, twin));
        } else {
            // SAFETY: a live handle of this type, not used again.
            unsafe { (self.free)(handle) };
        }
    }

    fn get(&self, index: u8) -> Option<&(*mut T, W)> {
        (!self.items.is_empty()).then(|| &self.items[usize::from(index) % self.items.len()])
    }

    fn get_mut(&mut self, index: u8) -> Option<&mut (*mut T, W)> {
        let len = self.items.len();
        (len != 0).then(|| &mut self.items[usize::from(index) % len])
    }

    fn take(&mut self, index: u8) -> Option<(*mut T, W)> {
        (!self.items.is_empty()).then(|| {
            self.items
                .swap_remove(usize::from(index) % self.items.len())
        })
    }
}

impl<T, W> Drop for Slots<T, W> {
    fn drop(&mut self) {
        for &(handle, _) in &self.items {
            // SAFETY: a live handle of this type, not used again.
            unsafe { (self.free)(handle) };
        }
    }
}

/// Stores a handle through `new`, checking its status against `twin`, and
/// keeps it on success.
fn create<T, W>(
    slots: &mut Slots<T, W>,
    twin: Result<W, isize>,
    new: impl FnOnce(*mut *mut T) -> isize,
) {
    let mut handle = ptr::null_mut();
    let got = new(&mut handle);
    match twin {
        Ok(twin) => {
            assert_eq!(got, 0);
            slots.keep(handle, twin);
        }
        Err(expected) => {
            assert_eq!(got, expected);
            assert!(handle.is_null());
        }
    }
}

fn twin<T>(result: Result<T, Error>) -> Result<T, isize> {
    result.map_err(code)
}

// The binding's algorithm ids, as `rind-dart/lib/src/ffi.dart` numbers them.

fn aead_algorithm(id: u8) -> Option<&'static aead::Algorithm> {
    Some(match id {
        0 => &aead::AES_128_GCM,
        1 => &aead::AES_192_GCM,
        2 => &aead::AES_256_GCM,
        3 => &aead::CHACHA20_POLY1305,
        _ => return None,
    })
}

fn cipher_algorithm(id: u8) -> Option<&'static cipher::Algorithm> {
    Some(match id {
        0 => &cipher::AES_128,
        1 => &cipher::AES_192,
        2 => &cipher::AES_256,
        _ => return None,
    })
}

fn digest_algorithm(id: u8) -> Option<&'static digest::Algorithm> {
    Some(match id {
        0 => &digest::SHA256,
        1 => &digest::SHA384,
        2 => &digest::SHA512,
        3 => &digest::SHA512_256,
        4 => &digest::SHA3_256,
        5 => &digest::SHA3_384,
        6 => &digest::SHA3_512,
        100 => &digest::legacy::SHA1,
        101 => &digest::legacy::MD5,
        _ => return None,
    })
}

fn hmac_algorithm(id: u8) -> Option<&'static hmac::Algorithm> {
    Some(match id {
        0 => &hmac::HMAC_SHA256,
        1 => &hmac::HMAC_SHA384,
        2 => &hmac::HMAC_SHA512,
        100 => &hmac::legacy::HMAC_SHA1,
        _ => return None,
    })
}

fn hkdf_algorithm(id: u8) -> Option<&'static hkdf::Algorithm> {
    Some(match id {
        0 => &hkdf::HKDF_SHA256,
        1 => &hkdf::HKDF_SHA384,
        2 => &hkdf::HKDF_SHA512,
        100 => &hkdf::legacy::HKDF_SHA1,
        _ => return None,
    })
}

fn pbkdf2_algorithm(id: u8) -> Option<&'static pbkdf2::Algorithm> {
    Some(match id {
        0 => &pbkdf2::PBKDF2_HMAC_SHA256,
        1 => &pbkdf2::PBKDF2_HMAC_SHA384,
        2 => &pbkdf2::PBKDF2_HMAC_SHA512,
        100 => &pbkdf2::legacy::PBKDF2_HMAC_SHA1,
        _ => return None,
    })
}

fn agreement_algorithm(id: u8) -> Option<&'static agreement::Algorithm> {
    Some(match id {
        0 => &agreement::X25519,
        1 => &agreement::ECDH_P256,
        2 => &agreement::ECDH_P384,
        3 => &agreement::ECDH_P521,
        _ => return None,
    })
}

fn ecdsa_algorithm(id: u8) -> Option<&'static ecdsa::SigningAlgorithm> {
    Some(match id {
        0 => &ecdsa::sign::P256_SHA256_ASN1,
        1 => &ecdsa::sign::P256_SHA256_FIXED,
        2 => &ecdsa::sign::P384_SHA384_ASN1,
        3 => &ecdsa::sign::P384_SHA384_FIXED,
        4 => &ecdsa::sign::P521_SHA512_ASN1,
        5 => &ecdsa::sign::P521_SHA512_FIXED,
        _ => return None,
    })
}

/// The verification algorithm of the same name as each signing one.
fn ecdsa_verification(id: u8) -> &'static ecdsa::VerificationAlgorithm {
    match id {
        0 => &ecdsa::verify::P256_SHA256_ASN1,
        1 => &ecdsa::verify::P256_SHA256_FIXED,
        2 => &ecdsa::verify::P384_SHA384_ASN1,
        3 => &ecdsa::verify::P384_SHA384_FIXED,
        4 => &ecdsa::verify::P521_SHA512_ASN1,
        _ => &ecdsa::verify::P521_SHA512_FIXED,
    }
}

fn rsa_signing_algorithm(id: u8) -> Option<&'static rsa::SigningAlgorithm> {
    Some(match id {
        0 => &rsa::sign::PKCS1_SHA256,
        1 => &rsa::sign::PKCS1_SHA384,
        2 => &rsa::sign::PKCS1_SHA512,
        3 => &rsa::sign::PSS_SHA256,
        4 => &rsa::sign::PSS_SHA384,
        5 => &rsa::sign::PSS_SHA512,
        _ => return None,
    })
}

fn rsa_verification_algorithm(id: u8) -> Option<&'static rsa::VerificationAlgorithm> {
    Some(match id {
        0 => &rsa::verify::PKCS1_SHA256,
        1 => &rsa::verify::PKCS1_SHA384,
        2 => &rsa::verify::PKCS1_SHA512,
        3 => &rsa::verify::PSS_SHA256,
        4 => &rsa::verify::PSS_SHA384,
        5 => &rsa::verify::PSS_SHA512,
        6 => &rsa::verify::PSS_SHA256_ANY_SALT,
        7 => &rsa::verify::PSS_SHA384_ANY_SALT,
        8 => &rsa::verify::PSS_SHA512_ANY_SALT,
        100 => &rsa::verify::legacy::PKCS1_SHA1,
        101 => &rsa::verify::legacy::PKCS1_1024_SHA1,
        102 => &rsa::verify::legacy::PKCS1_1024_SHA256,
        103 => &rsa::verify::legacy::PKCS1_1024_SHA512,
        104 => &rsa::verify::legacy::PKCS1_3072_SHA384,
        _ => return None,
    })
}

enum Verification {
    Ecdsa(&'static ecdsa::VerificationAlgorithm),
    Ed25519,
    Rsa(&'static rsa::VerificationAlgorithm),
}

fn verification_algorithm(id: u8) -> Option<Verification> {
    use ecdsa::verify::*;
    Some(match id {
        20 => Verification::Ecdsa(&P256_SHA256_ASN1),
        21 => Verification::Ecdsa(&P256_SHA384_ASN1),
        22 => Verification::Ecdsa(&P256_SHA512_ASN1),
        23 => Verification::Ecdsa(&P384_SHA256_ASN1),
        24 => Verification::Ecdsa(&P384_SHA384_ASN1),
        25 => Verification::Ecdsa(&P384_SHA512_ASN1),
        26 => Verification::Ecdsa(&P521_SHA256_ASN1),
        27 => Verification::Ecdsa(&P521_SHA384_ASN1),
        28 => Verification::Ecdsa(&P521_SHA512_ASN1),
        29 => Verification::Ecdsa(&P256_SHA256_FIXED),
        30 => Verification::Ecdsa(&P384_SHA384_FIXED),
        31 => Verification::Ecdsa(&P521_SHA512_FIXED),
        32 => Verification::Ed25519,
        _ => Verification::Rsa(rsa_verification_algorithm(id)?),
    })
}

fn oaep_algorithm(id: u8) -> Option<&'static rsa::OaepAlgorithm> {
    Some(match id {
        0 => &rsa::OAEP_SHA256,
        1 => &rsa::OAEP_SHA384,
        2 => &rsa::OAEP_SHA512,
        100 => &rsa::legacy::OAEP_SHA1,
        _ => return None,
    })
}

/// rind's twin of a `PublicKey` handle.
#[allow(clippy::large_enum_variant)]
enum Public {
    Ecdsa(ecdsa::PublicKey),
    Ed25519(ed25519::PublicKey),
    Rsa(rsa::PublicKey, &'static rsa::VerificationAlgorithm),
}

impl Public {
    fn verify(&self, message: &[u8], signature: &[u8]) -> Result<(), Error> {
        match self {
            Self::Ecdsa(key) => key.verify(message, signature),
            Self::Ed25519(key) => key.verify(message, signature),
            Self::Rsa(key, algorithm) => key.verify(algorithm, message, signature),
        }
    }

    fn export(&self, spki: bool) -> Vec<u8> {
        match (self, spki) {
            (Self::Ecdsa(key), false) => key.as_ref().to_vec(),
            (Self::Ed25519(key), false) => key.as_ref().to_vec(),
            (Self::Rsa(key, _), false) => key.as_ref().to_vec(),
            (Self::Ecdsa(key), true) => key.to_spki().as_ref().to_vec(),
            (Self::Ed25519(key), true) => key.to_spki().as_ref().to_vec(),
            (Self::Rsa(key, _), true) => key.to_spki().as_ref().to_vec(),
        }
    }
}

type Decapsulation = kem::DecapsulationKey<kem::MlKem768>;
type Encapsulation = kem::EncapsulationKey<kem::MlKem768>;

#[derive(Arbitrary, Debug)]
enum Op {
    Message {
        cap: u8,
    },
    RandFill {
        len: u16,
    },
    ConstantTimeVerify {
        a: Vec<u8>,
        b: Vec<u8>,
    },

    AeadKeyNew {
        algorithm: u8,
        key: Vec<u8>,
    },
    AeadSeal {
        key: u8,
        nonce: Vec<u8>,
        aad: Vec<u8>,
        in_out: Vec<u8>,
    },
    AeadOpen {
        key: u8,
        nonce: Vec<u8>,
        aad: Vec<u8>,
        in_out: Vec<u8>,
    },
    RandomizedNonceKeyNew {
        key: Vec<u8>,
    },
    RandomizedNonceKeySeal {
        key: u8,
        aad: Vec<u8>,
        in_out: Vec<u8>,
    },
    RandomizedNonceKeyOpen {
        key: u8,
        nonce: Vec<u8>,
        aad: Vec<u8>,
        in_out: Vec<u8>,
    },

    AesCbcEncryptingKeyNew {
        algorithm: u8,
        key: Vec<u8>,
    },
    AesCbcEncrypt {
        key: u8,
        iv: Vec<u8>,
        pad: u32,
        in_out: Vec<u8>,
        len: u16,
    },
    AesCbcDecryptingKeyNew {
        algorithm: u8,
        key: Vec<u8>,
    },
    AesCbcDecrypt {
        key: u8,
        iv: Vec<u8>,
        pad: u32,
        in_out: Vec<u8>,
    },
    AesCtrNew {
        algorithm: u8,
        key: Vec<u8>,
        counter_bits: u32,
    },
    AesCtrApply {
        key: u8,
        counter_block: Vec<u8>,
        in_out: Vec<u8>,
    },
    ChaCha20New {
        key: Vec<u8>,
    },
    ChaCha20Apply {
        key: u8,
        nonce: Vec<u8>,
        counter: u32,
        in_out: Vec<u8>,
    },

    Digest {
        algorithm: u8,
        data: Vec<u8>,
        cap: u8,
    },
    DigestContextNew {
        algorithm: u8,
    },
    DigestContextUpdate {
        context: u8,
        data: Vec<u8>,
    },
    DigestContextFinish {
        context: u8,
        cap: u8,
    },

    HmacKeyNew {
        algorithm: u8,
        key: Vec<u8>,
    },
    HmacSign {
        key: u8,
        data: Vec<u8>,
        cap: u8,
    },
    HmacVerify {
        key: u8,
        data: Vec<u8>,
        tag: Vec<u8>,
    },
    HmacContextNew {
        key: u8,
    },
    HmacContextUpdate {
        context: u8,
        data: Vec<u8>,
    },
    HmacContextSign {
        context: u8,
        cap: u8,
    },

    HkdfSaltNew {
        algorithm: u8,
        salt: Vec<u8>,
    },
    HkdfExtract {
        salt: u8,
        secret: Vec<u8>,
    },
    HkdfExpand {
        prk: u8,
        info: Vec<u8>,
        len: u16,
    },

    Pbkdf2SecretNew {
        algorithm: u8,
        secret: Vec<u8>,
    },
    Pbkdf2Derive {
        secret: u8,
        rounds: u8,
        salt: Vec<u8>,
        len: u16,
    },
    Pbkdf2Verify {
        secret: u8,
        rounds: u8,
        salt: Vec<u8>,
        previous: Vec<u8>,
    },

    AgreementPrivateKeyNew {
        algorithm: u8,
        source: u8,
        bytes: Material,
    },
    AgreementPrivateKeyExport {
        key: u8,
        what: u8,
        cap: u8,
    },
    AgreementAgree {
        key: u8,
        peer: Vec<u8>,
        cap: u8,
    },
    AgreementPublicKey {
        algorithm: u8,
        spki: u8,
        bytes: Material,
        export: u8,
        cap: u8,
    },

    EcdsaKeyPairNew {
        algorithm: u8,
        source: u8,
        bytes: Material,
        public_key: Vec<u8>,
    },
    EcdsaSign {
        pair: u8,
        message: Vec<u8>,
        cap: u8,
    },
    EcdsaKeyPairExport {
        pair: u8,
        what: u8,
        cap: u8,
    },
    Ed25519KeyPairNew {
        source: u8,
        bytes: Material,
        public_key: Vec<u8>,
    },
    Ed25519Sign {
        pair: u8,
        message: Vec<u8>,
        cap: u8,
    },
    Ed25519KeyPairExport {
        pair: u8,
        what: u8,
        cap: u8,
    },
    RsaKeyPairNew {
        source: u8,
        size: u8,
        bytes: Material,
    },
    RsaSign {
        pair: u8,
        algorithm: u8,
        message: Vec<u8>,
        cap: u16,
    },
    RsaKeyPairExport {
        pair: u8,
        what: u8,
        cap: u16,
    },
    KeyPairPublicKey {
        kind: u8,
        pair: u8,
        algorithm: u8,
    },
    PublicKeyNew {
        algorithm: u8,
        source: u8,
        bytes: Material,
        exponent: Vec<u8>,
    },
    PublicKeyVerify {
        key: u8,
        message: Vec<u8>,
        signature: Vec<u8>,
    },
    PublicKeyExport {
        key: u8,
        spki: u8,
        cap: u16,
    },

    DecapsulationKeyGenerate {
        algorithm: u8,
    },
    DecapsulationKeyPublicKey {
        key: u8,
        cap: u16,
    },
    Decapsulate {
        key: u8,
        ciphertext: Vec<u8>,
        cap: u8,
    },
    EncapsulationKeyNew {
        algorithm: u8,
        bytes: Vec<u8>,
    },
    /// Loads the public key of a decapsulation key, encapsulates to it, and
    /// decapsulates.
    EncapsulateTo {
        key: u8,
        ciphertext_cap: u16,
        secret_cap: u8,
    },
    Encapsulate {
        key: u8,
        ciphertext_cap: u16,
        secret_cap: u8,
    },

    DecryptingKeyNew {
        algorithm: u8,
        source: u8,
        size: u8,
        bytes: Material,
    },
    DecryptingKeyPublicKey {
        key: u8,
    },
    Decrypt {
        key: u8,
        ciphertext: Vec<u8>,
        label: Vec<u8>,
        cap: u16,
    },
    DecryptingKeyExport {
        key: u8,
        what: u8,
        cap: u16,
    },
    EncryptingKeyNew {
        algorithm: u8,
        source: u8,
        bytes: Material,
        exponent: Vec<u8>,
    },
    Encrypt {
        key: u8,
        message: Vec<u8>,
        label: Vec<u8>,
        cap: u16,
    },
    EncryptingKeyExport {
        key: u8,
        spki: u8,
        cap: u16,
    },
    EncryptingKeyMaxMessageLen {
        key: u8,
    },
}

/// Every live handle, by type.
struct State {
    aead: Slots<aead::Key, aead::Key>,
    randomized: Slots<aead::RandomizedNonceKey, aead::RandomizedNonceKey>,
    cbc_encrypting: Slots<cipher::AesCbcEncryptingKey, cipher::AesCbcEncryptingKey>,
    cbc_decrypting: Slots<cipher::AesCbcDecryptingKey, cipher::AesCbcDecryptingKey>,
    ctr: Slots<cipher::AesCtr, cipher::AesCtr>,
    chacha20: Slots<cipher::ChaCha20, cipher::ChaCha20>,
    digest: Slots<digest::Context, digest::Context>,
    hmac_key: Slots<hmac::Key, hmac::Key>,
    hmac_context: Slots<hmac::Context, hmac::Context>,
    salt: Slots<hkdf::Salt, hkdf::Salt>,
    prk: Slots<hkdf::Prk, hkdf::Prk>,
    pbkdf2: Slots<pbkdf2::Secret, pbkdf2::Secret>,
    agreement: Slots<agreement::PrivateKey, agreement::PrivateKey>,
    ecdsa: Slots<EcdsaKeyPair, (EcdsaKeyPair, u8)>,
    ed25519: Slots<Ed25519KeyPair, Ed25519KeyPair>,
    rsa: Slots<RsaKeyPair, RsaKeyPair>,
    public: Slots<PublicKey, Public>,
    decapsulation: Slots<Decapsulation, ()>,
    encapsulation: Slots<Encapsulation, ()>,
    decrypting: Slots<rsa::DecryptingKey, (rsa::DecryptingKey, &'static rsa::OaepAlgorithm)>,
    /// With the decrypting key it came from, if any.
    encrypting: Slots<rsa::EncryptingKey, (rsa::EncryptingKey, Option<rsa::DecryptingKey>)>,
}

fuzz_target!(|ops: Vec<Op>| {
    let mut state = State {
        aead: Slots::new(rind_dart_aead_key_free),
        randomized: Slots::new(rind_dart_randomized_nonce_key_free),
        cbc_encrypting: Slots::new(rind_dart_aes_cbc_encrypting_key_free),
        cbc_decrypting: Slots::new(rind_dart_aes_cbc_decrypting_key_free),
        ctr: Slots::new(rind_dart_aes_ctr_free),
        chacha20: Slots::new(rind_dart_chacha20_free),
        digest: Slots::new(rind_dart_digest_context_free),
        hmac_key: Slots::new(rind_dart_hmac_key_free),
        hmac_context: Slots::new(rind_dart_hmac_context_free),
        salt: Slots::new(rind_dart_hkdf_salt_free),
        prk: Slots::new(rind_dart_hkdf_prk_free),
        pbkdf2: Slots::new(rind_dart_pbkdf2_secret_free),
        agreement: Slots::new(rind_dart_agreement_private_key_free),
        ecdsa: Slots::new(rind_dart_ecdsa_key_pair_free),
        ed25519: Slots::new(rind_dart_ed25519_key_pair_free),
        rsa: Slots::new(rind_dart_rsa_key_pair_free),
        public: Slots::new(rind_dart_public_key_free),
        decapsulation: Slots::new(rind_dart_decapsulation_key_free),
        encapsulation: Slots::new(rind_dart_encapsulation_key_free),
        decrypting: Slots::new(rind_dart_decrypting_key_free),
        encrypting: Slots::new(rind_dart_encrypting_key_free),
    };
    // Each call is cheap but for RSA, so a long sequence adds no coverage.
    for op in ops.iter().take(64) {
        // SAFETY: every call below passes pointers valid for their lengths
        // and live handles of their types, as the ABI requires.
        unsafe { run(&mut state, op) };
    }
});

unsafe fn run(s: &mut State, op: &Op) {
    match op {
        Op::Message { cap } => {
            let mut out = vec![0; usize::from(*cap)];
            let len = rind_dart_message(output(&mut out), out.len());
            assert!(len >= 0);
        }
        Op::RandFill { len } => {
            let mut out = vec![0; usize::from(*len)];
            assert_eq!(rind_dart_rand_fill(output(&mut out), out.len()), 0);
        }
        Op::ConstantTimeVerify { a, b } => {
            let expected = status(&rind::constant_time::verify(a, b), 0);
            let got = rind_dart_constant_time_verify(input(a), a.len(), input(b), b.len());
            assert_eq!(got, expected);
        }

        Op::AeadKeyNew { algorithm, key } => {
            let twin = aead_algorithm(*algorithm)
                .ok_or(MISUSE)
                .and_then(|a| twin(aead::Key::new(a, key)));
            create(&mut s.aead, twin, |out| {
                rind_dart_aead_key_new(u32::from(*algorithm), input(key), key.len(), out)
            });
        }
        Op::AeadSeal {
            key,
            nonce,
            aad,
            in_out,
        } => {
            let Some(&(handle, ref twin)) = s.aead.get(*key) else {
                return;
            };
            let mut expected = in_out.clone();
            let want = match expected.split_last_chunk_mut::<16>() {
                None => Err(MISUSE),
                Some((plaintext, tag)) => match <[u8; 12]>::try_from(&nonce[..]) {
                    Err(_) => Err(-1),
                    Ok(n) => {
                        let n = aead::Nonce::assume_unique_for_key(n);
                        twin.seal_in_place_separate_tag(n, aad, plaintext)
                            .map(|t| tag.copy_from_slice(t.as_ref()))
                            .map_err(code)
                    }
                },
            };
            let mut buf = in_out.clone();
            let got = rind_dart_aead_seal(
                handle,
                input(nonce),
                nonce.len(),
                input(aad),
                aad.len(),
                output(&mut buf),
                buf.len(),
            );
            match want {
                Ok(()) => {
                    assert_eq!(got, buf.len() as isize);
                    assert_eq!(buf, expected);
                }
                Err(want) => assert_eq!(got, want),
            }
        }
        Op::AeadOpen {
            key,
            nonce,
            aad,
            in_out,
        } => {
            let Some(&(handle, ref twin)) = s.aead.get(*key) else {
                return;
            };
            let mut expected = in_out.clone();
            let want = match <[u8; 12]>::try_from(&nonce[..]) {
                Err(_) => Err(-1),
                Ok(n) => twin
                    .open_in_place(aead::Nonce::assume_unique_for_key(n), aad, &mut expected)
                    .map(|p| p.to_vec())
                    .map_err(code),
            };
            let mut buf = in_out.clone();
            let got = rind_dart_aead_open(
                handle,
                input(nonce),
                nonce.len(),
                input(aad),
                aad.len(),
                output(&mut buf),
                buf.len(),
            );
            match want {
                Ok(plaintext) => {
                    assert_eq!(got, plaintext.len() as isize);
                    assert_eq!(&buf[..plaintext.len()], plaintext);
                }
                Err(want) => assert_eq!(got, want),
            }
        }
        Op::RandomizedNonceKeyNew { key } => {
            let twin = <&[u8; 32]>::try_from(&key[..])
                .map(aead::RandomizedNonceKey::new)
                .map_err(|_| -1);
            create(&mut s.randomized, twin, |out| {
                rind_dart_randomized_nonce_key_new(input(key), key.len(), out)
            });
        }
        Op::RandomizedNonceKeySeal { key, aad, in_out } => {
            let Some(&(handle, ref twin)) = s.randomized.get(*key) else {
                return;
            };
            let mut buf = in_out.clone();
            let mut nonce = [0; 24];
            let got = rind_dart_randomized_nonce_key_seal(
                handle,
                input(aad),
                aad.len(),
                output(&mut buf),
                buf.len(),
                nonce.as_mut_ptr(),
            );
            if in_out.len() < 16 {
                assert_eq!(got, MISUSE);
                return;
            }
            assert_eq!(got, buf.len() as isize);
            // The nonce is random, so the twin opens what the binding sealed.
            let opened = twin.open_in_place(nonce.into(), aad, &mut buf).unwrap();
            assert_eq!(opened, &in_out[..in_out.len() - 16]);
        }
        Op::RandomizedNonceKeyOpen {
            key,
            nonce,
            aad,
            in_out,
        } => {
            let Some(&(handle, ref twin)) = s.randomized.get(*key) else {
                return;
            };
            let mut expected = in_out.clone();
            let want = match <[u8; 24]>::try_from(&nonce[..]) {
                Err(_) => Err(-1),
                Ok(n) => twin
                    .open_in_place(n.into(), aad, &mut expected)
                    .map(|p| p.to_vec())
                    .map_err(code),
            };
            let mut buf = in_out.clone();
            let got = rind_dart_randomized_nonce_key_open(
                handle,
                input(nonce),
                nonce.len(),
                input(aad),
                aad.len(),
                output(&mut buf),
                buf.len(),
            );
            match want {
                Ok(plaintext) => {
                    assert_eq!(got, plaintext.len() as isize);
                    assert_eq!(&buf[..plaintext.len()], plaintext);
                }
                Err(want) => assert_eq!(got, want),
            }
        }

        Op::AesCbcEncryptingKeyNew { algorithm, key } => {
            let twin = cipher_algorithm(*algorithm)
                .ok_or(MISUSE)
                .and_then(|a| twin(cipher::AesCbcEncryptingKey::new(a, key)));
            create(&mut s.cbc_encrypting, twin, |out| {
                rind_dart_aes_cbc_encrypting_key_new(
                    u32::from(*algorithm),
                    input(key),
                    key.len(),
                    out,
                )
            });
        }
        Op::AesCbcEncrypt {
            key,
            iv,
            pad,
            in_out,
            len,
        } => {
            let Some(&(handle, ref twin)) = s.cbc_encrypting.get(*key) else {
                return;
            };
            let len = usize::from(*len);
            let padded_len = if *pad == 0 { len } else { (len / 16 + 1) * 16 };
            let want = match <[u8; 16]>::try_from(&iv[..]) {
                Err(_) => Err(-1),
                Ok(_) if padded_len > in_out.len() => Err(MISUSE),
                Ok(iv) => {
                    let iv = cipher::CbcIv::assume_unpredictable(iv);
                    let mut expected = in_out[..len].to_vec();
                    if *pad == 0 {
                        twin.encrypt_blocks(iv, &mut expected)
                    } else {
                        twin.encrypt(iv, &mut expected)
                    }
                    .map(|()| expected)
                    .map_err(code)
                }
            };
            let mut buf = in_out.clone();
            let got = rind_dart_aes_cbc_encrypt(
                handle,
                input(iv),
                iv.len(),
                *pad,
                output(&mut buf),
                buf.len(),
                len,
            );
            match want {
                Ok(ciphertext) => {
                    assert_eq!(got, ciphertext.len() as isize);
                    assert_eq!(&buf[..ciphertext.len()], ciphertext);
                }
                Err(want) => assert_eq!(got, want),
            }
        }
        Op::AesCbcDecryptingKeyNew { algorithm, key } => {
            let twin = cipher_algorithm(*algorithm)
                .ok_or(MISUSE)
                .and_then(|a| twin(cipher::AesCbcDecryptingKey::new(a, key)));
            create(&mut s.cbc_decrypting, twin, |out| {
                rind_dart_aes_cbc_decrypting_key_new(
                    u32::from(*algorithm),
                    input(key),
                    key.len(),
                    out,
                )
            });
        }
        Op::AesCbcDecrypt {
            key,
            iv,
            pad,
            in_out,
        } => {
            let Some(&(handle, ref twin)) = s.cbc_decrypting.get(*key) else {
                return;
            };
            let mut expected = in_out.clone();
            let want = match <&[u8; 16]>::try_from(&iv[..]) {
                Err(_) => Err(-1),
                Ok(iv) if *pad == 0 => twin
                    .decrypt_blocks(iv, &mut expected)
                    .map(|()| expected.clone())
                    .map_err(code),
                Ok(iv) => twin
                    .decrypt(iv, &mut expected)
                    .map(|p| p.to_vec())
                    .map_err(code),
            };
            let mut buf = in_out.clone();
            let got = rind_dart_aes_cbc_decrypt(
                handle,
                input(iv),
                iv.len(),
                *pad,
                output(&mut buf),
                buf.len(),
            );
            match want {
                Ok(plaintext) => {
                    assert_eq!(got, plaintext.len() as isize);
                    assert_eq!(&buf[..plaintext.len()], plaintext);
                }
                Err(want) => assert_eq!(got, want),
            }
        }
        Op::AesCtrNew {
            algorithm,
            key,
            counter_bits,
        } => {
            let twin = cipher_algorithm(*algorithm).ok_or(MISUSE).and_then(|a| {
                let bits = u8::try_from(*counter_bits).map_err(|_| -1_isize)?;
                twin(cipher::AesCtr::new(a, key, bits))
            });
            create(&mut s.ctr, twin, |out| {
                rind_dart_aes_ctr_new(
                    u32::from(*algorithm),
                    input(key),
                    key.len(),
                    *counter_bits,
                    out,
                )
            });
        }
        Op::AesCtrApply {
            key,
            counter_block,
            in_out,
        } => {
            let Some(&(handle, ref twin)) = s.ctr.get(*key) else {
                return;
            };
            let mut expected = in_out.clone();
            let want = match <&[u8; 16]>::try_from(&counter_block[..]) {
                Err(_) => Err(-1),
                Ok(block) => twin.apply_keystream(block, &mut expected).map_err(code),
            };
            let mut buf = in_out.clone();
            let got = rind_dart_aes_ctr_apply_keystream(
                handle,
                input(counter_block),
                counter_block.len(),
                output(&mut buf),
                buf.len(),
            );
            match want {
                Ok(()) => {
                    assert_eq!(got, buf.len() as isize);
                    assert_eq!(buf, expected);
                }
                Err(want) => assert_eq!(got, want),
            }
        }
        Op::ChaCha20New { key } => {
            let twin = <&[u8; 32]>::try_from(&key[..])
                .map(cipher::ChaCha20::new)
                .map_err(|_| -1);
            create(&mut s.chacha20, twin, |out| {
                rind_dart_chacha20_new(input(key), key.len(), out)
            });
        }
        Op::ChaCha20Apply {
            key,
            nonce,
            counter,
            in_out,
        } => {
            let Some(&(handle, ref twin)) = s.chacha20.get(*key) else {
                return;
            };
            let mut expected = in_out.clone();
            let want = match <&[u8; 12]>::try_from(&nonce[..]) {
                Err(_) => Err(-1),
                Ok(n) => twin
                    .apply_keystream(n, *counter, &mut expected)
                    .map_err(code),
            };
            let mut buf = in_out.clone();
            let got = rind_dart_chacha20_apply_keystream(
                handle,
                input(nonce),
                nonce.len(),
                *counter,
                output(&mut buf),
                buf.len(),
            );
            match want {
                Ok(()) => {
                    assert_eq!(got, buf.len() as isize);
                    assert_eq!(buf, expected);
                }
                Err(want) => assert_eq!(got, want),
            }
        }

        Op::Digest {
            algorithm,
            data,
            cap,
        } => {
            let expected = digest_algorithm(*algorithm).map(|a| digest::digest(a, data));
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_digest(
                u32::from(*algorithm),
                input(data),
                data.len(),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected.ok_or(MISUSE));
        }
        Op::DigestContextNew { algorithm } => {
            let twin = digest_algorithm(*algorithm)
                .map(digest::Context::new)
                .ok_or(MISUSE);
            create(&mut s.digest, twin, |out| {
                rind_dart_digest_context_new(u32::from(*algorithm), out)
            });
        }
        Op::DigestContextUpdate { context, data } => {
            let Some((handle, twin)) = s.digest.get_mut(*context) else {
                return;
            };
            twin.update(data);
            assert_eq!(
                rind_dart_digest_context_update(*handle, input(data), data.len()),
                0
            );
        }
        Op::DigestContextFinish { context, cap } => {
            let Some((handle, twin)) = s.digest.get_mut(*context) else {
                return;
            };
            let expected = twin.finish();
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_digest_context_finish(*handle, output(&mut out), out.len());
            check_write(got, &out, Ok(expected.as_ref()));
        }

        Op::HmacKeyNew { algorithm, key } => {
            let twin = hmac_algorithm(*algorithm)
                .map(|a| hmac::Key::new(a, key))
                .ok_or(MISUSE);
            create(&mut s.hmac_key, twin, |out| {
                rind_dart_hmac_key_new(u32::from(*algorithm), input(key), key.len(), out)
            });
        }
        Op::HmacSign { key, data, cap } => {
            let Some(&(handle, ref twin)) = s.hmac_key.get(*key) else {
                return;
            };
            let expected = hmac::sign(twin, data);
            let mut out = vec![0; usize::from(*cap)];
            let got =
                rind_dart_hmac_sign(handle, input(data), data.len(), output(&mut out), out.len());
            check_write(got, &out, Ok(expected.as_ref()));
        }
        Op::HmacVerify { key, data, tag } => {
            let Some(&(handle, ref twin)) = s.hmac_key.get(*key) else {
                return;
            };
            let expected = status(&hmac::verify(twin, data, tag), 0);
            let got = rind_dart_hmac_verify(handle, input(data), data.len(), input(tag), tag.len());
            assert_eq!(got, expected);
        }
        Op::HmacContextNew { key } => {
            let Some(&(handle, ref twin)) = s.hmac_key.get(*key) else {
                return;
            };
            let twin = hmac::Context::with_key(twin);
            create(&mut s.hmac_context, Ok(twin), |out| {
                rind_dart_hmac_context_new(handle, out)
            });
        }
        Op::HmacContextUpdate { context, data } => {
            let Some((handle, twin)) = s.hmac_context.get_mut(*context) else {
                return;
            };
            twin.update(data);
            assert_eq!(
                rind_dart_hmac_context_update(*handle, input(data), data.len()),
                0
            );
        }
        Op::HmacContextSign { context, cap } => {
            // The call frees the context.
            let Some((handle, mut twin)) = s.hmac_context.take(*context) else {
                return;
            };
            let expected = twin.sign();
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_hmac_context_sign(handle, output(&mut out), out.len());
            check_write(got, &out, Ok(expected.as_ref()));
        }

        Op::HkdfSaltNew { algorithm, salt } => {
            let twin = hkdf_algorithm(*algorithm)
                .map(|a| hkdf::Salt::new(a, salt))
                .ok_or(MISUSE);
            create(&mut s.salt, twin, |out| {
                rind_dart_hkdf_salt_new(u32::from(*algorithm), input(salt), salt.len(), out)
            });
        }
        Op::HkdfExtract { salt, secret } => {
            let Some(&(handle, ref twin)) = s.salt.get(*salt) else {
                return;
            };
            let twin = twin.extract(secret).map_err(code);
            create(&mut s.prk, twin, |out| {
                rind_dart_hkdf_extract(handle, input(secret), secret.len(), out)
            });
        }
        Op::HkdfExpand { prk, info, len } => {
            let Some(&(handle, ref twin)) = s.prk.get(*prk) else {
                return;
            };
            let mut expected = vec![0; usize::from(*len)];
            let want = twin.fill(&[info], &mut expected);
            let mut out = vec![0; usize::from(*len)];
            let got =
                rind_dart_hkdf_expand(handle, input(info), info.len(), output(&mut out), out.len());
            assert_eq!(got, status(&want, out.len() as isize));
            if want.is_ok() {
                assert_eq!(out, expected);
            }
        }

        Op::Pbkdf2SecretNew { algorithm, secret } => {
            let twin = pbkdf2_algorithm(*algorithm)
                .map(|a| pbkdf2::Secret::new(a, secret))
                .ok_or(MISUSE);
            create(&mut s.pbkdf2, twin, |out| {
                rind_dart_pbkdf2_secret_new(u32::from(*algorithm), input(secret), secret.len(), out)
            });
        }
        Op::Pbkdf2Derive {
            secret,
            rounds,
            salt,
            len,
        } => {
            let Some(&(handle, ref twin)) = s.pbkdf2.get(*secret) else {
                return;
            };
            // Long outputs cost a block of rounds each.
            let len = usize::from(*len % 1024);
            let mut expected = vec![0; len];
            let want = match NonZeroU32::new(u32::from(*rounds)) {
                None => Err(MISUSE),
                Some(n) => twin.derive(n, salt, &mut expected).map_err(code),
            };
            let mut out = vec![0; len];
            let got = rind_dart_pbkdf2_derive(
                handle,
                u32::from(*rounds),
                input(salt),
                salt.len(),
                output(&mut out),
                out.len(),
            );
            match want {
                Ok(()) => {
                    assert_eq!(got, len as isize);
                    assert_eq!(out, expected);
                }
                Err(want) => assert_eq!(got, want),
            }
        }
        Op::Pbkdf2Verify {
            secret,
            rounds,
            salt,
            previous,
        } => {
            let Some(&(handle, ref twin)) = s.pbkdf2.get(*secret) else {
                return;
            };
            let previous = &previous[..previous.len().min(1024)];
            let want = match NonZeroU32::new(u32::from(*rounds)) {
                None => MISUSE,
                Some(n) => status(&twin.verify(n, salt, previous), 0),
            };
            let got = rind_dart_pbkdf2_verify(
                handle,
                u32::from(*rounds),
                input(salt),
                salt.len(),
                input(previous),
                previous.len(),
            );
            assert_eq!(got, want);
        }

        Op::AgreementPrivateKeyNew {
            algorithm,
            source,
            bytes,
        } => {
            use agreement::PrivateKey;
            let bytes = bytes.bytes();
            let mut generated = false;
            let twin = match (agreement_algorithm(*algorithm), source) {
                (None, _) => Err(MISUSE),
                (Some(_), 4..) => Err(MISUSE),
                (Some(a), 0) => {
                    generated = true;
                    // A twin of the binding's random key, from its scalar
                    // below.
                    twin(PrivateKey::generate(a))
                }
                (Some(a), 1) => twin(PrivateKey::from_scalar(a, &bytes)),
                (Some(a), 2) => twin(PrivateKey::from_pkcs8(a, &bytes)),
                (Some(a), 3) => twin(PrivateKey::from_sec1(a, &bytes)),
            };
            let mut handle = ptr::null_mut();
            let got = rind_dart_agreement_private_key_new(
                u32::from(*algorithm),
                u32::from(*source),
                input(&bytes),
                bytes.len(),
                &mut handle,
            );
            assert_eq!(got, twin.as_ref().map_or_else(|&e| e, |_| 0));
            let Ok(mut twin) = twin else { return };
            if generated {
                let mut scalar = [0; 66];
                let len = rind_dart_agreement_private_key_export(
                    handle,
                    2,
                    scalar.as_mut_ptr(),
                    scalar.len(),
                );
                twin = PrivateKey::from_scalar(twin.algorithm(), &scalar[..len as usize]).unwrap();
            }
            s.agreement.keep(handle, twin);
        }
        Op::AgreementPrivateKeyExport { key, what, cap } => {
            let Some(&(handle, ref twin)) = s.agreement.get(*key) else {
                return;
            };
            let expected = match what {
                0 => Ok(twin.public_key().as_ref().to_vec()),
                1 => Ok(twin.to_pkcs8().as_ref().to_vec()),
                2 => Ok(twin.to_scalar().as_ref().to_vec()),
                _ => Err(MISUSE),
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_agreement_private_key_export(
                handle,
                u32::from(*what),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected);
        }
        Op::AgreementAgree { key, peer, cap } => {
            let Some(&(handle, ref twin)) = s.agreement.get(*key) else {
                return;
            };
            let expected = twin.agree(peer);
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_agreement_agree(
                handle,
                input(peer),
                peer.len(),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected.map_err(code));
        }
        Op::AgreementPublicKey {
            algorithm,
            spki,
            bytes,
            export,
            cap,
        } => {
            use agreement::PublicKey;
            let bytes = bytes.bytes();
            let expected = agreement_algorithm(*algorithm).ok_or(MISUSE).and_then(|a| {
                let key = match spki {
                    0 => PublicKey::new(a, &bytes),
                    _ => PublicKey::from_spki(a, &bytes),
                }
                .map_err(code)?;
                Ok(match export {
                    0 => key.as_ref().to_vec(),
                    _ => key.to_spki().as_ref().to_vec(),
                })
            });
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_agreement_public_key(
                u32::from(*algorithm),
                u32::from(*spki),
                input(&bytes),
                bytes.len(),
                u32::from(*export),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected);
        }

        Op::EcdsaKeyPairNew {
            algorithm,
            source,
            bytes,
            public_key,
        } => {
            let bytes = bytes.bytes();
            let twin = match (ecdsa_algorithm(*algorithm), source) {
                (None, _) | (Some(_), 4..) => Err(MISUSE),
                (Some(a), 0) => twin(EcdsaKeyPair::generate(a)),
                (Some(a), 1) => twin(EcdsaKeyPair::from_pkcs8(a, &bytes)),
                (Some(a), 2) => twin(EcdsaKeyPair::from_sec1(a, &bytes)),
                (Some(a), 3) => twin(EcdsaKeyPair::from_scalar_and_public_key(
                    a, &bytes, public_key,
                )),
            };
            let mut handle = ptr::null_mut();
            let got = rind_dart_ecdsa_key_pair_new(
                u32::from(*algorithm),
                u32::from(*source),
                input(&bytes),
                bytes.len(),
                input(public_key),
                public_key.len(),
                &mut handle,
            );
            assert_eq!(got, twin.as_ref().map_or_else(|&e| e, |_| 0));
            let Ok(mut twin) = twin else { return };
            if *source == 0 {
                // The binding's key is its own random one: its twin loads
                // from its PKCS#8.
                let mut der = [0; 512];
                let len = rind_dart_ecdsa_key_pair_export(handle, 1, der.as_mut_ptr(), der.len());
                twin = EcdsaKeyPair::from_pkcs8(
                    ecdsa_algorithm(*algorithm).unwrap(),
                    &der[..len as usize],
                )
                .unwrap();
            }
            s.ecdsa.keep(handle, (twin, *algorithm));
        }
        Op::EcdsaSign { pair, message, cap } => {
            let Some(&(handle, (ref twin, algorithm))) = s.ecdsa.get(*pair) else {
                return;
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_ecdsa_sign(
                handle,
                input(message),
                message.len(),
                output(&mut out),
                out.len(),
            );
            if got == MISUSE {
                assert!(usize::from(*cap) < signature_max_len(algorithm));
                return;
            }
            // Signatures are randomized: rind verifies the binding's.
            let signature = &out[..got as usize];
            let public = twin.public_key().as_ref();
            ecdsa::PublicKey::new(ecdsa_verification(algorithm), public)
                .unwrap()
                .verify(message, signature)
                .unwrap();
        }
        Op::EcdsaKeyPairExport { pair, what, cap } => {
            let Some(&(handle, (ref twin, _))) = s.ecdsa.get(*pair) else {
                return;
            };
            let expected = match what {
                1 => Ok(twin.to_pkcs8().as_ref().to_vec()),
                2 => Ok(twin.to_sec1().as_ref().to_vec()),
                3 => Ok(twin.to_scalar().as_ref().to_vec()),
                4 => Ok(twin.public_key().to_spki().as_ref().to_vec()),
                _ => Err(MISUSE),
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_ecdsa_key_pair_export(
                handle,
                u32::from(*what),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected);
        }
        Op::Ed25519KeyPairNew {
            source,
            bytes,
            public_key,
        } => {
            let bytes = bytes.bytes();
            let twin = match source {
                0 => twin(Ed25519KeyPair::generate()),
                1 => twin(Ed25519KeyPair::from_pkcs8(&bytes)),
                2 => twin(Ed25519KeyPair::from_seed(&bytes)),
                3 => twin(Ed25519KeyPair::from_seed_and_public_key(&bytes, public_key)),
                _ => Err(MISUSE),
            };
            let mut handle = ptr::null_mut();
            let got = rind_dart_ed25519_key_pair_new(
                u32::from(*source),
                input(&bytes),
                bytes.len(),
                input(public_key),
                public_key.len(),
                &mut handle,
            );
            assert_eq!(got, twin.as_ref().map_or_else(|&e| e, |_| 0));
            let Ok(mut twin) = twin else { return };
            if *source == 0 {
                let mut seed = [0; 32];
                assert_eq!(
                    rind_dart_ed25519_key_pair_export(handle, 3, seed.as_mut_ptr(), 32),
                    32
                );
                twin = Ed25519KeyPair::from_seed(&seed).unwrap();
            }
            s.ed25519.keep(handle, twin);
        }
        Op::Ed25519Sign { pair, message, cap } => {
            let Some(&(handle, ref twin)) = s.ed25519.get(*pair) else {
                return;
            };
            let expected = twin.sign(message);
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_ed25519_sign(
                handle,
                input(message),
                message.len(),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, Ok(expected.as_ref()));
        }
        Op::Ed25519KeyPairExport { pair, what, cap } => {
            let Some(&(handle, ref twin)) = s.ed25519.get(*pair) else {
                return;
            };
            let expected = match what {
                1 => Ok(twin.to_pkcs8().as_ref().to_vec()),
                2 => Ok(twin.to_pkcs8v1().as_ref().to_vec()),
                3 => Ok(twin.to_seed().as_ref().to_vec()),
                4 => Ok(twin.public_key().to_spki().as_ref().to_vec()),
                _ => Err(MISUSE),
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_ed25519_key_pair_export(
                handle,
                u32::from(*what),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected);
        }
        Op::RsaKeyPairNew {
            source,
            size,
            bytes,
        } => {
            let bytes = bytes.bytes();
            let twin = match source {
                // Generation takes seconds; only its refusal of an unknown
                // size runs.
                0 if *size < 5 => return,
                1 => twin(RsaKeyPair::from_pkcs8(&bytes)),
                2 => twin(RsaKeyPair::from_pkcs1(&bytes)),
                _ => Err(MISUSE),
            };
            create(&mut s.rsa, twin, |out| {
                rind_dart_rsa_key_pair_new(
                    u32::from(*source),
                    u32::from(*size),
                    input(&bytes),
                    bytes.len(),
                    out,
                )
            });
        }
        Op::RsaSign {
            pair,
            algorithm,
            message,
            cap,
        } => {
            let Some(&(handle, ref twin)) = s.rsa.get(*pair) else {
                return;
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_rsa_sign(
                handle,
                u32::from(*algorithm),
                input(message),
                message.len(),
                output(&mut out),
                out.len(),
            );
            let Some(a) = rsa_signing_algorithm(*algorithm) else {
                assert_eq!(got, MISUSE);
                return;
            };
            let expected = twin.sign(a, message).unwrap();
            if out.len() < expected.as_ref().len() {
                assert_eq!(got, MISUSE);
            } else if *algorithm < 3 {
                // PKCS#1 v1.5 is deterministic.
                check_write(got, &out, Ok(expected.as_ref()));
            } else {
                let verification = rsa_verification_algorithm(*algorithm).unwrap();
                let signature = &out[..got as usize];
                twin.public_key()
                    .verify(verification, message, signature)
                    .unwrap();
            }
        }
        Op::RsaKeyPairExport { pair, what, cap } => {
            let Some(&(handle, ref twin)) = s.rsa.get(*pair) else {
                return;
            };
            let expected = match what {
                1 => Ok(twin.to_pkcs8().as_ref().to_vec()),
                4 => Ok(twin.public_key().to_spki().as_ref().to_vec()),
                _ => Err(MISUSE),
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_rsa_key_pair_export(
                handle,
                u32::from(*what),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected);
        }
        Op::KeyPairPublicKey {
            kind,
            pair,
            algorithm,
        } => {
            let (pair, twin) = match kind {
                0 => {
                    let Some(&(handle, (ref twin, _))) = s.ecdsa.get(*pair) else {
                        return;
                    };
                    (
                        handle.cast_const().cast::<u8>(),
                        Ok(Public::Ecdsa(twin.public_key().clone())),
                    )
                }
                1 => {
                    let Some(&(handle, ref twin)) = s.ed25519.get(*pair) else {
                        return;
                    };
                    (
                        handle.cast_const().cast(),
                        Ok(Public::Ed25519(twin.public_key().clone())),
                    )
                }
                2 => {
                    let Some(&(handle, ref twin)) = s.rsa.get(*pair) else {
                        return;
                    };
                    let twin = match rsa_signing_algorithm(*algorithm) {
                        None => Err(MISUSE),
                        Some(_) => Ok(Public::Rsa(
                            twin.public_key().clone(),
                            rsa_verification_algorithm(*algorithm).unwrap(),
                        )),
                    };
                    (handle.cast_const().cast(), twin)
                }
                // The binding refuses the kind before it reads the handle.
                _ => (ptr::null(), Err(MISUSE)),
            };
            create(&mut s.public, twin, |out| {
                rind_dart_key_pair_public_key(u32::from(*kind), pair, u32::from(*algorithm), out)
            });
        }
        Op::PublicKeyNew {
            algorithm,
            source,
            bytes,
            exponent,
        } => {
            let bytes = bytes.bytes();
            let twin = match (source, verification_algorithm(*algorithm)) {
                (_, None) => Err(MISUSE),
                (0, Some(Verification::Ecdsa(a))) => {
                    twin(ecdsa::PublicKey::new(a, &bytes).map(Public::Ecdsa))
                }
                (1, Some(Verification::Ecdsa(a))) => {
                    twin(ecdsa::PublicKey::from_spki(a, &bytes).map(Public::Ecdsa))
                }
                (0, Some(Verification::Ed25519)) => {
                    twin(ed25519::PublicKey::new(&bytes).map(Public::Ed25519))
                }
                (1, Some(Verification::Ed25519)) => {
                    twin(ed25519::PublicKey::from_spki(&bytes).map(Public::Ed25519))
                }
                (0, Some(Verification::Rsa(a))) => twin(
                    rsa::PublicKey::new(&bytes)
                        .or_else(|_| rsa::PublicKey::from_spki(&bytes))
                        .map(|k| Public::Rsa(k, a)),
                ),
                (1, Some(Verification::Rsa(a))) => {
                    twin(rsa::PublicKey::from_spki(&bytes).map(|k| Public::Rsa(k, a)))
                }
                (2, Some(Verification::Rsa(a))) => twin(
                    rsa::PublicKey::from_components(&rsa::PublicKeyComponents {
                        n: &bytes[..],
                        e: &exponent[..],
                    })
                    .map(|k| Public::Rsa(k, a)),
                ),
                _ => Err(MISUSE),
            };
            create(&mut s.public, twin, |out| {
                rind_dart_public_key_new(
                    u32::from(*algorithm),
                    u32::from(*source),
                    input(&bytes),
                    bytes.len(),
                    input(exponent),
                    exponent.len(),
                    out,
                )
            });
        }
        Op::PublicKeyVerify {
            key,
            message,
            signature,
        } => {
            let Some(&(handle, ref twin)) = s.public.get(*key) else {
                return;
            };
            let expected = status(&twin.verify(message, signature), 0);
            let got = rind_dart_public_key_verify(
                handle,
                input(message),
                message.len(),
                input(signature),
                signature.len(),
            );
            assert_eq!(got, expected);
        }
        Op::PublicKeyExport { key, spki, cap } => {
            let Some(&(handle, ref twin)) = s.public.get(*key) else {
                return;
            };
            let expected = twin.export(*spki != 0);
            let mut out = vec![0; usize::from(*cap)];
            let got =
                rind_dart_public_key_export(handle, u32::from(*spki), output(&mut out), out.len());
            check_write(got, &out, Ok(&expected));
        }

        Op::DecapsulationKeyGenerate { algorithm } => {
            let twin = if *algorithm == 0 { Ok(()) } else { Err(MISUSE) };
            create(&mut s.decapsulation, twin, |out| {
                rind_dart_decapsulation_key_generate(u32::from(*algorithm), out)
            });
        }
        Op::DecapsulationKeyPublicKey { key, cap } => {
            let Some(&(handle, ())) = s.decapsulation.get(*key) else {
                return;
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_decapsulation_key_public_key(handle, output(&mut out), out.len());
            if out.len() < 1184 {
                assert_eq!(got, MISUSE);
            } else {
                assert_eq!(got, 1184);
                Encapsulation::new(&out[..1184]).unwrap();
            }
        }
        Op::Decapsulate {
            key,
            ciphertext,
            cap,
        } => {
            let Some(&(handle, ())) = s.decapsulation.get(*key) else {
                return;
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_decapsulate(
                handle,
                input(ciphertext),
                ciphertext.len(),
                output(&mut out),
                out.len(),
            );
            let expected = match kem::Ciphertext::<kem::MlKem768>::new(ciphertext) {
                Err(error) => code(error),
                Ok(_) if out.len() < 32 => MISUSE,
                Ok(_) => 32,
            };
            assert_eq!(got, expected);
        }
        Op::EncapsulationKeyNew { algorithm, bytes } => {
            let twin = if *algorithm != 0 {
                Err(MISUSE)
            } else {
                Encapsulation::new(bytes).map(drop).map_err(code)
            };
            create(&mut s.encapsulation, twin, |out| {
                rind_dart_encapsulation_key_new(
                    u32::from(*algorithm),
                    input(bytes),
                    bytes.len(),
                    out,
                )
            });
        }
        Op::EncapsulateTo {
            key,
            ciphertext_cap,
            secret_cap,
        } => {
            let Some(&(handle, ())) = s.decapsulation.get(*key) else {
                return;
            };
            let mut public = [0; 1184];
            assert_eq!(
                rind_dart_decapsulation_key_public_key(handle, public.as_mut_ptr(), 1184),
                1184
            );
            let mut encapsulation = ptr::null_mut();
            assert_eq!(
                rind_dart_encapsulation_key_new(0, public.as_ptr(), 1184, &mut encapsulation),
                0
            );
            let mut ciphertext = vec![0; usize::from(*ciphertext_cap)];
            let mut secret = vec![0; usize::from(*secret_cap)];
            let got = rind_dart_encapsulate(
                encapsulation,
                output(&mut ciphertext),
                ciphertext.len(),
                output(&mut secret),
                secret.len(),
            );
            rind_dart_encapsulation_key_free(encapsulation);
            if ciphertext.len() < 1088 || secret.len() < 32 {
                assert_eq!(got, MISUSE);
                return;
            }
            assert_eq!(got, 1088);
            let mut decapsulated = [0; 32];
            let got = rind_dart_decapsulate(
                handle,
                ciphertext.as_ptr(),
                1088,
                decapsulated.as_mut_ptr(),
                32,
            );
            assert_eq!(got, 32);
            assert_eq!(decapsulated, secret[..32]);
            // rind, encapsulating to the same key, agrees with the binding's
            // decapsulation, so neither side's secret is the binding's alone.
            let (ciphertext, secret) = Encapsulation::new(&public).unwrap().encapsulate().unwrap();
            let got = rind_dart_decapsulate(
                handle,
                ciphertext.as_ref().as_ptr(),
                1088,
                decapsulated.as_mut_ptr(),
                32,
            );
            assert_eq!(got, 32);
            assert_eq!(decapsulated, secret.as_ref());
        }
        Op::Encapsulate {
            key,
            ciphertext_cap,
            secret_cap,
        } => {
            let Some(&(handle, ())) = s.encapsulation.get(*key) else {
                return;
            };
            let mut ciphertext = vec![0; usize::from(*ciphertext_cap)];
            let mut secret = vec![0; usize::from(*secret_cap)];
            let got = rind_dart_encapsulate(
                handle,
                output(&mut ciphertext),
                ciphertext.len(),
                output(&mut secret),
                secret.len(),
            );
            let expected = if ciphertext.len() < 1088 || secret.len() < 32 {
                MISUSE
            } else {
                1088
            };
            assert_eq!(got, expected);
        }

        Op::DecryptingKeyNew {
            algorithm,
            source,
            size,
            bytes,
        } => {
            use rsa::DecryptingKey;
            let bytes = bytes.bytes();
            let twin = match (oaep_algorithm(*algorithm), source) {
                (None, _) => Err(MISUSE),
                // Generation takes seconds; only its refusal of an unknown
                // size runs.
                (Some(_), 0) if *size < 5 => return,
                (Some(a), 1) => twin(DecryptingKey::from_pkcs8(a, &bytes).map(|k| (k, a))),
                (Some(a), 2) => twin(DecryptingKey::from_pkcs1(a, &bytes).map(|k| (k, a))),
                (Some(_), _) => Err(MISUSE),
            };
            create(&mut s.decrypting, twin, |out| {
                rind_dart_decrypting_key_new(
                    u32::from(*algorithm),
                    u32::from(*source),
                    u32::from(*size),
                    input(&bytes),
                    bytes.len(),
                    out,
                )
            });
        }
        Op::DecryptingKeyPublicKey { key } => {
            let Some(&(handle, (ref twin, algorithm))) = s.decrypting.get(*key) else {
                return;
            };
            let der = twin.to_pkcs8();
            let decrypting = rsa::DecryptingKey::from_pkcs8(algorithm, der.as_ref()).unwrap();
            let twin = (twin.public_key().clone(), Some(decrypting));
            create(&mut s.encrypting, Ok(twin), |out| {
                rind_dart_decrypting_key_public_key(handle, out)
            });
        }
        Op::Decrypt {
            key,
            ciphertext,
            label,
            cap,
        } => {
            let Some(&(handle, (ref twin, _))) = s.decrypting.get(*key) else {
                return;
            };
            let expected = twin.decrypt(ciphertext, label);
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_decrypt(
                handle,
                input(ciphertext),
                ciphertext.len(),
                input(label),
                label.len(),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected.map_err(code));
        }
        Op::DecryptingKeyExport { key, what, cap } => {
            let Some(&(handle, (ref twin, _))) = s.decrypting.get(*key) else {
                return;
            };
            let expected = match what {
                1 => Ok(twin.to_pkcs8().as_ref().to_vec()),
                4 => Ok(twin.public_key().to_spki().as_ref().to_vec()),
                _ => Err(MISUSE),
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_decrypting_key_export(
                handle,
                u32::from(*what),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, expected);
        }
        Op::EncryptingKeyNew {
            algorithm,
            source,
            bytes,
            exponent,
        } => {
            use rsa::EncryptingKey;
            let bytes = bytes.bytes();
            let twin = match (oaep_algorithm(*algorithm), source) {
                (None, _) => Err(MISUSE),
                (Some(a), 0) => twin(
                    EncryptingKey::new(a, &bytes).or_else(|_| EncryptingKey::from_spki(a, &bytes)),
                ),
                (Some(a), 2) => twin(EncryptingKey::from_components(
                    a,
                    &rsa::PublicKeyComponents {
                        n: &bytes[..],
                        e: &exponent[..],
                    },
                )),
                (Some(_), _) => Err(MISUSE),
            };
            create(&mut s.encrypting, twin.map(|k| (k, None)), |out| {
                rind_dart_encrypting_key_new(
                    u32::from(*algorithm),
                    u32::from(*source),
                    input(&bytes),
                    bytes.len(),
                    input(exponent),
                    exponent.len(),
                    out,
                )
            });
        }
        Op::Encrypt {
            key,
            message,
            label,
            cap,
        } => {
            let Some(&(handle, (ref twin, ref decrypting))) = s.encrypting.get(*key) else {
                return;
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_encrypt(
                handle,
                input(message),
                message.len(),
                input(label),
                label.len(),
                output(&mut out),
                out.len(),
            );
            // Encryption is randomized: compare the status, and decrypt
            // when the key's private half is known.
            let expected = twin.encrypt(message, label);
            match expected {
                Err(error) => assert_eq!(got, code(error)),
                Ok(c) if out.len() < c.as_ref().len() => assert_eq!(got, MISUSE),
                Ok(c) => {
                    assert_eq!(got, c.as_ref().len() as isize);
                    if let Some(decrypting) = decrypting {
                        let plaintext = decrypting.decrypt(&out[..got as usize], label).unwrap();
                        assert_eq!(plaintext.as_ref(), message);
                    }
                }
            }
        }
        Op::EncryptingKeyExport { key, spki, cap } => {
            let Some(&(handle, (ref twin, _))) = s.encrypting.get(*key) else {
                return;
            };
            let expected = match spki {
                0 => twin.as_ref().to_vec(),
                _ => twin.to_spki().as_ref().to_vec(),
            };
            let mut out = vec![0; usize::from(*cap)];
            let got = rind_dart_encrypting_key_export(
                handle,
                u32::from(*spki),
                output(&mut out),
                out.len(),
            );
            check_write(got, &out, Ok(&expected));
        }
        Op::EncryptingKeyMaxMessageLen { key } => {
            let Some(&(handle, (ref twin, _))) = s.encrypting.get(*key) else {
                return;
            };
            assert_eq!(
                rind_dart_encrypting_key_max_message_len(handle),
                twin.max_message_len() as isize
            );
        }
    }
}

/// The longest signature of an ECDSA signing algorithm.
fn signature_max_len(algorithm: u8) -> usize {
    [72, 64, 104, 96, 139, 132][usize::from(algorithm)]
}
