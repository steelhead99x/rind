#![no_main]

//! RSA blind signatures with each message tampered with in flight: the
//! client's blinded message, the server's reply, and the finalized
//! signature, and a key the fuzzer writes.
//!
//! No reference implements blind RSA on aws-lc, so this checks rind against
//! itself and `blind-rsa-signatures`, over RustCrypto's `rsa`: an untampered
//! exchange verifies, and a tampered message fails as its step documents,
//! rather than panicking or verifying. Where rind accepts a step, the crate
//! signs the same blinded message to the same bytes and verifies the same
//! signature, and its client finalizes rind's reply to a signature rind
//! verifies.

use std::sync::LazyLock;

use blind_rsa_signatures::{
    DefaultRng, Deterministic, MessagePrepare, MessageRandomizer, PSS, PSSZero, Randomized,
    SaltMode, SecretKey, Sha384,
};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::Error;
use rind::blind_rsa::*;

mod edit;

const PKCS8: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");

const ALGORITHMS: [&Algorithm; 4] = [
    &RSABSSA_SHA384_PSS_RANDOMIZED,
    &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
    &RSABSSA_SHA384_PSS_DETERMINISTIC,
    &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
];

static KEYS: LazyLock<[KeyPair; 4]> =
    LazyLock::new(|| ALGORITHMS.map(|algorithm| KeyPair::from_pkcs8(algorithm, PKCS8).unwrap()));

/// The same key in `blind-rsa-signatures`, in `ALGORITHMS`' order.
static INDEPENDENT: LazyLock<[Box<dyn Independent>; 4]> = LazyLock::new(|| {
    [
        Box::new(SecretKey::<Sha384, PSS, Randomized>::from_der(PKCS8).unwrap()),
        Box::new(SecretKey::<Sha384, PSSZero, Randomized>::from_der(PKCS8).unwrap()),
        Box::new(SecretKey::<Sha384, PSS, Deterministic>::from_der(PKCS8).unwrap()),
        Box::new(SecretKey::<Sha384, PSSZero, Deterministic>::from_der(PKCS8).unwrap()),
    ]
});

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    message: Vec<u8>,
    blinded: edit::Edit,
    reply: edit::Edit,
    signature: edit::Edit,
    spki: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.algorithm % 4);
    let key_pair = &KEYS[index];
    let public_key = key_pair.public_key();
    let independent = &INDEPENDENT[index];

    // Their client, our server.
    let signature = independent.client(&input.message, &|blinded| {
        key_pair.blind_sign(blinded).unwrap().as_ref().to_vec()
    });
    public_key.verify(&input.message, &signature).unwrap();

    let mut spki = public_key.to_spki().as_ref().to_vec();
    let spki_changed = input.spki.apply(&mut spki);
    if let Ok(parsed) = PublicKey::from_spki(ALGORITHMS[index], &spki) {
        // Only a change to the modulus or exponent survives, which makes
        // another key.
        if !spki_changed {
            assert_eq!(parsed.to_spki().as_ref(), public_key.to_spki().as_ref());
        }
    }

    let (blinded, blinding) = public_key.blind(&input.message).unwrap();
    let mut blinded = blinded.as_ref().to_vec();
    let blinded_changed = input.blinded.apply(&mut blinded);
    let reply = match key_pair.blind_sign(&blinded) {
        Ok(reply) => {
            assert_eq!(
                independent.blind_sign(&blinded).as_deref(),
                Some(reply.as_ref())
            );
            reply
        }
        Err(e) => {
            assert_eq!(e, Error::WrongLength);
            assert!(blinded_changed);
            return;
        }
    };
    let mut reply = reply.as_ref().to_vec();
    let changed = input.reply.apply(&mut reply) | blinded_changed;
    let signature = match blinding.finalize(&reply) {
        Ok(signature) => signature,
        Err(e) => {
            assert_eq!(e, Error::BadSignature);
            assert!(changed);
            return;
        }
    };
    assert!(!changed);

    let mut signature = signature.as_ref().to_vec();
    let changed = input.signature.apply(&mut signature);
    let result = public_key.verify(&input.message, &signature);
    assert_eq!(result.is_ok(), !changed, "{result:?}");
    if result.is_ok() {
        assert!(independent.verify(&input.message, &signature));
    }
});

/// One of `blind-rsa-signatures`' typed keys, behind one interface.
trait Independent: Send + Sync {
    /// The blind signature of `blinded`, or `None` if refused.
    fn blind_sign(&self, blinded: &[u8]) -> Option<Vec<u8>>;

    /// Whether `signature`, with any randomizer as rind prefixes it,
    /// verifies over `message`.
    fn verify(&self, message: &[u8], signature: &[u8]) -> bool;

    /// The signature its client finalizes from `server`'s reply to its
    /// blinding of `message`, prefixed by any randomizer as rind's is.
    fn client(&self, message: &[u8], server: &dyn Fn(&[u8]) -> Vec<u8>) -> Vec<u8>;
}

impl<S: SaltMode + Send + Sync, M: MessagePrepare + Send + Sync> Independent
    for SecretKey<Sha384, S, M>
{
    fn blind_sign(&self, blinded: &[u8]) -> Option<Vec<u8>> {
        Some(SecretKey::blind_sign(self, blinded).ok()?.0)
    }

    fn verify(&self, message: &[u8], signature: &[u8]) -> bool {
        let prefix = if M::RANDOMIZE { 32 } else { 0 };
        let Some((randomizer, signature)) = signature.split_at_checked(prefix) else {
            return false;
        };
        let randomizer = M::RANDOMIZE.then(|| MessageRandomizer(randomizer.try_into().unwrap()));
        self.public_key()
            .unwrap()
            .verify(&signature.to_vec().into(), randomizer, message)
            .is_ok()
    }

    fn client(&self, message: &[u8], server: &dyn Fn(&[u8]) -> Vec<u8>) -> Vec<u8> {
        let public_key = self.public_key().unwrap();
        let result = public_key.blind(&mut DefaultRng, message).unwrap();
        let reply = server(result.blind_message.as_ref()).into();
        let signature = public_key.finalize(&reply, &result, message).unwrap();
        let prefix = result.msg_randomizer.as_ref().map_or(&[][..], |r| &r.0[..]);
        [prefix, &signature].concat()
    }
}
