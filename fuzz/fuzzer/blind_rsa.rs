#![no_main]

//! RSA blind signatures with each message tampered with in flight: the
//! client's blinded message, the server's reply, and the finalized
//! signature, under a private key the fuzzer edits from one of several sizes
//! and exponents, and a public key it edits from that.
//!
//! No reference implements blind RSA on aws-lc, so this checks rind against
//! itself and `blind-rsa-signatures`, over RustCrypto's `rsa`: an untampered
//! exchange verifies, and a tampered message fails as its step documents,
//! rather than panicking or verifying. Where rind accepts a step, the crate
//! signs the same blinded message to the same bytes and verifies the same
//! signature, and its client finalizes rind's reply to a signature rind
//! verifies. A private key rind loads, the crate loads as the same key, and
//! it signs: rind refuses at load any key it could not sign with. The crate
//! takes only exponents 3 and 65537, moduli up to 4096 bits, and keys its
//! `rsa` decodes, which refuses some aws-lc takes, such as a private exponent
//! of at least the modulus, so rind alone checks the rest, such as the
//! exponent `2^32 + 1` key.

use blind_rsa_signatures::{
    DefaultRng, Deterministic, MessagePrepare, MessageRandomizer, PSS, PSSZero, Randomized,
    SaltMode, SecretKey, Sha384,
};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::Error;
use rind::blind_rsa::*;

mod edit;

/// The keys the fuzzer edits: the sizes either side of a byte boundary, a
/// non-standard exponent, and larger moduli.
const KEYS: [&[u8]; 8] = [
    include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa2048-e33.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa2049.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa2050.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa2056.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa2560.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa3072.pkcs8.der"),
    include_bytes!("../../rind/src/high/rsa/rsa4096.pkcs8.der"),
];

const ALGORITHMS: [&Algorithm; 4] = [
    &RSABSSA_SHA384_PSS_RANDOMIZED,
    &RSABSSA_SHA384_PSSZERO_RANDOMIZED,
    &RSABSSA_SHA384_PSS_DETERMINISTIC,
    &RSABSSA_SHA384_PSSZERO_DETERMINISTIC,
];

/// The key `der` in `blind-rsa-signatures`, for `ALGORITHMS[index]`, or
/// `None` if it refuses the key.
fn independent(index: usize, der: &[u8]) -> Option<Box<dyn Independent>> {
    Some(match index {
        0 => Box::new(SecretKey::<Sha384, PSS, Randomized>::from_der(der).ok()?),
        1 => Box::new(SecretKey::<Sha384, PSSZero, Randomized>::from_der(der).ok()?),
        2 => Box::new(SecretKey::<Sha384, PSS, Deterministic>::from_der(der).ok()?),
        _ => Box::new(SecretKey::<Sha384, PSSZero, Deterministic>::from_der(der).ok()?),
    })
}

/// Whether `blind-rsa-signatures` takes the PKCS#8 key `der`, which rind
/// loaded: only a modulus of 2048 to 4096 bits and an exponent of 3 or 65537,
/// and only a key its `rsa` decodes, which refuses some that rind and aws-lc
/// take, such as a private exponent of at least the modulus.
fn supported(der: &[u8]) -> bool {
    use blind_rsa_signatures::reexports::rsa::{
        PrivateKey, pkcs8::DecodePrivateKey, traits::PublicKeyParts,
    };
    let Ok(key) = PrivateKey::from_pkcs8_der(der) else {
        return false;
    };
    let e = key.e().to_be_bytes();
    let e = &e[e.iter().take_while(|&&b| b == 0).count()..];
    (2048..=4096).contains(&(key.size() * 8)) && (e == [3] || e == [1, 0, 1])
}

#[derive(Arbitrary, Debug)]
struct Input {
    algorithm: u8,
    key: u8,
    pkcs8: edit::Edit,
    message: Vec<u8>,
    blinded: edit::Edit,
    reply: edit::Edit,
    signature: edit::Edit,
    spki: edit::Edit,
}

fuzz_target!(|input: Input| {
    let index = usize::from(input.algorithm % 4);
    let mut pkcs8 = KEYS[usize::from(input.key) % KEYS.len()].to_vec();
    input.pkcs8.apply(&mut pkcs8);
    let Ok(key_pair) = KeyPair::from_pkcs8(ALGORITHMS[index], &pkcs8) else {
        return;
    };
    let public_key = key_pair.public_key();
    // The crate reads the key rind wrote, as rind ignores what it may not
    // round-trip, such as a version 2 document's public key.
    let der = key_pair.to_pkcs8();
    let independent = independent(index, der.as_ref());
    assert_eq!(
        independent.is_some(),
        supported(der.as_ref()),
        "blind-rsa-signatures refused a key rind loaded"
    );

    // Their client, our server.
    if let Some(independent) = &independent {
        let signature = independent.client(&input.message, &|blinded| {
            key_pair.blind_sign(blinded).unwrap().as_ref().to_vec()
        });
        public_key.verify(&input.message, &signature).unwrap();
    }

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
            if let Some(independent) = &independent {
                assert_eq!(
                    independent.blind_sign(&blinded).as_deref(),
                    Some(reply.as_ref())
                );
            }
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
    if let (Ok(()), Some(independent)) = (&result, &independent) {
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
