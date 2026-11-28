//! RFC 9474's RSABSSA-SHA384-PSS-Deterministic with a 2048-bit key, Privacy
//! Pass's publicly verifiable tokens: the client's blind, the server's
//! signature, the client's finalize, and anyone's verify. Both libraries use
//! the same key, generated in each row's setup.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use blind_rsa_signatures::{
    BlindSignature, BlindingResult, DefaultRng, Deterministic, PSS, Sha384,
};
#[cfg(not(target_arch = "xtensa"))]
use common::Dit;
#[cfg(not(target_arch = "xtensa"))]
use rind::blind_rsa::{KeyPair, PublicKey, RSABSSA_SHA384_PSS_DETERMINISTIC as ALGORITHM};

#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = b"a Privacy Pass token input";

#[cfg(not(target_arch = "xtensa"))]
type RcSecretKey = blind_rsa_signatures::SecretKey<Sha384, PSS, Deterministic>;
#[cfg(not(target_arch = "xtensa"))]
type RcPublicKey = blind_rsa_signatures::PublicKey<Sha384, PSS, Deterministic>;

#[cfg(not(target_arch = "xtensa"))]
struct Keys {
    rind: KeyPair,
    rind_public: PublicKey,
    rustcrypto: RcSecretKey,
    rustcrypto_public: RcPublicKey,
}

#[cfg(not(target_arch = "xtensa"))]
fn keys() -> Keys {
    let rind = KeyPair::generate(&ALGORITHM, rind::rsa::KeySize::Rsa2048).unwrap();
    let rustcrypto = RcSecretKey::from_der(rind.to_pkcs8().as_ref()).unwrap();
    let keys = Keys {
        rind_public: rind.public_key().clone(),
        rustcrypto_public: rustcrypto.public_key().unwrap(),
        rind,
        rustcrypto,
    };
    // Each library verifies the other's signature, so the rows time the same
    // scheme.
    let (blinded, blinding) = keys.rind_public.blind(MESSAGE).unwrap();
    let signature = blinding
        .finalize(keys.rind.blind_sign(blinded.as_ref()).unwrap().as_ref())
        .unwrap();
    keys.rustcrypto_public
        .verify(
            &blind_rsa_signatures::Signature(signature.as_ref().to_vec()),
            None,
            MESSAGE,
        )
        .unwrap();
    let blinded = keys
        .rustcrypto_public
        .blind(&mut DefaultRng, MESSAGE)
        .unwrap();
    let signature = keys
        .rustcrypto_public
        .finalize(
            &keys.rustcrypto.blind_sign(&blinded.blind_message).unwrap(),
            &blinded,
            MESSAGE,
        )
        .unwrap();
    keys.rind_public.verify(MESSAGE, &signature).unwrap();
    keys
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_keys() -> Dit<Keys> {
    Dit::hold(keys())
}

#[cfg(not(target_arch = "xtensa"))]
mod blind_rsa2048_blind {
    use swole::bench;

    use super::*;

    #[bench(setup = rind_keys)]
    fn rind(keys: &Dit<Keys>) {
        black_box(keys.rind_public.blind(MESSAGE).unwrap());
    }

    #[bench(setup = keys)]
    fn rustcrypto(keys: &Keys) {
        black_box(
            keys.rustcrypto_public
                .blind(&mut DefaultRng, MESSAGE)
                .unwrap(),
        );
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod blind_rsa2048_sign {
    use swole::bench;

    use super::*;

    fn rind_input() -> Dit<(Keys, Vec<u8>)> {
        let keys = keys();
        let (blinded, _) = keys.rind_public.blind(MESSAGE).unwrap();
        Dit::hold((keys, blinded.as_ref().to_vec()))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(Keys, Vec<u8>)>) {
        let (keys, blinded) = &**input;
        black_box(keys.rind.blind_sign(blinded).unwrap());
    }

    #[bench(setup = rustcrypto_blinded)]
    fn rustcrypto((keys, blinded): &(Keys, BlindingResult)) {
        black_box(keys.rustcrypto.blind_sign(&blinded.blind_message).unwrap());
    }
}

/// The keys and a message they blinded.
#[cfg(not(target_arch = "xtensa"))]
fn rustcrypto_blinded() -> (Keys, BlindingResult) {
    let keys = keys();
    let blinded = keys
        .rustcrypto_public
        .blind(&mut DefaultRng, MESSAGE)
        .unwrap();
    (keys, blinded)
}

// rind's finalize consumes its blinding, so before each call a step blinds
// afresh, untimed. Both check the unblinded signature, as RFC 9474 requires.
#[cfg(not(target_arch = "xtensa"))]
mod blind_rsa2048_finalize {
    use swole::bench;

    use super::*;

    /// The keys, and the blinding and the server's reply the next call
    /// finalizes.
    type Finalize = (
        Keys,
        Option<(rind::blind_rsa::Blinding, rind::blind_rsa::BlindSignature)>,
    );

    fn rind_input() -> Dit<Finalize> {
        Dit::hold((keys(), None))
    }

    fn blind(input: &mut Dit<Finalize>) {
        let (keys, next) = &mut **input;
        let (blinded, blinding) = keys.rind_public.blind(MESSAGE).unwrap();
        let reply = keys.rind.blind_sign(blinded.as_ref()).unwrap();
        *next = Some((blinding, reply));
    }

    #[bench(setup = rind_input, before = blind)]
    fn rind(input: &mut Dit<Finalize>) {
        let (blinding, reply) = input.1.take().unwrap();
        black_box(blinding.finalize(reply.as_ref()).unwrap());
    }

    fn rustcrypto_input() -> (Keys, BlindingResult, BlindSignature) {
        let (keys, blinded) = rustcrypto_blinded();
        let reply = keys.rustcrypto.blind_sign(&blinded.blind_message).unwrap();
        (keys, blinded, reply)
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((keys, blinded, reply): &(Keys, BlindingResult, BlindSignature)) {
        black_box(
            keys.rustcrypto_public
                .finalize(reply, blinded, MESSAGE)
                .unwrap(),
        );
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod blind_rsa2048_verify {
    use swole::bench;

    use super::*;

    /// The keys and a token rind signed with them.
    fn signed() -> (Keys, Vec<u8>) {
        let keys = keys();
        let (blinded, blinding) = keys.rind_public.blind(MESSAGE).unwrap();
        let signature = blinding
            .finalize(keys.rind.blind_sign(blinded.as_ref()).unwrap().as_ref())
            .unwrap();
        (keys, signature.as_ref().to_vec())
    }

    fn rind_input() -> Dit<(Keys, Vec<u8>)> {
        Dit::hold(signed())
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Dit<(Keys, Vec<u8>)>) {
        let (keys, signature) = &**input;
        keys.rind_public.verify(MESSAGE, signature).unwrap()
    }

    fn rustcrypto_input() -> (Keys, blind_rsa_signatures::Signature) {
        let (keys, signature) = signed();
        (keys, blind_rsa_signatures::Signature(signature))
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((keys, signature): &(Keys, blind_rsa_signatures::Signature)) {
        keys.rustcrypto_public
            .verify(signature, None, MESSAGE)
            .unwrap()
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
