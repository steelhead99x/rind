//! RFC 9381's ECVRF try-and-increment suites: a proof of one key
//! transparency label, and its verification from the encoded proof against a
//! parsed public key.
#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;
#[cfg(not(target_arch = "xtensa"))]
use std::sync::Once;

#[cfg(not(target_arch = "xtensa"))]
use common::Dit;

#[cfg(not(target_arch = "xtensa"))]
const ALPHA: &[u8] = b"alice@example.com";
#[cfg(not(target_arch = "xtensa"))]
const SEED: [u8; 32] = [0x42; 32];

// rind's `prove` returns the proof and its output together, so the other
// library's rows encode both too.
#[cfg(not(target_arch = "xtensa"))]
fn edwards() -> vrf_rfc9381::Ciphersuite {
    vrf_rfc9381::Ciphersuite::ECVRF_EDWARDS25519_SHA512_TAI
}

#[cfg(not(target_arch = "xtensa"))]
fn p256() -> vrf_rfc9381::Ciphersuite {
    vrf_rfc9381::Ciphersuite::ECVRF_P256_SHA256_TAI
}

/// Checks, once a process, that both libraries prove the same output from
/// the same seed, and each verifies the other's proof, so the rows time the
/// same suites. Every row's setup runs it.
#[cfg(not(target_arch = "xtensa"))]
fn check_interop() {
    static CHECKED: Once = Once::new();
    CHECKED.call_once(interop);
}

#[cfg(not(target_arch = "xtensa"))]
fn interop() {
    use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, ECVRF_P256_SHA256_TAI, KeyPair, PublicKey};
    use vrf_rfc9381::ec::edwards25519::tai::{EdVrfEdwards25519Tai, EdVrfEdwards25519TaiSecretKey};
    use vrf_rfc9381::ec::p256::tai::{EcVrfP256Tai, EcVrfP256TaiSecretKey};
    use vrf_rfc9381::{Prover, VRF};

    let ours = KeyPair::from_seed(&ECVRF_EDWARDS25519_SHA512_TAI, &SEED).unwrap();
    let theirs = EdVrfEdwards25519TaiSecretKey::from_slice(&SEED).unwrap();
    let (proof, output) = ours.prove(ALPHA).unwrap();
    let pi = EdVrfEdwards25519Tai.prove(&theirs, ALPHA).unwrap();
    let theirs_output = EdVrfEdwards25519Tai
        .verify(&theirs.verifier(), ALPHA, proof.as_ref())
        .unwrap();
    assert_eq!(output.as_ref(), theirs_output.as_slice());
    let public_key =
        PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, ours.public_key().as_ref()).unwrap();
    public_key.verify(ALPHA, &pi).unwrap();

    let ours = KeyPair::from_seed(&ECVRF_P256_SHA256_TAI, &SEED).unwrap();
    let theirs = EcVrfP256TaiSecretKey::from_slice(&SEED).unwrap();
    let (proof, output) = ours.prove(ALPHA).unwrap();
    let pi = EcVrfP256Tai.prove(&theirs, ALPHA).unwrap();
    let theirs_output = EcVrfP256Tai
        .verify(&theirs.verifier(), ALPHA, proof.as_ref())
        .unwrap();
    assert_eq!(output.as_ref(), theirs_output.as_slice());
    let public_key = PublicKey::new(&ECVRF_P256_SHA256_TAI, ours.public_key().as_ref()).unwrap();
    public_key.verify(ALPHA, &pi).unwrap();
}

/// rind's key pair for `suite`, from the seed.
#[cfg(not(target_arch = "xtensa"))]
fn rind_key(suite: &'static rind::vrf::Algorithm) -> Dit<rind::vrf::KeyPair> {
    check_interop();
    Dit::hold(rind::vrf::KeyPair::from_seed(suite, &SEED).unwrap())
}

/// rind's proof under `suite`, and the public key that verifies it.
#[cfg(not(target_arch = "xtensa"))]
fn rind_proof(
    suite: &'static rind::vrf::Algorithm,
) -> Dit<(rind::vrf::PublicKey, rind::vrf::Proof)> {
    check_interop();
    let key = rind::vrf::KeyPair::from_seed(suite, &SEED).unwrap();
    let (proof, _) = key.prove(ALPHA).unwrap();
    let public_key = rind::vrf::PublicKey::new(suite, key.public_key().as_ref()).unwrap();
    Dit::hold((public_key, proof))
}

#[cfg(not(target_arch = "xtensa"))]
mod vrf_edwards25519_prove {
    use swole::bench;
    use vrf_rfc9381::ec::edwards25519::tai::EdVrfEdwards25519TaiSecretKey;

    use super::*;

    fn rind_input() -> Dit<rind::vrf::KeyPair> {
        rind_key(&rind::vrf::ECVRF_EDWARDS25519_SHA512_TAI)
    }

    #[bench(setup = rind_input)]
    fn rind(key: &Dit<rind::vrf::KeyPair>) {
        black_box(key.prove(ALPHA).unwrap());
    }

    fn rustcrypto_input() -> EdVrfEdwards25519TaiSecretKey {
        use vrf_rfc9381::Prover;
        check_interop();
        EdVrfEdwards25519TaiSecretKey::from_slice(&SEED).unwrap()
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto(key: &EdVrfEdwards25519TaiSecretKey) {
        use vrf_rfc9381::{Proof, Prover};
        let proof = key.prove(ALPHA).unwrap();
        black_box((
            proof.encode_to_pi(),
            proof.proof_to_hash(edwards()).unwrap(),
        ));
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod vrf_p256_prove {
    use swole::bench;
    use vrf_rfc9381::ec::p256::tai::EcVrfP256TaiSecretKey;

    use super::*;

    fn rind_input() -> Dit<rind::vrf::KeyPair> {
        rind_key(&rind::vrf::ECVRF_P256_SHA256_TAI)
    }

    #[bench(setup = rind_input)]
    fn rind(key: &Dit<rind::vrf::KeyPair>) {
        black_box(key.prove(ALPHA).unwrap());
    }

    fn rustcrypto_input() -> EcVrfP256TaiSecretKey {
        use vrf_rfc9381::Prover;
        check_interop();
        EcVrfP256TaiSecretKey::from_slice(&SEED).unwrap()
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto(key: &EcVrfP256TaiSecretKey) {
        use vrf_rfc9381::{Proof, Prover};
        let proof = key.prove(ALPHA).unwrap();
        black_box((proof.encode_to_pi(), proof.proof_to_hash(p256()).unwrap()));
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod vrf_edwards25519_verify {
    use swole::bench;
    use vrf_rfc9381::ec::edwards25519::tai::{
        EdVrfEdwards25519Tai, EdVrfEdwards25519TaiPublicKey, EdVrfEdwards25519TaiSecretKey,
    };

    use super::*;

    type Rind = Dit<(rind::vrf::PublicKey, rind::vrf::Proof)>;

    fn rind_input() -> Rind {
        rind_proof(&rind::vrf::ECVRF_EDWARDS25519_SHA512_TAI)
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Rind) {
        let (public_key, proof) = &**input;
        black_box(public_key.verify(ALPHA, proof.as_ref()).unwrap());
    }

    type RustCrypto = (EdVrfEdwards25519TaiPublicKey, Vec<u8>);

    fn rustcrypto_input() -> RustCrypto {
        use vrf_rfc9381::{Prover, VRF};
        check_interop();
        let key = EdVrfEdwards25519TaiSecretKey::from_slice(&SEED).unwrap();
        let pi = EdVrfEdwards25519Tai.prove(&key, ALPHA).unwrap();
        (key.verifier(), pi)
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((public_key, pi): &RustCrypto) {
        use vrf_rfc9381::VRF;
        black_box(EdVrfEdwards25519Tai.verify(public_key, ALPHA, pi).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod vrf_p256_verify {
    use swole::bench;
    use vrf_rfc9381::ec::p256::tai::{EcVrfP256Tai, EcVrfP256TaiPublicKey, EcVrfP256TaiSecretKey};

    use super::*;

    type Rind = Dit<(rind::vrf::PublicKey, rind::vrf::Proof)>;

    fn rind_input() -> Rind {
        rind_proof(&rind::vrf::ECVRF_P256_SHA256_TAI)
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Rind) {
        let (public_key, proof) = &**input;
        black_box(public_key.verify(ALPHA, proof.as_ref()).unwrap());
    }

    type RustCrypto = (EcVrfP256TaiPublicKey, Vec<u8>);

    fn rustcrypto_input() -> RustCrypto {
        use vrf_rfc9381::{Prover, VRF};
        check_interop();
        let key = EcVrfP256TaiSecretKey::from_slice(&SEED).unwrap();
        let pi = EcVrfP256Tai.prove(&key, ALPHA).unwrap();
        (key.verifier(), pi)
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((public_key, pi): &RustCrypto) {
        use vrf_rfc9381::VRF;
        black_box(EcVrfP256Tai.verify(public_key, ALPHA, pi).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
