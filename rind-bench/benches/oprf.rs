//! RFC 9497's OPRF mode on ristretto255, and its VOPRF mode on P-384,
//! Privacy Pass's privately verifiable tokens: the client's blind, the
//! server's evaluation, and the client's finalize.
//!
//! rind's API takes and returns each message as its wire encoding, so the
//! RustCrypto rows encode and decode theirs too: `voprf` hands over decoded
//! points, and timing it without that would leave out the point decodings
//! and encodings rind's rows pay, each about a tenth of a multiplication.
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
use getrandom::SysRng;
#[cfg(not(target_arch = "xtensa"))]
use p384::NistP384;
#[cfg(not(target_arch = "xtensa"))]
use rind::oprf::{RISTRETTO255_SHA512, voprf as rind_voprf};
#[cfg(not(target_arch = "xtensa"))]
use voprf::{
    BlindedElement, EvaluationElement, OprfClient, OprfServer, Proof, Ristretto255, VoprfClient,
    VoprfServer,
};

#[cfg(not(target_arch = "xtensa"))]
const INPUT: &[u8] = b"a Privacy Pass token input";
#[cfg(not(target_arch = "xtensa"))]
const SEED: [u8; 32] = [0x42; 32];
#[cfg(not(target_arch = "xtensa"))]
const INFO: &[u8] = b"rind-bench";

/// Both derive the same key, and so the same output, by RFC 9497's
/// DeriveKeyPair.
#[cfg(not(target_arch = "xtensa"))]
fn rind_oprf_server() -> rind::oprf::ServerKey {
    rind::oprf::ServerKey::derive(&RISTRETTO255_SHA512, &SEED, INFO).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn oprf_server() -> OprfServer<Ristretto255> {
    OprfServer::<Ristretto255>::new_from_seed(&SEED, INFO).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn voprf_suite() -> &'static rind::oprf::Suite {
    &rind::oprf::P384_SHA384
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_voprf_server() -> rind_voprf::ServerKey {
    rind_voprf::ServerKey::derive(voprf_suite(), &SEED, INFO).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn voprf_server() -> VoprfServer<NistP384> {
    VoprfServer::<NistP384>::new_from_seed(&SEED, INFO).unwrap()
}

/// Checks, once a process, that both libraries give the same output, and
/// that the timed path, blind to finalize, gives it on both. Every row's
/// setup runs it.
#[cfg(not(target_arch = "xtensa"))]
fn check_interop() {
    static CHECKED: Once = Once::new();
    CHECKED.call_once(|| {
        oprf_interop();
        voprf_interop();
    });
}

#[cfg(not(target_arch = "xtensa"))]
fn oprf_interop() {
    let rind_server = rind_oprf_server();
    let server = oprf_server();
    let output = server.evaluate(INPUT).unwrap();
    assert_eq!(
        rind_server.evaluate(INPUT).unwrap().as_ref(),
        output.as_slice()
    );
    let (blind, blinded) = rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap();
    let evaluated = rind_server.blind_evaluate(blinded.as_ref()).unwrap();
    assert_eq!(
        blind.finalize(evaluated.as_ref()).unwrap().as_ref(),
        output.as_slice()
    );
    let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
    let evaluated = server.blind_evaluate(&blinded.message);
    assert_eq!(blinded.state.finalize(INPUT, &evaluated).unwrap(), output);
}

#[cfg(not(target_arch = "xtensa"))]
fn voprf_interop() {
    let rind_server = rind_voprf_server();
    let rind_public =
        rind_voprf::PublicKey::new(voprf_suite(), rind_server.public_key().as_ref()).unwrap();
    let server = voprf_server();
    let output = server.evaluate(INPUT).unwrap();
    assert_eq!(
        rind_server.evaluate(INPUT).unwrap().as_ref(),
        output.as_slice()
    );
    // The timed path checks the proof too.
    let (blind, blinded) = rind_voprf::Blind::new(voprf_suite(), INPUT).unwrap();
    let (evaluated, proof) = rind_server.blind_evaluate(blinded.as_ref()).unwrap();
    assert_eq!(
        blind
            .finalize(evaluated.as_ref(), proof.as_ref(), &rind_public)
            .unwrap()
            .as_ref(),
        output.as_slice()
    );
    let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
    let evaluated = server.blind_evaluate(&mut SysRng, &blinded.message);
    let finalized = blinded
        .state
        .finalize(
            INPUT,
            &evaluated.message,
            &evaluated.proof,
            server.get_public_key(),
        )
        .unwrap();
    assert_eq!(finalized, output);
}

#[cfg(not(target_arch = "xtensa"))]
fn checked() {
    check_interop();
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_checked() -> Dit<()> {
    check_interop();
    Dit::hold(())
}

#[cfg(not(target_arch = "xtensa"))]
mod oprf_ristretto255_blind {
    use swole::bench;

    use super::*;

    #[bench(setup = rind_checked)]
    fn rind(_: &Dit<()>) {
        black_box(rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap());
    }

    #[bench(setup = checked)]
    fn rustcrypto(_: &()) {
        let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
        black_box((blinded.state, blinded.message.serialize()));
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod oprf_ristretto255_evaluate {
    use swole::bench;

    use super::*;

    type Rind = Dit<(rind::oprf::ServerKey, rind::oprf::BlindedElement)>;

    fn rind_input() -> Rind {
        check_interop();
        let (_, blinded) = rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap();
        Dit::hold((rind_oprf_server(), blinded))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Rind) {
        let (server, blinded) = &**input;
        black_box(server.blind_evaluate(blinded.as_ref()).unwrap());
    }

    type RustCrypto = (OprfServer<Ristretto255>, Vec<u8>);

    fn rustcrypto_input() -> RustCrypto {
        check_interop();
        let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
        (oprf_server(), blinded.message.serialize().to_vec())
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((server, blinded): &RustCrypto) {
        let blinded = BlindedElement::<Ristretto255>::deserialize(blinded).unwrap();
        black_box(server.blind_evaluate(&blinded).serialize());
    }
}

/// rind's finalize consumes its blind, so each call blinds afresh, untimed.
#[cfg(not(target_arch = "xtensa"))]
mod oprf_ristretto255_finalize {
    use swole::bench;

    use super::*;

    /// A blind and its evaluation, with the DIT guard held across the call
    /// that consumes them.
    type Rind = (
        rind::cpu::Dit,
        rind::oprf::Blind,
        rind::oprf::EvaluatedElement,
    );

    fn rind_input() -> Rind {
        check_interop();
        let (blind, blinded) = rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap();
        let evaluated = rind_oprf_server().blind_evaluate(blinded.as_ref()).unwrap();
        (rind::cpu::Dit::hold(), blind, evaluated)
    }

    #[bench(setup = rind_input)]
    fn rind((dit, blind, evaluated): Rind) -> impl Sized + use<> {
        (blind.finalize(evaluated.as_ref()).unwrap(), dit)
    }

    type RustCrypto = (OprfClient<Ristretto255>, Vec<u8>);

    fn rustcrypto_input() -> RustCrypto {
        check_interop();
        let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
        let evaluated = oprf_server().blind_evaluate(&blinded.message).serialize();
        (blinded.state, evaluated.to_vec())
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((client, evaluated): &RustCrypto) {
        let evaluated = EvaluationElement::<Ristretto255>::deserialize(evaluated).unwrap();
        black_box(client.finalize(INPUT, &evaluated).unwrap());
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod voprf_p384_blind {
    use swole::bench;

    use super::*;

    #[bench(setup = rind_checked)]
    fn rind(_: &Dit<()>) {
        black_box(rind_voprf::Blind::new(voprf_suite(), INPUT).unwrap());
    }

    #[bench(setup = checked)]
    fn rustcrypto(_: &()) {
        let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
        black_box((blinded.state, blinded.message.serialize()));
    }
}

/// The evaluation includes the proof.
#[cfg(not(target_arch = "xtensa"))]
mod voprf_p384_evaluate {
    use swole::bench;

    use super::*;

    type Rind = Dit<(rind_voprf::ServerKey, rind::oprf::BlindedElement)>;

    fn rind_input() -> Rind {
        check_interop();
        let (_, blinded) = rind_voprf::Blind::new(voprf_suite(), INPUT).unwrap();
        Dit::hold((rind_voprf_server(), blinded))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Rind) {
        let (server, blinded) = &**input;
        black_box(server.blind_evaluate(blinded.as_ref()).unwrap());
    }

    type RustCrypto = (VoprfServer<NistP384>, Vec<u8>);

    fn rustcrypto_input() -> RustCrypto {
        check_interop();
        let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
        (voprf_server(), blinded.message.serialize().to_vec())
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((server, blinded): &RustCrypto) {
        let blinded = BlindedElement::<NistP384>::deserialize(blinded).unwrap();
        let evaluated = server.blind_evaluate(&mut SysRng, &blinded);
        black_box((evaluated.message.serialize(), evaluated.proof.serialize()));
    }
}

/// The finalize includes the proof's verification.
#[cfg(not(target_arch = "xtensa"))]
mod voprf_p384_finalize {
    use swole::bench;

    use super::*;

    /// A blind, its evaluation and proof, and the server's public key, with
    /// the DIT guard held across the call that consumes them.
    type Rind = (
        rind::cpu::Dit,
        rind_voprf::Blind,
        rind_voprf::EvaluatedElements,
        rind_voprf::Proof,
        rind_voprf::PublicKey,
    );

    fn rind_input() -> Rind {
        check_interop();
        let server = rind_voprf_server();
        let public_key =
            rind_voprf::PublicKey::new(voprf_suite(), server.public_key().as_ref()).unwrap();
        let (blind, blinded) = rind_voprf::Blind::new(voprf_suite(), INPUT).unwrap();
        let (evaluated, proof) = server.blind_evaluate(blinded.as_ref()).unwrap();
        (rind::cpu::Dit::hold(), blind, evaluated, proof, public_key)
    }

    #[bench(setup = rind_input)]
    fn rind((dit, blind, evaluated, proof, public_key): Rind) -> impl Sized + use<> {
        let output = blind
            .finalize(evaluated.as_ref(), proof.as_ref(), &public_key)
            .unwrap();
        (output, dit, public_key)
    }

    struct RustCrypto {
        client: VoprfClient<NistP384>,
        message: Vec<u8>,
        proof: Vec<u8>,
        server: VoprfServer<NistP384>,
    }

    fn rustcrypto_input() -> RustCrypto {
        check_interop();
        let server = voprf_server();
        let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
        let evaluated = server.blind_evaluate(&mut SysRng, &blinded.message);
        RustCrypto {
            client: blinded.state,
            message: evaluated.message.serialize().to_vec(),
            proof: evaluated.proof.serialize().to_vec(),
            server,
        }
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto(input: &RustCrypto) {
        let message = EvaluationElement::<NistP384>::deserialize(&input.message).unwrap();
        let proof = Proof::<NistP384>::deserialize(&input.proof).unwrap();
        black_box(
            input
                .client
                .finalize(INPUT, &message, &proof, input.server.get_public_key())
                .unwrap(),
        );
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
