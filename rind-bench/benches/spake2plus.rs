//! RFC 9383's SPAKE2+-P256-SHA256-HKDF-SHA256-HMAC-SHA256, one row per step
//! of an exchange: the prover's share, the verifier's share and
//! confirmation, the prover's confirmation and key, and the verifier's key.
//! The steps before each run untimed.
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
use getrandom::{SysRng, rand_core::UnwrapErr};
#[cfg(not(target_arch = "xtensa"))]
use rind::spake2plus::{ProverSecrets, RFC9383, Rfc9383, Session, VerifierRecord};
#[cfg(not(target_arch = "xtensa"))]
use spake2plus::{Context, P256Sha256, Prover, ProverSecret, Verifier};

#[cfg(not(target_arch = "xtensa"))]
const CONTEXT: &[u8] = b"rind-bench";
#[cfg(not(target_arch = "xtensa"))]
const PROVER: &[u8] = b"client";
#[cfg(not(target_arch = "xtensa"))]
const VERIFIER: &[u8] = b"server";
#[cfg(not(target_arch = "xtensa"))]
const SESSION: Session<'static> = Session {
    context: CONTEXT,
    id_prover: PROVER,
    id_verifier: VERIFIER,
};

// w0s and w1s, the password hash's output, which each library reduces into
// the same w0 and w1.
#[cfg(not(target_arch = "xtensa"))]
const W0S: [u8; 40] = [0x11; 40];
#[cfg(not(target_arch = "xtensa"))]
const W1S: [u8; 40] = [0x22; 40];

#[cfg(not(target_arch = "xtensa"))]
fn context() -> Context<'static> {
    Context {
        context: CONTEXT,
        prover_id: PROVER,
        verifier_id: VERIFIER,
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn rng() -> UnwrapErr<SysRng> {
    UnwrapErr(SysRng)
}

#[cfg(not(target_arch = "xtensa"))]
fn rustcrypto_secret() -> ProverSecret<P256Sha256> {
    ProverSecret::from_pbkdf_output(&[W0S, W1S].concat()).unwrap()
}

/// Checks, once a process, that a rind prover and the other library's
/// verifier agree on a key, so the rows time the same protocol. Every row's
/// setup runs it.
#[cfg(not(target_arch = "xtensa"))]
fn check_interop() {
    static CHECKED: Once = Once::new();
    CHECKED.call_once(interop);
}

#[cfg(not(target_arch = "xtensa"))]
fn interop() {
    let prover = ProverSecrets::new(&W0S, &W1S).unwrap();
    let record = rustcrypto_secret().verifier_record();
    let (share_p, prover) = prover.start(&RFC9383, &SESSION).unwrap();
    let (verifier, share_v) = Verifier::start(&record, &context(), &mut rng());
    let (verifier, confirm_v) = verifier
        .receive(&spake2plus::ShareP::from_bytes(share_p.as_ref()).unwrap())
        .unwrap();
    let share_v = rind::spake2plus::Share::new(share_v.as_bytes().as_ref()).unwrap();
    let confirm_v = rind::spake2plus::Confirm::new(confirm_v.as_bytes().as_ref()).unwrap();
    let (confirm_p, prover_key) = prover.finish(&share_v, &confirm_v).unwrap();
    let verifier_key = verifier
        .finish(&spake2plus::ConfirmP::from_bytes(confirm_p.as_ref()).unwrap())
        .unwrap();
    assert_eq!(prover_key.as_ref(), verifier_key.as_bytes().as_ref());
}

#[cfg(not(target_arch = "xtensa"))]
fn secrets() -> ProverSecrets {
    check_interop();
    ProverSecrets::new(&W0S, &W1S).unwrap()
}

#[cfg(not(target_arch = "xtensa"))]
fn record() -> VerifierRecord {
    VerifierRecord::from_w1(&W0S, &W1S).unwrap()
}

/// RustCrypto's prover secret and the verifier's record of it.
#[cfg(not(target_arch = "xtensa"))]
struct RustCrypto {
    secret: ProverSecret<P256Sha256>,
    record: spake2plus::VerifierRecord<P256Sha256>,
    context: Context<'static>,
}

#[cfg(not(target_arch = "xtensa"))]
fn rustcrypto() -> RustCrypto {
    check_interop();
    let secret = rustcrypto_secret();
    let record = secret.verifier_record();
    RustCrypto {
        secret,
        record,
        context: context(),
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod spake2plus_p256_prover_start {
    use swole::bench;

    use super::*;

    fn rind_input() -> Dit<ProverSecrets> {
        Dit::hold(secrets())
    }

    #[bench(setup = rind_input)]
    fn rind(secrets: &Dit<ProverSecrets>) {
        black_box(secrets.start(&RFC9383, &SESSION).unwrap());
    }

    #[bench(setup = super::rustcrypto)]
    fn rustcrypto(input: &RustCrypto) {
        black_box(Prover::start(&input.secret, &input.context, &mut rng()));
    }
}

/// The verifier's share and its confirmation of the prover's share.
#[cfg(not(target_arch = "xtensa"))]
mod spake2plus_p256_verifier_start {
    use swole::bench;

    use super::*;

    type Rind = Dit<(VerifierRecord, rind::spake2plus::Share<Rfc9383>)>;

    fn rind_input() -> Rind {
        let (share_p, _) = secrets().start(&RFC9383, &SESSION).unwrap();
        Dit::hold((record(), share_p))
    }

    #[bench(setup = rind_input)]
    fn rind(input: &Rind) {
        let (record, share_p) = &**input;
        black_box(record.start(&RFC9383, &SESSION, share_p).unwrap());
    }

    type RustCryptoInput = (RustCrypto, spake2plus::ShareP<P256Sha256>);

    fn rustcrypto_input() -> RustCryptoInput {
        let input = super::rustcrypto();
        let (_, share_p) = Prover::start(&input.secret, &context(), &mut rng());
        (input, share_p)
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((input, share_p): &RustCryptoInput) {
        let (verifier, share_v) = Verifier::start(&input.record, &input.context, &mut rng());
        black_box((share_v, verifier.receive(share_p).unwrap()));
    }
}

/// Each side's finish consumes its state, so each call runs the steps before
/// it untimed, and returns its output, which drops untimed.
#[cfg(not(target_arch = "xtensa"))]
mod spake2plus_p256_prover_finish {
    use swole::bench;

    use super::*;

    /// The prover's state and the verifier's reply, with the DIT guard held
    /// across the call that consumes them.
    type Rind = (
        rind::cpu::Dit,
        rind::spake2plus::ProverAwaiting<Rfc9383>,
        rind::spake2plus::Share<Rfc9383>,
        rind::spake2plus::Confirm<Rfc9383>,
    );

    fn rind_input() -> Rind {
        let (share_p, prover) = secrets().start(&RFC9383, &SESSION).unwrap();
        let (share_v, confirm_v, _) = record().start(&RFC9383, &SESSION, &share_p).unwrap();
        (rind::cpu::Dit::hold(), prover, share_v, confirm_v)
    }

    #[bench(setup = rind_input)]
    fn rind((dit, prover, share_v, confirm_v): Rind) -> impl Sized + use<> {
        (prover.finish(&share_v, &confirm_v).unwrap(), dit)
    }

    type RustCryptoInput = (
        Prover<P256Sha256>,
        spake2plus::ShareV<P256Sha256>,
        spake2plus::ConfirmV<P256Sha256>,
    );

    fn rustcrypto_input() -> RustCryptoInput {
        let input = super::rustcrypto();
        let context = context();
        let (prover, share_p) = Prover::start(&input.secret, &context, &mut rng());
        let (verifier, share_v) = Verifier::start(&input.record, &context, &mut rng());
        let (_, confirm_v) = verifier.receive(&share_p).unwrap();
        (prover, share_v, confirm_v)
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((prover, share_v, confirm_v): RustCryptoInput) -> impl Sized + use<> {
        prover
            .receive(&share_v)
            .unwrap()
            .finish(&confirm_v)
            .unwrap()
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod spake2plus_p256_verifier_finish {
    use swole::bench;

    use super::*;

    /// The verifier's state and the prover's confirmation, with the DIT
    /// guard held across the call that consumes them.
    type Rind = (
        rind::cpu::Dit,
        rind::spake2plus::VerifierAwaiting<Rfc9383>,
        rind::spake2plus::Confirm<Rfc9383>,
    );

    fn rind_input() -> Rind {
        let (share_p, prover) = secrets().start(&RFC9383, &SESSION).unwrap();
        let (share_v, confirm_v, verifier) = record().start(&RFC9383, &SESSION, &share_p).unwrap();
        let (confirm_p, _) = prover.finish(&share_v, &confirm_v).unwrap();
        (rind::cpu::Dit::hold(), verifier, confirm_p)
    }

    #[bench(setup = rind_input)]
    fn rind((dit, verifier, confirm_p): Rind) -> impl Sized + use<> {
        (verifier.finish(&confirm_p).unwrap(), dit)
    }

    type RustCryptoInput = (
        spake2plus::VerifierConfirming<P256Sha256>,
        spake2plus::ConfirmP<P256Sha256>,
    );

    fn rustcrypto_input() -> RustCryptoInput {
        let input = super::rustcrypto();
        let context = context();
        let (prover, share_p) = Prover::start(&input.secret, &context, &mut rng());
        let (verifier, share_v) = Verifier::start(&input.record, &context, &mut rng());
        let (verifier, confirm_v) = verifier.receive(&share_p).unwrap();
        let (confirm_p, _) = prover
            .receive(&share_v)
            .unwrap()
            .finish(&confirm_v)
            .unwrap();
        (verifier, confirm_p)
    }

    #[bench(setup = rustcrypto_input)]
    fn rustcrypto((verifier, confirm_p): RustCryptoInput) -> impl Sized + use<> {
        verifier.finish(&confirm_p).unwrap()
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
