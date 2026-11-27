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
mod criterion;
#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
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

#[cfg(not(target_arch = "xtensa"))]
fn oprf(c: &mut Criterion) {
    // Both derive the same key, and so the same output, by RFC 9497's
    // DeriveKeyPair.
    let rind_server = rind::oprf::ServerKey::derive(&RISTRETTO255_SHA512, &SEED, INFO).unwrap();
    let server = OprfServer::<Ristretto255>::new_from_seed(&SEED, INFO).unwrap();
    let output = server.evaluate(INPUT).unwrap();
    assert_eq!(
        rind_server.evaluate(INPUT).unwrap().as_ref(),
        output.as_slice()
    );
    // The timed path, blind to finalize, gives that same output on both.
    let (blind, blinded) = rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap();
    let evaluated = rind_server.blind_evaluate(blinded.as_ref()).unwrap();
    assert_eq!(
        blind.finalize(evaluated.as_ref()).unwrap().as_ref(),
        output.as_slice()
    );
    let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
    let evaluated = server.blind_evaluate(&blinded.message);
    assert_eq!(blinded.state.finalize(INPUT, &evaluated).unwrap(), output);

    let mut group = c.benchmark_group("oprf-ristretto255-blind");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let _dit = criterion::rind_dit();
        b.iter(|| black_box(rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        b.iter(|| {
            let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
            black_box((blinded.state, blinded.message.serialize()))
        });
    });
    group.finish();

    let mut group = c.benchmark_group("oprf-ristretto255-evaluate");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let _dit = criterion::rind_dit();
        let (_, blinded) = rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap();
        b.iter(|| black_box(rind_server.blind_evaluate(blinded.as_ref()).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
        let blinded = blinded.message.serialize();
        b.iter(|| {
            let blinded = BlindedElement::<Ristretto255>::deserialize(&blinded).unwrap();
            black_box(server.blind_evaluate(&blinded).serialize())
        });
    });
    group.finish();

    // rind's finalize consumes its blind, so each iteration blinds afresh,
    // untimed.
    let mut group = c.benchmark_group("oprf-ristretto255-finalize");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let _dit = criterion::rind_dit();
        b.iter_batched(
            || {
                let (blind, blinded) = rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap();
                (blind, rind_server.blind_evaluate(blinded.as_ref()).unwrap())
            },
            |(blind, evaluated)| black_box(blind.finalize(evaluated.as_ref()).unwrap()),
            BatchSize::SmallInput,
        );
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
        let evaluated = server.blind_evaluate(&blinded.message).serialize();
        b.iter(|| {
            let evaluated = EvaluationElement::<Ristretto255>::deserialize(&evaluated).unwrap();
            black_box(blinded.state.finalize(INPUT, &evaluated).unwrap())
        });
    });
}

#[cfg(not(target_arch = "xtensa"))]
fn voprf(c: &mut Criterion) {
    let suite = &rind::oprf::P384_SHA384;
    let rind_server = rind_voprf::ServerKey::derive(suite, &SEED, INFO).unwrap();
    let rind_public = rind_voprf::PublicKey::new(suite, rind_server.public_key().as_ref()).unwrap();
    let server = VoprfServer::<NistP384>::new_from_seed(&SEED, INFO).unwrap();
    let output = server.evaluate(INPUT).unwrap();
    assert_eq!(
        rind_server.evaluate(INPUT).unwrap().as_ref(),
        output.as_slice()
    );
    // The timed path, blind to finalize with the proof, gives that same
    // output on both.
    let (blind, blinded) = rind_voprf::Blind::new(suite, INPUT).unwrap();
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

    let mut group = c.benchmark_group("voprf-p384-blind");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let _dit = criterion::rind_dit();
        b.iter(|| black_box(rind_voprf::Blind::new(suite, INPUT).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        b.iter(|| {
            let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
            black_box((blinded.state, blinded.message.serialize()))
        });
    });
    group.finish();

    // The evaluation includes the proof.
    let mut group = c.benchmark_group("voprf-p384-evaluate");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let _dit = criterion::rind_dit();
        let (_, blinded) = rind_voprf::Blind::new(suite, INPUT).unwrap();
        b.iter(|| black_box(rind_server.blind_evaluate(blinded.as_ref()).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
        let blinded = blinded.message.serialize();
        b.iter(|| {
            let blinded = BlindedElement::<NistP384>::deserialize(&blinded).unwrap();
            let evaluated = server.blind_evaluate(&mut SysRng, &blinded);
            black_box((evaluated.message.serialize(), evaluated.proof.serialize()))
        });
    });
    group.finish();

    // The finalize includes the proof's verification.
    let mut group = c.benchmark_group("voprf-p384-finalize");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let _dit = criterion::rind_dit();
        b.iter_batched(
            || {
                let (blind, blinded) = rind_voprf::Blind::new(suite, INPUT).unwrap();
                (blind, rind_server.blind_evaluate(blinded.as_ref()).unwrap())
            },
            |(blind, (evaluated, proof))| {
                black_box(
                    blind
                        .finalize(evaluated.as_ref(), proof.as_ref(), &rind_public)
                        .unwrap(),
                )
            },
            BatchSize::SmallInput,
        );
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
        let evaluated = server.blind_evaluate(&mut SysRng, &blinded.message);
        let (message, proof) = (evaluated.message.serialize(), evaluated.proof.serialize());
        let public_key = server.get_public_key();
        b.iter(|| {
            let message = EvaluationElement::<NistP384>::deserialize(&message).unwrap();
            let proof = Proof::<NistP384>::deserialize(&proof).unwrap();
            black_box(
                blinded
                    .state
                    .finalize(INPUT, &message, &proof, public_key)
                    .unwrap(),
            )
        });
    });
}

#[cfg(not(target_arch = "xtensa"))]
criterion_group!(benches, oprf, voprf);
#[cfg(not(target_arch = "xtensa"))]
criterion_main!(benches);
