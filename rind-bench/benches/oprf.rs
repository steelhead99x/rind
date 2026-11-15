//! RFC 9497's OPRF mode on ristretto255, and its VOPRF mode on P-384,
//! Privacy Pass's privately verifiable tokens: the client's blind, the
//! server's evaluation, and the client's finalize.
mod criterion;
use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};
use getrandom::SysRng;
use p384::NistP384;
use rind::oprf::{RISTRETTO255_SHA512, voprf as rind_voprf};
use voprf::{OprfClient, OprfServer, Ristretto255, VoprfClient, VoprfServer};

const INPUT: &[u8] = b"a Privacy Pass token input";
const SEED: [u8; 32] = [0x42; 32];
const INFO: &[u8] = b"rind-bench";

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
        b.iter(|| black_box(rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        b.iter(|| black_box(OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap()));
    });
    group.finish();

    let mut group = c.benchmark_group("oprf-ristretto255-evaluate");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let (_, blinded) = rind::oprf::Blind::new(&RISTRETTO255_SHA512, INPUT).unwrap();
        b.iter(|| black_box(rind_server.blind_evaluate(blinded.as_ref()).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = OprfClient::<Ristretto255>::blind(INPUT, &mut SysRng).unwrap();
        b.iter(|| black_box(server.blind_evaluate(&blinded.message)));
    });
    group.finish();

    // rind's finalize consumes its blind, so each iteration blinds afresh,
    // untimed.
    let mut group = c.benchmark_group("oprf-ristretto255-finalize");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
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
        let evaluated = server.blind_evaluate(&blinded.message);
        b.iter(|| black_box(blinded.state.finalize(INPUT, &evaluated).unwrap()));
    });
}

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
        b.iter(|| black_box(rind_voprf::Blind::new(suite, INPUT).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        b.iter(|| black_box(VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap()));
    });
    group.finish();

    // The evaluation includes the proof.
    let mut group = c.benchmark_group("voprf-p384-evaluate");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
        let (_, blinded) = rind_voprf::Blind::new(suite, INPUT).unwrap();
        b.iter(|| black_box(rind_server.blind_evaluate(blinded.as_ref()).unwrap()));
    });
    group.bench_function("rustcrypto", |b| {
        let blinded = VoprfClient::<NistP384>::blind(INPUT, &mut SysRng).unwrap();
        b.iter(|| black_box(server.blind_evaluate(&mut SysRng, &blinded.message)));
    });
    group.finish();

    // The finalize includes the proof's verification.
    let mut group = c.benchmark_group("voprf-p384-finalize");
    group.throughput(Throughput::Elements(1));
    group.bench_function("rind", |b| {
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
        let public_key = server.get_public_key();
        b.iter(|| {
            black_box(
                blinded
                    .state
                    .finalize(INPUT, &evaluated.message, &evaluated.proof, public_key)
                    .unwrap(),
            )
        });
    });
}

criterion_group!(benches, oprf, voprf);
criterion_main!(benches);
