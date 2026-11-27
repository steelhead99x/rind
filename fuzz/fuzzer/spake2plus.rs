#![no_main]

//! SPAKE2+ in both suites, under password scalars and session labels the
//! fuzzer writes, with each message tampered with in flight: the prover's
//! share, the verifier's share and confirmation, the prover's
//! confirmation, and the context the verifier binds.
//!
//! An untampered handshake agrees on the key, and a tampered one, or one
//! whose `w0` or `w1` reduces to zero, fails with `BadSignature` on the side
//! that checks it, rather than panicking or agreeing. Lengths past the
//! limits are refused, a stored record loads as the record it was saved
//! from, and its `L` is the oracle's `w1 * G`.
//!
//! No reference implements SPAKE2+ on aws-lc, so RFC 9383's suite also runs
//! against pakery-spake2plus, over RustCrypto's P-256, which shares no code
//! with rind, at ephemeral scalars the fuzzer writes: each side finishes a
//! handshake with the other's, to the same key. Matter's suite differs only
//! in its key schedule, which its vectors check.

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use num_bigint::BigUint;
use rind::Error;
use rind::spake2plus::*;

mod edit;
mod oracle;

/// The P-256 group order, big-endian.
const ORDER: [u8; 32] = [
    0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
    0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63, 0x25, 0x51,
];

/// The longest `w0` or `w1` rind takes, and the longest label.
const MAX_SCALAR: usize = 128;
const MAX_LABEL: usize = 1024;

#[derive(Arbitrary, Debug)]
struct Input {
    matter: bool,
    w0: Vec<u8>,
    w1: Vec<u8>,
    /// Whether the verifier loads its record from `w0` and `L`, as stored,
    /// rather than from `w0` and `w1`.
    stored: bool,
    context: Vec<u8>,
    id_prover: Vec<u8>,
    id_verifier: Vec<u8>,
    /// The oracle's ephemeral scalars, reduced.
    x: [u8; 32],
    y: [u8; 32],
    verifier_context: edit::Edit,
    share_p: edit::Edit,
    share_v: edit::Edit,
    confirm_v: edit::Edit,
    confirm_p: edit::Edit,
}

fuzz_target!(|input: Input| {
    let prover = ProverSecrets::new(&input.w0, &input.w1);
    let record = VerifierRecord::from_w1(&input.w0, &input.w1);
    let fits = |w: &[u8]| (1..=MAX_SCALAR).contains(&w.len());
    if !fits(&input.w0) || !fits(&input.w1) {
        assert_eq!(prover.unwrap_err(), Error::WrongLength);
        assert_eq!(record.unwrap_err(), Error::WrongLength);
        return;
    }
    let (prover, record) = (prover.unwrap(), record.unwrap());
    let (w0, w1) = (reduce(&input.w0), reduce(&input.w1));

    // `L` is `w1 * G`, which a zero `w1` makes the identity, which a stored
    // record cannot hold.
    let l = record.l();
    let stored = VerifierRecord::from_record(&input.w0, &l);
    let w1_zero = w1 == [0; 32];
    match &stored {
        Ok(stored) => {
            assert!(!w1_zero);
            assert_eq!(stored.l(), l);
            assert_eq!(&l[..], oracle::Nist::public_key(&oracle::p256(), &w1));
        }
        Err(e) => {
            assert!(w1_zero);
            assert!(matches!(e, Error::KeyRejected(_)), "{e:?}");
        }
    }
    let record = match stored {
        Ok(stored) if input.stored => stored,
        _ => record,
    };

    let session = Session {
        context: &input.context,
        id_prover: &input.id_prover,
        id_verifier: &input.id_verifier,
    };
    let zero = w0 == [0; 32] || w1_zero;
    if input.matter {
        handshake(&MATTER_PASE, &input, &prover, &record, &session, zero);
    } else {
        handshake(&RFC9383, &input, &prover, &record, &session, zero);
        if session_fits(&session) && !zero {
            pakery::check(&input, &prover, &record, &session, &w0, &l);
        }
    }
});

/// Whether every label is at most `MAX_LABEL` bytes.
fn session_fits(session: &Session<'_>) -> bool {
    [session.context, session.id_prover, session.id_verifier]
        .iter()
        .all(|label| label.len() <= MAX_LABEL)
}

/// `bytes`, big-endian, reduced mod the group order, in 32 bytes.
fn reduce(bytes: &[u8]) -> [u8; 32] {
    let reduced = BigUint::from_bytes_be(bytes) % BigUint::from_bytes_be(&ORDER);
    let reduced = reduced.to_bytes_be();
    let mut out = [0; 32];
    out[32 - reduced.len()..].copy_from_slice(&reduced);
    out
}

/// rind's prover and verifier, with the input's edits: the key agrees
/// exactly when nothing changed and no password scalar is zero.
fn handshake<S: 'static>(
    suite: &'static Suite<S>,
    input: &Input,
    prover: &ProverSecrets,
    record: &VerifierRecord,
    session: &Session<'_>,
    zero: bool,
) {
    let started = prover.start(suite, session);
    if !session_fits(session) {
        assert_eq!(started.unwrap_err(), Error::WrongLength);
        return;
    }
    let (share_p, prover) = started.unwrap();

    let mut bytes = share_p.as_ref().to_vec();
    let mut changed = input.share_p.apply(&mut bytes);
    let Ok(share_p) = Share::<S>::new(&bytes) else {
        assert!(changed);
        return;
    };
    // The verifier binds a context edited from the prover's, which is no
    // longer, so it fits too.
    let mut context = input.context.clone();
    changed |= input.verifier_context.apply(&mut context);
    let verifier_session = Session {
        context: &context,
        ..*session
    };
    let (share_v, confirm_v, verifier) = match record.start(suite, &verifier_session, &share_p) {
        Ok(started) => started,
        // Only a share of `w0 * M` makes the verifier's point the identity.
        Err(e) => {
            assert_eq!(e, Error::BadSignature);
            assert!(changed);
            return;
        }
    };

    let mut bytes = share_v.as_ref().to_vec();
    changed |= input.share_v.apply(&mut bytes);
    let Ok(share_v) = Share::<S>::new(&bytes) else {
        assert!(changed);
        return;
    };
    let mut bytes = confirm_v.as_ref().to_vec();
    changed |= input.confirm_v.apply(&mut bytes);
    let Ok(confirm_v) = Confirm::<S>::new(&bytes) else {
        assert!(changed);
        return;
    };

    let (confirm_p, key) = match prover.finish(&share_v, &confirm_v) {
        Ok(finished) => finished,
        Err(e) => {
            assert_eq!(e, Error::BadSignature);
            assert!(changed || zero);
            return;
        }
    };
    assert!(!changed && !zero);
    let mut bytes = confirm_p.as_ref().to_vec();
    let changed = input.confirm_p.apply(&mut bytes);
    let Ok(confirm_p) = Confirm::<S>::new(&bytes) else {
        assert!(changed);
        return;
    };
    match verifier.finish(&confirm_p) {
        Ok(verifier_key) => {
            assert!(!changed);
            assert_eq!(verifier_key.as_ref(), key.as_ref());
        }
        Err(e) => {
            assert_eq!(e, Error::BadSignature);
            assert!(changed);
        }
    }
}

/// pakery-spake2plus's RFC 9383 suite on P-256.
mod pakery {
    use p256::elliptic_curve::ff::PrimeField;
    use pakery_crypto::{
        HkdfSha256, HmacSha256, P256Group, SPAKE2_P256_M_COMPRESSED, SPAKE2_P256_N_COMPRESSED,
        Sha256Hash,
    };
    use pakery_spake2plus::{Prover, Spake2PlusCiphersuite, Verifier};
    use rind::spake2plus::*;

    use super::{Input, reduce};

    struct Pakery;

    impl Spake2PlusCiphersuite for Pakery {
        type Group = P256Group;
        type Hash = Sha256Hash;
        type Kdf = HkdfSha256;
        type Mac = HmacSha256;
        const NH: usize = 32;
        const M_BYTES: &'static [u8] = &SPAKE2_P256_M_COMPRESSED;
        const N_BYTES: &'static [u8] = &SPAKE2_P256_N_COMPRESSED;
    }

    /// The reduced scalar `bytes`, or one where it reduces to zero.
    fn scalar(bytes: &[u8]) -> p256::Scalar {
        let mut reduced = reduce(bytes);
        if reduced == [0; 32] {
            reduced[31] = 1;
        }
        p256::Scalar::from_repr(reduced.into()).unwrap()
    }

    /// Each side's prover finishes a handshake with the other's verifier,
    /// at the input's ephemeral scalars on pakery's side, to the same key.
    pub fn check(
        input: &Input,
        prover: &ProverSecrets,
        record: &VerifierRecord,
        session: &Session<'_>,
        w0: &[u8; 32],
        l: &[u8; 65],
    ) {
        let (w0, w1) = (scalar(w0), scalar(&input.w1));
        let labels = (session.context, session.id_prover, session.id_verifier);

        // Their prover, our verifier.
        let (share_p, theirs) = Prover::<Pakery>::start_with_scalar(
            &w0,
            &w1,
            &scalar(&input.x),
            labels.0,
            labels.1,
            labels.2,
        )
        .unwrap();
        let share_p = Share::new(&share_p).unwrap();
        let (share_v, confirm_v, ours) = record.start(&RFC9383, session, &share_p).unwrap();
        let finished = theirs
            .finish(share_v.as_ref(), confirm_v.as_ref())
            .expect("pakery refused rind's verifier");
        let key = ours
            .finish(&Confirm::new(&finished.confirm_p).unwrap())
            .unwrap();
        assert_eq!(key.as_ref(), finished.session_key.as_bytes());

        // Our prover, their verifier.
        let (share_p, ours) = prover.start(&RFC9383, session).unwrap();
        let (share_v, confirm_v, theirs) = Verifier::<Pakery>::start_with_scalar(
            share_p.as_ref(),
            &w0,
            l,
            &scalar(&input.y),
            labels.0,
            labels.1,
            labels.2,
        )
        .unwrap();
        let (confirm_p, key) = ours
            .finish(
                &Share::new(&share_v).unwrap(),
                &Confirm::new(&confirm_v).unwrap(),
            )
            .expect("rind refused pakery's verifier");
        let theirs = theirs
            .finish(confirm_p.as_ref())
            .expect("pakery refused rind's prover");
        assert_eq!(key.as_ref(), theirs.session_key.as_bytes());
    }
}
