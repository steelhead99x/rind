#![no_main]

//! FROST in every suite, against the Zcash Foundation's frost crates,
//! which share no code with rind on x86_64 and aarch64, under a group key,
//! threshold, and signer set the fuzzer writes, signers split between rind
//! and the reference, and each value tampered with in flight: the dealer's
//! commitment, a signing share, a participant's commitments, a signature
//! share, and the signature.
//!
//! The reference's dealer splits the fuzzer's key, so edge-case keys are
//! reached, and draws its coefficients and nonces from a generator the
//! input seeds; rind's own nonces are fresh. rind loads every share the
//! reference deals and refuses each tampered one, and verifies a share
//! against a tampered commitment exactly when the reference does; its own
//! dealer refuses the thresholds the reference's does and deals shares the
//! reference loads. An untampered round with enough signers aggregates to
//! the reference's signature, which both verify. Too few signers, a
//! tampered commitment, or a tampered share is refused where its step
//! documents, rather than panicking or aggregating, and a tampered
//! signature verifies on rind exactly when it does on the reference.
//!
//! On armv7 and the portable backend, frost-ed25519 and frost-ristretto255
//! run curve25519-dalek, as rind does, so there only frost-p256 is
//! independent of rind's arithmetic.

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::Error;
use rind::frost::*;

mod edit;

/// Every suite's identifiers and scalars are 32 bytes.
const SCALAR_LEN: usize = 32;

/// The most participants a dealer splits the key between.
const MAX_SIGNERS: u8 = 6;

#[derive(Arbitrary, Debug)]
struct Input {
    suite: u8,
    /// The group's signing key, as the reference deserializes it.
    key: Vec<u8>,
    min_signers: u8,
    max_signers: u8,
    /// Seeds the reference's coefficients and nonces.
    seed: [u8; 32],
    /// Which participants sign, by bit.
    signers: u8,
    /// Which signers run rind, by bit; the rest run the reference.
    ours: u8,
    message: Vec<u8>,
    commitment: edit::Edit,
    share: edit::Edit,
    /// Which signer's commitments `commitments` edits.
    edited: u8,
    commitments: edit::Edit,
    signature_share: edit::Edit,
    signature: edit::Edit,
}

fuzz_target!(|input: Input| {
    match input.suite % 3 {
        0 => differential!(frost_ed25519, &ED25519_SHA512, &input),
        1 => differential!(frost_ristretto255, &RISTRETTO255_SHA512, &input),
        _ => differential!(frost_p256, &P256_SHA256, &input),
    }
});

/// One round of FROST in `$suite`, against `$frost`.
macro_rules! differential {
    ($frost:ident, $suite:expr, $input:expr) => {{
        use std::collections::BTreeMap;

        use $frost::keys::{
            IdentifierList, KeyPackage, SecretShare, SigningShare as FrostShare,
            VerifiableSecretSharingCommitment, split,
        };
        use $frost::round1::{NonceCommitment, SigningCommitments};
        use $frost::{
            Identifier as FrostId, Signature as FrostSignature, SigningKey,
            SigningPackage as FrostPackage, round1, round2,
        };

        let (suite, input): (&'static Suite, &Input) = ($suite, $input);
        let mut rng = Rng::new(&input.seed);
        let (min, max) = (
            u16::from(input.min_signers % (MAX_SIGNERS + 1)),
            u16::from(input.max_signers % (MAX_SIGNERS + 1)),
        );

        // rind's dealer refuses the thresholds the reference's does, and
        // deals shares the reference loads.
        let dealt = deal(suite, min, max);
        let Ok(key) = SigningKey::deserialize(&input.key) else {
            return;
        };
        let split = split(&key, max, min, IdentifierList::Default, &mut rng);
        assert_eq!(dealt.is_ok(), split.is_ok());
        let (Ok((shares, commitment)), Ok((secret_shares, pubkeys))) = (dealt, split) else {
            return;
        };
        let theirs =
            VerifiableSecretSharingCommitment::deserialize_whole(commitment.as_ref()).unwrap();
        for share in &shares {
            let id = FrostId::deserialize(share.identifier().as_ref()).unwrap();
            let scalar = FrostShare::deserialize(share.to_scalar().as_ref()).unwrap();
            KeyPackage::try_from(SecretShare::new(id, scalar, theirs.clone()))
                .expect("the reference refused a share rind dealt");
        }

        // rind loads the reference's commitment and shares, and refuses
        // the shares tampered. A tampered commitment rind loads, the
        // reference loads too, and both judge each share against it alike:
        // some edits keep a share valid, such as swapping two terms, whose
        // sum is all participant 1's check reads.
        let vss = secret_shares
            .values()
            .next()
            .unwrap()
            .commitment()
            .serialize_whole()
            .unwrap();
        let commitment = VssCommitment::new(suite, &vss).unwrap();
        assert_eq!(commitment.min_signers(), min);
        assert_eq!(
            commitment.public_key().as_ref(),
            pubkeys.verifying_key().serialize().unwrap()
        );
        let mut edited = vss.clone();
        input.commitment.apply(&mut edited);
        let edited = VssCommitment::new(suite, &edited).ok().map(|ours| {
            let theirs = VerifiableSecretSharingCommitment::deserialize_whole(&edited)
                .expect("the reference refused a commitment rind loaded");
            (ours, theirs)
        });
        let mut ours = BTreeMap::new();
        for (id, share) in &secret_shares {
            let identifier = Identifier::new(suite, &id.serialize()).unwrap();
            let scalar = share.signing_share().serialize();
            let loaded = SigningShare::from_scalar(&identifier, &scalar, &commitment).unwrap();
            assert_eq!(loaded.to_scalar().as_ref(), &scalar[..]);
            if let Some((ours, theirs)) = &edited {
                let loaded = SigningShare::from_scalar(&identifier, &scalar, ours);
                let valid = KeyPackage::try_from(SecretShare::new(
                    *id,
                    *share.signing_share(),
                    theirs.clone(),
                ));
                assert_eq!(loaded.is_ok(), valid.is_ok());
            }
            let mut tampered = scalar.clone();
            if input.share.apply(&mut tampered) {
                assert!(SigningShare::from_scalar(&identifier, &tampered, &commitment).is_err());
            }
            ours.insert(*id, loaded);
        }

        // Each signer commits: rind's from its own nonces, the reference's
        // from the seeded ones.
        let signers: Vec<FrostId> = (1..=max)
            .filter(|n| input.signers >> (n - 1) & 1 == 1)
            .map(|n| FrostId::try_from(n).unwrap())
            .collect();
        let is_ours = |id: &FrostId| {
            let n = signers.iter().position(|s| s == id).unwrap();
            input.ours >> n & 1 == 1
        };
        let mut our_nonces = BTreeMap::new();
        let mut their_nonces = BTreeMap::new();
        let mut commitments = Vec::new();
        for id in &signers {
            if is_ours(id) {
                let (nonces, c) = SigningNonces::commit(&ours[id]).unwrap();
                our_nonces.insert(*id, nonces);
                commitments.push(c);
            } else {
                let (nonces, c) = round1::commit(secret_shares[id].signing_share(), &mut rng);
                their_nonces.insert(*id, nonces);
                commitments.push(commitments_of(suite, &c, id));
            }
        }
        if signers.is_empty() {
            assert_eq!(
                SigningPackage::new(commitment.public_key(), &commitments, &input.message)
                    .unwrap_err(),
                Error::WrongLength
            );
            return;
        }

        // A participant's tampered commitments: the package is refused,
        // or that participant refuses to sign it.
        let index = usize::from(input.edited) % signers.len();
        let mut bytes = commitments[index].as_ref().to_vec();
        if input.commitments.apply(&mut bytes) {
            let mut tampered = commitments.clone();
            let Ok(edited) = Commitments::new(suite, &bytes) else {
                return;
            };
            tampered[index] = edited;
            let Ok(package) =
                SigningPackage::new(commitment.public_key(), &tampered, &input.message)
            else {
                return;
            };
            let id = &signers[index];
            match our_nonces.remove(id) {
                Some(nonces) => assert!(nonces.sign(&ours[id], &package).is_err()),
                None => {
                    let package = FrostPackage::new(
                        tampered.iter().map(frost_commitments).collect(),
                        &input.message,
                    );
                    let key_package = KeyPackage::try_from(secret_shares[id].clone()).unwrap();
                    assert!(round2::sign(&package, &their_nonces[id], &key_package).is_err());
                }
            }
            return;
        }

        let package =
            SigningPackage::new(commitment.public_key(), &commitments, &input.message).unwrap();
        let frost_package = FrostPackage::new(
            commitments.iter().map(frost_commitments).collect(),
            &input.message,
        );
        // Below the threshold, every signer refuses to sign.
        if signers.len() < usize::from(min) {
            for id in &signers {
                match our_nonces.remove(id) {
                    Some(nonces) => assert_eq!(
                        nonces.sign(&ours[id], &package).unwrap_err(),
                        Error::WrongLength
                    ),
                    None => {
                        let key_package = KeyPackage::try_from(secret_shares[id].clone()).unwrap();
                        assert!(
                            round2::sign(&frost_package, &their_nonces[id], &key_package).is_err()
                        );
                    }
                }
            }
            return;
        }

        let mut shares = Vec::new();
        let mut frost_shares = BTreeMap::new();
        for id in &signers {
            let share = match our_nonces.remove(id) {
                Some(nonces) => nonces.sign(&ours[id], &package).unwrap(),
                None => {
                    let key_package = KeyPackage::try_from(secret_shares[id].clone()).unwrap();
                    let share = round2::sign(&frost_package, &their_nonces[id], &key_package)
                        .unwrap()
                        .serialize();
                    SignatureShare::new(suite, &[id.serialize(), share].concat()).unwrap()
                }
            };
            package.verify_share(&share, &commitment).unwrap();
            frost_shares.insert(
                *id,
                round2::SignatureShare::deserialize(&share.as_ref()[SCALAR_LEN..]).unwrap(),
            );
            shares.push(share);
        }

        // A tampered share fails its own check and the aggregate.
        let index = usize::from(input.edited) % shares.len();
        let mut bytes = shares[index].as_ref().to_vec();
        if input.signature_share.apply(&mut bytes) {
            let Ok(edited) = SignatureShare::new(suite, &bytes) else {
                return;
            };
            assert!(package.verify_share(&edited, &commitment).is_err());
            let mut tampered = shares.clone();
            tampered[index] = edited;
            assert!(package.aggregate(&tampered).is_err());
            return;
        }

        let signature = package.aggregate(&shares).unwrap();
        let frost_signature = $frost::aggregate(&frost_package, &frost_shares, &pubkeys).unwrap();
        assert_eq!(signature.as_ref(), frost_signature.serialize().unwrap());
        let public_key = commitment.public_key();
        public_key
            .verify(&input.message, signature.as_ref())
            .unwrap();

        let mut bytes = signature.as_ref().to_vec();
        let changed = input.signature.apply(&mut bytes);
        let ours = public_key.verify(&input.message, &bytes);
        let theirs = FrostSignature::deserialize(&bytes)
            .is_ok_and(|s| pubkeys.verifying_key().verify(&input.message, &s).is_ok());
        assert_eq!(ours.is_ok(), theirs, "{ours:?}");
        assert_eq!(ours.is_ok(), !changed);

        /// rind's commitments of the reference's signer `id`.
        fn commitments_of(
            suite: &'static Suite,
            c: &SigningCommitments,
            id: &FrostId,
        ) -> Commitments {
            let bytes = [
                id.serialize(),
                c.hiding().serialize().unwrap(),
                c.binding().serialize().unwrap(),
            ]
            .concat();
            Commitments::new(suite, &bytes).unwrap()
        }

        /// The reference's reading of rind's commitments.
        fn frost_commitments(c: &Commitments) -> (FrostId, SigningCommitments) {
            let len = (c.as_ref().len() - SCALAR_LEN) / 2;
            let (id, rest) = c.as_ref().split_at(SCALAR_LEN);
            (
                FrostId::deserialize(id).unwrap(),
                SigningCommitments::new(
                    NonceCommitment::deserialize(&rest[..len]).unwrap(),
                    NonceCommitment::deserialize(&rest[len..]).unwrap(),
                ),
            )
        }
    }};
}
use differential;

/// SHA-256 of a seed and a counter, so the reference's draws replay from
/// the input.
struct Rng {
    seed: [u8; 32],
    counter: u64,
}

impl Rng {
    fn new(seed: &[u8; 32]) -> Self {
        Self {
            seed: *seed,
            counter: 0,
        }
    }
}

impl rand_core_voprf::RngCore for Rng {
    fn next_u32(&mut self) -> u32 {
        rand_core_voprf::impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        rand_core_voprf::impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        use sha2::Digest;
        for chunk in dest.chunks_mut(32) {
            let block = sha2::Sha256::new()
                .chain_update(self.seed)
                .chain_update(self.counter.to_le_bytes())
                .finalize();
            self.counter += 1;
            chunk.copy_from_slice(&block[..chunk.len()]);
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core_voprf::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// Seeded from the fuzzer's input, as a reference's test only needs.
impl rand_core_voprf::CryptoRng for Rng {}
