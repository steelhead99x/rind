//! Differential tests of HPKE, ECVRF, OPRF, and FROST against independent
//! implementations, which Miri cannot run.
#![cfg(not(any(miri, target_family = "wasm")))]

/// HPKE against hpke-rs, as aws-lc-rs exposes none: rind-rustls's tests
/// compare its twelve suites with rustls's over aws-lc's primitives.
mod hpke {
    use hpke_rs::hpke_types::{AeadAlgorithm, KdfAlgorithm, KemAlgorithm};
    use hpke_rs::rustcrypto::HpkeRustCrypto;
    use hpke_rs::{Hpke, HpkePrivateKey, HpkePublicKey, Mode};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::hpke::*;

    // hpke-rs's RustCrypto backend has no P-521; RFC 9180's vectors cover it.
    const KEMS: [(&Kem, KemAlgorithm); 3] = [
        (&DHKEM_X25519_HKDF_SHA256, KemAlgorithm::DhKem25519),
        (&DHKEM_P256_HKDF_SHA256, KemAlgorithm::DhKemP256),
        (&DHKEM_P384_HKDF_SHA384, KemAlgorithm::DhKemP384),
    ];
    const KDFS: [(&Kdf, KdfAlgorithm); 3] = [
        (&HKDF_SHA256, KdfAlgorithm::HkdfSha256),
        (&HKDF_SHA384, KdfAlgorithm::HkdfSha384),
        (&HKDF_SHA512, KdfAlgorithm::HkdfSha512),
    ];
    // `None` is export-only.
    const AEADS: [(Option<&Aead>, AeadAlgorithm); 4] = [
        (Some(&AES_128_GCM), AeadAlgorithm::Aes128Gcm),
        (Some(&AES_256_GCM), AeadAlgorithm::Aes256Gcm),
        (Some(&CHACHA20_POLY1305), AeadAlgorithm::ChaCha20Poly1305),
        (None, AeadAlgorithm::HpkeExport),
    ];

    fn export(f: impl FnOnce(&mut [u8]) -> Result<(), rind::Error>, len: usize) -> Vec<u8> {
        let mut out = vec![0; len];
        f(&mut out).unwrap();
        out
    }

    proptest! {
        #[test]
        fn matches_hpke_rs(
            kem in 0..KEMS.len(),
            kdf in 0..KDFS.len(),
            aead in 0..AEADS.len(),
            ikm in vec(any::<u8>(), 0..80),
            info in vec(any::<u8>(), 0..64),
            aad in vec(any::<u8>(), 0..64),
            plaintext in vec(any::<u8>(), 0..300),
            context in vec(any::<u8>(), 0..64),
            len in 0..300usize,
        ) {
            let ((kem, their_kem), (kdf, their_kdf), (aead, their_aead)) = (KEMS[kem], KDFS[kdf], AEADS[aead]);
            let mut theirs = Hpke::<HpkeRustCrypto>::new(Mode::Base, their_kem, their_kdf, their_aead);

            // `DeriveKeyPair` gives the same key, which each side loads.
            let private_key = PrivateKey::derive(kem, &ikm).unwrap();
            let public_key = private_key.public_key();
            let (their_private, their_public) = theirs.derive_key_pair(&ikm).unwrap().into_keys();
            prop_assert_eq!(public_key.as_ref(), their_public.as_slice());
            let loaded = PrivateKey::from_scalar(kem, their_private.as_slice()).unwrap();
            let loaded = loaded.public_key();
            prop_assert_eq!(loaded.as_ref(), public_key.as_ref());
            let their_private = HpkePrivateKey::new(private_key.to_scalar().as_ref().to_vec());
            let their_public = HpkePublicKey::new(public_key.as_ref().to_vec());

            // Their sender to our recipient.
            let (enc, mut their_sender) = theirs
                .setup_sender(&their_public, &info, None, None, None)
                .unwrap();
            let their_export = their_sender.export(&context, len).unwrap();
            match aead {
                Some(aead) => {
                    let suite = Suite { kdf, aead };
                    let ct = their_sender.seal(&aad, &plaintext).unwrap();
                    let mut recipient = Recipient::new(suite, &private_key, &enc, &info).unwrap();
                    let mut in_out = ct.clone();
                    prop_assert_eq!(&*recipient.open_in_place(&aad, &mut in_out).unwrap(), &plaintext[..]);
                    prop_assert_eq!(export(|out| recipient.export(&context, out), len), their_export);
                }
                None => {
                    let recipient = Exporter::recipient(kdf, &private_key, &enc, &info).unwrap();
                    prop_assert_eq!(export(|out| recipient.export(&context, out), len), their_export);
                }
            }

            // Our sender to their recipient.
            let (enc, our_export, ct) = match aead {
                Some(aead) => {
                    let (enc, mut sender) = Sender::new(Suite { kdf, aead }, public_key, &info).unwrap();
                    let mut ct = plaintext.clone();
                    sender.seal_in_place_append_tag(&aad, &mut ct).unwrap();
                    (enc, export(|out| sender.export(&context, out), len), Some(ct))
                }
                None => {
                    let (enc, sender) = Exporter::sender(kdf, public_key, &info).unwrap();
                    (enc, export(|out| sender.export(&context, out), len), None)
                }
            };
            let mut their_recipient = theirs
                .setup_receiver(enc.as_ref(), &their_private, &info, None, None, None)
                .unwrap();
            prop_assert_eq!(their_recipient.export(&context, len).unwrap(), our_export);
            if let Some(ct) = ct {
                prop_assert_eq!(their_recipient.open(&aad, &ct).unwrap(), plaintext);
            }
        }
    }
}

/// ECVRF against `akd_core`'s Edwards25519 suite, which key transparency's
/// `akd` runs, and `vrf-rfc9381`'s P-256 suite: each proves the same bytes
/// for a key and input, and verifies the other's proofs.
mod vrf {
    use akd_core::ecvrf::{VRFPrivateKey, VRFPublicKey};
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rind::vrf::*;
    use vrf_rfc9381::ec::p256::EcVrfProof;
    use vrf_rfc9381::ec::p256::tai::{EcVrfP256TaiPublicKey, EcVrfP256TaiSecretKey};
    use vrf_rfc9381::{Proof as _, Prover as _, Verifier as _};

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(64))]

        #[test]
        fn matches_akd(seed in any::<[u8; 32]>(), alpha in vec(any::<u8>(), 0..300)) {
            let ours = KeyPair::from_seed(&ECVRF_EDWARDS25519_SHA512_TAI, &seed).unwrap();
            let theirs = VRFPrivateKey::try_from(&seed[..]).unwrap();
            let their_public = VRFPublicKey::from(&theirs);
            prop_assert_eq!(ours.public_key().as_ref(), their_public.as_bytes());

            let (proof, output) = ours.prove(&alpha).unwrap();
            let their_proof = theirs.prove(&alpha);
            prop_assert_eq!(proof.as_ref(), their_proof.to_bytes());
            their_public.verify(&their_proof, &alpha).unwrap();

            let public_key =
                PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, their_public.as_bytes()).unwrap();
            let verified = public_key.verify(&alpha, &their_proof.to_bytes()).unwrap();
            prop_assert_eq!(verified.as_ref(), output.as_ref());
        }

        #[test]
        fn matches_vrf_rfc9381(alpha in vec(any::<u8>(), 0..300)) {
            let ours = KeyPair::generate(&ECVRF_P256_SHA256_TAI).unwrap();
            let theirs = EcVrfP256TaiSecretKey::from_slice(ours.to_seed().as_ref()).unwrap();
            let their_public = theirs.verifier();

            let (proof, output) = ours.prove(&alpha).unwrap();
            let their_proof = theirs.prove(&alpha).unwrap();
            prop_assert_eq!(proof.as_ref(), &their_proof.encode_to_pi()[..]);
            prop_assert!(
                EcVrfP256TaiPublicKey::from_slice(ours.public_key().as_ref()).unwrap()
                    == their_public
            );
            let their_output = their_public
                .verify(&alpha, EcVrfProof::decode_pi(proof.as_ref()).unwrap())
                .unwrap();
            prop_assert_eq!(&their_output[..], output.as_ref());

            let verified = ours
                .public_key()
                .verify(&alpha, &their_proof.encode_to_pi())
                .unwrap();
            prop_assert_eq!(verified.as_ref(), output.as_ref());
        }
    }
}

mod oprf {
    use proptest::collection::vec;
    use proptest::prelude::*;
    use rand_core_voprf::OsRng;
    use rind::oprf::voprf as rind_voprf;
    use rind::oprf::{P256_SHA256, P384_SHA384, P521_SHA512, RISTRETTO255_SHA512};
    use voprf::{
        BlindedElement, EvaluationElement, Group, OprfClient, OprfServer, Proof, VoprfClient,
        VoprfServer,
    };

    /// Each suite against the `voprf` crate: the same key from one seed,
    /// rind's clients finalizing the crate's evaluations and proofs, the
    /// crate's clients finalizing rind's, and both servers' direct outputs.
    macro_rules! matches_voprf {
        ($cs:ty, $suite:expr, $seed:expr, $info:expr, $inputs:expr) => {{
            let (seed, info, inputs): ([u8; 32], Vec<u8>, Vec<Vec<u8>>) = ($seed, $info, $inputs);
            type G = <$cs as voprf::CipherSuite>::Group;
            let suite = $suite;

            // The OPRF mode.
            let ours = rind::oprf::ServerKey::derive(suite, &seed, &info).unwrap();
            let theirs = OprfServer::<$cs>::new_from_seed(&seed, &info).unwrap();
            // The crate derives the same key: loaded from rind's
            // encoding, it evaluates as the key it derived.
            let loaded = OprfServer::<$cs>::new_with_key(ours.to_scalar().as_ref()).unwrap();
            prop_assert_eq!(
                &loaded.evaluate(b"key").unwrap()[..],
                &theirs.evaluate(b"key").unwrap()[..]
            );
            for input in &inputs {
                let direct = theirs.evaluate(input).unwrap();
                let output = ours.evaluate(input).unwrap();
                prop_assert_eq!(output.as_ref(), &direct[..]);

                let (blind, blinded) = rind::oprf::Blind::new(suite, input).unwrap();
                let evaluated =
                    theirs.blind_evaluate(&BlindedElement::deserialize(blinded.as_ref()).unwrap());
                let output = blind.finalize(&evaluated.serialize()).unwrap();
                prop_assert_eq!(output.as_ref(), &direct[..]);

                let blinded = OprfClient::<$cs>::blind(input, &mut OsRng).unwrap();
                let evaluated = ours.blind_evaluate(&blinded.message.serialize()).unwrap();
                let output = blinded
                    .state
                    .finalize(
                        input,
                        &EvaluationElement::deserialize(evaluated.as_ref()).unwrap(),
                    )
                    .unwrap();
                prop_assert_eq!(&output[..], &direct[..]);
            }

            // The VOPRF mode, batched.
            let ours = rind_voprf::ServerKey::derive(suite, &seed, &info).unwrap();
            let theirs = VoprfServer::<$cs>::new_from_seed(&seed, &info).unwrap();
            prop_assert_eq!(
                ours.public_key().as_ref(),
                &G::serialize_elem(theirs.get_public_key())[..]
            );
            let direct = inputs
                .iter()
                .map(|input| theirs.evaluate(input).unwrap().to_vec())
                .collect::<Vec<_>>();
            for (input, direct) in inputs.iter().zip(&direct) {
                let output = ours.evaluate(input).unwrap();
                prop_assert_eq!(output.as_ref(), &direct[..]);
            }

            let mut blinds = Vec::new();
            let mut blinded = Vec::new();
            for input in &inputs {
                let (blind, element) = rind_voprf::Blind::new(suite, input).unwrap();
                blinds.push(blind);
                blinded.push(BlindedElement::<$cs>::deserialize(element.as_ref()).unwrap());
            }
            let evaluated = theirs.batch_blind_evaluate(&mut OsRng, &blinded).unwrap();
            let messages = evaluated
                .messages
                .iter()
                .flat_map(|message| message.serialize())
                .collect::<Vec<_>>();
            let public_key =
                rind_voprf::PublicKey::new(suite, &G::serialize_elem(theirs.get_public_key()))
                    .unwrap();
            let outputs = rind_voprf::Blind::finalize_batch(
                blinds,
                &messages,
                &evaluated.proof.serialize(),
                &public_key,
            )
            .unwrap();
            for (output, direct) in outputs.iter().zip(&direct) {
                prop_assert_eq!(output.as_ref(), &direct[..]);
            }

            let mut clients = Vec::new();
            let mut blinded = Vec::new();
            for input in &inputs {
                let result = VoprfClient::<$cs>::blind(input, &mut OsRng).unwrap();
                clients.push(result.state);
                blinded.extend_from_slice(&result.message.serialize());
            }
            let (evaluated, proof) = ours.blind_evaluate(&blinded).unwrap();
            let element_len = evaluated.as_ref().len() / inputs.len();
            let messages = evaluated
                .as_ref()
                .chunks(element_len)
                .map(|bytes| EvaluationElement::<$cs>::deserialize(bytes).unwrap())
                .collect::<Vec<_>>();
            let proof = Proof::<$cs>::deserialize(proof.as_ref()).unwrap();
            let outputs = VoprfClient::batch_finalize(
                &inputs,
                &clients,
                &messages,
                &proof,
                theirs.get_public_key(),
            )
            .unwrap();
            for (output, direct) in outputs.zip(&direct) {
                prop_assert_eq!(&output.unwrap()[..], &direct[..]);
            }
        }};
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(16))]

        #[test]
        fn ristretto255_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(voprf::Ristretto255, &RISTRETTO255_SHA512, seed, info, inputs);
        }

        #[test]
        fn p256_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(p256_voprf::NistP256, &P256_SHA256, seed, info, inputs);
        }

        #[test]
        fn p384_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(p384_voprf::NistP384, &P384_SHA384, seed, info, inputs);
        }

        #[test]
        fn p521_matches_voprf(
            seed in any::<[u8; 32]>(),
            info in vec(any::<u8>(), 0..40),
            inputs in vec(vec(any::<u8>(), 0..100), 1..4),
        ) {
            matches_voprf!(p521_voprf::NistP521, &P521_SHA512, seed, info, inputs);
        }
    }
}

/// FROST against the Zcash Foundation's `frost-*` crates, as aws-lc-rs has
/// no FROST.
mod frost {
    use std::collections::{BTreeMap, BTreeSet};

    use rand_core_voprf::OsRng;
    use rind::frost::*;

    /// Every suite's identifiers and scalars are 32 bytes.
    const SCALAR_LEN: usize = 32;

    macro_rules! differential {
        ($frost:ident, $suite:expr) => {
            use $frost::keys::{
                IdentifierList, KeyPackage, PublicKeyPackage, SecretShare,
                SigningShare as FrostShare, VerifiableSecretSharingCommitment,
                generate_with_dealer,
            };
            use $frost::round1::{NonceCommitment, SigningCommitments};
            use $frost::{Identifier as FrostId, SigningPackage as FrostPackage, round1, round2};

            const SUITE: &Suite = $suite;

            fn commitments_of(c: &SigningCommitments, id: &FrostId) -> Commitments {
                let bytes = [
                    id.serialize(),
                    c.hiding().serialize().unwrap(),
                    c.binding().serialize().unwrap(),
                ]
                .concat();
                Commitments::new(SUITE, &bytes).unwrap()
            }

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

            /// The reference's dealer, and signers split between rind and
            /// the reference: each side's coordinator reaches the same
            /// signature, and each verifies it.
            #[test]
            fn reference_dealer_mixed_signers() {
                for message in [&b""[..], b"message", &[0xa5; 1000]] {
                    let (secret_shares, pubkeys) =
                        generate_with_dealer(5, 3, IdentifierList::Default, &mut OsRng).unwrap();
                    let vss = secret_shares
                        .values()
                        .next()
                        .unwrap()
                        .commitment()
                        .serialize_whole()
                        .unwrap();
                    let commitment = VssCommitment::new(SUITE, &vss).unwrap();
                    assert_eq!(
                        commitment.public_key().as_ref(),
                        pubkeys.verifying_key().serialize().unwrap()
                    );

                    // Participants 1 and 4 run rind; 3 runs the reference.
                    let mut ours = BTreeMap::new();
                    for n in [1u16, 4] {
                        let id = FrostId::try_from(n).unwrap();
                        let share = &secret_shares[&id];
                        let identifier = Identifier::new(SUITE, &id.serialize()).unwrap();
                        let share = rind::frost::SigningShare::from_scalar(
                            &identifier,
                            &share.signing_share().serialize(),
                            &commitment,
                        )
                        .unwrap();
                        ours.insert(id, share);
                    }
                    let theirs_id = FrostId::try_from(3u16).unwrap();
                    let theirs = KeyPackage::try_from(secret_shares[&theirs_id].clone()).unwrap();

                    let mut our_nonces = BTreeMap::new();
                    let mut commitments = Vec::new();
                    for (id, share) in &ours {
                        let (n, c) = SigningNonces::commit(share).unwrap();
                        our_nonces.insert(*id, n);
                        commitments.push(c);
                    }
                    let (their_nonces, their_commitments) =
                        round1::commit(theirs.signing_share(), &mut OsRng);
                    commitments.push(commitments_of(&their_commitments, &theirs_id));

                    let package =
                        SigningPackage::new(commitment.public_key(), &commitments, message)
                            .unwrap();
                    let frost_package = FrostPackage::new(
                        commitments.iter().map(frost_commitments).collect(),
                        message,
                    );

                    let mut shares = Vec::new();
                    let mut frost_shares = BTreeMap::new();
                    for (id, n) in our_nonces {
                        let share = n.sign(&ours[&id], &package).unwrap();
                        frost_shares.insert(
                            id,
                            round2::SignatureShare::deserialize(&share.as_ref()[SCALAR_LEN..])
                                .unwrap(),
                        );
                        shares.push(share);
                    }
                    let their_share = round2::sign(&frost_package, &their_nonces, &theirs).unwrap();
                    let bytes = [theirs_id.serialize(), their_share.serialize()].concat();
                    shares.push(SignatureShare::new(SUITE, &bytes).unwrap());
                    frost_shares.insert(theirs_id, their_share);

                    for share in &shares {
                        package.verify_share(share, &commitment).unwrap();
                    }
                    let signature = package.aggregate(&shares).unwrap();
                    let frost_signature =
                        $frost::aggregate(&frost_package, &frost_shares, &pubkeys).unwrap();
                    assert_eq!(signature.as_ref(), frost_signature.serialize().unwrap());
                    commitment
                        .public_key()
                        .verify(message, signature.as_ref())
                        .unwrap();
                    pubkeys
                        .verifying_key()
                        .verify(message, &frost_signature)
                        .unwrap();
                }
            }

            /// rind's dealer, whose shares and commitment the reference
            /// loads and signs with, and whose signature rind verifies.
            #[test]
            fn rind_dealer_reference_signers() {
                let (shares, commitment) = deal(SUITE, 3, 4).unwrap();
                let frost_commitment =
                    VerifiableSecretSharingCommitment::deserialize_whole(commitment.as_ref())
                        .unwrap();
                let ids: BTreeSet<FrostId> = shares
                    .iter()
                    .map(|s| FrostId::deserialize(s.identifier().as_ref()).unwrap())
                    .collect();
                let pubkeys = PublicKeyPackage::from_commitment(&ids, &frost_commitment).unwrap();
                assert_eq!(
                    pubkeys.verifying_key().serialize().unwrap(),
                    commitment.public_key().as_ref()
                );

                let key_packages: BTreeMap<FrostId, KeyPackage> = shares[1..]
                    .iter()
                    .map(|s| {
                        let id = FrostId::deserialize(s.identifier().as_ref()).unwrap();
                        let share = FrostShare::deserialize(s.to_scalar().as_ref()).unwrap();
                        let secret = SecretShare::new(id, share, frost_commitment.clone());
                        (id, KeyPackage::try_from(secret).unwrap())
                    })
                    .collect();
                let mut nonces = BTreeMap::new();
                let mut frost_commitments = BTreeMap::new();
                for (id, key_package) in &key_packages {
                    let (n, c) = round1::commit(key_package.signing_share(), &mut OsRng);
                    nonces.insert(*id, n);
                    frost_commitments.insert(*id, c);
                }
                let frost_package = FrostPackage::new(frost_commitments.clone(), b"message");
                let commitments: Vec<_> = frost_commitments
                    .iter()
                    .map(|(id, c)| commitments_of(c, id))
                    .collect();
                let package =
                    SigningPackage::new(commitment.public_key(), &commitments, b"message").unwrap();
                let signature_shares: Vec<_> = key_packages
                    .iter()
                    .map(|(id, key_package)| {
                        let share = round2::sign(&frost_package, &nonces[id], key_package).unwrap();
                        let bytes = [id.serialize(), share.serialize()].concat();
                        SignatureShare::new(SUITE, &bytes).unwrap()
                    })
                    .collect();
                for share in &signature_shares {
                    package.verify_share(share, &commitment).unwrap();
                }
                let signature = package.aggregate(&signature_shares).unwrap();
                commitment
                    .public_key()
                    .verify(b"message", signature.as_ref())
                    .unwrap();
                let frost_signature = $frost::Signature::deserialize(signature.as_ref()).unwrap();
                pubkeys
                    .verifying_key()
                    .verify(b"message", &frost_signature)
                    .unwrap();
            }
        };
    }

    mod ed25519 {
        use super::*;
        differential!(frost_ed25519, &ED25519_SHA512);
    }

    mod ristretto255 {
        use super::*;
        differential!(frost_ristretto255, &RISTRETTO255_SHA512);
    }

    mod p256 {
        use super::*;
        differential!(frost_p256, &P256_SHA256);
    }
}
