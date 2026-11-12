//! MLS groups whose members run rind-openmls and openmls_rust_crypto side by
//! side, for every ciphersuite both offer.

use openmls::prelude::tls_codec::{Deserialize, Serialize};
use openmls::prelude::*;
use openmls_basic_credential::SignatureKeyPair;
use openmls_traits::signatures::{Signer, SignerError};

/// Signs with rind-openmls, as openmls_basic_credential signs with RustCrypto.
struct RindSigner {
    scheme: SignatureScheme,
    private: Vec<u8>,
}

impl Signer for RindSigner {
    fn sign(&self, payload: &[u8]) -> Result<Vec<u8>, SignerError> {
        rind_openmls::RustCrypto::default()
            .sign(self.scheme, payload, &self.private)
            .map_err(SignerError::CryptoError)
    }

    fn signature_scheme(&self) -> SignatureScheme {
        self.scheme
    }
}

/// A group member on either provider.
struct Member<P, S> {
    provider: P,
    signer: S,
    credential: CredentialWithKey,
}

fn credential(name: &str, public: Vec<u8>) -> CredentialWithKey {
    CredentialWithKey {
        credential: BasicCredential::new(name.into()).into(),
        signature_key: public.into(),
    }
}

fn rind_member(
    name: &str,
    ciphersuite: Ciphersuite,
) -> Member<rind_openmls::OpenMlsRustCrypto, RindSigner> {
    let provider = rind_openmls::OpenMlsRustCrypto::default();
    let scheme = ciphersuite.signature_algorithm();
    let (private, public) = provider.crypto().signature_key_gen(scheme).unwrap();
    Member {
        provider,
        signer: RindSigner { scheme, private },
        credential: credential(name, public),
    }
}

fn rust_crypto_member(
    name: &str,
    ciphersuite: Ciphersuite,
) -> Member<openmls_rust_crypto::OpenMlsRustCrypto, SignatureKeyPair> {
    let keys = SignatureKeyPair::new(ciphersuite.signature_algorithm()).unwrap();
    Member {
        provider: openmls_rust_crypto::OpenMlsRustCrypto::default(),
        credential: credential(name, keys.to_public_vec()),
        signer: keys,
    }
}

/// Sends `message` over the wire, as bytes.
fn wire(message: MlsMessageOut) -> MlsMessageIn {
    MlsMessageIn::tls_deserialize_exact(message.tls_serialize_detached().unwrap()).unwrap()
}

fn process(
    group: &mut MlsGroup,
    provider: &impl OpenMlsProvider,
    message: MlsMessageOut,
) -> ProcessedMessageContent {
    let message = wire(message).try_into_protocol_message().unwrap();
    group
        .process_message(provider, message)
        .unwrap()
        .into_content()
}

fn merge(group: &mut MlsGroup, provider: &impl OpenMlsProvider, message: MlsMessageOut) {
    match process(group, provider, message) {
        ProcessedMessageContent::StagedCommitMessage(commit) => {
            group.merge_staged_commit(provider, *commit).unwrap()
        }
        _ => panic!("expected a commit"),
    }
}

fn application(
    group: &mut MlsGroup,
    provider: &impl OpenMlsProvider,
    message: MlsMessageOut,
) -> Vec<u8> {
    match process(group, provider, message) {
        ProcessedMessageContent::ApplicationMessage(message) => message.into_bytes(),
        _ => panic!("expected an application message"),
    }
}

/// `creator` makes a group, adds `joiner`, and the two exchange messages,
/// update their keys, and export the same secrets.
fn group<A: OpenMlsProvider, S: Signer, B: OpenMlsProvider, T: Signer>(
    ciphersuite: Ciphersuite,
    creator: &Member<A, S>,
    joiner: &Member<B, T>,
) {
    let config = MlsGroupCreateConfig::builder()
        .ciphersuite(ciphersuite)
        .use_ratchet_tree_extension(true)
        .build();
    let mut a = MlsGroup::new(
        &creator.provider,
        &creator.signer,
        &config,
        creator.credential.clone(),
    )
    .unwrap();

    let key_package = KeyPackage::builder()
        .build(
            ciphersuite,
            &joiner.provider,
            &joiner.signer,
            joiner.credential.clone(),
        )
        .unwrap();
    let (_, welcome, _) = a
        .add_members(
            &creator.provider,
            &creator.signer,
            core::slice::from_ref(key_package.key_package()),
        )
        .unwrap();
    a.merge_pending_commit(&creator.provider).unwrap();

    let welcome = wire(welcome).into_welcome().unwrap();
    let mut b =
        StagedWelcome::new_from_welcome(&joiner.provider, config.join_config(), welcome, None)
            .unwrap()
            .into_group(&joiner.provider)
            .unwrap();

    let message = a
        .create_message(&creator.provider, &creator.signer, b"from the creator")
        .unwrap();
    assert_eq!(
        application(&mut b, &joiner.provider, message),
        b"from the creator"
    );
    let message = b
        .create_message(&joiner.provider, &joiner.signer, b"from the joiner")
        .unwrap();
    assert_eq!(
        application(&mut a, &creator.provider, message),
        b"from the joiner"
    );

    // A commit with an update path HPKE-encrypts a path secret to each member.
    let (commit, _, _) = b
        .self_update(
            &joiner.provider,
            &joiner.signer,
            LeafNodeParameters::default(),
        )
        .unwrap()
        .into_contents();
    merge(&mut a, &creator.provider, commit);
    b.merge_pending_commit(&joiner.provider).unwrap();
    let (commit, _, _) = a
        .self_update(
            &creator.provider,
            &creator.signer,
            LeafNodeParameters::default(),
        )
        .unwrap()
        .into_contents();
    merge(&mut b, &joiner.provider, commit);
    a.merge_pending_commit(&creator.provider).unwrap();

    assert_eq!(a.epoch(), b.epoch());
    assert_eq!(
        a.export_secret(creator.provider.crypto(), "label", b"context", 32)
            .unwrap(),
        b.export_secret(joiner.provider.crypto(), "label", b"context", 32)
            .unwrap(),
    );
    let message = a
        .create_message(&creator.provider, &creator.signer, b"after the update")
        .unwrap();
    assert_eq!(
        application(&mut b, &joiner.provider, message),
        b"after the update"
    );
}

#[test]
fn rind_creates_rust_crypto_joins() {
    let rust_crypto = openmls_rust_crypto::OpenMlsRustCrypto::default();
    for ciphersuite in rust_crypto.crypto().supported_ciphersuites() {
        group(
            ciphersuite,
            &rind_member("rind", ciphersuite),
            &rust_crypto_member("rust_crypto", ciphersuite),
        );
    }
}

#[test]
fn rust_crypto_creates_rind_joins() {
    let rust_crypto = openmls_rust_crypto::OpenMlsRustCrypto::default();
    for ciphersuite in rust_crypto.crypto().supported_ciphersuites() {
        group(
            ciphersuite,
            &rust_crypto_member("rust_crypto", ciphersuite),
            &rind_member("rind", ciphersuite),
        );
    }
}

#[test]
fn same_ciphersuites() {
    assert_eq!(
        rind_openmls::OpenMlsRustCrypto::default()
            .crypto()
            .supported_ciphersuites(),
        openmls_rust_crypto::OpenMlsRustCrypto::default()
            .crypto()
            .supported_ciphersuites(),
    );
}
