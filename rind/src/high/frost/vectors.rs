// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RFC 9591 appendix E, from the CFRG draft's `poc` JSON.

use super::protocol::{self, Group, Party, commit_with_randomness, deal_from_coefficients};
use super::{ed25519::Ed25519, p256::P256, ristretto::Ristretto};
use crate::error::Error;
use crate::low::{Entry, ct};

#[test]
fn rfc9591_ed25519() {
    let _entry = Entry::new_secret();
    let signature = vector::<Ed25519>("frost-ed25519-sha512.json");
    let file = read("frost-ed25519-sha512.json");
    let message = hex_bytes(file["inputs"]["message"].as_str().unwrap());
    let group = hex_bytes(file["inputs"]["group_public_key"].as_str().unwrap());
    let key = crate::signature::PublicKey::new(&crate::signature::verify::ED25519, &group).unwrap();
    key.verify(&message, &signature).unwrap();
}

#[test]
fn rfc9591_ristretto255() {
    let _entry = Entry::new_secret();
    vector::<Ristretto>("frost-ristretto255-sha512.json");
}

#[test]
fn rfc9591_p256() {
    let _entry = Entry::new_secret();
    vector::<P256>("frost-p256-sha256.json");
}

fn vector<G: Group>(name: &str) -> Vec<u8> {
    let file = read(name);
    let max = number(&file["config"]["MAX_PARTICIPANTS"]);
    let min = number(&file["config"]["MIN_PARTICIPANTS"]);
    let secret = hex32(file["inputs"]["group_secret_key"].as_str().unwrap());
    let coefficients: Vec<[u8; 32]> = file["inputs"]["share_polynomial_coefficients"]
        .as_array()
        .unwrap()
        .iter()
        .map(|coefficient| hex32(coefficient.as_str().unwrap()))
        .collect();
    let dealt = deal_from_coefficients::<G>(&secret, &coefficients, max).unwrap();
    let group = hex_bytes(file["inputs"]["group_public_key"].as_str().unwrap());
    assert_eq!(&dealt.group[..G::ELEMENT_LEN], group.as_slice());

    for share in file["inputs"]["participant_shares"].as_array().unwrap() {
        let identifier = share["identifier"].as_u64().unwrap() as usize;
        assert_eq!(
            dealt.shares[identifier - 1].scalar,
            hex32(share["participant_share"].as_str().unwrap())
        );
    }

    let message = hex_bytes(file["inputs"]["message"].as_str().unwrap());
    let mut parties = Vec::new();
    let mut signing = Vec::new();
    for output in file["round_one_outputs"]["outputs"].as_array().unwrap() {
        let identifier = output["identifier"].as_u64().unwrap() as usize;
        let share = &dealt.shares[identifier - 1];
        let nonces = commit_with_randomness::<G>(
            &share.scalar,
            &hex32(output["hiding_nonce_randomness"].as_str().unwrap()),
            &hex32(output["binding_nonce_randomness"].as_str().unwrap()),
        )
        .unwrap();
        // The nonces are secret. Declassify only this comparison with the vector.
        let hiding = nonces.hiding;
        let binding = nonces.binding;
        ct::public_slice(&hiding);
        ct::public_slice(&binding);
        assert_eq!(hiding, hex32(output["hiding_nonce"].as_str().unwrap()));
        assert_eq!(binding, hex32(output["binding_nonce"].as_str().unwrap()));
        assert_eq!(
            &nonces.hiding_commitment[..G::ELEMENT_LEN],
            hex_bytes(output["hiding_nonce_commitment"].as_str().unwrap()).as_slice()
        );
        assert_eq!(
            &nonces.binding_commitment[..G::ELEMENT_LEN],
            hex_bytes(output["binding_nonce_commitment"].as_str().unwrap()).as_slice()
        );
        parties.push(Party {
            identifier: share.identifier,
            hiding: nonces.hiding_commitment,
            binding: nonces.binding_commitment,
        });
        signing.push((
            share.identifier,
            share.scalar,
            nonces.hiding,
            nonces.binding,
        ));
    }
    parties
        .sort_by(|left, right| protocol::cmp_identifiers::<G>(&left.identifier, &right.identifier));
    signing.sort_by(|left, right| protocol::cmp_identifiers::<G>(&left.0, &right.0));

    for output in file["round_one_outputs"]["outputs"].as_array().unwrap() {
        let identifier = identifier_bytes::<G>(output["identifier"].as_u64().unwrap() as u16);
        assert_eq!(
            protocol::binding_factor::<G>(&group, &parties, &message, &identifier).unwrap(),
            hex32(output["binding_factor"].as_str().unwrap())
        );
    }

    let mut shares = Vec::new();
    let mut verifying = Vec::new();
    let round_two = file["round_two_outputs"]["outputs"].as_array().unwrap();
    for (identifier, scalar, hiding, binding) in &signing {
        let output = round_two
            .iter()
            .find(|output| {
                identifier_bytes::<G>(output["identifier"].as_u64().unwrap() as u16) == *identifier
            })
            .unwrap();
        let signature_share = protocol::sign::<G>(
            scalar, identifier, min, max, hiding, binding, &group, &parties, &message,
        )
        .unwrap();
        assert_eq!(
            signature_share,
            hex32(output["sig_share"].as_str().unwrap()),
            "participant {}",
            output["identifier"]
        );
        shares.push((*identifier, signature_share));
        let element = dealt
            .shares
            .iter()
            .find(|share| share.identifier == *identifier)
            .unwrap()
            .verifying;
        verifying.push((*identifier, element));
    }

    let signature =
        protocol::aggregate::<G>(&group, &parties, &message, &shares, &verifying, min, max)
            .unwrap();
    assert_eq!(
        signature,
        hex_bytes(file["final_output"]["sig"].as_str().unwrap())
    );
    protocol::verify::<G>(&group, &message, &signature).unwrap();
    signature
}

fn identifier_bytes<G: Group>(identifier: u16) -> [u8; 32] {
    let mut bytes = [0u8; 32];
    if G::SCALAR_BE {
        bytes[30..].copy_from_slice(&identifier.to_be_bytes());
    } else {
        bytes[..2].copy_from_slice(&identifier.to_le_bytes());
    }
    bytes
}

fn read(name: &str) -> serde_json::Value {
    let path = format!(
        "{}/../thirdparty/vectors/rfc9591/{name}",
        env!("CARGO_MANIFEST_DIR")
    );
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn number(value: &serde_json::Value) -> u16 {
    value.as_str().unwrap().parse().unwrap()
}

fn hex32(value: &str) -> [u8; 32] {
    hex_bytes(value).try_into().unwrap()
}

fn hex_bytes(value: &str) -> Vec<u8> {
    hex::decode(value).unwrap()
}

#[test]
fn refuses_a_bad_commitment() {
    let _entry = Entry::new_public();
    let err = super::Commitments::from_bytes(&super::ED25519_SHA512, &[0; 10]).unwrap_err();
    assert_eq!(err, Error::WrongLength);
    // The identity element, which RFC 9591 refuses.
    let mut bytes = vec![0u8; 96];
    bytes[0] = 1;
    bytes[32] = 1;
    bytes[64] = 1;
    let err = super::Commitments::from_bytes(&super::ED25519_SHA512, &bytes).unwrap_err();
    assert!(matches!(err, Error::KeyRejected(_)));
}
