//! ring takes a key pair's public key only uncompressed, which rind-ring keeps
//! though rind also takes it compressed.

use rind_ring::{rand, signature};

/// A DER element of `tag` holding `body`, under 256 bytes.
fn der(tag: u8, body: &[u8]) -> Vec<u8> {
    let len = u8::try_from(body.len()).unwrap();
    match len {
        0..=0x7f => [&[tag, len][..], body].concat(),
        _ => [&[tag, 0x81, len][..], body].concat(),
    }
}

#[test]
fn key_pair_public_key_forms() {
    for (ours, rind, curve) in [
        (
            &signature::ECDSA_P256_SHA256_ASN1_SIGNING,
            &rind::signature::sign::ECDSA_P256_SHA256_ASN1,
            "2a8648ce3d030107",
        ),
        (
            &signature::ECDSA_P384_SHA384_ASN1_SIGNING,
            &rind::signature::sign::ECDSA_P384_SHA384_ASN1,
            "2b81040022",
        ),
    ] {
        let key = rind::signature::EcdsaKeyPair::generate(rind).unwrap();
        let scalar = key.to_scalar();
        let public = key.public_key();
        let point = public.as_ref();
        let (x, y) = point[1..].split_at(point.len() / 2);
        let compressed = [&[0x02 | (y[y.len() - 1] & 1)][..], x].concat();
        let curve = hex::decode(curve).unwrap();
        let pkcs8 = |version: u8, public_key: Option<&[u8]>| {
            let public_key = public_key.map_or(vec![], |key| {
                der(0xa1, &der(0x03, &[&[0][..], key].concat()))
            });
            let sec1 = der(
                0x30,
                &[
                    &[0x02, 0x01, 0x01][..],
                    &der(0x04, scalar.as_ref()),
                    &public_key,
                ]
                .concat(),
            );
            let algorithm = [
                &der(0x06, &hex::decode("2a8648ce3d0201").unwrap())[..],
                &der(0x06, &curve),
            ]
            .concat();
            der(
                0x30,
                &[
                    &[0x02, 0x01, version][..],
                    &der(0x30, &algorithm),
                    &der(0x04, &sec1),
                ]
                .concat(),
            )
        };

        let rng = rand::SystemRandom::new();
        // rind takes a v2 document without its public key, as aws-lc-rs
        // does, and ring refuses any v2 ECDSA document.
        for (version, public_key, ok) in [
            (0, Some(point), true),
            (0, Some(&compressed), false),
            (0, None, false),
            (1, Some(point), false),
        ] {
            let pkcs8 = pkcs8(version, public_key);
            // rind takes each, so any refusal is rind-ring's.
            let rind = rind::signature::EcdsaKeyPair::from_pkcs8(rind, &pkcs8);
            assert!(rind.is_ok(), "{public_key:02x?} {rind:?}");
            let loaded = signature::EcdsaKeyPair::from_pkcs8(ours, &pkcs8, &rng);
            assert_eq!(loaded.is_ok(), ok, "{public_key:02x?}");
        }
        for (public_key, ok) in [(point, true), (&compressed, false)] {
            let loaded = signature::EcdsaKeyPair::from_private_key_and_public_key(
                ours,
                scalar.as_ref(),
                public_key,
                &rng,
            );
            assert_eq!(loaded.is_ok(), ok, "{public_key:02x?}");
        }
    }
}
