//! ring signs only with moduli of 2048 to 4096 bits, which rind-ring keeps
//! though rind loads keys up to 8192 bits; ring's own vectors stop at 4096.

#![cfg(feature = "alloc")]

use rind_ring::{rand, signature};

#[test]
fn key_pair_modulus_sizes() {
    for (bits, ok) in [
        (2048, true),
        (3072, true),
        (4096, true),
        (6144, false),
        (8192, false),
    ] {
        let der = std::fs::read(format!(
            "{}/../rind/src/high/rsa/rsa{bits}.der",
            env!("CARGO_MANIFEST_DIR")
        ))
        .unwrap();
        let key_pair = signature::RsaKeyPair::from_der(&der);
        assert_eq!(key_pair.is_ok(), ok, "{bits} bits");
        let Ok(key_pair) = key_pair else { continue };
        assert_eq!(key_pair.public_modulus_len(), bits / 8);

        let mut signature = vec![0; key_pair.public_modulus_len()];
        key_pair
            .sign(
                &signature::RSA_PSS_SHA256,
                &rand::SystemRandom::new(),
                b"message",
                &mut signature,
            )
            .unwrap();
        signature::UnparsedPublicKey::new(
            &signature::RSA_PSS_2048_8192_SHA256,
            key_pair.public().as_ref(),
        )
        .verify(b"message", &signature)
        .unwrap();
    }
}

/// rind takes a v2 document without its public key, as aws-lc-rs does, and
/// ring refuses any v2 RSA document.
#[test]
fn key_pair_pkcs8_v1_only() {
    let der = std::fs::read(format!(
        "{}/../rind/src/high/rsa/rsa2048.der",
        env!("CARGO_MANIFEST_DIR")
    ))
    .unwrap();
    let mut pkcs8 = rind::rsa::KeyPair::from_pkcs1(&der)
        .unwrap()
        .to_pkcs8()
        .as_ref()
        .to_vec();
    assert!(signature::RsaKeyPair::from_pkcs8(&pkcs8).is_ok());
    assert_eq!(pkcs8[4..7], [0x02, 0x01, 0x00]);
    pkcs8[6] = 1;
    assert!(rind::rsa::KeyPair::from_pkcs8(&pkcs8).is_ok());
    assert_eq!(
        signature::RsaKeyPair::from_pkcs8(&pkcs8)
            .err()
            .unwrap()
            .to_string(),
        "VersionNotSupported"
    );
}
