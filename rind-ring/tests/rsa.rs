//! ring signs only with moduli of 2048 to 4096 bits, which rind-ring keeps
//! though rind loads keys up to 8192 bits; ring's own vectors stop at 4096.

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

/// ring's `Version::V1Only`. rind takes version 1 when the public key is absent.
#[test]
fn pkcs8_v1_only() {
    let der = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");
    let mut v2 = der.to_vec();
    let start = match v2[1] {
        0x81 => 3,
        0x82 => 4,
        _ => 2,
    };
    assert_eq!(&v2[start..start + 3], &[0x02, 0x01, 0x00]);
    v2[start + 2] = 0x01;
    assert!(rind::signature::RsaKeyPair::from_pkcs8(&v2).is_ok());
    assert!(signature::RsaKeyPair::from_pkcs8(&v2).is_err());
    assert!(signature::RsaKeyPair::from_pkcs8(der).is_ok());
}
