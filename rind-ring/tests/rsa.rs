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

/// A PKCS#1 key's integers in `RSAPrivateKey` order (n, e, d, p, q, dP, dQ,
/// qInv), read with rind-ring's own DER reader.
#[cfg(not(target_family = "wasm"))]
fn components(pkcs1: &[u8]) -> Vec<Vec<u8>> {
    use rind_ring::{error, io::der};
    untrusted::Input::from(pkcs1)
        .read_all(error::Unspecified, |input| {
            der::nested(input, der::Tag::Sequence, error::Unspecified, |input| {
                der::small_nonnegative_integer(input)?;
                (0..8)
                    .map(|_| {
                        der::positive_integer(input)
                            .map(|x| x.big_endian_without_leading_zero().to_vec())
                    })
                    .collect()
            })
        })
        .unwrap()
}

/// Loads a key from its integers as ring does, or refuses it alike, with
/// any one of them changed: given a leading zero byte, a bit flipped, or a
/// byte cut off. Only a private integer with a leading zero byte differs,
/// which rind takes and ring may refuse, and integers that disagree, which
/// rind refuses as aws-lc-rs does: ring takes a wrong `d`, which it never
/// uses, and finds the others only when it signs.
// ring does not build for wasm.
#[cfg(not(target_family = "wasm"))]
#[test]
fn key_pair_from_components() {
    use rind_ring::rsa as ours;
    use ring::rsa as theirs;

    for bits in [2048, 3072, 4096] {
        let der = std::fs::read(format!(
            "{}/../rind/src/high/rsa/rsa{bits}.der",
            env!("CARGO_MANIFEST_DIR")
        ))
        .unwrap();
        let fields = components(&der);
        for field in 0..8 {
            for change in 0..4 {
                let mut fields = fields.clone();
                let value = &mut fields[field];
                match change {
                    0 => {}
                    1 => value.insert(0, 0),
                    2 => {
                        let at = field * 7 % value.len();
                        value[at] ^= 0x10;
                    }
                    _ => {
                        value.pop();
                    }
                }
                let [n, e, d, p, q, dp, dq, qi] = &fields[..] else {
                    unreachable!()
                };
                let ours = ours::KeyPair::from_components(&ours::KeyPairComponents {
                    public_key: ours::PublicKeyComponents { n, e },
                    d,
                    p,
                    q,
                    dP: dp,
                    dQ: dq,
                    qInv: qi,
                });
                let theirs = theirs::KeyPair::from_components(&theirs::KeyPairComponents {
                    public_key: theirs::PublicKeyComponents { n, e },
                    d,
                    p,
                    q,
                    dP: dp,
                    dQ: dq,
                    qInv: qi,
                });
                let at = format!("{bits} bits, field {field}, change {change}");
                if change == 1 && field >= 2 {
                    assert!(ours.is_ok(), "{at}");
                    continue;
                }
                // A changed `d` disagrees with the rest, which rind refuses
                // even where ring, never reading it, takes it.
                if field == 2 && change >= 2 {
                    assert!(ours.is_err(), "{at}");
                }
                let ring_signs = |key: &theirs::KeyPair| {
                    let mut signature = vec![0; key.public().modulus_len()];
                    key.sign(
                        &ring::signature::RSA_PKCS1_SHA256,
                        &ring::rand::SystemRandom::new(),
                        b"message",
                        &mut signature,
                    )
                    .map(|()| signature)
                };
                let (ours, theirs) = match (ours, theirs) {
                    (Ok(ours), Ok(theirs)) => (ours, theirs),
                    (Err(_), Err(_)) => continue,
                    // ring never uses `d`, so it signs with a wrong one,
                    // and checks `e` and the CRT integers only when it
                    // signs, so a key whose others disagree fails there.
                    (Err(_), Ok(theirs)) => {
                        assert_eq!(ring_signs(&theirs).is_ok(), field == 2, "{at}");
                        continue;
                    }
                    (Ok(_), Err(_)) => panic!("{at}: ring refuses it"),
                };
                assert_eq!(ours.public().as_ref(), theirs.public().as_ref());
                let mut signature = vec![0; ours.public().modulus_len()];
                ours.sign(
                    &signature::RSA_PKCS1_SHA256,
                    &rand::SystemRandom::new(),
                    b"message",
                    &mut signature,
                )
                .unwrap();
                assert_eq!(signature, ring_signs(&theirs).unwrap(), "{at}");
            }
        }
    }
}

/// `Debug` shows what ring's does, the public key, and none of the private
/// integers.
// ring does not build for wasm.
#[cfg(not(target_family = "wasm"))]
#[test]
fn key_pair_components_debug() {
    use rind_ring::rsa as ours;
    use ring::rsa as theirs;

    let private = [0xffu8];
    let ours = ours::KeyPairComponents {
        public_key: ours::PublicKeyComponents { n: [1u8], e: [3u8] },
        d: private,
        p: private,
        q: private,
        dP: private,
        dQ: private,
        qInv: private,
    };
    let theirs = theirs::KeyPairComponents {
        public_key: theirs::PublicKeyComponents { n: [1u8], e: [3u8] },
        d: private,
        p: private,
        q: private,
        dP: private,
        dQ: private,
        qInv: private,
    };
    let shown = format!("{ours:?}");
    assert_eq!(shown, format!("{theirs:?}"));
    assert!(!shown.contains("255"), "{shown}");
}
