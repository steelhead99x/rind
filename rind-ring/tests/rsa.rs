//! ring signs only with moduli of 2047 to 4096 bits, which rind-ring keeps
//! though rind loads keys up to 8192 bits; ring's own vectors stop at 4096.

#![cfg(feature = "alloc")]

use rind_ring::{rand, signature};

/// PKCS#1 keys, and whether ring loads each: it sizes a key by its primes,
/// which must be `ceil(n / 2)` bits and a multiple of 512, so it takes a
/// 2047-bit modulus of two 1024-bit primes, or 3071 bits of two 1536-bit
/// ones, and refuses 2560 bits, whose primes are 1280, and a 3072-bit
/// modulus whose primes are 1537 and 1535 bits. The 2086-bit one has primes
/// of 1028 and 1058, and the `rsa2560-unbalanced` one of 1280 and 1281, so
/// its first prime is right and its multiple of 512 is what fails. The
/// 3071-bit `rsa3071-unbalanced-q` has primes of 1536 and 1535 bits, so its
/// first prime and its multiple of 512 pass and only its second fails. ring
/// signs only with moduli up to 4096 bits, which rind-ring keeps though rind
/// loads keys up to 8192 bits.
const KEYS: [(&str, bool); 14] = [
    ("../rind/src/high/rsa/rsa2047.der", true),
    ("../rind/src/high/rsa/rsa2048.der", true),
    ("../rind/src/high/rsa/rsa2086-unbalanced.der", false),
    ("tests/rsa/rsa2560.der", false),
    ("tests/rsa/rsa2560-unbalanced.der", false),
    ("tests/rsa/rsa3071.der", true),
    ("tests/rsa/rsa3071-unbalanced-q.der", false),
    ("../rind/src/high/rsa/rsa3072.der", true),
    ("tests/rsa/rsa3072-unbalanced.der", false),
    ("tests/rsa/rsa4095.der", true),
    ("../rind/src/high/rsa/rsa4096.der", true),
    ("../rind/src/high/rsa/rsa4096-other.der", true),
    ("../rind/src/high/rsa/rsa6144.der", false),
    ("../rind/src/high/rsa/rsa8192.der", false),
];

fn read(path: &str) -> Vec<u8> {
    std::fs::read(format!("{}/{path}", env!("CARGO_MANIFEST_DIR"))).unwrap()
}

/// Each key loads as ring does, or is refused for its reason, and signs and
/// verifies once it loads.
#[test]
fn key_pair_prime_lengths() {
    for (path, ok) in KEYS {
        let der = read(path);
        let key_pair = signature::RsaKeyPair::from_der(&der);
        assert_eq!(key_pair.is_ok(), ok, "{path}");
        let Ok(key_pair) = key_pair else { continue };

        let mut signature = vec![0; key_pair.public_modulus_len()];
        key_pair
            .sign(
                &signature::RSA_PSS_SHA256,
                &rand::SystemRandom::new(),
                b"message",
                &mut signature,
            )
            .unwrap();
        // ring counts a modulus floor in whole bytes, so the 2047-bit key
        // verifies under the 2048-bit floor.
        signature::UnparsedPublicKey::new(
            &signature::RSA_PSS_2048_8192_SHA256,
            key_pair.public().as_ref(),
        )
        .verify(b"message", &signature)
        .unwrap();
    }
}

/// Every loader gives ring's verdict and reason for each key, and the same
/// signature once it loads.
// ring does not build for wasm.
#[cfg(not(target_family = "wasm"))]
#[test]
fn key_pair_prime_lengths_match_ring() {
    use rind_ring::rsa as ours;
    use ring::rsa as theirs;

    for (path, ok) in KEYS {
        let der = read(path);
        let pkcs8 = rind::rsa::KeyPair::from_pkcs1(&der)
            .unwrap()
            .to_pkcs8()
            .as_ref()
            .to_vec();
        let fields = components(&der);
        let [n, e, d, p, q, dp, dq, qi] = &fields[..] else {
            unreachable!()
        };
        let ours_components = ours::KeyPair::from_components(&ours::KeyPairComponents {
            public_key: ours::PublicKeyComponents { n, e },
            d,
            p,
            q,
            dP: dp,
            dQ: dq,
            qInv: qi,
        });
        let theirs_components = theirs::KeyPair::from_components(&theirs::KeyPairComponents {
            public_key: theirs::PublicKeyComponents { n, e },
            d,
            p,
            q,
            dP: dp,
            dQ: dq,
            qInv: qi,
        });
        let loaded = [
            (
                "from_der",
                ours::KeyPair::from_der(&der),
                theirs::KeyPair::from_der(&der),
            ),
            (
                "from_pkcs8",
                ours::KeyPair::from_pkcs8(&pkcs8),
                theirs::KeyPair::from_pkcs8(&pkcs8),
            ),
            ("from_components", ours_components, theirs_components),
        ];
        for (loader, ours, theirs) in loaded {
            let at = format!("{path}, {loader}");
            assert_eq!(theirs.is_ok(), ok, "{at}: ring");
            match (ours, theirs) {
                (Ok(ours), Ok(theirs)) => {
                    assert_eq!(ours.public().as_ref(), theirs.public().as_ref(), "{at}");
                    let sign = |sign: &dyn Fn(&mut [u8])| {
                        let mut signature = vec![0; ours.public_modulus_len()];
                        sign(&mut signature);
                        signature
                    };
                    let from_ours = sign(&|out| {
                        ours.sign(
                            &signature::RSA_PKCS1_SHA256,
                            &rand::SystemRandom::new(),
                            b"message",
                            out,
                        )
                        .unwrap()
                    });
                    let from_theirs = sign(&|out| {
                        theirs
                            .sign(
                                &ring::signature::RSA_PKCS1_SHA256,
                                &ring::rand::SystemRandom::new(),
                                b"message",
                                out,
                            )
                            .unwrap()
                    });
                    assert_eq!(from_ours, from_theirs, "{at}");
                }
                (Err(ours), Err(theirs)) => {
                    assert_eq!(ours.to_string(), theirs.to_string(), "{at}");
                }
                (ours, theirs) => panic!("{at}: {ours:?}, ring {theirs:?}"),
            }
        }
    }
}

/// Every verification algorithm gives ring's verdict for each key's
/// signature under each padding and hash, so a modulus a bit under an
/// algorithm's floor verifies where ring counts it in whole bytes: 2047 bits
/// under the 2048-bit algorithms, and 3071 under the 3072-bit one.
// ring does not build for wasm.
#[cfg(not(target_family = "wasm"))]
#[test]
fn verification_floors_match_ring() {
    use rind::rsa::sign;

    macro_rules! algorithms {
        ($($name:ident),*) => {
            [$((stringify!($name), &signature::$name, &ring::signature::$name)),*]
        };
    }
    let algorithms = algorithms![
        RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_2048_8192_SHA256,
        RSA_PKCS1_2048_8192_SHA384,
        RSA_PKCS1_2048_8192_SHA512,
        RSA_PKCS1_3072_8192_SHA384,
        RSA_PSS_2048_8192_SHA256,
        RSA_PSS_2048_8192_SHA384,
        RSA_PSS_2048_8192_SHA512
    ];
    let signers = [
        &sign::PKCS1_SHA256,
        &sign::PKCS1_SHA384,
        &sign::PKCS1_SHA512,
        &sign::PSS_SHA256,
        &sign::PSS_SHA384,
        &sign::PSS_SHA512,
    ];

    let mut verified = Vec::new();
    for (path, _) in KEYS {
        let key = rind::rsa::KeyPair::from_pkcs1(&read(path)).unwrap();
        let public = key.public_key().as_ref();
        let fields = components(&read(path));
        let (n, e) = (&fields[0], &fields[1]);
        for signer in signers {
            let signature = key.sign(signer, b"message").unwrap();
            let signature = signature.as_ref();
            for (name, ours, theirs) in algorithms {
                let at = format!("{path}, {signer:?}, {name}");
                let theirs_verifies = ring::signature::UnparsedPublicKey::new(theirs, public)
                    .verify(b"message", signature)
                    .is_ok();
                let ours_verifies = signature::UnparsedPublicKey::new(ours, public)
                    .verify(b"message", signature)
                    .is_ok();
                assert_eq!(ours_verifies, theirs_verifies, "{at}");
                let theirs_verifies = ring::rsa::PublicKeyComponents { n, e }
                    .verify(theirs, b"message", signature)
                    .is_ok();
                let ours_verifies = rind_ring::rsa::PublicKeyComponents { n, e }
                    .verify(ours, b"message", signature)
                    .is_ok();
                assert_eq!(ours_verifies, theirs_verifies, "{at}, components");
                if theirs_verifies {
                    verified.push((path, name));
                }
            }
        }
    }
    // The odd sizes are among what verifies, so the test checks the floors.
    for (path, name) in [
        (
            "../rind/src/high/rsa/rsa2047.der",
            "RSA_PSS_2048_8192_SHA256",
        ),
        ("tests/rsa/rsa3071.der", "RSA_PKCS1_3072_8192_SHA384"),
    ] {
        assert!(verified.contains(&(path, name)), "{path}, {name}");
    }
}

/// A public key as a PKCS#1 `RSAPublicKey`, from a 128-byte modulus whose
/// top bit is clear and an exponent of 65537.
#[cfg(not(target_family = "wasm"))]
fn public_key_der(n: &[u8]) -> Vec<u8> {
    assert!(n.len() == 128 && n[0] & 0x80 == 0);
    let mut der = vec![0x30, 0x81, 0x88, 0x02, 0x81, 0x80];
    der.extend_from_slice(n);
    der.extend_from_slice(&[0x02, 0x03, 0x01, 0x00, 0x01]);
    der
}

/// A 1023-bit modulus fills 128 bytes, so ring's byte-counted floor takes it
/// under the 1024-bit legacy algorithm, through both entry points, as
/// `rind::rsa::PublicKey` itself would refuse it, and under no algorithm
/// whose floor is higher.
// ring does not build for wasm.
#[cfg(not(target_family = "wasm"))]
#[test]
fn legacy_floor_counts_bytes() {
    let n = read("tests/rsa/rsa1023.n");
    let e = [1, 0, 1];
    let signature = read("tests/rsa/rsa1023.sig");
    let public = public_key_der(&n);

    macro_rules! algorithms {
        ($($name:ident),*) => {
            [$((stringify!($name), &signature::$name, &ring::signature::$name)),*]
        };
    }
    let mut verified = Vec::new();
    for (name, ours, theirs) in algorithms![
        RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_2048_8192_SHA256
    ] {
        let theirs_verifies = ring::signature::UnparsedPublicKey::new(theirs, &public)
            .verify(b"message", &signature)
            .is_ok();
        let ours_verifies = signature::UnparsedPublicKey::new(ours, &public)
            .verify(b"message", &signature)
            .is_ok();
        assert_eq!(ours_verifies, theirs_verifies, "{name}");
        let (n, e) = (&n[..], &e[..]);
        let theirs_components = ring::rsa::PublicKeyComponents { n, e }
            .verify(theirs, b"message", &signature)
            .is_ok();
        let ours_components = rind_ring::rsa::PublicKeyComponents { n, e }
            .verify(ours, b"message", &signature)
            .is_ok();
        assert_eq!(ours_components, theirs_components, "{name}, components");
        assert_eq!(theirs_verifies, theirs_components, "{name}, ring");
        if theirs_verifies {
            verified.push(name);
        }
    }
    // The control: ring takes it, so the test checks the floor.
    assert_eq!(verified, ["RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY"]);
}

/// Both SHA-1 verifiers take a valid SHA-1 signature, as ring's do, through
/// both entry points; no other test signs with SHA-1.
// ring does not build for wasm.
#[cfg(not(target_family = "wasm"))]
#[test]
fn sha1_verification_matches_ring() {
    let key = rind::rsa::KeyPair::from_pkcs1(&read("../rind/src/high/rsa/rsa2048.der")).unwrap();
    let public = key.public_key().as_ref();
    let fields = components(&read("../rind/src/high/rsa/rsa2048.der"));
    let (n, e) = (&fields[0], &fields[1]);
    // `openssl dgst -sha1 -sign rsa2048.der -keyform DER` over "message".
    let signature = read("tests/rsa/rsa2048-sha1.sig");

    macro_rules! algorithms {
        ($($name:ident),*) => {
            [$((stringify!($name), &signature::$name, &ring::signature::$name)),*]
        };
    }
    for (name, ours, theirs) in algorithms![
        RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
        RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY
    ] {
        ring::signature::UnparsedPublicKey::new(theirs, public)
            .verify(b"message", &signature)
            .expect(name);
        signature::UnparsedPublicKey::new(ours, public)
            .verify(b"message", &signature)
            .expect(name);
        ring::rsa::PublicKeyComponents { n, e }
            .verify(theirs, b"message", &signature)
            .expect(name);
        rind_ring::rsa::PublicKeyComponents { n, e }
            .verify(ours, b"message", &signature)
            .expect(name);
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
