//! Every operation of rind's API that handles a secret, each timed once for
//! every secret input it takes.
//!
//! The fixed class holds one random secret, the random class a new one per
//! value. Every other input is the same for both. A comparison of a secret
//! against a presented value instead compares two wrong values, both
//! refused: the fixed one differs from the secret only in its last byte, and
//! the random ones almost always in their first. Whether a call fails is
//! public, but where the values first differ is not.
//!
//! Not timed, since rind's API cannot set their secrets: key generation and
//! encapsulation, which draw them from the system, and an ML-KEM
//! decapsulation key, which rind can neither import nor copy, so its fixed
//! class could not be separate values of one secret.

use std::num::NonZeroU32;
use std::sync::OnceLock;

use rind::{
    aead, agreement, cipher, constant_time, digest, hkdf, hmac, kem, key_wrap, oprf, pbkdf2, rsa,
    signature,
};

use crate::dudect::{Classes, Config, Report, classes, measure, measure_built};

pub struct Case {
    pub name: String,
    pub run: Box<dyn Fn(&Config) -> Report>,
}

fn case(name: impl Into<String>, run: impl Fn(&Config) -> Report + 'static) -> Case {
    Case {
        name: name.into(),
        run: Box::new(run),
    }
}

/// Values in each class of byte strings and cheap keys.
const VALUES: usize = 64;
/// Values in each class of RSA keys.
const RSA_KEYS: usize = 8;
/// A message length that takes the bulk path of every cipher and leaves a
/// partial final block.
const LEN: usize = 1347;
const MESSAGE: &[u8] = b"a public message";
const AAD: &[u8] = b"public associated data";
const NONCE: [u8; 12] = [7; 12];

/// The planted leak, which must be seen, then the controls and every case.
pub fn all() -> Vec<Case> {
    let mut cases = vec![
        case("planted/early-exit-compare", |config| {
            let expected = random::<32>();
            measure(config, &mismatches(&expected), |b| {
                early_exit_eq(&expected, b)
            })
        }),
        // Both classes hold one secret, so nothing but the harness could
        // tell them apart: once for bytes, once for keys built from them.
        case("control/sha256-same-input", |config| {
            let data = random_vec(LEN);
            let inputs = classes(VALUES, fixed(data.clone()), fixed(data));
            measure(config, &inputs, |data| {
                digest::digest(&digest::SHA256, data)
            })
        }),
        case("control/aes-128-gcm-same-key", |config| {
            let secret = random::<16>();
            let new = |secret: &[u8; 16]| aead::Key::new(&aead::AES_128_GCM, secret).unwrap();
            let plaintext = random::<LEN>();
            let secrets = classes(VALUES, fixed(secret), fixed(secret));
            measure_built(config, &secrets, new, |key| {
                let mut buf = plaintext;
                let nonce = aead::Nonce::assume_unique_for_key(NONCE);
                key.seal_in_place_separate_tag(nonce, AAD, &mut buf)
            })
        }),
        case("constant_time/verify", |config| {
            let expected = random::<32>();
            measure(config, &mismatches(&expected), |b| {
                constant_time::verify(&expected, b)
            })
        }),
    ];

    for (name, algorithm) in [
        ("md5", &digest::legacy::MD5),
        ("sha1", &digest::legacy::SHA1),
        ("sha256", &digest::SHA256),
        ("sha512", &digest::SHA512),
        ("sha3-256", &digest::SHA3_256),
    ] {
        cases.push(case(format!("digest/{name}"), move |config| {
            measure(config, &secrets(LEN), |data| {
                digest::digest(algorithm, data)
            })
        }));
    }

    hmac_cases(&mut cases);
    kdf_cases(&mut cases);
    aead_cases(&mut cases);
    cipher_cases(&mut cases);
    agreement_cases(&mut cases);
    oprf_cases(&mut cases);
    kem_cases(&mut cases);
    rsa_cases(&mut cases);
    signature_cases(&mut cases);
    cases
}

fn hmac_cases(cases: &mut Vec<Case>) {
    cases.push(case("hmac/sha256/key", |config| {
        measure(config, &secrets(32), |key| {
            hmac::Key::new(&hmac::HMAC_SHA256, key)
        })
    }));
    for (name, algorithm) in [
        ("sha256", &hmac::HMAC_SHA256),
        ("sha512", &hmac::HMAC_SHA512),
    ] {
        cases.push(case(format!("hmac/{name}/sign"), move |config| {
            let new = |key: &Vec<u8>| hmac::Key::new(algorithm, key);
            measure_built(config, &secrets(32), new, |key| hmac::sign(key, MESSAGE))
        }));
    }
    cases.push(case("hmac/sha256/verify", |config| {
        let key = hmac::Key::new(&hmac::HMAC_SHA256, &random::<32>());
        let tag = hmac::sign(&key, MESSAGE);
        measure(config, &mismatches(tag.as_ref()), |tag| {
            hmac::verify(&key, MESSAGE, tag)
        })
    }));
}

fn kdf_cases(cases: &mut Vec<Case>) {
    let salt = || hkdf::Salt::new(&hkdf::HKDF_SHA256, b"public salt");
    cases.push(case("hkdf/sha256/extract", move |config| {
        let salt = salt();
        measure(config, &secrets(32), |secret| salt.extract(secret))
    }));
    cases.push(case("hkdf/sha256/expand", move |config| {
        let salt = salt();
        let extract = |secret: &Vec<u8>| salt.extract(secret).unwrap();
        measure_built(config, &secrets(32), extract, |prk| {
            let mut out = [0; 32];
            prk.expand(&[b"public info"], out.len())
                .and_then(|okm| okm.fill(&mut out))
                .map(|()| out)
        })
    }));

    let iterations = NonZeroU32::new(2).unwrap();
    cases.push(case("pbkdf2/sha256/derive", move |config| {
        measure(config, &secrets(16), |password| {
            let mut out = [0; 32];
            pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, password)
                .derive(iterations, b"public salt", &mut out)
                .map(|()| out)
        })
    }));
    cases.push(case("pbkdf2/sha256/verify", move |config| {
        let secret = pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, &random::<16>());
        let mut derived = [0; 32];
        secret
            .derive(iterations, b"public salt", &mut derived)
            .unwrap();
        measure(config, &mismatches(&derived), |derived| {
            secret.verify(iterations, b"public salt", derived)
        })
    }));
}

fn aead_cases(cases: &mut Vec<Case>) {
    for (name, algorithm) in [
        ("aes-128-gcm", &aead::AES_128_GCM),
        ("aes-192-gcm", &aead::AES_192_GCM),
        ("aes-256-gcm", &aead::AES_256_GCM),
        ("chacha20-poly1305", &aead::CHACHA20_POLY1305),
    ] {
        let len = algorithm.key_len();
        let new = move |key: &[u8]| aead::Key::new(algorithm, key).unwrap();
        let build = move |key: &Vec<u8>| new(key);
        let nonce = || aead::Nonce::assume_unique_for_key(NONCE);

        cases.push(case(format!("aead/{name}/key"), move |config| {
            measure(config, &secrets(len), |key| aead::Key::new(algorithm, key))
        }));
        cases.push(case(format!("aead/{name}/seal-key"), move |config| {
            let plaintext = random::<LEN>();
            measure_built(config, &secrets(len), build, |key| {
                let mut buf = plaintext;
                key.seal_in_place_separate_tag(nonce(), AAD, &mut buf)
            })
        }));
        cases.push(case(format!("aead/{name}/seal-plaintext"), move |config| {
            let key = new(&random::<32>()[..len]);
            let plaintexts = classes(VALUES, fixed(random::<LEN>()), random::<LEN>);
            measure(config, &plaintexts, |plaintext| {
                let mut buf = *plaintext;
                key.seal_in_place_separate_tag(nonce(), AAD, &mut buf)
            })
        }));
        cases.push(case(
            format!("aead/{name}/open-ciphertext"),
            move |config| {
                let key = new(&random::<32>()[..len]);
                let seal = || {
                    let mut buf = random::<LEN>();
                    let tag = key.seal_in_place_separate_tag(nonce(), AAD, &mut buf);
                    (buf, tag.unwrap())
                };
                let ciphertexts = classes(VALUES, fixed(seal()), seal);
                measure(config, &ciphertexts, |(ciphertext, tag)| {
                    let mut buf = *ciphertext;
                    key.open_in_place_separate_tag(nonce(), AAD, *tag, &mut buf)
                        .map(|plaintext| plaintext[0])
                })
            },
        ));
        cases.push(case(format!("aead/{name}/open-tag"), move |config| {
            let key = new(&random::<32>()[..len]);
            let mut ciphertext = random::<LEN>();
            let tag = key
                .seal_in_place_separate_tag(nonce(), AAD, &mut ciphertext)
                .unwrap();
            measure(config, &mismatches(tag.as_ref()), |tag| {
                let mut buf = ciphertext;
                let tag = aead::Tag::try_from(&tag[..]).unwrap();
                key.open_in_place_separate_tag(nonce(), AAD, tag, &mut buf)
                    .map(|plaintext| plaintext[0])
            })
        }));
    }

    cases.push(case("aead/xchacha20-poly1305/seal-key", |config| {
        let new = |key: &Vec<u8>| aead::RandomizedNonceKey::new(key[..].try_into().unwrap());
        let plaintext = random::<LEN>();
        measure_built(config, &secrets(32), new, |key| {
            let mut buf = Vec::with_capacity(LEN + 16);
            buf.extend_from_slice(&plaintext);
            key.seal_in_place_append_tag(AAD, &mut buf)
        })
    }));

    // WebCrypto's AES-GCM: any IV length, truncated tags.
    cases.push(case("aead/gcm-truncated/open-tag", |config| {
        use aead::gcm::{Iv, Key, TagLength};
        let key = Key::new(&cipher::AES_128, &random::<16>(), TagLength::Truncated96).unwrap();
        let iv = random::<16>();
        let mut ciphertext = random::<LEN>();
        let tag = key
            .seal_in_place_separate_tag(
                Iv::assume_unique_for_key(&iv).unwrap(),
                AAD,
                &mut ciphertext,
            )
            .unwrap();
        measure(config, &mismatches(tag.as_ref()), |tag| {
            let mut buf = ciphertext;
            let iv = Iv::assume_unique_for_key(&iv).unwrap();
            key.open_in_place_separate_tag(iv, AAD, tag, &mut buf)
                .map(|plaintext| plaintext[0])
        })
    }));

    for (name, algorithm) in [
        ("aes-128", &aead::quic::AES_128),
        ("aes-256", &aead::quic::AES_256),
        ("chacha20", &aead::quic::CHACHA20),
    ] {
        cases.push(case(format!("quic/{name}/mask"), move |config| {
            let sample = random::<{ aead::quic::SAMPLE_LEN }>();
            measure(config, &secrets(algorithm.key_len()), |key| {
                aead::quic::HeaderProtectionKey::new(algorithm, key).map(|key| key.mask(&sample))
            })
        }));
    }
}

fn cipher_cases(cases: &mut Vec<Case>) {
    for (name, algorithm, len) in [
        ("aes-128", &cipher::AES_128, 16),
        ("aes-192", &cipher::AES_192, 24),
        ("aes-256", &cipher::AES_256, 32),
    ] {
        cases.push(case(format!("cipher/{name}/key"), move |config| {
            let block = random::<16>();
            measure(config, &secrets(len), |key| {
                let mut block = block;
                cipher::Aes::new(algorithm, key).map(|aes| {
                    aes.encrypt_block(&mut block);
                    block
                })
            })
        }));
    }
    cases.push(case("cipher/aes-256/block", |config| {
        let aes = cipher::Aes::new(&cipher::AES_256, &random::<32>()).unwrap();
        let blocks = classes(VALUES, fixed(random::<16>()), random::<16>);
        measure(config, &blocks, |block| {
            let mut block = *block;
            aes.encrypt_block(&mut block);
            block
        })
    }));
    cases.push(case("cipher/aes-128-ctr/key", |config| {
        let counter = random::<16>();
        measure(config, &secrets(16), |key| {
            let mut buf = [0; 256];
            cipher::AesCtr::new(&cipher::AES_128, key, 32)
                .and_then(|ctr| ctr.apply_keystream(&counter, &mut buf))
                .map(|()| buf)
        })
    }));
    cases.push(case("cipher/chacha20/key", |config| {
        measure(config, &secrets(32), |key| {
            let mut buf = [0; 256];
            cipher::ChaCha20::new(key[..].try_into().unwrap())
                .apply_keystream(&NONCE, 0, &mut buf)
                .map(|()| buf)
        })
    }));

    let iv = [9; 16];
    cases.push(case("cipher/aes-128-cbc/encrypt", move |config| {
        let key = cipher::AesCbcEncryptingKey::new(&cipher::AES_128, &random::<16>()).unwrap();
        let plaintexts = classes(VALUES, fixed(random::<256>()), random::<256>);
        measure(config, &plaintexts, |plaintext| {
            let mut buf = *plaintext;
            key.encrypt_blocks(cipher::CbcIv::assume_unpredictable(iv), &mut buf)
                .map(|()| buf)
        })
    }));
    cases.push(case("cipher/aes-128-cbc/decrypt-key", move |config| {
        let ciphertext = random::<256>();
        measure(config, &secrets(16), |key| {
            let mut buf = ciphertext;
            cipher::AesCbcDecryptingKey::new(&cipher::AES_128, key)
                .and_then(|key| key.decrypt_blocks(&iv, &mut buf))
                .map(|()| buf)
        })
    }));
    // Padding a decryption refuses: a valid padding's length is public once
    // the call returns, but where an invalid one breaks is not. Each claims
    // a whole block of padding with one byte wrong: the fixed one's the byte
    // furthest from the end, the random ones' anywhere before the last.
    cases.push(case("cipher/aes-128-cbc/decrypt-padding", move |config| {
        let secret = random::<16>();
        let encrypt = cipher::AesCbcEncryptingKey::new(&cipher::AES_128, &secret).unwrap();
        let decrypt = cipher::AesCbcDecryptingKey::new(&cipher::AES_128, &secret).unwrap();
        let prefix = random::<48>();
        let wrong_at = |at: usize| {
            let mut buf = [16; 64];
            buf[..48].copy_from_slice(&prefix);
            buf[48 + at] ^= random::<1>()[0] | 1;
            encrypt
                .encrypt_blocks(cipher::CbcIv::assume_unpredictable(iv), &mut buf)
                .unwrap();
            buf
        };
        let anywhere = || wrong_at(usize::from(random::<1>()[0]) % 15);
        let ciphertexts = classes(VALUES, fixed(wrong_at(0)), anywhere);
        measure(config, &ciphertexts, |ciphertext| {
            let mut buf = *ciphertext;
            decrypt
                .decrypt(&iv, &mut buf)
                .map(|plaintext| plaintext.len())
        })
    }));

    cases.push(case("key-wrap/aes-256/wrap-kek", |config| {
        let new = |kek: &Vec<u8>| key_wrap::AesKek::new(&key_wrap::AES_256, kek).unwrap();
        let key = random::<32>();
        measure_built(config, &secrets(32), new, |kek| {
            let mut wrapped = [0; 40];
            kek.wrap(&key, &mut wrapped).map(|()| wrapped)
        })
    }));
    cases.push(case("key-wrap/aes-256/wrap-key", move |config| {
        let kek = key_wrap::AesKek::new(&key_wrap::AES_256, &random::<32>()).unwrap();
        measure(
            config,
            &classes(VALUES, fixed(random::<32>()), random::<32>),
            |key| {
                let mut wrapped = [0; 40];
                kek.wrap(key, &mut wrapped).map(|()| wrapped)
            },
        )
    }));
    cases.push(case("key-wrap/aes-256/unwrap-kek", |config| {
        // Refused under every key.
        let wrapped = random::<40>();
        measure(config, &secrets(32), |kek| {
            let mut key = [0; 32];
            key_wrap::AesKek::new(&key_wrap::AES_256, kek)
                .and_then(|kek| kek.unwrap(&wrapped, &mut key))
                .map(|()| key)
        })
    }));
    // The integrity value an unwrap recovers, compared with RFC 3394's: keys
    // wrapped by hand from wrong initial values, all of one key.
    cases.push(case("key-wrap/aes-256/unwrap-integrity", |config| {
        let secret = random::<32>();
        let kek = key_wrap::AesKek::new(&key_wrap::AES_256, &secret).unwrap();
        let key = random::<32>();
        let wrap = |iv: &Vec<u8>| wrap_from(&secret, iv[..].try_into().unwrap(), &key);
        let mut wrapped = [0; 40];
        kek.wrap(&key, &mut wrapped).unwrap();
        assert_eq!(wrap(&vec![0xa6; 8]), wrapped);
        let wrapped = mismatches(&[0xa6; 8]).map(|ivs| ivs.iter().map(wrap).collect());
        measure(config, &wrapped, |wrapped| {
            let mut key = [0; 32];
            kek.unwrap(wrapped, &mut key).map(|()| key)
        })
    }));
    // RFC 5649's integrity value adds the key's length, which a flip of its
    // last bit would leave valid, so the fixed one's is out of range.
    cases.push(case("key-wrap/aes-256/unwrap-padded-integrity", |config| {
        let secret = random::<32>();
        let kek = key_wrap::AesKek::new(&key_wrap::AES_256, &secret).unwrap();
        let key = random::<20>();
        let padded = [&key[..], &[0; 4]].concat();
        let wrap = |aiv: &Vec<u8>| wrap_from(&secret, aiv[..].try_into().unwrap(), &padded);
        let aiv = [0xa6, 0x59, 0x59, 0xa6, 0, 0, 0, 20];
        let mut wrapped = [0; 32];
        kek.wrap_padded(&key, &mut wrapped).unwrap();
        assert_eq!(wrap(&aiv.to_vec()), wrapped);
        let mut late = aiv;
        late[7] ^= 0x80;
        let other = || loop {
            let value = random::<8>();
            if value[..4] != aiv[..4] {
                return value.to_vec();
            }
        };
        let aivs = classes(VALUES, fixed(late.to_vec()), other);
        let wrapped = aivs.map(|aivs| aivs.iter().map(wrap).collect());
        measure(config, &wrapped, |wrapped| {
            let mut key = [0; 24];
            kek.unwrap_padded(wrapped, &mut key).map(|key| key.len())
        })
    }));
}

fn agreement_cases(cases: &mut Vec<Case>) {
    for (name, algorithm) in [
        ("x25519", &agreement::X25519),
        ("p256", &agreement::ECDH_P256),
        ("p384", &agreement::ECDH_P384),
        ("p521", &agreement::ECDH_P521),
    ] {
        let generate = move || agreement::PrivateKey::generate(algorithm).unwrap();
        let scalar = move || generate().to_scalar().as_ref().to_vec();
        let from_scalar = move |s: &[u8]| agreement::PrivateKey::from_scalar(algorithm, s);

        cases.push(case(
            format!("agreement/{name}/public-key"),
            move |config| {
                let scalars = classes(VALUES, fixed(scalar()), scalar);
                measure(config, &scalars, |s| {
                    from_scalar(s).map(|key| key.public_key().clone())
                })
            },
        ));
        cases.push(case(format!("agreement/{name}/agree-key"), move |config| {
            let peer = generate().public_key().clone();
            let scalars = classes(VALUES, fixed(scalar()), scalar);
            let new = |s: &Vec<u8>| from_scalar(s).unwrap();
            measure_built(config, &scalars, new, |key| key.agree(peer.as_ref()))
        }));
        cases.push(case(
            format!("agreement/{name}/agree-peer"),
            move |config| {
                let key = generate();
                let peer = move || generate().public_key().as_ref().to_vec();
                let peers = classes(VALUES, fixed(peer()), peer);
                measure(config, &peers, |peer| key.agree(peer))
            },
        ));
    }
}

/// The OPRF input is the secret hashed to the curve. The server scalar stays
/// fixed, so the two classes differ only in that message.
fn oprf_cases(cases: &mut Vec<Case>) {
    for (name, suite, scalar_len) in [
        ("p256", &oprf::P256_SHA256, 32),
        ("p384", &oprf::P384_SHA384, 48),
        ("p521", &oprf::P521_SHA512, 66),
    ] {
        cases.push(case(format!("oprf/{name}/input"), move |config| {
            let mut scalar = vec![0u8; scalar_len];
            scalar[scalar_len - 1] = 2;
            let key = oprf::ServerKey::from_bytes(suite, &scalar).unwrap();
            measure(config, &secrets(32), |input| key.evaluate(input).unwrap())
        }));
    }
}

fn kem_cases(cases: &mut Vec<Case>) {
    let setup = || {
        let key = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
        let public = key.public_key();
        let encapsulate = move || public.encapsulate().unwrap().0.as_ref().to_vec();
        (key, encapsulate)
    };
    cases.push(case("kem/ml-kem-768/decapsulate", move |config| {
        let (key, encapsulate) = setup();
        let ciphertexts = classes(VALUES, fixed(encapsulate()), encapsulate);
        measure(config, &ciphertexts, |c| key.decapsulate(c))
    }));
    // A tampered ciphertext must cost what a valid one does, or the implicit
    // rejection that hides it is undone.
    cases.push(case("kem/ml-kem-768/decapsulate-reject", move |config| {
        let (key, encapsulate) = setup();
        let valid = encapsulate();
        let tampered = || {
            let mut c = valid.clone();
            let [at, flip] = random::<2>();
            let at = usize::from(at) * c.len() / 256;
            c[at] ^= flip | 1;
            c
        };
        let ciphertexts = classes(VALUES, fixed(valid.clone()), tampered);
        measure(config, &ciphertexts, |c| key.decapsulate(c))
    }));
}

fn rsa_cases(cases: &mut Vec<Case>) {
    for (bits, size) in RSA_SIZES {
        let name = |op: &str| format!("rsa-{bits}/{op}");
        let signing = |der: &Vec<u8>| signature::RsaKeyPair::from_pkcs8(der).unwrap();
        let decrypting =
            |der: &[u8]| rsa::DecryptingKey::from_pkcs8(&rsa::OAEP_SHA256, der).unwrap();

        cases.push(case(name("from-pkcs1"), move |config| {
            measure(config, rsa_keys_one_modulus(size), |der| {
                signature::RsaKeyPair::from_pkcs1(der)
            })
        }));
        cases.push(case(name("sign-key"), move |config| {
            measure_built(config, rsa_keys(size), signing, |key| {
                key.sign(&signature::sign::RSA_PKCS1_SHA256, MESSAGE)
            })
        }));
        cases.push(case(name("sign-message"), move |config| {
            let key = signing(&rsa_keys(size)[0][0]);
            let messages = classes(VALUES, fixed(random::<32>()), random::<32>);
            measure(config, &messages, |message| {
                key.sign(&signature::sign::RSA_PKCS1_SHA256, message)
            })
        }));
        cases.push(case(name("oaep-decrypt-key"), move |config| {
            // Each key with a ciphertext of its own.
            let encrypted = |der: &Vec<u8>| {
                let public = decrypting(der).public_key();
                let c = full_length(|| {
                    public
                        .encrypt(&random::<32>(), b"")
                        .unwrap()
                        .as_ref()
                        .to_vec()
                });
                (der.clone(), c)
            };
            let keys = rsa_keys(size)
                .each_ref()
                .map(|keys| keys.iter().map(encrypted).collect());
            let build = |(der, c): &(Vec<u8>, Vec<u8>)| (decrypting(der), c.clone());
            measure_built(config, &keys, build, |(key, c)| key.decrypt(c, b""))
        }));
        // Padding a decryption refuses, as in Manger's attack: the fixed
        // ciphertext's encoding fails as late as one can, the random ones'
        // almost always at its first byte.
        cases.push(case(name("oaep-decrypt-padding"), move |config| {
            let pkcs1 = &rsa_keys_one_modulus(size)[0][0];
            let key = rsa::DecryptingKey::from_pkcs1(&rsa::OAEP_SHA256, pkcs1).unwrap();
            // The encoded message is as long as the modulus.
            let len = key.public_key().encrypt(b"", b"").unwrap().as_ref().len();
            let encrypt = |em: &dyn Fn() -> Vec<u8>| {
                full_length(|| crate::rsa_keys::encrypt_raw(pkcs1, &em()))
            };
            let valid = encrypt(&|| oaep(len, true));
            assert!(key.decrypt(&valid, b"").unwrap().as_ref().is_empty());
            // Random values, which decrypt to their remainder modulo n.
            let anything = || encrypt(&|| random_vec(len));
            let ciphertexts = classes(VALUES, fixed(encrypt(&|| oaep(len, false))), anything);
            measure(config, &ciphertexts, |c| key.decrypt(c, b""))
        }));
        cases.push(case(name("oaep-decrypt-ciphertext"), move |config| {
            let key = decrypting(&rsa_keys(size)[0][0]);
            let public = key.public_key();
            let encrypt = || {
                full_length(|| {
                    public
                        .encrypt(&random::<32>(), b"")
                        .unwrap()
                        .as_ref()
                        .to_vec()
                })
            };
            let ciphertexts = classes(VALUES, fixed(encrypt()), encrypt);
            measure(config, &ciphertexts, |c| key.decrypt(c, b""))
        }));
    }
}

/// The sizes with their own code: on x86_64, aws-lc's RSAZ for 2048, its
/// AVX-512 RSAZ for 2048, 3072, and 4096, and the generic exponentiation the
/// others share with CPUs that lack them.
const RSA_SIZES: [(u32, rsa::KeySize); 3] = [
    (2048, rsa::KeySize::Rsa2048),
    (3072, rsa::KeySize::Rsa3072),
    (4096, rsa::KeySize::Rsa4096),
];

/// PKCS#8 encodings of RSA keys of `size`, generated once: the fixed class
/// one key, the random class others.
fn rsa_keys(size: rsa::KeySize) -> &'static Classes<Vec<u8>> {
    static KEYS: [OnceLock<Classes<Vec<u8>>>; 3] = [const { OnceLock::new() }; 3];
    let i = RSA_SIZES.iter().position(|&(_, s)| s == size).unwrap();
    KEYS[i].get_or_init(|| {
        let generate = || {
            let key = signature::RsaKeyPair::generate(size).unwrap();
            key.to_pkcs8().as_ref().to_vec()
        };
        classes(RSA_KEYS, fixed(generate()), generate)
    })
}

/// PKCS#1 encodings of RSA keys of `size` that share one public key (see
/// [`crate::rsa_keys`]), generated once: the fixed class one of them, the
/// random class the others in turn.
fn rsa_keys_one_modulus(size: rsa::KeySize) -> &'static Classes<Vec<u8>> {
    static KEYS: [OnceLock<Classes<Vec<u8>>>; 3] = [const { OnceLock::new() }; 3];
    let i = RSA_SIZES.iter().position(|&(_, s)| s == size).unwrap();
    KEYS[i].get_or_init(|| {
        // A key may have no other variant of the same widths; draw another.
        let keys = loop {
            let pkcs8 = signature::RsaKeyPair::generate(size).unwrap().to_pkcs8();
            let keys = crate::rsa_keys::variants(pkcs8.as_ref());
            if keys.len() > 1 {
                break keys;
            }
        };
        let mut others = keys[1..].iter().cycle();
        classes(RSA_KEYS, fixed(keys[0].clone()), || {
            others.next().unwrap().clone()
        })
    })
}

fn signature_cases(cases: &mut Vec<Case>) {
    for (name, algorithm) in [
        ("p256", &signature::sign::ECDSA_P256_SHA256_FIXED),
        ("p384", &signature::sign::ECDSA_P384_SHA384_FIXED),
        ("p521", &signature::sign::ECDSA_P521_SHA512_FIXED),
    ] {
        let der = move || {
            signature::EcdsaKeyPair::generate(algorithm)
                .unwrap()
                .to_pkcs8()
                .as_ref()
                .to_vec()
        };
        let from = move |der: &[u8]| signature::EcdsaKeyPair::from_pkcs8(algorithm, der).unwrap();

        cases.push(case(format!("ecdsa/{name}/from-pkcs8"), move |config| {
            let ders = classes(VALUES, fixed(der()), der);
            measure(config, &ders, |der| {
                signature::EcdsaKeyPair::from_pkcs8(algorithm, der)
            })
        }));
        cases.push(case(format!("ecdsa/{name}/sign-key"), move |config| {
            let ders = classes(VALUES, fixed(der()), der);
            measure_built(config, &ders, |der| from(der), |key| key.sign(MESSAGE))
        }));
        cases.push(case(format!("ecdsa/{name}/sign-message"), move |config| {
            let key = from(&der());
            let messages = classes(VALUES, fixed(random::<32>()), random::<32>);
            measure(config, &messages, |message| key.sign(message))
        }));
    }

    let seed = || {
        signature::Ed25519KeyPair::generate()
            .unwrap()
            .to_seed()
            .as_ref()
            .to_vec()
    };
    let from = |seed: &[u8]| signature::Ed25519KeyPair::from_seed(seed).unwrap();
    cases.push(case("ed25519/from-seed", move |config| {
        let seeds = classes(VALUES, fixed(seed()), seed);
        measure(config, &seeds, |seed| {
            signature::Ed25519KeyPair::from_seed(seed)
        })
    }));
    cases.push(case("ed25519/sign-key", move |config| {
        let seeds = classes(VALUES, fixed(seed()), seed);
        measure_built(config, &seeds, |seed| from(seed), |key| key.sign(MESSAGE))
    }));
    // The message picks the nonce, so it is a secret input too.
    cases.push(case("ed25519/sign-message", move |config| {
        let key = from(&seed());
        let messages = classes(VALUES, fixed(random::<32>()), random::<32>);
        measure(config, &messages, |message| key.sign(message))
    }));
}

fn random<const N: usize>() -> [u8; N] {
    let mut bytes = [0; N];
    rind::rand::fill(&mut bytes).unwrap();
    bytes
}

fn random_vec(len: usize) -> Vec<u8> {
    let mut bytes = vec![0; len];
    rind::rand::fill(&mut bytes).unwrap();
    bytes
}

/// A function that clones `value`, for a fixed class.
fn fixed<T: Clone>(value: T) -> impl FnMut() -> T {
    move || value.clone()
}

/// Secret byte strings of `len`.
fn secrets(len: usize) -> Classes<Vec<u8>> {
    classes(VALUES, fixed(random_vec(len)), || random_vec(len))
}

/// Wrong values to compare `expected` with: the fixed one differs only in
/// its last byte.
fn mismatches(expected: &[u8]) -> Classes<Vec<u8>> {
    let mut last = expected.to_vec();
    *last.last_mut().unwrap() ^= 1;
    classes(VALUES, fixed(last), || {
        loop {
            let value = random_vec(expected.len());
            if value != expected {
                return value;
            }
        }
    })
}

/// A comparison that stops at the first difference, which the harness must
/// find.
#[inline(never)]
fn early_exit_eq(a: &[u8], b: &[u8]) -> bool {
    // `black_box` keeps the compiler from turning the loop into `bcmp`,
    // whose wide loads compare 32 bytes without exiting early.
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| std::hint::black_box(*x) == *y)
}

/// An RSA ciphertext from `encrypt` whose first byte is not zero: parsing
/// one trims leading zeros, in time that depends on them but on nothing
/// secret, so every class has none. Each call to `encrypt` must draw new
/// randomness, or a zero first byte repeats forever.
fn full_length(mut encrypt: impl FnMut() -> Vec<u8>) -> Vec<u8> {
    loop {
        let c = encrypt();
        if c[0] != 0 {
            return c;
        }
    }
}

/// RFC 3394's wrapping of `plaintext` under the AES-256 key `kek` from the
/// initial value `iv`, which rind's API fixes.
fn wrap_from(kek: &[u8], iv: [u8; 8], plaintext: &[u8]) -> Vec<u8> {
    let aes = cipher::Aes::new(&cipher::AES_256, kek).unwrap();
    let mut a = iv;
    let mut r = plaintext.to_vec();
    let mut t = 0u64;
    for _ in 0..6 {
        for r_i in r.as_chunks_mut::<8>().0 {
            t += 1;
            let mut block = [0; 16];
            block[..8].copy_from_slice(&a);
            block[8..].copy_from_slice(r_i);
            aes.encrypt_block(&mut block);
            a = (u64::from_be_bytes(block[..8].try_into().unwrap()) ^ t).to_be_bytes();
            r_i.copy_from_slice(&block[8..]);
        }
    }
    [&a[..], &r].concat()
}

/// An RSA-OAEP encoded message of `len` bytes, for SHA-256 and an empty
/// label, holding the empty message: its first byte zero and its label hash
/// right, and the 0x01 that ends its zero padding there if `separator`.
fn oaep(len: usize, separator: bool) -> Vec<u8> {
    let seed = random::<32>();
    let mut db = vec![0; len - 33];
    db[..32].copy_from_slice(digest::digest(&digest::SHA256, b"").as_ref());
    *db.last_mut().unwrap() = u8::from(separator);
    xor_mgf1(&mut db, &seed);
    let mut masked_seed = seed;
    xor_mgf1(&mut masked_seed, &db);
    [&[0][..], &masked_seed, &db].concat()
}

/// XORs MGF1 with SHA-256 of `seed` into `out`.
fn xor_mgf1(out: &mut [u8], seed: &[u8]) {
    for (counter, chunk) in (0u32..).zip(out.chunks_mut(32)) {
        let mask = digest::digest(&digest::SHA256, &[seed, &counter.to_be_bytes()].concat());
        for (out, mask) in chunk.iter_mut().zip(mask.as_ref()) {
            *out ^= mask;
        }
    }
}
