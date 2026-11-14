mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

/// libcrux's RSA-PSS key, which holds the modulus and private exponent
/// alone, so it signs without the CRT.
fn libcrux_key(private_key: &[u8]) -> libcrux_rsa::PrivateKey<256> {
    use rsa::pkcs1::DecodeRsaPrivateKey;
    use rsa::traits::{PrivateKeyParts, PublicKeyParts};
    let key = rsa::RsaPrivateKey::from_pkcs1_der(private_key).unwrap();
    let be = |bytes: &[u8]| {
        let mut out = [0u8; 256];
        out[256 - bytes.len()..].copy_from_slice(bytes);
        out
    };
    libcrux_rsa::PrivateKey::<256>::from_components(
        be(&key.n_bytes()),
        be(&key.d().to_be_bytes_trimmed_vartime()),
    )
}

fn rsa2048_pkcs1_sha256_sign(c: &mut Criterion) {
    let private_key = include_bytes!("../../rind/src/high/rsa/rsa2048.der");
    let message =
        b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";

    let mut group = c.benchmark_group("rsa2048-pkcs1-sha256-sign");
    group.throughput(Throughput::Elements(1));

    group.bench_function("ring", |b| {
        use ring::{rand, rsa, signature};

        let key = rsa::KeyPair::from_der(private_key).unwrap();
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let mut signature = [0u8; 256];
            black_box(key.sign(&signature::RSA_PKCS1_SHA256, &rng, message, &mut signature))
                .unwrap();
        })
    });

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{rand, rsa, signature};

        let key = rsa::KeyPair::from_der(private_key).unwrap();
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let mut signature = [0u8; 256];
            black_box(key.sign(&signature::RSA_PKCS1_SHA256, &rng, message, &mut signature))
                .unwrap();
        })
    });

    group.bench_function("rustcrypto", |b| {
        use rsa::pkcs1::DecodeRsaPrivateKey;
        use rsa::signature::Signer;
        let key = rsa::pkcs1v15::SigningKey::<sha2::Sha256>::new(
            rsa::RsaPrivateKey::from_pkcs1_der(private_key).unwrap(),
        );

        b.iter(|| {
            black_box(key.sign(message));
        });
    });

    group.bench_function("rind", |b| {
        use rind::signature::{RsaKeyPair, sign};
        let key = RsaKeyPair::from_pkcs1(private_key).unwrap();

        b.iter(|| {
            black_box(key.sign(&sign::RSA_PKCS1_SHA256, message)).unwrap();
        })
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        let key = graviola::signing::rsa::SigningKey::from_pkcs1_der(private_key).unwrap();

        b.iter(|| {
            let mut signature = [0u8; 256];
            black_box(key.sign_pkcs1_sha256(&mut signature, message).unwrap());
        })
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        use openssl::hash::MessageDigest;
        use openssl::pkey::PKey;
        use openssl::rsa::Rsa;
        use openssl::sign::Signer;
        let key = PKey::from_rsa(Rsa::private_key_from_der(private_key).unwrap()).unwrap();

        b.iter(|| {
            let mut signer = Signer::new(MessageDigest::sha256(), &key).unwrap();
            black_box(signer.sign_oneshot_to_vec(message).unwrap());
        })
    });
}

fn rsa2048_pss_sha256_sign(c: &mut Criterion) {
    let private_key = include_bytes!("../../rind/src/high/rsa/rsa2048.der");
    let message =
        b"\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00\x00";

    let mut group = c.benchmark_group("rsa2048-pss-sha256-sign");
    group.throughput(Throughput::Elements(1));

    group.bench_function("ring", |b| {
        use ring::{rand, rsa, signature};

        let key = rsa::KeyPair::from_der(private_key).unwrap();
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let mut signature = [0u8; 256];
            black_box(key.sign(&signature::RSA_PSS_SHA256, &rng, message, &mut signature)).unwrap();
        })
    });

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{rand, rsa, signature};

        let key = rsa::KeyPair::from_der(private_key).unwrap();
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let mut signature = [0u8; 256];
            black_box(key.sign(&signature::RSA_PSS_SHA256, &rng, message, &mut signature)).unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::signature::{RsaKeyPair, sign};
        let key = RsaKeyPair::from_pkcs1(private_key).unwrap();

        b.iter(|| {
            black_box(key.sign(&sign::RSA_PSS_SHA256, message)).unwrap();
        })
    });

    group.bench_function("rustcrypto", |b| {
        use getrandom::{SysRng, rand_core::UnwrapErr};
        use rsa::pkcs1::DecodeRsaPrivateKey;
        use rsa::signature::RandomizedSigner;
        let key = rsa::pss::SigningKey::<sha2::Sha256>::new(
            rsa::RsaPrivateKey::from_pkcs1_der(private_key).unwrap(),
        );

        b.iter(|| {
            black_box(key.sign_with_rng(&mut UnwrapErr(SysRng), message));
        });
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        let key = graviola::signing::rsa::SigningKey::from_pkcs1_der(private_key).unwrap();

        b.iter(|| {
            let mut signature = [0u8; 256];
            black_box(key.sign_pss_sha256(&mut signature, message).unwrap());
        })
    });

    group.bench_function("libcrux", |b| {
        let key = libcrux_key(private_key);

        b.iter(|| {
            let mut salt = [0u8; 32];
            getrandom::fill(&mut salt).unwrap();
            let mut signature = [0u8; 256];
            libcrux_rsa::sign_2048(
                libcrux_rsa::DigestAlgorithm::Sha2_256,
                &key,
                message,
                &salt,
                &mut signature,
            )
            .unwrap();
            black_box(signature);
        })
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        use openssl::hash::MessageDigest;
        use openssl::pkey::PKey;
        use openssl::rsa::{Padding, Rsa};
        use openssl::sign::{RsaPssSaltlen, Signer};
        let key = PKey::from_rsa(Rsa::private_key_from_der(private_key).unwrap()).unwrap();

        b.iter(|| {
            let mut signer = Signer::new(MessageDigest::sha256(), &key).unwrap();
            signer.set_rsa_padding(Padding::PKCS1_PSS).unwrap();
            signer
                .set_rsa_pss_saltlen(RsaPssSaltlen::DIGEST_LENGTH)
                .unwrap();
            black_box(signer.sign_oneshot_to_vec(message).unwrap());
        })
    });
}

/// Signing at the other sizes, whose primes take a different Montgomery
/// multiplication from RSA-2048's on some CPUs: 2056 bits for primes of an
/// odd number of words, and 2560 for a multiple of four but not eight.
fn rsa_pkcs1_sha256_sign_sizes(c: &mut Criterion) {
    let keys: [(u32, &[u8]); 6] = [
        (
            2056,
            include_bytes!("../../rind/src/high/rsa/rsa2056.pkcs8.der"),
        ),
        (
            2560,
            include_bytes!("../../rind/src/high/rsa/rsa2560.pkcs8.der"),
        ),
        (
            3072,
            include_bytes!("../../rind/src/high/rsa/rsa3072.pkcs8.der"),
        ),
        (
            4096,
            include_bytes!("../../rind/src/high/rsa/rsa4096.pkcs8.der"),
        ),
        (
            6144,
            include_bytes!("../../rind/src/high/rsa/rsa6144.pkcs8.der"),
        ),
        (
            8192,
            include_bytes!("../../rind/src/high/rsa/rsa8192.pkcs8.der"),
        ),
    ];
    let message = b"hello";
    for (bits, private_key) in keys {
        let mut group = c.benchmark_group(format!("rsa{bits}-pkcs1-sha256-sign"));
        group.throughput(Throughput::Elements(1));

        // ring signs only with primes of a multiple of 512 bits, and
        // moduli of at most 4096.
        if matches!(bits, 3072 | 4096) {
            group.bench_function("ring", |b| {
                use ring::{rand, rsa, signature};
                let key = rsa::KeyPair::from_pkcs8(private_key).unwrap();
                let rng = rand::SystemRandom::new();
                let mut signature = vec![0u8; key.public().modulus_len()];
                b.iter(|| {
                    black_box(key.sign(
                        &signature::RSA_PKCS1_SHA256,
                        &rng,
                        message,
                        &mut signature,
                    ))
                    .unwrap();
                })
            });
        }
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_function("aws-lc-rs", |b| {
            use aws_lc_rs::{rand, rsa, signature};

            let key = rsa::KeyPair::from_pkcs8(private_key).unwrap();
            let rng = rand::SystemRandom::new();
            let mut signature = vec![0u8; key.public_modulus_len()];

            b.iter(|| {
                black_box(key.sign(&signature::RSA_PKCS1_SHA256, &rng, message, &mut signature))
                    .unwrap();
            })
        });

        group.bench_function("rind", |b| {
            use rind::signature::{RsaKeyPair, sign};
            let key = RsaKeyPair::from_pkcs8(private_key).unwrap();

            b.iter(|| {
                black_box(key.sign(&sign::RSA_PKCS1_SHA256, message)).unwrap();
            })
        });
    }
}

fn rsa2048_oaep_sha256_decrypt(c: &mut Criterion) {
    // Encrypted here, since OAEP ciphertexts are randomized.
    use rind::rsa::{DecryptingKey, OAEP_SHA256};
    let private_key = include_bytes!("../../rind/src/high/rsa/rsa2048.der");
    let message = [0u8; 32];
    let ciphertext = DecryptingKey::from_pkcs1(&OAEP_SHA256, private_key)
        .unwrap()
        .public_key()
        .encrypt(&message, b"")
        .unwrap();
    let ciphertext = ciphertext.as_ref();

    let mut group = c.benchmark_group("rsa2048-oaep-sha256-decrypt");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::rsa::{
            OAEP_SHA256_MGF1SHA256, OaepPrivateDecryptingKey, PrivateDecryptingKey,
        };
        let pkcs8 = DecryptingKey::from_pkcs1(&OAEP_SHA256, private_key)
            .unwrap()
            .to_pkcs8();
        let key = OaepPrivateDecryptingKey::new(
            PrivateDecryptingKey::from_pkcs8(pkcs8.as_ref()).unwrap(),
        )
        .unwrap();

        b.iter(|| {
            let mut plaintext = [0u8; 256];
            black_box(key.decrypt(&OAEP_SHA256_MGF1SHA256, ciphertext, &mut plaintext, None))
                .unwrap();
        })
    });

    group.bench_function("rustcrypto", |b| {
        use rsa::pkcs1::DecodeRsaPrivateKey;
        let key = rsa::RsaPrivateKey::from_pkcs1_der(private_key).unwrap();

        b.iter(|| {
            black_box(key.decrypt(rsa::Oaep::<sha2::Sha256>::new(), ciphertext)).unwrap();
        });
    });

    group.bench_function("rind", |b| {
        let key = DecryptingKey::from_pkcs1(&OAEP_SHA256, private_key).unwrap();

        b.iter(|| {
            black_box(key.decrypt(ciphertext, b"")).unwrap();
        })
    });
}

/// Loading a key checks its components agree, which should stay small next
/// to a signature at every size.
fn rsa_load(c: &mut Criterion) {
    let keys: [(u32, &[u8]); 2] = [
        (2048, include_bytes!("../../rind/src/high/rsa/rsa2048.der")),
        (8192, include_bytes!("../../rind/src/high/rsa/rsa8192.der")),
    ];
    for (bits, private_key) in keys {
        let mut group = c.benchmark_group(format!("rsa{bits}-load"));
        group.throughput(Throughput::Elements(1));

        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_function("aws-lc-rs", |b| {
            use aws_lc_rs::rsa;

            b.iter(|| black_box(rsa::KeyPair::from_der(black_box(private_key)).unwrap()))
        });

        group.bench_function("rind", |b| {
            use rind::signature::RsaKeyPair;

            b.iter(|| black_box(RsaKeyPair::from_pkcs1(black_box(private_key)).unwrap()))
        });

        group.bench_function("rind-sign", |b| {
            use rind::signature::{RsaKeyPair, sign};
            let key = RsaKeyPair::from_pkcs1(private_key).unwrap();
            b.iter(|| black_box(key.sign(&sign::RSA_PKCS1_SHA256, b"hello")).unwrap())
        });
    }
}

criterion_group!(
    benches,
    rsa2048_pkcs1_sha256_sign,
    rsa2048_pss_sha256_sign,
    rsa_pkcs1_sha256_sign_sizes,
    rsa2048_oaep_sha256_decrypt,
    rsa_load
);
criterion_main!(benches);
