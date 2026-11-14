mod criterion;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl_ec;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

const PUBLIC_KEY: &[u8; 65] = b"\x04\
\x62\xd5\xbd\x33\x72\xaf\x75\xfe\x85\xa0\x40\x71\x5d\x0f\x50\x24\x28\xe0\x70\x46\x86\x8b\x0b\xfd\xfa\x61\xd7\x31\xaf\xe4\x4f\x26\
\xac\x33\x3a\x93\xa9\xe7\x0a\x81\xcd\x5a\x95\xb5\xbf\x8d\x13\x99\x0e\xb7\x41\xc8\xc3\x88\x72\xb4\xa0\x7d\x27\x5a\x01\x4e\x30\xcf";

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
const P256_NID: openssl::nid::Nid = openssl::nid::Nid::X9_62_PRIME256V1;

fn ecdh(c: &mut Criterion) {
    let mut group = c.benchmark_group("p256-ecdh");
    group.throughput(Throughput::Elements(1));

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        let mut curve = ossl_ec::Curve::new(P256_NID, openssl::hash::MessageDigest::sha256());
        b.iter(|| curve.ecdh(PUBLIC_KEY));
    });

    group.bench_function("ring", |b| {
        use ring::{agreement, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let our_private_key =
                agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());

            let peer_public_key =
                agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, PUBLIC_KEY);

            agreement::agree_ephemeral(our_private_key, &peer_public_key, |key_material| {
                black_box(key_material);
            })
            .unwrap();
        })
    });

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, error, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let our_private_key =
                agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());

            let peer_public_key =
                agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, PUBLIC_KEY);

            agreement::agree_ephemeral(
                our_private_key,
                peer_public_key,
                error::Unspecified,
                |key_material| {
                    black_box(key_material);
                    Ok(())
                },
            )
            .unwrap();
        })
    });

    group.bench_function("p256-rustcrypto", |b| {
        use p256::PublicKey;
        use p256::ecdh::EphemeralSecret;
        use p256::elliptic_curve::Generate;

        b.iter(|| {
            let our_private_key = EphemeralSecret::generate();
            black_box(our_private_key.public_key());

            let peer = PublicKey::from_sec1_bytes(PUBLIC_KEY).unwrap();
            let secret = our_private_key.diffie_hellman(&peer);
            black_box(secret);
        });
    });

    group.bench_function("rind", |b| {
        b.iter(|| {
            use rind::agreement::*;
            let our_private_key = PrivateKey::generate(&ECDH_P256).unwrap();
            let our_public_key = our_private_key.public_key();
            black_box(our_public_key);

            let secret = our_private_key.agree(PUBLIC_KEY).unwrap();
            black_box(secret);
        })
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::key_agreement::p256::{PrivateKey, PublicKey};

        b.iter(|| {
            let our_private_key = PrivateKey::new_random().unwrap();
            black_box(our_private_key.public_key_uncompressed());

            let peer = PublicKey::from_x962_uncompressed(PUBLIC_KEY).unwrap();
            black_box(our_private_key.diffie_hellman(&peer).unwrap());
        })
    });

    group.bench_function("libcrux", |b| {
        use libcrux_ecdh::p256::uncompressed_to_coordinates;
        use libcrux_ecdh::{P256PublicKey, p256_derive, p256_key_gen};

        b.iter(|| {
            let (our_private_key, our_public_key) = p256_key_gen(&mut getrandom::SysRng).unwrap();
            black_box(our_public_key);

            let peer = P256PublicKey(uncompressed_to_coordinates(PUBLIC_KEY).unwrap());
            black_box(p256_derive(&peer, &our_private_key).unwrap());
        })
    });
}

fn keygen(c: &mut Criterion) {
    let mut group = c.benchmark_group("p256-keygen");
    group.throughput(Throughput::Elements(1));

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        use openssl::pkey::PKey;

        b.iter(|| {
            let priv_key = PKey::ec_gen("prime256v1").unwrap();
            black_box(priv_key.public_key_to_der().unwrap());
        });
    });

    group.bench_function("ring", |b| {
        use ring::{agreement, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let our_private_key =
                agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());
        })
    });

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let our_private_key =
                agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P256, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());
        })
    });

    group.bench_function("p256-rustcrypto", |b| {
        use p256::ecdh::EphemeralSecret;
        use p256::elliptic_curve::Generate;

        b.iter(|| {
            let our_private_key = EphemeralSecret::generate();
            black_box(our_private_key.public_key());
        });
    });

    group.bench_function("rind", |b| {
        b.iter(|| {
            use rind::agreement::*;
            let our_private_key = PrivateKey::generate(&ECDH_P256).unwrap();
            black_box(our_private_key.public_key());
        })
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        b.iter(|| {
            let key = graviola::key_agreement::p256::PrivateKey::new_random().unwrap();
            black_box(key.public_key_uncompressed());
        })
    });

    group.bench_function("libcrux", |b| {
        b.iter(|| black_box(libcrux_ecdh::p256_key_gen(&mut getrandom::SysRng).unwrap()));
    });
}

fn ecdsa_keygen(c: &mut Criterion) {
    let mut group = c.benchmark_group("p256-ecdsa-keygen");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::signature::{ECDSA_P256_SHA256_FIXED_SIGNING, EcdsaKeyPair, KeyPair};

        b.iter(|| {
            let key = EcdsaKeyPair::generate(&ECDSA_P256_SHA256_FIXED_SIGNING).unwrap();
            black_box(key.public_key().as_ref());
        })
    });

    group.bench_function("rind", |b| {
        use rind::signature::{EcdsaKeyPair, sign};

        b.iter(|| {
            let key = EcdsaKeyPair::generate(&sign::ECDSA_P256_SHA256_FIXED).unwrap();
            black_box(key.public_key().as_ref());
        })
    });
}

fn ecdsa_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("p256-ecdsa-verify");
    group.throughput(Throughput::Elements(1));

    let public_key = b"\x04\
\x29\x27\xb1\x05\x12\xba\xe3\xed\xdc\xfe\x46\x78\x28\x12\x8b\xad\x29\x03\x26\x99\x19\xf7\x08\x60\x69\xc8\xc4\xdf\x6c\x73\x28\x38\
\xc7\x78\x79\x64\xea\xac\x00\xe5\x92\x1f\xb1\x49\x8a\x60\xf4\x60\x67\x66\xb3\xd9\x68\x50\x01\x55\x8d\x1a\x97\x4e\x73\x41\x51\x3e";
    let message = b"\x31\x32\x33\x34\x30\x30";
    let signature = b"\x2b\xa3\xa8\xbe\x6b\x94\xd5\xec\x80\xa6\xd9\xd1\x19\x0a\x43\x6e\xff\xe5\x0d\x85\xa1\xee\xe8\x59\xb8\xcc\x6a\xf9\xbd\x5c\x2e\x18\x4c\xd6\x0b\x85\x5d\x44\x2f\x5b\x3c\x7b\x11\xeb\x6c\x4e\x0a\xe7\x52\x5f\xe7\x10\xfa\xb9\xaa\x7c\x77\xa6\x7f\x79\xe6\xfa\xdd\x76";

    group.bench_function("ring", |b| {
        let public_key = ring::signature::UnparsedPublicKey::new(
            &ring::signature::ECDSA_P256_SHA256_FIXED,
            public_key,
        );

        b.iter(|| {
            public_key.verify(message, signature).unwrap();
        })
    });

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        let public_key = aws_lc_rs::signature::UnparsedPublicKey::new(
            &aws_lc_rs::signature::ECDSA_P256_SHA256_FIXED,
            public_key,
        );

        b.iter(|| {
            public_key.verify(message, signature).unwrap();
        })
    });

    group.bench_function("rustcrypto", |b| {
        use p256::ecdsa::{Signature, VerifyingKey, signature::Verifier};
        let verifying_key = VerifyingKey::from_sec1_bytes(public_key).unwrap();

        b.iter(|| {
            verifying_key
                .verify(message, &Signature::from_slice(signature).unwrap())
                .unwrap();
        });
    });

    group.bench_function("rind", |b| {
        use rind::signature::{PublicKey, verify};

        b.iter(|| {
            PublicKey::new(&verify::ECDSA_P256_SHA256_FIXED, public_key)
                .unwrap()
                .verify(message, signature)
                .unwrap();
        })
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::hashing::Sha256;
        use graviola::signing::ecdsa::{P256, VerifyingKey};

        b.iter(|| {
            VerifyingKey::<P256>::from_x962_uncompressed(public_key)
                .unwrap()
                .verify::<Sha256>(&[message], signature)
                .unwrap();
        })
    });

    group.bench_function("libcrux", |b| {
        use libcrux_ecdsa::p256::{PublicKey, Signature, uncompressed_to_coordinates, verify};
        let signature = Signature::from_bytes(*signature);

        b.iter(|| {
            let public_key = PublicKey(uncompressed_to_coordinates(public_key).unwrap());
            verify(
                libcrux_sha2::Algorithm::Sha256,
                message,
                &signature,
                &public_key,
            )
            .unwrap();
        })
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        let mut curve = ossl_ec::Curve::new(P256_NID, openssl::hash::MessageDigest::sha256());
        let signature = ossl_ec::Curve::der(signature);
        b.iter(|| curve.verify(public_key, message, &signature));
    });
    group.finish();

    // A key parsed once, as a JWT verifier holds it, keeps its multiplication table.
    let mut group = c.benchmark_group("p256-ecdsa-verify-parsed");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::signature;
        let public_key =
            signature::ParsedPublicKey::new(&signature::ECDSA_P256_SHA256_FIXED, public_key)
                .unwrap();

        b.iter(|| {
            public_key.verify_sig(message, signature).unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::signature::{PublicKey, verify};
        let public_key = PublicKey::new(&verify::ECDSA_P256_SHA256_FIXED, public_key).unwrap();

        b.iter(|| {
            public_key.verify(message, signature).unwrap();
        })
    });
    group.finish();

    // A digest the caller computed, as node's `createVerify` holds it.
    let mut group = c.benchmark_group("p256-ecdsa-verify-digest");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{digest, signature};
        let public_key =
            signature::ParsedPublicKey::new(&signature::ECDSA_P256_SHA256_FIXED, public_key)
                .unwrap();
        let digest = digest::digest(&digest::SHA256, message);

        b.iter(|| {
            public_key.verify_digest_sig(&digest, signature).unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::digest;
        use rind::signature::{PublicKey, verify};
        let public_key = PublicKey::new(&verify::ECDSA_P256_SHA256_FIXED, public_key).unwrap();
        let digest = digest::digest(&digest::SHA256, message);

        b.iter(|| {
            public_key.verify_digest(&digest, signature).unwrap();
        })
    });
}

fn ecdsa_sign(c: &mut Criterion) {
    let mut group = c.benchmark_group("p256-ecdsa-sign");
    group.throughput(Throughput::Elements(1));
    let message = b"\x31\x32\x33\x34\x30\x30";

    group.bench_function("ring", |b| {
        use ring::{rand, signature};
        let rng = rand::SystemRandom::new();

        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            &rng,
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            private_key.as_ref(),
            &rng,
        )
        .unwrap();

        b.iter(|| {
            black_box(private_key.sign(&rng, message).unwrap());
        })
    });

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{rand, signature};
        let rng = rand::SystemRandom::new();

        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            &rng,
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            private_key.as_ref(),
        )
        .unwrap();

        b.iter(|| {
            black_box(private_key.sign(&rng, message).unwrap());
        })
    });

    group.bench_function("rustcrypto", |b| {
        use p256::ecdsa::{Signature, SigningKey, signature::Signer};
        use p256::elliptic_curve::Generate;
        let signing_key = SigningKey::generate();

        b.iter(|| {
            let _sig: Signature = signing_key.sign(message);
            black_box(_sig);
        });
    });

    group.bench_function("rind", |b| {
        use rind::signature::{EcdsaKeyPair, sign};
        let signing_key = EcdsaKeyPair::generate(&sign::ECDSA_P256_SHA256_FIXED).unwrap();

        b.iter(|| {
            black_box(signing_key.sign(message).unwrap());
        });
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::hashing::Sha256;
        use graviola::signing::ecdsa::{P256, SigningKey};
        let signing_key = SigningKey::<P256>::generate().unwrap();
        let mut signature = [0u8; 64];

        b.iter(|| {
            black_box(
                signing_key
                    .sign::<Sha256>(&[message], &mut signature)
                    .unwrap(),
            );
        });
    });

    group.bench_function("libcrux", |b| {
        use libcrux_ecdsa::p256::rand::{generate_key_pair, sign};
        let (signing_key, _) = generate_key_pair(&mut getrandom::SysRng).unwrap();

        b.iter(|| {
            black_box(
                sign(
                    libcrux_sha2::Algorithm::Sha256,
                    message,
                    &signing_key,
                    &mut getrandom::SysRng,
                )
                .unwrap(),
            );
        });
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        let curve = ossl_ec::Curve::new(P256_NID, openssl::hash::MessageDigest::sha256());
        let signing_key = curve.generate();
        b.iter(|| black_box(curve.sign(&signing_key, message)));
    });
    group.finish();

    // A digest the caller computed, as node's `createSign` holds it.
    let mut group = c.benchmark_group("p256-ecdsa-sign-digest");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{digest, rand, signature};
        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            &rand::SystemRandom::new(),
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            private_key.as_ref(),
        )
        .unwrap();
        let digest = digest::digest(&digest::SHA256, message);

        b.iter(|| {
            black_box(private_key.sign_digest(&digest).unwrap());
        })
    });

    group.bench_function("rind", |b| {
        use rind::digest;
        use rind::signature::{EcdsaKeyPair, sign};
        let signing_key = EcdsaKeyPair::generate(&sign::ECDSA_P256_SHA256_FIXED).unwrap();
        let digest = digest::digest(&digest::SHA256, message);

        b.iter(|| {
            black_box(signing_key.sign_digest(&digest).unwrap());
        });
    });
}

// Agree with a stored key, loaded once, as WebCrypto's `deriveBits` and
// node's `ECDH` do: the variable-base multiplication alone.
fn stored(c: &mut Criterion) {
    let mut group = c.benchmark_group("p256-ecdh-stored");
    group.throughput(Throughput::Elements(1));
    let public_key: &[u8] = PUBLIC_KEY;
    let scalar = [1u8; 32];

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, error};
        let key = agreement::PrivateKey::from_private_key(&agreement::ECDH_P256, &scalar).unwrap();

        b.iter(|| {
            let peer = agreement::UnparsedPublicKey::new(&agreement::ECDH_P256, public_key);
            agreement::agree(&key, peer, error::Unspecified, |key_material| {
                black_box(key_material);
                Ok(())
            })
            .unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::agreement::*;
        let key = PrivateKey::from_scalar(&ECDH_P256, &scalar).unwrap();

        b.iter(|| black_box(key.agree(public_key).unwrap()))
    });
}

criterion_group!(
    benches,
    ecdh,
    keygen,
    ecdsa_keygen,
    ecdsa_verify,
    ecdsa_sign,
    stored
);
criterion_main!(benches);
