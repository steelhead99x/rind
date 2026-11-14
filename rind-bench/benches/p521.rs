mod criterion;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl_ec;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

// RFC6979 A.2.7's public key, and its SHA-512 signature over "sample".
const PUBLIC_KEY: &str = "0401894550d0785932e00eaa23b694f213f8c3121f86dc97a04e5a7167db4e5bcd371123d46e45db6b5d5370a7f20fb633155d38ffa16d2bd761dcac474b9a2f5023a400493101c962cd4d2fddf782285e64584139c2f91b47f87ff82354d6630f746a28a0db25741b5b34a828008b22acc23f924faafbd4d33f81ea66956dfeaa2bfdfcf5";
const MESSAGE: &[u8] = b"sample";
const SIGNATURE: &str = "00c328fafcbd79dd77850370c46325d987cb525569fb63c5d3bc53950e6d4c5f174e25a1ee9017b5d450606add152b534931d7d4e8455cc91f9b15bf05ec36e377fa00617cce7cf5064806c467f678d3b4080d6f1cc50af26ca209417308281b68af282623eaa63e5b5c0723d8b8c37ff0777b1a20f8ccb1dccc43997f1ee0e44da4a67a";

fn ecdh(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-ecdh");
    group.throughput(Throughput::Elements(1));
    let public_key = hex::decode(PUBLIC_KEY).unwrap();

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, error, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let our_private_key =
                agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P521, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());

            let peer_public_key =
                agreement::UnparsedPublicKey::new(&agreement::ECDH_P521, &public_key);

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

    group.bench_function("rind", |b| {
        b.iter(|| {
            use rind::agreement::*;
            let our_private_key = PrivateKey::generate(&ECDH_P521).unwrap();
            let our_public_key = our_private_key.public_key();
            black_box(our_public_key);

            let secret = our_private_key.agree(&public_key).unwrap();
            black_box(secret);
        })
    });

    group.bench_function("rustcrypto", |b| {
        use p521::PublicKey;
        use p521::ecdh::EphemeralSecret;
        use p521::elliptic_curve::Generate;

        b.iter(|| {
            let our_private_key = EphemeralSecret::generate();
            black_box(our_private_key.public_key());

            let peer = PublicKey::from_sec1_bytes(&public_key).unwrap();
            black_box(our_private_key.diffie_hellman(&peer));
        });
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        let mut curve = ossl_ec::Curve::new(
            openssl::nid::Nid::SECP521R1,
            openssl::hash::MessageDigest::sha512(),
        );
        b.iter(|| curve.ecdh(&public_key));
    });
}

fn keygen(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-keygen");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let our_private_key =
                agreement::EphemeralPrivateKey::generate(&agreement::ECDH_P521, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());
        })
    });

    group.bench_function("rind", |b| {
        b.iter(|| {
            use rind::agreement::*;
            let our_private_key = PrivateKey::generate(&ECDH_P521).unwrap();
            black_box(our_private_key.public_key());
        })
    });
}

fn ecdsa_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-ecdsa-verify");
    group.throughput(Throughput::Elements(1));
    let public_key = hex::decode(PUBLIC_KEY).unwrap();
    let signature = hex::decode(SIGNATURE).unwrap();

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        let public_key = aws_lc_rs::signature::UnparsedPublicKey::new(
            &aws_lc_rs::signature::ECDSA_P521_SHA512_FIXED,
            &public_key,
        );

        b.iter(|| {
            public_key.verify(MESSAGE, &signature).unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::signature::{PublicKey, verify};

        b.iter(|| {
            PublicKey::new(&verify::ECDSA_P521_SHA512_FIXED, &public_key)
                .unwrap()
                .verify(MESSAGE, &signature)
                .unwrap();
        })
    });

    group.bench_function("rustcrypto", |b| {
        use p521::ecdsa::{Signature, VerifyingKey, signature::Verifier};

        b.iter(|| {
            VerifyingKey::from_sec1_bytes(&public_key)
                .unwrap()
                .verify(MESSAGE, &Signature::from_slice(&signature).unwrap())
                .unwrap();
        });
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        let mut curve = ossl_ec::Curve::new(
            openssl::nid::Nid::SECP521R1,
            openssl::hash::MessageDigest::sha512(),
        );
        let signature = ossl_ec::Curve::der(&signature);
        b.iter(|| curve.verify(&public_key, MESSAGE, &signature));
    });
    group.finish();

    // A key parsed once, as a JWT verifier holds it, keeps its multiplication table.
    let mut group = c.benchmark_group("p521-ecdsa-verify-parsed");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::signature;
        let public_key =
            signature::ParsedPublicKey::new(&signature::ECDSA_P521_SHA512_FIXED, &public_key)
                .unwrap();

        b.iter(|| {
            public_key.verify_sig(MESSAGE, &signature).unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::signature::{PublicKey, verify};
        let public_key = PublicKey::new(&verify::ECDSA_P521_SHA512_FIXED, &public_key).unwrap();

        b.iter(|| {
            public_key.verify(MESSAGE, &signature).unwrap();
        })
    });
    group.finish();

    // A digest the caller computed, as node's `createVerify` holds it.
    let mut group = c.benchmark_group("p521-ecdsa-verify-digest");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{digest, signature};
        let public_key =
            signature::ParsedPublicKey::new(&signature::ECDSA_P521_SHA512_FIXED, &public_key)
                .unwrap();
        let digest = digest::digest(&digest::SHA512, MESSAGE);

        b.iter(|| {
            public_key.verify_digest_sig(&digest, &signature).unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::digest;
        use rind::signature::{PublicKey, verify};
        let public_key = PublicKey::new(&verify::ECDSA_P521_SHA512_FIXED, &public_key).unwrap();
        let digest = digest::digest(&digest::SHA512, MESSAGE);

        b.iter(|| {
            public_key.verify_digest(&digest, &signature).unwrap();
        })
    });
}

fn ecdsa_sign(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-ecdsa-sign");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{rand, signature};
        let rng = rand::SystemRandom::new();

        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P521_SHA512_FIXED_SIGNING,
            &rng,
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P521_SHA512_FIXED_SIGNING,
            private_key.as_ref(),
        )
        .unwrap();

        b.iter(|| {
            black_box(private_key.sign(&rng, MESSAGE).unwrap());
        })
    });

    group.bench_function("rind", |b| {
        use rind::signature::{EcdsaKeyPair, sign};
        let signing_key = EcdsaKeyPair::generate(&sign::ECDSA_P521_SHA512_FIXED).unwrap();

        b.iter(|| {
            black_box(signing_key.sign(MESSAGE).unwrap());
        });
    });

    group.bench_function("rustcrypto", |b| {
        use p521::ecdsa::{Signature, SigningKey, signature::Signer};
        use p521::elliptic_curve::Generate;
        let signing_key = SigningKey::generate();

        b.iter(|| {
            let signature: Signature = signing_key.sign(MESSAGE);
            black_box(signature);
        });
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        let curve = ossl_ec::Curve::new(
            openssl::nid::Nid::SECP521R1,
            openssl::hash::MessageDigest::sha512(),
        );
        let signing_key = curve.generate();
        b.iter(|| black_box(curve.sign(&signing_key, MESSAGE)));
    });
    group.finish();

    // A digest the caller computed, as node's `createSign` holds it.
    let mut group = c.benchmark_group("p521-ecdsa-sign-digest");
    group.throughput(Throughput::Elements(1));

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{digest, rand, signature};
        let private_key = signature::EcdsaKeyPair::generate_pkcs8(
            &signature::ECDSA_P521_SHA512_FIXED_SIGNING,
            &rand::SystemRandom::new(),
        )
        .unwrap();
        let private_key = signature::EcdsaKeyPair::from_pkcs8(
            &signature::ECDSA_P521_SHA512_FIXED_SIGNING,
            private_key.as_ref(),
        )
        .unwrap();
        let digest = digest::digest(&digest::SHA512, MESSAGE);

        b.iter(|| {
            black_box(private_key.sign_digest(&digest).unwrap());
        })
    });

    group.bench_function("rind", |b| {
        use rind::digest;
        use rind::signature::{EcdsaKeyPair, sign};
        let signing_key = EcdsaKeyPair::generate(&sign::ECDSA_P521_SHA512_FIXED).unwrap();
        let digest = digest::digest(&digest::SHA512, MESSAGE);

        b.iter(|| {
            black_box(signing_key.sign_digest(&digest).unwrap());
        });
    });
}

// Agree with a stored key, loaded once, as WebCrypto's `deriveBits` and
// node's `ECDH` do: the variable-base multiplication alone.
fn stored(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-ecdh-stored");
    group.throughput(Throughput::Elements(1));
    let public_key: &[u8] = &hex::decode(PUBLIC_KEY).unwrap();
    let scalar = [1u8; 66];

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, error};
        let key = agreement::PrivateKey::from_private_key(&agreement::ECDH_P521, &scalar).unwrap();

        b.iter(|| {
            let peer = agreement::UnparsedPublicKey::new(&agreement::ECDH_P521, public_key);
            agreement::agree(&key, peer, error::Unspecified, |key_material| {
                black_box(key_material);
                Ok(())
            })
            .unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::agreement::*;
        let key = PrivateKey::from_scalar(&ECDH_P521, &scalar).unwrap();

        b.iter(|| black_box(key.agree(public_key).unwrap()))
    });
}

criterion_group!(benches, ecdh, keygen, ecdsa_verify, ecdsa_sign, stored);
criterion_main!(benches);
