mod criterion;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl_ec;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

// verified-garbage has no key generation: a random scalar, drawn again until
// it is in range, and its public key.
fn vg_generate() -> (
    verified_garbage::ec::PrivateKey<verified_garbage::ec::P521>,
    verified_garbage::ec::PublicKey<verified_garbage::ec::P521>,
) {
    loop {
        let mut d = [0u8; 66];
        getrandom::fill(&mut d).unwrap();
        // The order is just under 2^521: keep only the top byte's low bit.
        d[0] &= 1;
        let key = verified_garbage::ec::PrivateKey::from_bytes(&d);
        if let Ok(public_key) = key.public_key() {
            return (key, public_key);
        }
    }
}

// RFC6979 A.2.7's public key, and its SHA-512 signature over "sample".
const PUBLIC_KEY: &str = "0401894550d0785932e00eaa23b694f213f8c3121f86dc97a04e5a7167db4e5bcd371123d46e45db6b5d5370a7f20fb633155d38ffa16d2bd761dcac474b9a2f5023a400493101c962cd4d2fddf782285e64584139c2f91b47f87ff82354d6630f746a28a0db25741b5b34a828008b22acc23f924faafbd4d33f81ea66956dfeaa2bfdfcf5";
const MESSAGE: &[u8] = b"sample";
const SIGNATURE: &str = "00c328fafcbd79dd77850370c46325d987cb525569fb63c5d3bc53950e6d4c5f174e25a1ee9017b5d450606add152b534931d7d4e8455cc91f9b15bf05ec36e377fa00617cce7cf5064806c467f678d3b4080d6f1cc50af26ca209417308281b68af282623eaa63e5b5c0723d8b8c37ff0777b1a20f8ccb1dccc43997f1ee0e44da4a67a";

fn ecdh(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-ecdh");
    group.throughput(Throughput::Elements(1));
    let public_key = hex::decode(PUBLIC_KEY).unwrap();

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

    group.bench_function("verified-garbage", |b| {
        vg_agrees_with_rind();
        use verified_garbage::ec::PublicKey;
        let peer_bytes: [u8; 133] = public_key[..].try_into().unwrap();

        b.iter(|| {
            let (our_private_key, our_public_key) = vg_generate();
            black_box(our_public_key);

            let peer = PublicKey::from_bytes(&peer_bytes);
            black_box(our_private_key.exchange(&peer).unwrap());
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

    group.bench_function("verified-garbage", |b| {
        vg_agrees_with_rind();
        b.iter(|| black_box(vg_generate()));
    });
}

fn ecdsa_verify(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-ecdsa-verify");
    group.throughput(Throughput::Elements(1));
    let public_key = hex::decode(PUBLIC_KEY).unwrap();
    let signature = hex::decode(SIGNATURE).unwrap();

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

    // verified-garbage takes the key's bytes and validates it on every verify.
    group.bench_function("verified-garbage", |b| {
        use verified_garbage::hashes::sha512::Sha512;
        let public_key = verified_garbage::ec::PublicKey::<verified_garbage::ec::P521>::from_bytes(
            &public_key[..].try_into().unwrap(),
        );
        let signature: [u8; 132] = signature[..].try_into().unwrap();

        b.iter(|| {
            public_key.verify::<Sha512>(MESSAGE, &signature).unwrap();
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

    // verified-garbage validates the key on every verify, which rind's row parses once.
    group.bench_function("verified-garbage", |b| {
        use rind::digest;
        use verified_garbage::hashes::sha512::Sha512;
        let public_key = verified_garbage::ec::PublicKey::<verified_garbage::ec::P521>::from_bytes(
            &public_key[..].try_into().unwrap(),
        );
        let signature: [u8; 132] = signature[..].try_into().unwrap();
        let digest: [u8; 64] = digest::digest(&digest::SHA512, MESSAGE)
            .as_ref()
            .try_into()
            .unwrap();

        b.iter(|| {
            public_key
                .verify_prehashed::<Sha512>(&digest, &signature)
                .unwrap();
        })
    });
}

fn ecdsa_sign(c: &mut Criterion) {
    let mut group = c.benchmark_group("p521-ecdsa-sign");
    group.throughput(Throughput::Elements(1));

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

    // verified-garbage signs deterministically (RFC 6979), where rind hedges its nonce.
    group.bench_function("verified-garbage", |b| {
        use rind::signature::{PublicKey, verify};
        use verified_garbage::hashes::sha512::Sha512;
        let (signing_key, public_key) = vg_generate();
        // rind verifies verified-garbage's signature.
        let rind_key =
            PublicKey::new(&verify::ECDSA_P521_SHA512_FIXED, public_key.as_bytes()).unwrap();
        let signature = signing_key.sign::<Sha512>(MESSAGE).unwrap();
        rind_key.verify(MESSAGE, &signature).unwrap();

        b.iter(|| {
            black_box(signing_key.sign::<Sha512>(MESSAGE).unwrap());
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

    // verified-garbage signs deterministically (RFC 6979), where rind hedges its nonce.
    group.bench_function("verified-garbage", |b| {
        use rind::digest;
        use rind::signature::{PublicKey, verify};
        use verified_garbage::hashes::sha512::Sha512;
        let (signing_key, public_key) = vg_generate();
        // rind verifies verified-garbage's signature.
        let rind_key =
            PublicKey::new(&verify::ECDSA_P521_SHA512_FIXED, public_key.as_bytes()).unwrap();
        let signature = signing_key.sign::<Sha512>(MESSAGE).unwrap();
        rind_key.verify(MESSAGE, &signature).unwrap();
        let digest: [u8; 64] = digest::digest(&digest::SHA512, MESSAGE)
            .as_ref()
            .try_into()
            .unwrap();

        b.iter(|| {
            black_box(signing_key.sign_prehashed::<Sha512>(&digest).unwrap());
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

    group.bench_function("verified-garbage", |b| {
        use verified_garbage::ec::{PrivateKey, PublicKey};
        vg_agrees_with_rind();
        let key = PrivateKey::<verified_garbage::ec::P521>::from_bytes(&scalar);
        let peer_bytes: [u8; 133] = public_key[..].try_into().unwrap();

        b.iter(|| {
            let peer = PublicKey::from_bytes(&peer_bytes);
            black_box(key.exchange(&peer).unwrap())
        })
    });
}

// Checks verified-garbage's public key and exchange against rind's, from a
// fixed scalar, before any of its rows times them.
fn vg_agrees_with_rind() {
    use rind::agreement::{self, ECDH_P521};
    use verified_garbage::ec::{PrivateKey, PublicKey};
    let scalar = [1u8; 66];
    let public_key: &[u8] = &hex::decode(PUBLIC_KEY).unwrap();
    let key = PrivateKey::<verified_garbage::ec::P521>::from_bytes(&scalar);
    let peer_bytes: [u8; 133] = public_key.try_into().unwrap();
    let rind_key = agreement::PrivateKey::from_scalar(&ECDH_P521, &scalar).unwrap();
    assert_eq!(
        key.public_key().unwrap().as_bytes()[..],
        *rind_key.public_key().as_ref()
    );
    assert_eq!(
        key.exchange(&PublicKey::from_bytes(&peer_bytes)).unwrap()[..],
        *rind_key.agree(public_key).unwrap().as_ref()
    );
}

criterion_group!(benches, ecdh, keygen, ecdsa_verify, ecdsa_sign, stored);
criterion_main!(benches);
