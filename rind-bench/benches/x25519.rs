mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

const PUBLIC_KEY: &[u8; 32] = b"\xe6\xdb\x68\x67\x58\x30\x30\xdb\x35\x94\xc1\xa4\x24\xb1\x5f\x7c\x72\x66\x24\xec\x26\xb3\x35\x3b\x10\xa9\x03\xa6\xd0\xab\x1c\x4c";

fn x25519(c: &mut Criterion) {
    let mut group = c.benchmark_group("x25519-ecdh");
    group.throughput(Throughput::Elements(1));

    #[cfg(all(feature = "__bench_openssl", target_family = "unix",))]
    group.bench_function("openssl", |b| {
        b.iter(|| {
            use openssl::derive::Deriver;
            use openssl::pkey::{Id, PKey};

            let priv_key = PKey::generate_x25519().unwrap();
            black_box(priv_key.raw_public_key().unwrap());

            let peer = PKey::public_key_from_raw_bytes(PUBLIC_KEY, Id::X25519).unwrap();
            let mut deriver = Deriver::new(&priv_key).unwrap();
            deriver.set_peer(&peer).unwrap();
            let mut secret = [0u8; 32];
            deriver.derive(&mut secret).unwrap();
            black_box(secret);
        });
    });

    group.bench_function("ring", |b| {
        use ring::{agreement, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let our_private_key =
                agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());

            let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::X25519, PUBLIC_KEY);

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
                agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
            black_box(our_private_key.compute_public_key().unwrap());

            let peer_public_key = agreement::UnparsedPublicKey::new(&agreement::X25519, PUBLIC_KEY);

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

    group.bench_function("dalek", |b| {
        b.iter(|| {
            let our_priv = x25519_dalek::EphemeralSecret::random();
            let our_pub: x25519_dalek::PublicKey = (&our_priv).into();
            black_box(our_pub);

            let their_pub = x25519_dalek::PublicKey::from(*PUBLIC_KEY);

            let shared_secret = our_priv.diffie_hellman(&their_pub);
            black_box(shared_secret.as_bytes());
        });
    });

    group.bench_function("rind", |b| {
        b.iter(|| {
            use rind::agreement::*;
            let our_private_key = PrivateKey::generate(&X25519).unwrap();
            let our_public_key = our_private_key.public_key();
            black_box(our_public_key);

            let secret = our_private_key.agree(PUBLIC_KEY).unwrap();
            black_box(secret);
        })
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::key_agreement::x25519::{PrivateKey, PublicKey};

        b.iter(|| {
            let our_private_key = PrivateKey::new_random().unwrap();
            black_box(our_private_key.public_key());

            let peer = PublicKey::from_array(PUBLIC_KEY);
            black_box(our_private_key.diffie_hellman(&peer).unwrap());
        })
    });

    group.bench_function("libcrux", |b| {
        use libcrux_ecdh::{X25519PublicKey, x25519_derive, x25519_key_gen};

        b.iter(|| {
            let (our_private_key, our_public_key) = x25519_key_gen(&mut getrandom::SysRng).unwrap();
            black_box(our_public_key);

            let peer = X25519PublicKey(*PUBLIC_KEY);
            black_box(x25519_derive(&peer, &our_private_key).unwrap());
        })
    });
}

// Generate a key and its public key: the fixed-base multiplication alone,
// where `x25519-ecdh` adds the variable-base one.
fn keygen(c: &mut Criterion) {
    let mut group = c.benchmark_group("x25519-keygen");
    group.throughput(Throughput::Elements(1));

    group.bench_function("ring", |b| {
        use ring::{agreement, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let key = agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
            black_box(key.compute_public_key().unwrap());
        })
    });

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, rand};
        let rng = rand::SystemRandom::new();

        b.iter(|| {
            let key = agreement::EphemeralPrivateKey::generate(&agreement::X25519, &rng).unwrap();
            black_box(key.compute_public_key().unwrap());
        })
    });

    group.bench_function("dalek", |b| {
        b.iter(|| {
            let key = x25519_dalek::EphemeralSecret::random();
            black_box(x25519_dalek::PublicKey::from(&key));
        });
    });

    group.bench_function("rind", |b| {
        b.iter(|| {
            use rind::agreement::*;
            let key = PrivateKey::generate(&X25519).unwrap();
            black_box(key.public_key());
        })
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        b.iter(|| {
            let key = graviola::key_agreement::x25519::PrivateKey::new_random().unwrap();
            black_box(key.public_key());
        })
    });

    group.bench_function("libcrux", |b| {
        b.iter(|| black_box(libcrux_ecdh::x25519_key_gen(&mut getrandom::SysRng).unwrap()));
    });

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    group.bench_function("openssl", |b| {
        b.iter(|| {
            let key = openssl::pkey::PKey::generate_x25519().unwrap();
            black_box(key.raw_public_key().unwrap());
        });
    });
}

// Agree with a stored key, loaded once, as WebCrypto's `deriveBits` and
// node's `ECDH` do: the variable-base multiplication alone.
fn stored(c: &mut Criterion) {
    let mut group = c.benchmark_group("x25519-ecdh-stored");
    group.throughput(Throughput::Elements(1));
    let public_key: &[u8] = PUBLIC_KEY;
    let scalar = [1u8; 32];

    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::{agreement, error};
        let key = agreement::PrivateKey::from_private_key(&agreement::X25519, &scalar).unwrap();

        b.iter(|| {
            let peer = agreement::UnparsedPublicKey::new(&agreement::X25519, public_key);
            agreement::agree(&key, peer, error::Unspecified, |key_material| {
                black_box(key_material);
                Ok(())
            })
            .unwrap();
        })
    });

    group.bench_function("rind", |b| {
        use rind::agreement::*;
        let key = PrivateKey::from_scalar(&X25519, &scalar).unwrap();

        b.iter(|| black_box(key.agree(public_key).unwrap()))
    });
}

criterion_group!(benches, x25519, keygen, stored);
criterion_main!(benches);
