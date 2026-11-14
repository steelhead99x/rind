mod criterion;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl_aead;
use std::hint::black_box;

use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

fn test_ring_aes_gcm(key: &ring::aead::LessSafeKey, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    let _tag = key
        .seal_in_place_separate_tag(
            ring::aead::Nonce::assume_unique_for_key(*nonce),
            ring::aead::Aad::from(aad),
            buf,
        )
        .unwrap();
}

fn test_aws_aes_gcm(
    key: &aws_lc_rs::aead::LessSafeKey,
    nonce: &[u8; 12],
    aad: &[u8],
    buf: &mut [u8],
) {
    let _tag = key
        .seal_in_place_separate_tag(nonce.into(), aws_lc_rs::aead::Aad::from(aad), buf)
        .unwrap();
}

fn test_rc_aes128_gcm(key: &aes_gcm::Aes128Gcm, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    use aes_gcm::AeadInOut;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

fn test_rc_aes256_gcm(key: &aes_gcm::Aes256Gcm, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    use aes_gcm::AeadInOut;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

fn test_rind_aes_gcm(key: &rind::aead::Key, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    let _tag = key
        .seal_in_place_separate_tag(rind::aead::Nonce::assume_unique_for_key(*nonce), aad, buf)
        .unwrap();
}

// Expanding a key and its GHASH table, as each QUIC connection and derived
// track key pays. It drops each key in the loop, so their wiping is timed too.
fn key_setup(
    group: &mut criterion::BenchmarkGroup<'_, criterion::measurement::WallTime>,
    key: &[u8],
    ring: &'static ring::aead::Algorithm,
    aws: &'static aws_lc_rs::aead::Algorithm,
    ours: &'static rind::aead::Algorithm,
) {
    group.bench_function(BenchmarkId::new("ring", "key"), |b| {
        b.iter(|| ring::aead::UnboundKey::new(ring, black_box(key)).unwrap())
    });
    group.bench_function(BenchmarkId::new("aws-lc-rs", "key"), |b| {
        b.iter(|| aws_lc_rs::aead::UnboundKey::new(aws, black_box(key)).unwrap())
    });
    group.bench_function(BenchmarkId::new("rind", "key"), |b| {
        b.iter(|| rind::aead::Key::new(ours, black_box(key)).unwrap())
    });
}

/// The AEAD rows, then QUIC's ACK-sized packets under its 13 B short header.
fn rows() -> impl Iterator<Item = (usize, &'static str, &'static [u8])> {
    criterion::aead_rows().chain([
        (32, "quic-32B", &[0u8; 13][..]),
        (64, "quic-64B", &[0u8; 13][..]),
    ])
}

fn aes128_gcm(c: &mut Criterion) {
    let key = [0u8; 16];
    let nonce = [0u8; 12];

    let mut group = c.benchmark_group("aes128-gcm");
    key_setup(
        &mut group,
        &key,
        &ring::aead::AES_128_GCM,
        &aws_lc_rs::aead::AES_128_GCM,
        &rind::aead::AES_128_GCM,
    );

    for (size, size_name, aad) in rows() {
        // Sealing the same buffer in place each iteration times the cipher
        // alone, without an allocation or a copy of the input.
        let mut buf = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_function(BenchmarkId::new("ring", size_name), |b| {
            use ring::aead::{AES_128_GCM, LessSafeKey, UnboundKey};
            let key = UnboundKey::new(&AES_128_GCM, &key).unwrap();
            let key = LessSafeKey::new(key);
            b.iter(|| test_ring_aes_gcm(&key, &nonce, aad, &mut buf));
        });
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            use aws_lc_rs::aead::{AES_128_GCM, LessSafeKey, UnboundKey};
            let key = UnboundKey::new(&AES_128_GCM, &key).unwrap();
            let key = LessSafeKey::new(key);
            b.iter(|| test_aws_aes_gcm(&key, &nonce, aad, &mut buf));
        });
        group.bench_function(BenchmarkId::new("rustcrypto", size_name), |b| {
            use aes_gcm::KeyInit;
            let key = aes_gcm::Aes128Gcm::new_from_slice(&key).unwrap();
            b.iter(|| test_rc_aes128_gcm(&key, &nonce, aad, &mut buf));
        });
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_function(BenchmarkId::new(lib, size_name), |b| {
                use rind::aead::{AES_128_GCM, Key};
                let key = Key::new(&AES_128_GCM, &key).unwrap();
                b.iter(|| test_rind_aes_gcm(&key, &nonce, aad, &mut buf));
            });
        }
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new("graviola", size_name), |b| {
            let key = graviola::aead::AesGcm::new(&key);
            let mut tag = [0u8; 16];
            b.iter(|| key.encrypt(&nonce, aad, &mut buf, &mut tag));
        });
        // libcrux seals out of place.
        group.bench_function(BenchmarkId::new("libcrux", size_name), |b| {
            let key = libcrux_aes::AesGcm128Key::from(key);
            let nonce = libcrux_aes::AesGcm128Nonce::from(nonce);
            let mut tag = libcrux_aes::AesGcm128Tag::from([0u8; 16]);
            let mut ct = vec![0u8; size];
            b.iter(|| key.encrypt(&mut ct, &mut tag, &nonce, aad, &buf).unwrap());
        });
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_function(BenchmarkId::new("openssl", size_name), |b| {
            let mut key = ossl_aead::Sealer::new(openssl::cipher::Cipher::aes_128_gcm(), &key);
            b.iter(|| key.seal(&nonce, aad, &mut buf));
        });
    }
}

fn aes256_gcm(c: &mut Criterion) {
    let key = [0u8; 32];
    let nonce = [0u8; 12];

    let mut group = c.benchmark_group("aes256-gcm");
    key_setup(
        &mut group,
        &key,
        &ring::aead::AES_256_GCM,
        &aws_lc_rs::aead::AES_256_GCM,
        &rind::aead::AES_256_GCM,
    );

    for (size, size_name, aad) in rows() {
        // Sealing the same buffer in place each iteration times the cipher
        // alone, without an allocation or a copy of the input.
        let mut buf = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_function(BenchmarkId::new("ring", size_name), |b| {
            use ring::aead::{AES_256_GCM, LessSafeKey, UnboundKey};
            let key = UnboundKey::new(&AES_256_GCM, &key).unwrap();
            let key = LessSafeKey::new(key);
            b.iter(|| test_ring_aes_gcm(&key, &nonce, aad, &mut buf));
        });
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            use aws_lc_rs::aead::{AES_256_GCM, LessSafeKey, UnboundKey};
            let key = UnboundKey::new(&AES_256_GCM, &key).unwrap();
            let key = LessSafeKey::new(key);
            b.iter(|| test_aws_aes_gcm(&key, &nonce, aad, &mut buf));
        });
        group.bench_function(BenchmarkId::new("rustcrypto", size_name), |b| {
            use aes_gcm::KeyInit;
            let key = aes_gcm::Aes256Gcm::new_from_slice(&key).unwrap();
            b.iter(|| test_rc_aes256_gcm(&key, &nonce, aad, &mut buf));
        });
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_function(BenchmarkId::new(lib, size_name), |b| {
                use rind::aead::{AES_256_GCM, Key};
                let key = Key::new(&AES_256_GCM, &key).unwrap();
                b.iter(|| test_rind_aes_gcm(&key, &nonce, aad, &mut buf));
            });
        }
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new("graviola", size_name), |b| {
            let key = graviola::aead::AesGcm::new(&key);
            let mut tag = [0u8; 16];
            b.iter(|| key.encrypt(&nonce, aad, &mut buf, &mut tag));
        });
        // libcrux seals out of place.
        group.bench_function(BenchmarkId::new("libcrux", size_name), |b| {
            let key = libcrux_aes::AesGcm256Key::from(key);
            let nonce = libcrux_aes::AesGcm256Nonce::from(nonce);
            let mut tag = libcrux_aes::AesGcm256Tag::from([0u8; 16]);
            let mut ct = vec![0u8; size];
            b.iter(|| key.encrypt(&mut ct, &mut tag, &nonce, aad, &buf).unwrap());
        });
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_function(BenchmarkId::new("openssl", size_name), |b| {
            let mut key = ossl_aead::Sealer::new(openssl::cipher::Cipher::aes_256_gcm(), &key);
            b.iter(|| key.seal(&nonce, aad, &mut buf));
        });
    }
}

/// What opening needs that differs by key size.
trait KeySize {
    type RustCrypto: aes_gcm::KeyInit
        + aes_gcm::AeadInOut<
            NonceSize = aes_gcm::aead::consts::U12,
            TagSize = aes_gcm::aead::consts::U16,
        >;

    /// libcrux's open, out of place. Its key is the bare bytes, so building
    /// one in each call costs only the copy.
    fn libcrux(key: &[u8], nonce: &[u8; 12], aad: &[u8], ct: &[u8], tag: &[u8; 16], pt: &mut [u8]);

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl() -> &'static openssl::cipher::CipherRef;
}

struct Aes128;

impl KeySize for Aes128 {
    type RustCrypto = aes_gcm::Aes128Gcm;

    fn libcrux(key: &[u8], nonce: &[u8; 12], aad: &[u8], ct: &[u8], tag: &[u8; 16], pt: &mut [u8]) {
        let key = libcrux_aes::AesGcm128Key::from(<[u8; 16]>::try_from(key).unwrap());
        key.decrypt(pt, &(*nonce).into(), aad, ct, &(*tag).into())
            .unwrap()
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl() -> &'static openssl::cipher::CipherRef {
        openssl::cipher::Cipher::aes_128_gcm()
    }
}

struct Aes256;

impl KeySize for Aes256 {
    type RustCrypto = aes_gcm::Aes256Gcm;

    fn libcrux(key: &[u8], nonce: &[u8; 12], aad: &[u8], ct: &[u8], tag: &[u8; 16], pt: &mut [u8]) {
        let key = libcrux_aes::AesGcm256Key::from(<[u8; 32]>::try_from(key).unwrap());
        key.decrypt(pt, &(*nonce).into(), aad, ct, &(*tag).into())
            .unwrap()
    }

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    fn openssl() -> &'static openssl::cipher::CipherRef {
        openssl::cipher::Cipher::aes_256_gcm()
    }
}

// Decrypting and verifying each size's ciphertext, as a receiver pays.
fn open<K: KeySize>(
    c: &mut Criterion,
    name: &str,
    key: &[u8],
    ring: &'static ring::aead::Algorithm,
    aws: &'static aws_lc_rs::aead::Algorithm,
    ours: &'static rind::aead::Algorithm,
) {
    let nonce = [0u8; 12];
    let ring_key = ring::aead::LessSafeKey::new(ring::aead::UnboundKey::new(ring, key).unwrap());
    let aws_key =
        aws_lc_rs::aead::LessSafeKey::new(aws_lc_rs::aead::UnboundKey::new(aws, key).unwrap());
    let rind_key = rind::aead::Key::new(ours, key).unwrap();

    let mut group = c.benchmark_group(name);
    for (size, size_name, aad) in rows() {
        // Opening consumes its ciphertext, so each iteration first copies it
        // into a buffer a whole number of 4 KiB pages after it. Two separate
        // heap buffers can instead land with the destination just past the
        // source in a page, where Zen 3 and 4 run the `rep movsb` that
        // glibc's memcpy can pick for 16 KB about 30x slower.
        let stride = size.next_multiple_of(4096);
        let mut buf = vec![0u8; stride + size];
        let (ct, pt) = buf.split_at_mut(stride);
        let ct = &mut ct[..size];
        let tag = rind_key
            .seal_in_place_separate_tag(rind::aead::Nonce::assume_unique_for_key(nonce), aad, ct)
            .unwrap();
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_function(BenchmarkId::new("ring", size_name), |b| {
            let tag = ring::aead::Tag::try_from(tag.as_ref()).unwrap();
            b.iter(|| {
                pt.copy_from_slice(ct);
                ring_key
                    .open_in_place_separate_tag(
                        ring::aead::Nonce::assume_unique_for_key(nonce),
                        ring::aead::Aad::from(aad),
                        tag,
                        pt,
                        0..,
                    )
                    .unwrap();
            });
        });
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            b.iter(|| {
                pt.copy_from_slice(ct);
                aws_key
                    .open_in_place_separate_tag(
                        aws_lc_rs::aead::Nonce::assume_unique_for_key(nonce),
                        aws_lc_rs::aead::Aad::from(aad),
                        tag.as_ref(),
                        pt,
                    )
                    .unwrap();
            });
        });
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_function(BenchmarkId::new(lib, size_name), |b| {
                b.iter(|| {
                    pt.copy_from_slice(ct);
                    rind_key
                        .open_in_place_separate_tag(
                            rind::aead::Nonce::assume_unique_for_key(nonce),
                            aad,
                            tag,
                            pt,
                        )
                        .unwrap();
                });
            });
        }
        group.bench_function(BenchmarkId::new("rustcrypto", size_name), |b| {
            use aes_gcm::{AeadInOut, KeyInit};
            let key = K::RustCrypto::new_from_slice(key).unwrap();
            let tag = <&[u8; 16]>::try_from(tag.as_ref()).unwrap().into();
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.decrypt_inout_detached(&nonce.into(), aad, pt.into(), tag)
                    .unwrap();
            });
        });
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new("graviola", size_name), |b| {
            let key = graviola::aead::AesGcm::new(key);
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.decrypt(&nonce, aad, pt, tag.as_ref()).unwrap();
            });
        });
        // libcrux opens out of place, so it needs no copy.
        group.bench_function(BenchmarkId::new("libcrux", size_name), |b| {
            let tag = tag.as_ref().try_into().unwrap();
            b.iter(|| K::libcrux(key, &nonce, aad, ct, tag, pt));
        });
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_function(BenchmarkId::new("openssl", size_name), |b| {
            let mut key = ossl_aead::Opener::new(K::openssl(), key);
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.open(&nonce, aad, tag.as_ref(), pt);
            });
        });
    }
}

fn aes128_gcm_open(c: &mut Criterion) {
    open::<Aes128>(
        c,
        "aes128-gcm-open",
        &[0u8; 16],
        &ring::aead::AES_128_GCM,
        &aws_lc_rs::aead::AES_128_GCM,
        &rind::aead::AES_128_GCM,
    );
}

fn aes256_gcm_open(c: &mut Criterion) {
    open::<Aes256>(
        c,
        "aes256-gcm-open",
        &[0u8; 32],
        &ring::aead::AES_256_GCM,
        &aws_lc_rs::aead::AES_256_GCM,
        &rind::aead::AES_256_GCM,
    );
}

// AES-192-GCM, which only aws-lc-rs of the other libraries offers, both
// ways: WebCrypto and pyca take 192-bit keys.
fn aes192_gcm(c: &mut Criterion) {
    let key = [0u8; 24];
    let nonce = [0u8; 12];
    let aws_key = aws_lc_rs::aead::LessSafeKey::new(
        aws_lc_rs::aead::UnboundKey::new(&aws_lc_rs::aead::AES_192_GCM, &key).unwrap(),
    );
    let rind_key = rind::aead::Key::new(&rind::aead::AES_192_GCM, &key).unwrap();

    let mut group = c.benchmark_group("aes192-gcm");
    group.bench_function(BenchmarkId::new("aws-lc-rs", "key"), |b| {
        b.iter(|| {
            aws_lc_rs::aead::UnboundKey::new(&aws_lc_rs::aead::AES_192_GCM, black_box(&key))
                .unwrap()
        })
    });
    group.bench_function(BenchmarkId::new("rind", "key"), |b| {
        b.iter(|| rind::aead::Key::new(&rind::aead::AES_192_GCM, black_box(&key)).unwrap())
    });
    for (size, size_name, aad) in rows() {
        let mut buf = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            b.iter(|| test_aws_aes_gcm(&aws_key, &nonce, aad, &mut buf));
        });
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_function(BenchmarkId::new(lib, size_name), |b| {
                b.iter(|| test_rind_aes_gcm(&rind_key, &nonce, aad, &mut buf));
            });
        }
    }
    drop(group);

    let mut group = c.benchmark_group("aes192-gcm-open");
    for (size, size_name, aad) in rows() {
        // As in `open`, the ciphertext is copied into a buffer whole pages
        // after it.
        let stride = size.next_multiple_of(4096);
        let mut buf = vec![0u8; stride + size];
        let (ct, pt) = buf.split_at_mut(stride);
        let ct = &mut ct[..size];
        let tag = rind_key
            .seal_in_place_separate_tag(rind::aead::Nonce::assume_unique_for_key(nonce), aad, ct)
            .unwrap();
        group.throughput(Throughput::Bytes(size as u64));
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            b.iter(|| {
                pt.copy_from_slice(ct);
                aws_key
                    .open_in_place_separate_tag(
                        aws_lc_rs::aead::Nonce::assume_unique_for_key(nonce),
                        aws_lc_rs::aead::Aad::from(aad),
                        tag.as_ref(),
                        pt,
                    )
                    .unwrap();
            });
        });
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_function(BenchmarkId::new(lib, size_name), |b| {
                b.iter(|| {
                    pt.copy_from_slice(ct);
                    rind_key
                        .open_in_place_separate_tag(
                            rind::aead::Nonce::assume_unique_for_key(nonce),
                            aad,
                            tag,
                            pt,
                        )
                        .unwrap();
                });
            });
        }
    }
}

criterion_group!(
    benches,
    aes128_gcm,
    aes256_gcm,
    aes128_gcm_open,
    aes256_gcm_open,
    aes192_gcm
);
criterion_main!(benches);
