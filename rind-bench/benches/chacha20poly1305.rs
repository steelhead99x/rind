mod criterion;
#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl_aead;
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

fn test_ring_chacha(key: &ring::aead::LessSafeKey, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    let _tag = key
        .seal_in_place_separate_tag(
            ring::aead::Nonce::assume_unique_for_key(*nonce),
            ring::aead::Aad::from(aad),
            buf,
        )
        .unwrap();
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
fn test_aws_chacha(
    key: &aws_lc_rs::aead::LessSafeKey,
    nonce: &[u8; 12],
    aad: &[u8],
    buf: &mut [u8],
) {
    let _tag = key
        .seal_in_place_separate_tag(nonce.into(), aws_lc_rs::aead::Aad::from(aad), buf)
        .unwrap();
}

fn test_rc_chacha(
    key: &chacha20poly1305::ChaCha20Poly1305,
    nonce: &[u8; 12],
    aad: &[u8],
    buf: &mut [u8],
) {
    use chacha20poly1305::AeadInOut;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

fn test_rind_chacha(key: &rind::aead::Key, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) {
    let _tag = key
        .seal_in_place_separate_tag(rind::aead::Nonce::assume_unique_for_key(*nonce), aad, buf)
        .unwrap();
}

fn bench_chacha20poly1305(c: &mut Criterion) {
    let key = [0u8; 32];
    let nonce = [0u8; 12];

    let mut group = c.benchmark_group("chacha20poly1305");
    for (size, size_name, aad) in criterion::aead_rows() {
        // Sealing the same buffer in place each iteration times the cipher
        // alone, without an allocation or a copy of the input.
        let mut buf = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_function(BenchmarkId::new("ring", size_name), |b| {
            use ring::aead::{CHACHA20_POLY1305, LessSafeKey, UnboundKey};
            let key = UnboundKey::new(&CHACHA20_POLY1305, &key).unwrap();
            let key = LessSafeKey::new(key);
            b.iter(|| test_ring_chacha(&key, &nonce, aad, &mut buf));
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            use aws_lc_rs::aead::{CHACHA20_POLY1305, LessSafeKey, UnboundKey};
            let key = UnboundKey::new(&CHACHA20_POLY1305, &key).unwrap();
            let key = LessSafeKey::new(key);
            b.iter(|| test_aws_chacha(&key, &nonce, aad, &mut buf));
        });
        group.bench_function(BenchmarkId::new("rustcrypto", size_name), |b| {
            use chacha20poly1305::KeyInit;
            let key = chacha20poly1305::ChaCha20Poly1305::new_from_slice(&key).unwrap();
            b.iter(|| test_rc_chacha(&key, &nonce, aad, &mut buf));
        });
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_function(BenchmarkId::new(lib, size_name), |b| {
                use rind::aead::{CHACHA20_POLY1305, Key};
                let key = Key::new(&CHACHA20_POLY1305, &key).unwrap();
                b.iter(|| test_rind_chacha(&key, &nonce, aad, &mut buf));
            });
        }
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new("graviola", size_name), |b| {
            let key = graviola::aead::ChaCha20Poly1305::new(key);
            let mut tag = [0u8; 16];
            b.iter(|| key.encrypt(&nonce, aad, &mut buf, &mut tag));
        });
        // libcrux seals out of place.
        group.bench_function(BenchmarkId::new("libcrux", size_name), |b| {
            let mut ct = vec![0u8; size];
            let mut tag = [0u8; 16];
            b.iter(|| {
                libcrux_chacha20poly1305::encrypt_detached(
                    &key, &buf, &mut ct, &mut tag, aad, &nonce,
                )
                .unwrap();
            });
        });
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_function(BenchmarkId::new("openssl", size_name), |b| {
            let cipher = openssl::cipher::Cipher::chacha20_poly1305();
            let mut key = ossl_aead::Sealer::new(cipher, &key);
            b.iter(|| key.seal(&nonce, aad, &mut buf));
        });
    }
}

// Decrypting and verifying each size's ciphertext, as a receiver pays.
fn bench_chacha20poly1305_open(c: &mut Criterion) {
    let key = [0u8; 32];
    let nonce = [0u8; 12];
    let rind_key = rind::aead::Key::new(&rind::aead::CHACHA20_POLY1305, &key).unwrap();

    let mut group = c.benchmark_group("chacha20poly1305-open");
    for (size, size_name, aad) in criterion::aead_rows() {
        // As in `aes_gcm`, the ciphertext is copied into a buffer a whole number
        // of 4 KiB pages after it, so the copies do not share a page offset.
        let stride = size.next_multiple_of(4096);
        let mut buf = vec![0u8; stride + size];
        let (ct, pt) = buf.split_at_mut(stride);
        let ct = &mut ct[..size];
        let tag = rind_key
            .seal_in_place_separate_tag(rind::aead::Nonce::assume_unique_for_key(nonce), aad, ct)
            .unwrap();
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_function(BenchmarkId::new("ring", size_name), |b| {
            use ring::aead::{CHACHA20_POLY1305, LessSafeKey, UnboundKey};
            let key = LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, &key).unwrap());
            let tag = ring::aead::Tag::try_from(tag.as_ref()).unwrap();
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.open_in_place_separate_tag(
                    ring::aead::Nonce::assume_unique_for_key(nonce),
                    ring::aead::Aad::from(aad),
                    tag,
                    pt,
                    0..,
                )
                .unwrap();
            });
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            use aws_lc_rs::aead::{CHACHA20_POLY1305, LessSafeKey, UnboundKey};
            let key = LessSafeKey::new(UnboundKey::new(&CHACHA20_POLY1305, &key).unwrap());
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.open_in_place_separate_tag(
                    aws_lc_rs::aead::Nonce::assume_unique_for_key(nonce),
                    aws_lc_rs::aead::Aad::from(aad),
                    tag.as_ref(),
                    pt,
                )
                .unwrap();
            });
        });
        group.bench_function(BenchmarkId::new("rustcrypto", size_name), |b| {
            use chacha20poly1305::{AeadInOut, KeyInit};
            let key = chacha20poly1305::ChaCha20Poly1305::new_from_slice(&key).unwrap();
            let tag = <&[u8; 16]>::try_from(tag.as_ref()).unwrap().into();
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.decrypt_inout_detached(&nonce.into(), aad, pt.into(), tag)
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
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new("graviola", size_name), |b| {
            let key = graviola::aead::ChaCha20Poly1305::new(key);
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.decrypt(&nonce, aad, pt, tag.as_ref()).unwrap();
            });
        });
        // libcrux opens out of place, so it needs no copy.
        group.bench_function(BenchmarkId::new("libcrux", size_name), |b| {
            let tag = tag.as_ref().try_into().unwrap();
            b.iter(|| {
                libcrux_chacha20poly1305::decrypt_detached(&key, pt, ct, tag, aad, &nonce).unwrap();
            });
        });
        #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
        group.bench_function(BenchmarkId::new("openssl", size_name), |b| {
            let cipher = openssl::cipher::Cipher::chacha20_poly1305();
            let mut key = ossl_aead::Opener::new(cipher, &key);
            b.iter(|| {
                pt.copy_from_slice(ct);
                key.open(&nonce, aad, tag.as_ref(), pt);
            });
        });
    }
}

criterion_group!(benches, bench_chacha20poly1305, bench_chacha20poly1305_open);
criterion_main!(benches);
