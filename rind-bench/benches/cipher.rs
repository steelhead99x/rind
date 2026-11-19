mod criterion;
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

fn bench_aes_ctr(c: &mut Criterion) {
    let iv = [0u8; 16];

    for (name, key_len) in [("aes128-ctr", 16), ("aes192-ctr", 24), ("aes256-ctr", 32)] {
        let key = &[0u8; 32][..key_len];
        let mut group = c.benchmark_group(name);
        for (size, size_name) in criterion::SIZES {
            // Encrypting the same buffer in place each iteration times the
            // cipher alone, without an allocation or a copy of the input.
            let mut buf = vec![0u8; size];
            group.throughput(Throughput::Bytes(size as u64));

            #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
            group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
                use aws_lc_rs::cipher::{
                    AES_128, AES_192, AES_256, EncryptingKey, EncryptionContext, UnboundCipherKey,
                };
                let algorithm = match key_len {
                    16 => &AES_128,
                    24 => &AES_192,
                    _ => &AES_256,
                };
                let key =
                    EncryptingKey::ctr(UnboundCipherKey::new(algorithm, key).unwrap()).unwrap();
                b.iter(|| {
                    key.less_safe_encrypt(&mut buf, EncryptionContext::Iv128(iv.into()))
                        .unwrap()
                });
            });
            group.bench_function(BenchmarkId::new("rind", size_name), |b| {
                let key = rind::cipher::AesCtr::new(rind_aes(key_len), key, 128).unwrap();
                b.iter(|| key.apply_keystream(&iv, &mut buf).unwrap());
            });
            // verified-garbage takes the IV only with the key, so each
            // message expands the key again.
            group.bench_function(BenchmarkId::new("verified-garbage", size_name), |b| {
                use verified_garbage::cipher::aes::AesCtr;
                let mut expect = vec![0u8; size];
                rind::cipher::AesCtr::new(rind_aes(key_len), key, 128)
                    .unwrap()
                    .apply_keystream(&iv, &mut expect)
                    .unwrap();
                let mut ct = vec![0u8; size];
                AesCtr::new(key, &iv)
                    .unwrap()
                    .apply_keystream_final(&mut ct);
                assert_eq!(ct, expect);
                b.iter(|| {
                    AesCtr::new(key, &iv)
                        .unwrap()
                        .apply_keystream_final(&mut buf)
                });
            });
        }
    }
}

// AES-CBC with PKCS#7 padding, as WebCrypto runs it. Each iteration copies
// the input into a buffer of kept capacity, since both directions work in
// place and decryption consumes its ciphertext; the copy is the same for
// both libraries.
fn bench_aes_cbc(c: &mut Criterion) {
    let iv = [0u8; 16];

    for (name, key_len) in [("aes128-cbc", 16), ("aes192-cbc", 24), ("aes256-cbc", 32)] {
        let key = &[0u8; 32][..key_len];
        for op in ["encrypt", "decrypt"] {
            let mut group = c.benchmark_group(format!("{name}-{op}"));
            for (size, size_name) in criterion::SIZES {
                use rind::cipher::{AesCbcDecryptingKey, AesCbcEncryptingKey, CbcIv};
                let algorithm = rind_aes(key_len);
                let mut ct = vec![0u8; size];
                AesCbcEncryptingKey::new(algorithm, key)
                    .unwrap()
                    .encrypt(CbcIv::assume_unpredictable(iv), &mut ct)
                    .unwrap();
                let input = if op == "encrypt" { vec![0u8; size] } else { ct };
                let mut buf = Vec::with_capacity(size + 16);
                group.throughput(Throughput::Bytes(size as u64));

                #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
                group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
                    use aws_lc_rs::cipher::{
                        AES_128, AES_192, AES_256, DecryptionContext, EncryptionContext,
                        PaddedBlockDecryptingKey, PaddedBlockEncryptingKey, UnboundCipherKey,
                    };
                    let algorithm = match key_len {
                        16 => &AES_128,
                        24 => &AES_192,
                        _ => &AES_256,
                    };
                    let key = || UnboundCipherKey::new(algorithm, key).unwrap();
                    let enc = PaddedBlockEncryptingKey::cbc_pkcs7(key()).unwrap();
                    let dec = PaddedBlockDecryptingKey::cbc_pkcs7(key()).unwrap();
                    b.iter(|| {
                        buf.clear();
                        buf.extend_from_slice(&input);
                        if op == "encrypt" {
                            enc.less_safe_encrypt(&mut buf, EncryptionContext::Iv128(iv.into()))
                                .unwrap();
                        } else {
                            dec.decrypt(&mut buf, DecryptionContext::Iv128(iv.into()))
                                .unwrap();
                        }
                    });
                });
                group.bench_function(BenchmarkId::new("rind", size_name), |b| {
                    let enc = AesCbcEncryptingKey::new(algorithm, key).unwrap();
                    let dec = AesCbcDecryptingKey::new(algorithm, key).unwrap();
                    b.iter(|| {
                        buf.clear();
                        buf.extend_from_slice(&input);
                        if op == "encrypt" {
                            enc.encrypt(CbcIv::assume_unpredictable(iv), &mut buf)
                                .unwrap();
                        } else {
                            dec.decrypt(&iv, &mut buf).unwrap();
                        }
                    });
                });
                // verified-garbage has no padding, so its row pads and unpads
                // here, and takes the IV only with the key, so each message
                // expands the key again.
                group.bench_function(BenchmarkId::new("verified-garbage", size_name), |b| {
                    use verified_garbage::cipher::aes::{AesCbcDecryptor, AesCbcEncryptor};
                    let run = |buf: &mut Vec<u8>| {
                        buf.clear();
                        buf.extend_from_slice(&input);
                        if op == "encrypt" {
                            let pad = 16 - size % 16;
                            buf.resize(size + pad, pad as u8);
                            AesCbcEncryptor::new(key, &iv)
                                .unwrap()
                                .encrypt(buf)
                                .unwrap();
                        } else {
                            AesCbcDecryptor::new(key, &iv)
                                .unwrap()
                                .decrypt(buf)
                                .unwrap();
                            // Every padding byte, without branching on them, as
                            // rind checks it.
                            let last = &buf[buf.len() - 16..];
                            let pad = last[15];
                            let mut bad = u8::from(pad == 0) | u8::from(pad > 16);
                            for (i, &byte) in last.iter().enumerate() {
                                bad |= u8::from(15 - i < usize::from(pad)) & u8::from(byte != pad);
                            }
                            assert_eq!(bad, 0);
                            buf.truncate(buf.len() - usize::from(pad));
                        }
                    };
                    let mut expect = input.clone();
                    if op == "encrypt" {
                        AesCbcEncryptingKey::new(algorithm, key)
                            .unwrap()
                            .encrypt(CbcIv::assume_unpredictable(iv), &mut expect)
                            .unwrap();
                    } else {
                        let len = AesCbcDecryptingKey::new(algorithm, key)
                            .unwrap()
                            .decrypt(&iv, &mut expect)
                            .unwrap()
                            .len();
                        expect.truncate(len);
                    }
                    run(&mut buf);
                    assert_eq!(buf, expect);
                    b.iter(|| run(&mut buf));
                });
            }
        }
    }
}

// The bare ChaCha20 stream cipher, a fresh nonce per message. aws-lc-rs and
// ring expose no ChaCha20 without Poly1305.
fn bench_chacha20(c: &mut Criterion) {
    let key = [7u8; 32];
    let nonce = [9u8; 12];
    let mut counter_nonce = [0u8; 16];
    counter_nonce[4..].copy_from_slice(&nonce);
    let mut group = c.benchmark_group("chacha20");
    for (size, size_name) in criterion::SIZES {
        let mut buf = vec![0u8; size];
        group.throughput(Throughput::Bytes(size as u64));

        group.bench_function(BenchmarkId::new("rind", size_name), |b| {
            let key = rind::cipher::ChaCha20::new(&key);
            b.iter(|| key.apply_keystream(&nonce, 0, &mut buf).unwrap());
        });
        group.bench_function(BenchmarkId::new("verified-garbage", size_name), |b| {
            use verified_garbage::cipher::chacha20::ChaCha20;
            let mut expect = vec![0u8; size];
            rind::cipher::ChaCha20::new(&key)
                .apply_keystream(&nonce, 0, &mut expect)
                .unwrap();
            let mut cipher = ChaCha20::new(&key, &counter_nonce);
            let mut ct = vec![0u8; size];
            cipher.apply_keystream(&mut ct);
            assert_eq!(ct, expect);
            // Restarting the keystream for the nonce is VG's per-message
            // cost, as rind's call starts from the key and nonce.
            b.iter(|| {
                cipher.reset_nonce(&counter_nonce);
                cipher.apply_keystream(&mut buf);
            });
        });
    }
}

// The QUIC header protection mask: one cipher call on a 16-byte sample.
fn bench_header_protection(c: &mut Criterion) {
    let sample = [0x5au8; 16];
    let mut group = c.benchmark_group("quic-header-protection");

    for (name, key_len) in [("aes128", 16), ("aes256", 32), ("chacha20", 32)] {
        let key = &[0u8; 32][..key_len];
        group.bench_function(format!("{name}/ring"), |b| {
            use ring::aead::quic::{AES_128, AES_256, CHACHA20, HeaderProtectionKey};
            let algorithm = match name {
                "aes128" => &AES_128,
                "aes256" => &AES_256,
                _ => &CHACHA20,
            };
            let key = HeaderProtectionKey::new(algorithm, key).unwrap();
            b.iter(|| key.new_mask(&sample).unwrap());
        });
        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_function(format!("{name}/aws-lc-rs"), |b| {
            use aws_lc_rs::aead::quic::{AES_128, AES_256, CHACHA20, HeaderProtectionKey};
            let algorithm = match name {
                "aes128" => &AES_128,
                "aes256" => &AES_256,
                _ => &CHACHA20,
            };
            let key = HeaderProtectionKey::new(algorithm, key).unwrap();
            b.iter(|| key.new_mask(&sample).unwrap());
        });
        for (lib, _dit) in criterion::rind_rows() {
            group.bench_function(format!("{name}/{lib}"), |b| {
                use rind::aead::quic::{AES_128, AES_256, CHACHA20, HeaderProtectionKey};
                let algorithm = match name {
                    "aes128" => &AES_128,
                    "aes256" => &AES_256,
                    _ => &CHACHA20,
                };
                let key = HeaderProtectionKey::new(algorithm, key).unwrap();
                b.iter(|| key.mask(&sample));
            });
        }
        group.bench_function(format!("{name}/verified-garbage"), |b| {
            use rind::aead::quic::{AES_128, AES_256, CHACHA20, HeaderProtectionKey};
            use verified_garbage::cipher::aes::AesEcb;
            use verified_garbage::cipher::chacha20::ChaCha20;
            let algorithm = match name {
                "aes128" => &AES_128,
                "aes256" => &AES_256,
                _ => &CHACHA20,
            };
            let expect = HeaderProtectionKey::new(algorithm, key)
                .unwrap()
                .mask(&sample);
            // As rustls does, the AES key is expanded once; ChaCha20 takes the
            // sample as its counter and nonce, so each mask starts a cipher.
            let aes = (name != "chacha20").then(|| AesEcb::new(key).unwrap());
            let mut chacha = [0u8; 32];
            chacha[..key_len].copy_from_slice(key);
            let mask = || {
                let mut mask = [0u8; 5];
                match &aes {
                    Some(aes) => {
                        let mut block = sample;
                        aes.encrypt(&mut block).unwrap();
                        mask.copy_from_slice(&block[..5]);
                    }
                    None => ChaCha20::new(&chacha, &sample).apply_keystream(&mut mask),
                }
                mask
            };
            assert_eq!(mask(), expect);
            b.iter(mask);
        });
    }
}

fn rind_aes(key_len: usize) -> &'static rind::cipher::Algorithm {
    match key_len {
        16 => &rind::cipher::AES_128,
        24 => &rind::cipher::AES_192,
        _ => &rind::cipher::AES_256,
    }
}

criterion_group!(
    benches,
    bench_aes_ctr,
    bench_aes_cbc,
    bench_chacha20,
    bench_header_protection
);
criterion_main!(benches);
