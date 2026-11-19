mod criterion;
use criterion::{BenchmarkId, Criterion, Throughput, criterion_group, criterion_main};

/// aws-lc's XChaCha20-Poly1305, which aws-lc-rs does not expose.
#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
struct AwsXChaCha(*mut aws_lc_sys::EVP_AEAD_CTX);

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
impl AwsXChaCha {
    fn new(key: &[u8; 32]) -> Self {
        // SAFETY: the key pointer and length describe `key`, and aws-lc copies it.
        let ctx = unsafe {
            aws_lc_sys::EVP_AEAD_CTX_new(
                aws_lc_sys::EVP_aead_xchacha20_poly1305(),
                key.as_ptr(),
                key.len(),
                16,
            )
        };
        assert!(!ctx.is_null());
        Self(ctx)
    }

    fn seal(&self, aad: &[u8], buf: &mut [u8]) {
        let mut nonce = [0u8; 24];
        rind::rand::fill(&mut nonce).unwrap();
        let mut tag = [0u8; 16];
        let mut tag_len = 0;
        // SAFETY: each pointer and length describes a live buffer, and aws-lc
        // allows `out` to equal `in`.
        let ok = unsafe {
            aws_lc_sys::EVP_AEAD_CTX_seal_scatter(
                self.0,
                buf.as_mut_ptr(),
                tag.as_mut_ptr(),
                &mut tag_len,
                tag.len(),
                nonce.as_ptr(),
                nonce.len(),
                buf.as_ptr(),
                buf.len(),
                std::ptr::null(),
                0,
                aad.as_ptr(),
                aad.len(),
            )
        };
        assert_eq!(ok, 1);
    }
}

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
impl Drop for AwsXChaCha {
    fn drop(&mut self) {
        // SAFETY: `self.0` came from `EVP_AEAD_CTX_new` and is freed once.
        unsafe { aws_lc_sys::EVP_AEAD_CTX_free(self.0) }
    }
}

fn test_rc_chacha(key: &chacha20poly1305::XChaCha20Poly1305, aad: &[u8], buf: &mut [u8]) {
    use chacha20poly1305::AeadInOut;
    let mut nonce = [0u8; 24];
    rind::rand::fill(&mut nonce).unwrap();
    let nonce = &nonce;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

fn test_rind_chacha(
    key: &rind::aead::RandomizedNonceKey,
    aad: &[u8],
    buf: &mut Vec<u8>,
    len: usize,
) {
    // Drops the last iteration's tag; the capacity holds the next one.
    buf.truncate(len);
    let _nonce = key.seal_in_place_append_tag(aad, buf).unwrap();
}

fn bench_chacha20poly1305(c: &mut Criterion) {
    // Each seal draws a fresh random nonce, as a randomized-nonce key must.
    let key = [0u8; 32];

    let mut group = c.benchmark_group("xchacha20poly1305");
    for (size, size_name, aad) in criterion::aead_rows() {
        // Sealing the same buffer in place each iteration times the cipher
        // alone, without an allocation or a copy of the input. Its room for
        // rind's appended tag keeps sealing from reallocating.
        let mut buf = Vec::with_capacity(size + 16);
        buf.resize(size, 0u8);
        group.throughput(Throughput::Bytes(size as u64));

        #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
        group.bench_function(BenchmarkId::new("aws-lc-rs", size_name), |b| {
            let key = AwsXChaCha::new(&key);
            b.iter(|| key.seal(aad, &mut buf[..size]));
        });
        group.bench_function(BenchmarkId::new("rustcrypto", size_name), |b| {
            use chacha20poly1305::KeyInit;
            let key = chacha20poly1305::XChaCha20Poly1305::new_from_slice(&key).unwrap();
            b.iter(|| test_rc_chacha(&key, aad, &mut buf[..size]));
        });
        group.bench_function(BenchmarkId::new("rind", size_name), |b| {
            let key = rind::aead::RandomizedNonceKey::new(&key);
            b.iter(|| test_rind_chacha(&key, aad, &mut buf, size));
        });
        #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
        group.bench_function(BenchmarkId::new("graviola", size_name), |b| {
            let key = graviola::aead::XChaCha20Poly1305::new(key);
            let mut tag = [0u8; 16];
            b.iter(|| {
                let mut nonce = [0u8; 24];
                rind::rand::fill(&mut nonce).unwrap();
                key.encrypt(&nonce, aad, &mut buf[..size], &mut tag);
            });
        });
        // libcrux seals out of place, appending the tag.
        group.bench_function(BenchmarkId::new("libcrux", size_name), |b| {
            use libcrux_chacha20poly1305::xchacha20_poly1305::encrypt;
            let mut ct = vec![0u8; size + 16];
            b.iter(|| {
                let mut nonce = [0u8; 24];
                rind::rand::fill(&mut nonce).unwrap();
                encrypt(&key, &buf[..size], &mut ct, aad, &nonce).unwrap();
            });
        });
    }
}

criterion_group!(benches, bench_chacha20poly1305);
criterion_main!(benches);
