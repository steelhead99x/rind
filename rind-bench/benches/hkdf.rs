mod criterion;
use std::hint::black_box;

use criterion::measurement::WallTime;
use criterion::{BenchmarkGroup, Criterion, criterion_group, criterion_main};

/// An aws-lc-rs path, or `()` on Xtensa, which aws-lc builds for no target
/// of: there its rows are left out, and its algorithms passed as `()`.
#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
macro_rules! aws {
    ($($path:tt)+) => { aws_lc_rs::$($path)+ };
}
#[cfg(any(target_arch = "xtensa", target_os = "none"))]
macro_rules! aws {
    ($($path:tt)+) => {
        ()
    };
}

struct Len(usize);

#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
impl aws_lc_rs::hkdf::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

impl ring::hkdf::KeyType for Len {
    fn len(&self) -> usize {
        self.0
    }
}

// A 32-byte key for one label, from a PRK extracted once: what a QUIC token
// or an e2ee track key derives from a long-lived secret.
fn bench(
    c: &mut Criterion,
    name: &str,
    ring: ring::hkdf::Algorithm,
    aws: aws!(hkdf::Algorithm),
    ours: &'static rind::hkdf::Algorithm,
    hash: Hash,
) {
    let mut group = c.benchmark_group(name);
    let secret = [0x5a; 32];
    let info: [&[u8]; 1] = [b"label"];

    // aws-lc-rs extracts lazily, inside each expansion, so extraction is
    // timed with one expansion after it.
    group.bench_function("extract-expand/ring", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            ring::hkdf::Salt::new(ring, b"salt")
                .extract(&secret)
                .expand(&info, Len(32))
                .unwrap()
                .fill(&mut out)
                .unwrap();
            black_box(out)
        })
    });
    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("extract-expand/aws-lc-rs", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            aws_lc_rs::hkdf::Salt::new(aws, b"salt")
                .extract(&secret)
                .expand(&info, Len(32))
                .unwrap()
                .fill(&mut out)
                .unwrap();
            black_box(out)
        })
    });
    for (lib, _dit) in criterion::rind_rows() {
        group.bench_function(format!("extract-expand/{lib}"), |b| {
            b.iter(|| {
                let mut out = [0u8; 32];
                rind::hkdf::Salt::new(ours, b"salt")
                    .extract(&secret)
                    .expand(&info, out.len())
                    .fill(&mut out)
                    .unwrap();
                black_box(out)
            })
        });
    }

    let prk = ring::hkdf::Salt::new(ring, b"salt").extract(&secret);
    group.bench_function("expand/ring", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            prk.expand(&info, Len(32)).unwrap().fill(&mut out).unwrap();
            black_box(out)
        })
    });

    group.bench_function("expand-aes-256-gcm-key/ring", |b| {
        b.iter(|| {
            black_box(ring::aead::UnboundKey::from(
                prk.expand(&info, &ring::aead::AES_256_GCM).unwrap(),
            ))
        })
    });

    // aws-lc-rs's `extract` defers extraction to each expansion, so its PRK
    // is computed here instead.
    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    let prk_bytes = aws_lc_rs::hmac::sign(
        &aws_lc_rs::hmac::Key::new(aws.hmac_algorithm(), b"salt"),
        &secret,
    );
    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    let prk = aws_lc_rs::hkdf::Prk::new_less_safe(aws, prk_bytes.as_ref());
    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("expand/aws-lc-rs", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            prk.expand(&info, Len(32)).unwrap().fill(&mut out).unwrap();
            black_box(out)
        })
    });
    #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
    group.bench_function("expand-aes-256-gcm-key/aws-lc-rs", |b| {
        b.iter(|| {
            black_box(aws_lc_rs::aead::UnboundKey::from(
                prk.expand(&info, &aws_lc_rs::aead::AES_256_GCM).unwrap(),
            ))
        })
    });

    let prk = rind::hkdf::Salt::new(ours, b"salt").extract(&secret);
    for (lib, _dit) in criterion::rind_rows() {
        group.bench_function(format!("expand/{lib}"), |b| {
            b.iter(|| {
                let mut out = [0u8; 32];
                prk.expand(&info, out.len()).fill(&mut out).unwrap();
                black_box(out)
            })
        });
    }
    group.bench_function("expand-aes-256-gcm-key/rind", |b| {
        b.iter(|| {
            black_box(rind::aead::Key::from(
                prk.expand(&info, &rind::aead::AES_256_GCM),
            ))
        })
    });

    match hash {
        Hash::Sha1 => rustcrypto::<hkdf::hmac::Hmac<sha1::Sha1>>(&mut group, &secret, info[0]),
        Hash::Sha256 => rustcrypto::<hkdf::hmac::Hmac<sha2::Sha256>>(&mut group, &secret, info[0]),
        Hash::Sha384 => rustcrypto::<hkdf::hmac::Hmac<sha2::Sha384>>(&mut group, &secret, info[0]),
        Hash::Sha512 => rustcrypto::<hkdf::hmac::Hmac<sha2::Sha512>>(&mut group, &secret, info[0]),
    }
    libcrux(&mut group, hash, &secret, info[0]);
    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    openssl(&mut group, hash, &secret, info[0]);
}

#[derive(Clone, Copy)]
enum Hash {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
}

fn rustcrypto<H: hkdf::HmacImpl>(
    group: &mut BenchmarkGroup<'_, WallTime>,
    secret: &[u8],
    info: &[u8],
) {
    group.bench_function("extract-expand/rustcrypto", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            hkdf::GenericHkdf::<H>::new(Some(b"salt"), secret)
                .expand(info, &mut out)
                .unwrap();
            black_box(out)
        })
    });
    let prk = hkdf::GenericHkdf::<H>::new(Some(b"salt"), secret);
    group.bench_function("expand/rustcrypto", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            prk.expand(info, &mut out).unwrap();
            black_box(out)
        })
    });
}

fn libcrux(group: &mut BenchmarkGroup<'_, WallTime>, hash: Hash, secret: &[u8], info: &[u8]) {
    use libcrux_hkdf::{Algorithm, expand, extract, hkdf};
    let (algorithm, prk_len) = match hash {
        Hash::Sha1 => return,
        Hash::Sha256 => (Algorithm::Sha256, 32),
        Hash::Sha384 => (Algorithm::Sha384, 48),
        Hash::Sha512 => (Algorithm::Sha512, 64),
    };
    group.bench_function("extract-expand/libcrux", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            hkdf(algorithm, &mut out, b"salt", secret, info).unwrap();
            black_box(out)
        })
    });
    let mut prk = [0u8; 64];
    let prk = &mut prk[..prk_len];
    extract(algorithm, prk, b"salt", secret).unwrap();
    group.bench_function("expand/libcrux", |b| {
        b.iter(|| {
            let mut out = [0u8; 32];
            expand(algorithm, &mut out, prk, info).unwrap();
            black_box(out)
        })
    });
}

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
fn openssl(group: &mut BenchmarkGroup<'_, WallTime>, hash: Hash, secret: &[u8], info: &[u8]) {
    use openssl::md::Md;
    use openssl::pkey::Id;
    use openssl::pkey_ctx::{HkdfMode, PkeyCtx};
    let md = match hash {
        Hash::Sha1 => Md::sha1(),
        Hash::Sha256 => Md::sha256(),
        Hash::Sha384 => Md::sha384(),
        Hash::Sha512 => Md::sha512(),
    };
    // Expands `key` as a PRK, or extracts from it with the salt first.
    let derive = |expand_only: bool, key: &[u8]| {
        let mut out = [0u8; 32];
        let mut ctx = PkeyCtx::new_id(Id::HKDF).unwrap();
        ctx.derive_init().unwrap();
        ctx.set_hkdf_md(md).unwrap();
        if expand_only {
            ctx.set_hkdf_mode(HkdfMode::EXPAND_ONLY).unwrap();
        } else {
            ctx.set_hkdf_salt(b"salt").unwrap();
        }
        ctx.set_hkdf_key(key).unwrap();
        ctx.add_hkdf_info(info).unwrap();
        ctx.derive(Some(&mut out)).unwrap();
        out
    };
    group.bench_function("extract-expand/openssl", |b| {
        b.iter(|| black_box(derive(false, secret)))
    });
    let prk = aws_lc_rs::hmac::sign(
        &aws_lc_rs::hmac::Key::new(
            match hash {
                Hash::Sha1 => aws_lc_rs::hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
                Hash::Sha256 => aws_lc_rs::hmac::HMAC_SHA256,
                Hash::Sha384 => aws_lc_rs::hmac::HMAC_SHA384,
                Hash::Sha512 => aws_lc_rs::hmac::HMAC_SHA512,
            },
            b"salt",
        ),
        secret,
    );
    group.bench_function("expand/openssl", |b| {
        b.iter(|| black_box(derive(true, prk.as_ref())))
    });
}

fn hkdf(c: &mut Criterion) {
    bench(
        c,
        "hkdf-sha1",
        ring::hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY,
        aws!(hkdf::HKDF_SHA1_FOR_LEGACY_USE_ONLY),
        &rind::hkdf::legacy::HKDF_SHA1,
        Hash::Sha1,
    );
    bench(
        c,
        "hkdf-sha256",
        ring::hkdf::HKDF_SHA256,
        aws!(hkdf::HKDF_SHA256),
        &rind::hkdf::HKDF_SHA256,
        Hash::Sha256,
    );
    bench(
        c,
        "hkdf-sha384",
        ring::hkdf::HKDF_SHA384,
        aws!(hkdf::HKDF_SHA384),
        &rind::hkdf::HKDF_SHA384,
        Hash::Sha384,
    );
    bench(
        c,
        "hkdf-sha512",
        ring::hkdf::HKDF_SHA512,
        aws!(hkdf::HKDF_SHA512),
        &rind::hkdf::HKDF_SHA512,
        Hash::Sha512,
    );
}

criterion_group!(benches, hkdf);
criterion_main!(benches);
