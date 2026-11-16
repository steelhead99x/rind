mod criterion;
use std::hint::black_box;

use criterion::{BatchSize, Criterion, Throughput, criterion_group, criterion_main};

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl {
    //! The openssl crate does not yet wrap ML-KEM keygen/encaps/decaps.

    use std::ptr;

    use foreign_types::ForeignType;
    use openssl::pkey::{HasPrivate, HasPublic, PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;

    pub const CIPHERTEXT_LEN: usize = 1088;
    pub const SECRET_LEN: usize = 32;

    /// ML-KEM requires OpenSSL 3.5 or later at runtime.
    pub fn available() -> bool {
        let ok = openssl::version::number() >= 0x3050_0000;
        if !ok {
            eprintln!(
                "skipping openssl ML-KEM benchmark: {} is too old",
                openssl::version::version()
            );
        }
        ok
    }

    pub fn keygen() -> PKey<Private> {
        unsafe {
            let ctx = openssl_sys::EVP_PKEY_CTX_new_from_name(
                ptr::null_mut(),
                c"ML-KEM-768".as_ptr(),
                ptr::null(),
            );
            assert!(!ctx.is_null());
            let mut ctx = PkeyCtx::<()>::from_ptr(ctx);
            ctx.keygen_init().unwrap();
            ctx.keygen().unwrap()
        }
    }

    pub fn encaps<T: HasPublic>(key: &PKey<T>) -> ([u8; CIPHERTEXT_LEN], [u8; SECRET_LEN]) {
        let ctx = PkeyCtx::new(key).unwrap();
        let mut ciphertext = [0u8; CIPHERTEXT_LEN];
        let mut secret = [0u8; SECRET_LEN];
        let mut ciphertext_len = ciphertext.len();
        let mut secret_len = secret.len();
        unsafe {
            assert_eq!(
                openssl_sys::EVP_PKEY_encapsulate_init(ctx.as_ptr(), ptr::null()),
                1
            );
            assert_eq!(
                openssl_sys::EVP_PKEY_encapsulate(
                    ctx.as_ptr(),
                    ciphertext.as_mut_ptr(),
                    &mut ciphertext_len,
                    secret.as_mut_ptr(),
                    &mut secret_len,
                ),
                1
            );
        }
        assert_eq!(ciphertext_len, CIPHERTEXT_LEN);
        assert_eq!(secret_len, SECRET_LEN);
        (ciphertext, secret)
    }

    pub fn decaps<T: HasPrivate>(key: &PKey<T>, ciphertext: &[u8]) -> [u8; SECRET_LEN] {
        let ctx = PkeyCtx::new(key).unwrap();
        let mut secret = [0u8; SECRET_LEN];
        let mut secret_len = secret.len();
        unsafe {
            assert_eq!(
                openssl_sys::EVP_PKEY_decapsulate_init(ctx.as_ptr(), ptr::null()),
                1
            );
            assert_eq!(
                openssl_sys::EVP_PKEY_decapsulate(
                    ctx.as_ptr(),
                    secret.as_mut_ptr(),
                    &mut secret_len,
                    ciphertext.as_ptr(),
                    ciphertext.len(),
                ),
                1
            );
        }
        assert_eq!(secret_len, SECRET_LEN);
        secret
    }
}

/// A verified-garbage ML-KEM-768 key, which it generates only from a seed:
/// drawn here, as the other libraries draw theirs.
fn vg_generate() -> verified_garbage::mlkem768::DecapsulationKey768 {
    let mut seed = [0u8; 64];
    getrandom::fill(&mut seed).unwrap();
    verified_garbage::mlkem768::DecapsulationKey768::from_seed(&seed).unwrap()
}

/// Checks that verified-garbage and rind each decapsulate the other's
/// ciphertexts to the secret it encapsulated.
fn vg_agrees_with_rind() {
    use rind::kem::*;
    use verified_garbage::mlkem768::EncapsulationKey768;

    let ours = DecapsulationKey::<MlKem768>::generate().unwrap();
    let theirs =
        EncapsulationKey768::from_bytes(ours.public_key().as_ref().try_into().unwrap()).unwrap();
    let (secret, ciphertext) = theirs.encapsulate().unwrap();
    let ciphertext = Ciphertext::new(&ciphertext).unwrap();
    assert_eq!(ours.decapsulate(&ciphertext).as_ref(), secret);

    let theirs = vg_generate();
    let ours = EncapsulationKey::<MlKem768>::new(theirs.encapsulation_key().as_bytes()).unwrap();
    let (ciphertext, secret) = ours.encapsulate().unwrap();
    assert_eq!(
        theirs
            .decapsulate(ciphertext.as_ref().try_into().unwrap())
            .unwrap(),
        secret.as_ref()
    );
}

// client first operation
fn mlkem768_keygen(c: &mut Criterion) {
    let mut group = c.benchmark_group("mlkem768-keygen");
    group.throughput(Throughput::Elements(1));

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    if ossl::available() {
        group.bench_function("openssl", |b| {
            b.iter(|| {
                let decaps = ossl::keygen();
                black_box(decaps.raw_public_key().unwrap())
            })
        });
    }

    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::kem;

        b.iter(|| {
            let decaps = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
            black_box(decaps.encapsulation_key().unwrap())
        })
    });

    group.bench_function("libcrux-ml-kem", |b| {
        use libcrux_ml_kem::mlkem768;

        b.iter(|| {
            let mut rand = [0u8; 64];
            getrandom::fill(&mut rand).unwrap();
            black_box(mlkem768::generate_key_pair(rand).into_parts());
        });
    });

    group.bench_function("rustcrypto", |b| {
        use ml_kem::{Kem, MlKem768};

        b.iter(|| {
            black_box(MlKem768::generate_keypair());
        });
    });

    group.bench_function("rind", |b| {
        use rind::kem::*;

        b.iter(|| {
            black_box(DecapsulationKey::<MlKem768>::generate().unwrap());
        });
    });

    group.bench_function("verified-garbage", |b| {
        vg_agrees_with_rind();
        b.iter(|| black_box(vg_generate()));
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::key_agreement::mlkem768::DecapKey;

        b.iter(|| {
            black_box(DecapKey::generate().unwrap());
        });
    });
}

// server operation
fn mlkem768_encaps(c: &mut Criterion) {
    let mut group = c.benchmark_group("mlkem768-encaps");
    group.throughput(Throughput::Elements(1));

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    if ossl::available() {
        group.bench_function("openssl", |b| {
            use openssl::pkey::{KeyType, PKey};

            let encaps_bytes = ossl::keygen().raw_public_key().unwrap();

            b.iter(|| {
                let encaps = PKey::public_key_from_raw_bytes_ex(
                    None,
                    KeyType::ML_KEM_768,
                    None,
                    &encaps_bytes,
                )
                .unwrap();
                black_box(ossl::encaps(&encaps))
            })
        });
    }

    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::kem;

        let decaps = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
        let encaps_bytes = decaps
            .encapsulation_key()
            .unwrap()
            .key_bytes()
            .unwrap()
            .as_ref()
            .to_vec();

        b.iter(|| {
            let encaps = kem::EncapsulationKey::new(&kem::ML_KEM_768, &encaps_bytes).unwrap();
            black_box(encaps.encapsulate().unwrap());
        })
    });

    group.bench_function("libcrux-ml-kem", |b| {
        use libcrux_ml_kem::mlkem768;

        let mut rand = [0u8; 64];
        getrandom::fill(&mut rand).unwrap();
        let (_, encaps) = mlkem768::generate_key_pair(rand).into_parts();
        let encaps_bytes = encaps.as_slice().to_vec();

        b.iter(|| {
            let encaps = mlkem768::MlKem768PublicKey::try_from(encaps_bytes.as_slice()).unwrap();
            let mut rand = [0u8; 32];
            getrandom::fill(&mut rand).unwrap();
            black_box(mlkem768::encapsulate(&encaps, rand))
        });
    });

    group.bench_function("rustcrypto", |b| {
        use ml_kem::{Encapsulate, Kem, KeyExport, MlKem768, ml_kem_768::EncapsulationKey};

        let (_decaps, encaps) = MlKem768::generate_keypair();
        let encaps_bytes = encaps.to_bytes();

        b.iter(|| {
            let encaps = EncapsulationKey::new(&encaps_bytes).unwrap();
            black_box(encaps.encapsulate());
        });
    });

    group.bench_function("rind", |b| {
        use rind::kem::*;

        let encaps = DecapsulationKey::<MlKem768>::generate()
            .unwrap()
            .public_key();

        b.iter(|| {
            let encaps = EncapsulationKey::<MlKem768>::new(encaps.as_ref()).unwrap();
            black_box(encaps.encapsulate().unwrap());
        });
    });

    group.bench_function("verified-garbage", |b| {
        vg_agrees_with_rind();
        use verified_garbage::mlkem768::EncapsulationKey768;

        let encaps = *vg_generate().encapsulation_key().as_bytes();

        b.iter(|| {
            let encaps = EncapsulationKey768::from_bytes(&encaps).unwrap();
            black_box(encaps.encapsulate().unwrap());
        });
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::key_agreement::mlkem768::{DecapKey, EncapKey};

        let encaps = DecapKey::generate().unwrap().encapsulation_key().as_bytes();

        b.iter(|| {
            let encaps = EncapKey::from_bytes(&encaps).unwrap();
            black_box(encaps.encaps().unwrap());
        });
    });
}

// client second operation
fn mlkem768_decaps(c: &mut Criterion) {
    let mut group = c.benchmark_group("mlkem768-decaps");
    group.throughput(Throughput::Elements(1));

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    if ossl::available() {
        group.bench_function("openssl", |b| {
            let decaps = ossl::keygen();
            let (ciphertext, _secret) = ossl::encaps(&decaps);

            b.iter(|| black_box(ossl::decaps(&decaps, &ciphertext)))
        });
    }

    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::kem;

        let decaps = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
        let (ciphertext, _secret) = decaps.encapsulation_key().unwrap().encapsulate().unwrap();
        let ciphertext = ciphertext.as_ref().to_vec();

        b.iter(|| {
            let ciphertext = kem::Ciphertext::from(ciphertext.as_slice());
            black_box(decaps.decapsulate(ciphertext).unwrap())
        })
    });

    group.bench_function("libcrux-ml-kem", |b| {
        use libcrux_ml_kem::mlkem768;

        let mut rand = [0u8; 64];
        getrandom::fill(&mut rand).unwrap();
        let (decaps, encaps) = mlkem768::generate_key_pair(rand).into_parts();

        let mut rand = [0u8; 32];
        getrandom::fill(&mut rand).unwrap();
        let (ciphertext, _secret) = mlkem768::encapsulate(&encaps, rand);
        let ciphertext = ciphertext.as_slice().to_vec();

        b.iter(|| {
            let ciphertext = mlkem768::MlKem768Ciphertext::try_from(ciphertext.as_slice()).unwrap();
            black_box(mlkem768::decapsulate(&decaps, &ciphertext));
        });
    });

    group.bench_function("rustcrypto", |b| {
        use ml_kem::{Decapsulate, Encapsulate, Kem, MlKem768};

        let (decaps, encaps) = MlKem768::generate_keypair();
        let (ciphertext, _secret) = encaps.encapsulate();
        let ciphertext = ciphertext.as_slice().to_vec();

        b.iter(|| {
            black_box(decaps.decapsulate_slice(&ciphertext).unwrap());
        });
    });

    group.bench_function("rind", |b| {
        use rind::kem::*;

        let decaps = DecapsulationKey::<MlKem768>::generate().unwrap();
        let (ciphertext, _secret) = decaps.public_key().encapsulate().unwrap();

        b.iter(|| {
            let ciphertext = Ciphertext::<MlKem768>::new(ciphertext.as_ref()).unwrap();
            black_box(decaps.decapsulate(&ciphertext))
        })
    });

    group.bench_function("verified-garbage", |b| {
        vg_agrees_with_rind();
        let decaps = vg_generate();
        let (_secret, ciphertext) = decaps.encapsulation_key().encapsulate().unwrap();

        b.iter(|| black_box(decaps.decapsulate(&ciphertext).unwrap()))
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::key_agreement::mlkem768::DecapKey;

        // Decapsulation consumes its key here too.
        b.iter_batched(
            || {
                let decaps = DecapKey::generate().unwrap();
                let (_secret, ciphertext) = decaps.encapsulation_key().encaps().unwrap();
                (decaps, ciphertext)
            },
            |(decaps, ciphertext)| black_box(decaps.decaps(&ciphertext)),
            BatchSize::SmallInput,
        );
    });
}

// combined operation: keygen, encaps-encode, encaps-decode, encaps, decaps
fn mlkem768_combined(c: &mut Criterion) {
    let mut group = c.benchmark_group("mlkem768-combined");
    group.throughput(Throughput::Elements(1));

    #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
    if ossl::available() {
        group.bench_function("openssl", |b| {
            use openssl::pkey::{KeyType, PKey};

            b.iter(|| {
                let decaps = ossl::keygen();
                let encaps_encoded = decaps.raw_public_key().unwrap();
                let encaps = PKey::public_key_from_raw_bytes_ex(
                    None,
                    KeyType::ML_KEM_768,
                    None,
                    &encaps_encoded,
                )
                .unwrap();
                let (ciphertext, _secret) = ossl::encaps(&encaps);
                black_box(ossl::decaps(&decaps, &ciphertext))
            })
        });
    }

    group.bench_function("aws-lc-rs", |b| {
        use aws_lc_rs::kem;

        b.iter(|| {
            let decaps = kem::DecapsulationKey::generate(&kem::ML_KEM_768).unwrap();
            let encaps_encoded = decaps.encapsulation_key().unwrap().key_bytes().unwrap();
            let encaps =
                kem::EncapsulationKey::new(&kem::ML_KEM_768, encaps_encoded.as_ref()).unwrap();
            let (ciphertext, _secret) = encaps.encapsulate().unwrap();
            black_box(decaps.decapsulate(ciphertext).unwrap())
        })
    });

    group.bench_function("libcrux-ml-kem", |b| {
        use libcrux_ml_kem::mlkem768;

        b.iter(|| {
            let mut rand = [0u8; 64];
            getrandom::fill(&mut rand).unwrap();
            let (decaps, encaps) = mlkem768::generate_key_pair(rand).into_parts();
            let encaps_encoded = encaps.as_slice();
            let encaps = mlkem768::MlKem768PublicKey::from(encaps_encoded);

            let mut rand = [0u8; 32];
            getrandom::fill(&mut rand).unwrap();
            let (ciphertext, _secret) = mlkem768::encapsulate(&encaps, rand);
            black_box(mlkem768::decapsulate(&decaps, &ciphertext));
        });
    });

    group.bench_function("rustcrypto", |b| {
        use ml_kem::{
            Decapsulate, Encapsulate, Kem, KeyExport, MlKem768, ml_kem_768::EncapsulationKey,
        };

        b.iter(|| {
            let (decaps, encaps) = MlKem768::generate_keypair();
            let encaps_encoded = encaps.to_bytes();
            let encaps = EncapsulationKey::new(&encaps_encoded).unwrap();
            let (ciphertext, _secret) = encaps.encapsulate();
            black_box(decaps.decapsulate(&ciphertext));
        });
    });

    group.bench_function("rind", |b| {
        use rind::kem::*;

        b.iter(|| {
            let decaps = DecapsulationKey::<MlKem768>::generate().unwrap();
            let encaps_encoded = decaps.public_key();
            let encaps = EncapsulationKey::<MlKem768>::new(encaps_encoded.as_ref()).unwrap();
            let (ciphertext, _secret) = encaps.encapsulate().unwrap();
            let ciphertext = Ciphertext::<MlKem768>::new(ciphertext.as_ref()).unwrap();
            black_box(decaps.decapsulate(&ciphertext));
        });
    });

    group.bench_function("verified-garbage", |b| {
        vg_agrees_with_rind();
        use verified_garbage::mlkem768::EncapsulationKey768;

        b.iter(|| {
            let decaps = vg_generate();
            let encaps_encoded = decaps.encapsulation_key().as_bytes();
            let encaps = EncapsulationKey768::from_bytes(encaps_encoded).unwrap();
            let (_secret, ciphertext) = encaps.encapsulate().unwrap();
            black_box(decaps.decapsulate(&ciphertext).unwrap());
        });
    });

    #[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
    group.bench_function("graviola", |b| {
        use graviola::key_agreement::mlkem768::{DecapKey, EncapKey};

        b.iter(|| {
            let decaps = DecapKey::generate().unwrap();
            let encaps = EncapKey::from_bytes(&decaps.encapsulation_key().as_bytes()).unwrap();
            let (_secret, ciphertext) = encaps.encaps().unwrap();
            black_box(decaps.decaps(&ciphertext));
        });
    });
}

/// ML-KEM-512 and ML-KEM-1024 against aws-lc-rs and libcrux, each operation
/// measured as its ML-KEM-768 group measures it.
macro_rules! mlkem_set {
    (
        $keygen:ident, $encaps:ident, $decaps:ident, $name:literal, $set:ident, $aws:ident,
        $libcrux:ident, $public:ident, $ciphertext:ident
    ) => {
        fn $keygen(c: &mut Criterion) {
            let mut group = c.benchmark_group(concat!($name, "-keygen"));
            group.throughput(Throughput::Elements(1));

            group.bench_function("aws-lc-rs", |b| {
                use aws_lc_rs::kem;

                b.iter(|| {
                    let decaps = kem::DecapsulationKey::generate(&kem::$aws).unwrap();
                    black_box(decaps.encapsulation_key().unwrap())
                })
            });

            group.bench_function("libcrux-ml-kem", |b| {
                use libcrux_ml_kem::$libcrux;

                b.iter(|| {
                    let mut rand = [0u8; 64];
                    getrandom::fill(&mut rand).unwrap();
                    black_box($libcrux::generate_key_pair(rand).into_parts());
                });
            });

            group.bench_function("rind", |b| {
                use rind::kem::*;

                b.iter(|| {
                    black_box(DecapsulationKey::<$set>::generate().unwrap());
                });
            });
        }

        fn $encaps(c: &mut Criterion) {
            let mut group = c.benchmark_group(concat!($name, "-encaps"));
            group.throughput(Throughput::Elements(1));

            group.bench_function("aws-lc-rs", |b| {
                use aws_lc_rs::kem;

                let decaps = kem::DecapsulationKey::generate(&kem::$aws).unwrap();
                let encaps_bytes = decaps
                    .encapsulation_key()
                    .unwrap()
                    .key_bytes()
                    .unwrap()
                    .as_ref()
                    .to_vec();

                b.iter(|| {
                    let encaps = kem::EncapsulationKey::new(&kem::$aws, &encaps_bytes).unwrap();
                    black_box(encaps.encapsulate().unwrap());
                })
            });

            group.bench_function("libcrux-ml-kem", |b| {
                use libcrux_ml_kem::$libcrux;

                let mut rand = [0u8; 64];
                getrandom::fill(&mut rand).unwrap();
                let (_, encaps) = $libcrux::generate_key_pair(rand).into_parts();
                let encaps_bytes = encaps.as_slice().to_vec();

                b.iter(|| {
                    let encaps = $libcrux::$public::try_from(encaps_bytes.as_slice()).unwrap();
                    let mut rand = [0u8; 32];
                    getrandom::fill(&mut rand).unwrap();
                    black_box($libcrux::encapsulate(&encaps, rand))
                });
            });

            group.bench_function("rind", |b| {
                use rind::kem::*;

                let encaps = DecapsulationKey::<$set>::generate().unwrap().public_key();

                b.iter(|| {
                    let encaps = EncapsulationKey::<$set>::new(encaps.as_ref()).unwrap();
                    black_box(encaps.encapsulate().unwrap());
                });
            });
        }

        fn $decaps(c: &mut Criterion) {
            let mut group = c.benchmark_group(concat!($name, "-decaps"));
            group.throughput(Throughput::Elements(1));

            group.bench_function("aws-lc-rs", |b| {
                use aws_lc_rs::kem;

                let decaps = kem::DecapsulationKey::generate(&kem::$aws).unwrap();
                let (ciphertext, _secret) =
                    decaps.encapsulation_key().unwrap().encapsulate().unwrap();
                let ciphertext = ciphertext.as_ref().to_vec();

                b.iter(|| {
                    let ciphertext = kem::Ciphertext::from(ciphertext.as_slice());
                    black_box(decaps.decapsulate(ciphertext).unwrap())
                })
            });

            group.bench_function("libcrux-ml-kem", |b| {
                use libcrux_ml_kem::$libcrux;

                let mut rand = [0u8; 64];
                getrandom::fill(&mut rand).unwrap();
                let (decaps, encaps) = $libcrux::generate_key_pair(rand).into_parts();

                let mut rand = [0u8; 32];
                getrandom::fill(&mut rand).unwrap();
                let (ciphertext, _secret) = $libcrux::encapsulate(&encaps, rand);
                let ciphertext = ciphertext.as_slice().to_vec();

                b.iter(|| {
                    let ciphertext =
                        $libcrux::$ciphertext::try_from(ciphertext.as_slice()).unwrap();
                    black_box($libcrux::decapsulate(&decaps, &ciphertext));
                });
            });

            group.bench_function("rind", |b| {
                use rind::kem::*;

                let decaps = DecapsulationKey::<$set>::generate().unwrap();
                let (ciphertext, _secret) = decaps.public_key().encapsulate().unwrap();

                b.iter(|| {
                    let ciphertext = Ciphertext::<$set>::new(ciphertext.as_ref()).unwrap();
                    black_box(decaps.decapsulate(&ciphertext))
                })
            });
        }
    };
}

mlkem_set!(
    mlkem512_keygen,
    mlkem512_encaps,
    mlkem512_decaps,
    "mlkem512",
    MlKem512,
    ML_KEM_512,
    mlkem512,
    MlKem512PublicKey,
    MlKem512Ciphertext
);
mlkem_set!(
    mlkem1024_keygen,
    mlkem1024_encaps,
    mlkem1024_decaps,
    "mlkem1024",
    MlKem1024,
    ML_KEM_1024,
    mlkem1024,
    MlKem1024PublicKey,
    MlKem1024Ciphertext
);

criterion_group!(
    benches,
    mlkem512_keygen,
    mlkem512_encaps,
    mlkem512_decaps,
    mlkem768_keygen,
    mlkem768_encaps,
    mlkem768_decaps,
    mlkem768_combined,
    mlkem1024_keygen,
    mlkem1024_encaps,
    mlkem1024_decaps,
);
criterion_main!(benches);
