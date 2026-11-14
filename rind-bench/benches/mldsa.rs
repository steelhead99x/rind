mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl {
    //! The openssl crate does not yet wrap ML-DSA key generation.

    use std::ffi::CStr;
    use std::ptr;

    use foreign_types::ForeignType;
    use openssl::pkey::{PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;

    /// ML-DSA requires OpenSSL 3.5 or later at runtime.
    pub fn available() -> bool {
        let ok = openssl::version::number() >= 0x3050_0000;
        if !ok {
            eprintln!(
                "skipping openssl ML-DSA benchmark: {} is too old",
                openssl::version::version()
            );
        }
        ok
    }

    pub fn keygen(name: &CStr) -> PKey<Private> {
        unsafe {
            let ctx = openssl_sys::EVP_PKEY_CTX_new_from_name(
                ptr::null_mut(),
                name.as_ptr(),
                ptr::null(),
            );
            assert!(!ctx.is_null());
            let mut ctx = PkeyCtx::<()>::from_ptr(ctx);
            ctx.keygen_init().unwrap();
            ctx.keygen().unwrap()
        }
    }
}

// The message every library signs. Each signature draws fresh randomness, so
// the number of rejected attempts, and with it the time, varies alike.
const MESSAGE: &[u8] = b"rind ML-DSA benchmark message";

// The longest signature, ML-DSA-87's. Only the aws-lc-rs row writes into a
// buffer of this size; the other rows return their own.
#[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
const MAX_SIGNATURE_LEN: usize = 4627;

// One parameter set's key generation, signing, and verification, each library
// by its own name for the set.
macro_rules! ml_dsa {
    (
        $bench:ident, $id:literal,
        rind: $rind:ident, $rind_verify:ident,
        aws_lc_rs: $aws_signing:ident, $aws_verify:ident,
        libcrux: $libcrux:ident,
        rustcrypto: $rustcrypto:ident,
        openssl: $openssl:literal, $openssl_type:ident $(,)?
    ) => {
        fn $bench(c: &mut Criterion) {
            // Generate a key pair, and its public key.
            let mut group = c.benchmark_group(concat!($id, "-keygen"));
            group.throughput(Throughput::Elements(1));

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            if ossl::available() {
                group.bench_function("openssl", |b| {
                    b.iter(|| {
                        let key = ossl::keygen($openssl);
                        black_box(key.raw_public_key().unwrap());
                    })
                });
            }

            #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
            group.bench_function("aws-lc-rs", |b| {
                use aws_lc_rs::signature::{KeyPair, PqdsaKeyPair, $aws_signing};

                b.iter(|| {
                    let key = PqdsaKeyPair::generate(&$aws_signing).unwrap();
                    black_box(key.public_key().as_ref());
                })
            });

            group.bench_function("libcrux", |b| {
                b.iter(|| {
                    let mut seed = [0u8; 32];
                    getrandom::fill(&mut seed).unwrap();
                    black_box(libcrux_ml_dsa::$libcrux::generate_key_pair(seed));
                })
            });

            // RustCrypto's key computes its public key as it is made.
            group.bench_function("rustcrypto", |b| {
                use ml_dsa::{Generate, SigningKey, $rustcrypto};

                b.iter(|| {
                    black_box(SigningKey::<$rustcrypto>::generate());
                })
            });

            group.bench_function("rind", |b| {
                use rind::signature::sign::{MlDsaKeyPair, $rind};

                b.iter(|| {
                    let key = MlDsaKeyPair::<$rind>::generate().unwrap();
                    black_box(key.public_key());
                })
            });
            group.finish();

            // Sign with hedged randomness and the empty context.
            let mut group = c.benchmark_group(concat!($id, "-sign"));
            group.throughput(Throughput::Elements(1));

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            if ossl::available() {
                group.bench_function("openssl", |b| {
                    use openssl::sign::Signer;
                    let key = ossl::keygen($openssl);

                    b.iter(|| {
                        let mut signer = Signer::new_without_digest(&key).unwrap();
                        black_box(signer.sign_oneshot_to_vec(MESSAGE).unwrap());
                    })
                });
            }

            #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
            group.bench_function("aws-lc-rs", |b| {
                use aws_lc_rs::signature::{PqdsaKeyPair, $aws_signing};
                let key = PqdsaKeyPair::generate(&$aws_signing).unwrap();
                let mut signature = [0u8; MAX_SIGNATURE_LEN];

                b.iter(|| {
                    black_box(key.sign(MESSAGE, &mut signature).unwrap());
                })
            });

            group.bench_function("libcrux", |b| {
                let mut seed = [0u8; 32];
                getrandom::fill(&mut seed).unwrap();
                let key = libcrux_ml_dsa::$libcrux::generate_key_pair(seed);

                b.iter(|| {
                    let mut rnd = [0u8; 32];
                    getrandom::fill(&mut rnd).unwrap();
                    black_box(
                        libcrux_ml_dsa::$libcrux::sign(&key.signing_key, MESSAGE, b"", rnd)
                            .unwrap(),
                    );
                })
            });

            // RustCrypto's `Signer` is deterministic, so this signs through the
            // expanded key with randomness, as the others do.
            group.bench_function("rustcrypto", |b| {
                use ml_dsa::{Generate, SigningKey, $rustcrypto};
                let key = SigningKey::<$rustcrypto>::generate();

                b.iter(|| {
                    black_box(
                        key.expanded_key()
                            .sign_randomized(MESSAGE, b"", &mut getrandom::SysRng)
                            .unwrap(),
                    );
                })
            });

            group.bench_function("rind", |b| {
                use rind::signature::sign::{MlDsaKeyPair, $rind};
                let key = MlDsaKeyPair::<$rind>::generate().unwrap();

                b.iter(|| {
                    black_box(key.sign(MESSAGE).unwrap());
                })
            });
            group.finish();

            // Verify one signature. Each library parses the public key once,
            // outside the timed loop, and the signature in it.
            let mut group = c.benchmark_group(concat!($id, "-verify"));
            group.throughput(Throughput::Elements(1));

            let (public_key, signature) = {
                use rind::signature::sign::{MlDsaKeyPair, $rind};
                let key = MlDsaKeyPair::<$rind>::generate().unwrap();
                let signature = key.sign(MESSAGE).unwrap();
                (
                    key.public_key().as_ref().to_vec(),
                    signature.as_ref().to_vec(),
                )
            };

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            if ossl::available() {
                group.bench_function("openssl", |b| {
                    use openssl::pkey::{KeyType, PKey};
                    use openssl::sign::Verifier;
                    let key = PKey::public_key_from_raw_bytes_ex(
                        None,
                        KeyType::$openssl_type,
                        None,
                        &public_key,
                    )
                    .unwrap();

                    b.iter(|| {
                        let mut verifier = Verifier::new_without_digest(&key).unwrap();
                        assert!(verifier.verify_oneshot(&signature, MESSAGE).unwrap());
                    })
                });
            }

            #[cfg(not(any(target_arch = "xtensa", target_os = "none")))]
            group.bench_function("aws-lc-rs", |b| {
                use aws_lc_rs::signature::{ParsedPublicKey, $aws_verify};
                let key = ParsedPublicKey::new(&$aws_verify, &public_key).unwrap();

                b.iter(|| {
                    key.verify_sig(MESSAGE, &signature).unwrap();
                })
            });

            group.bench_function("libcrux", |b| {
                use libcrux_ml_dsa::{MLDSASignature, MLDSAVerificationKey};
                let key = MLDSAVerificationKey::new(public_key.as_slice().try_into().unwrap());

                b.iter(|| {
                    let signature = MLDSASignature::new(signature.as_slice().try_into().unwrap());
                    libcrux_ml_dsa::$libcrux::verify(&key, MESSAGE, b"", &signature).unwrap();
                })
            });

            group.bench_function("rustcrypto", |b| {
                use ml_dsa::{EncodedVerifyingKey, Signature, Verifier, VerifyingKey, $rustcrypto};
                let key = VerifyingKey::<$rustcrypto>::decode(
                    &EncodedVerifyingKey::<$rustcrypto>::try_from(public_key.as_slice()).unwrap(),
                );

                b.iter(|| {
                    let signature =
                        Signature::<$rustcrypto>::try_from(signature.as_slice()).unwrap();
                    key.verify(MESSAGE, &signature).unwrap();
                })
            });

            group.bench_function("rind", |b| {
                use rind::signature::{PublicKey, verify};
                let key = PublicKey::new(&verify::$rind_verify, &public_key).unwrap();

                b.iter(|| {
                    key.verify(MESSAGE, &signature).unwrap();
                })
            });
            group.finish();
        }
    };
}

ml_dsa!(
    mldsa44, "mldsa44",
    rind: MlDsa44, ML_DSA_44,
    aws_lc_rs: ML_DSA_44_SIGNING, ML_DSA_44,
    libcrux: ml_dsa_44,
    rustcrypto: MlDsa44,
    openssl: c"ML-DSA-44", ML_DSA_44,
);

ml_dsa!(
    mldsa65, "mldsa65",
    rind: MlDsa65, ML_DSA_65,
    aws_lc_rs: ML_DSA_65_SIGNING, ML_DSA_65,
    libcrux: ml_dsa_65,
    rustcrypto: MlDsa65,
    openssl: c"ML-DSA-65", ML_DSA_65,
);

ml_dsa!(
    mldsa87, "mldsa87",
    rind: MlDsa87, ML_DSA_87,
    aws_lc_rs: ML_DSA_87_SIGNING, ML_DSA_87,
    libcrux: ml_dsa_87,
    rustcrypto: MlDsa87,
    openssl: c"ML-DSA-87", ML_DSA_87,
);

criterion_group!(benches, mldsa44, mldsa65, mldsa87);
criterion_main!(benches);
