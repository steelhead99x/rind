mod criterion;
use std::hint::black_box;

use criterion::{Criterion, Throughput, criterion_group, criterion_main};

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
mod ossl {
    //! The openssl crate does not yet wrap SLH-DSA key generation.

    use std::ffi::CStr;
    use std::ptr;

    use foreign_types::ForeignType;
    use openssl::pkey::{PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;

    /// SLH-DSA requires OpenSSL 3.5 or later at runtime.
    pub fn available() -> bool {
        let ok = openssl::version::number() >= 0x3050_0000;
        if !ok {
            eprintln!(
                "skipping openssl SLH-DSA benchmark: {} is too old",
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

// The message every library signs. SLH-DSA signs without rejection, so its
// time does not depend on the randomness each signature draws.
const MESSAGE: &[u8] = b"rind SLH-DSA benchmark message";

// One parameter set's key generation, signing, and verification, each library
// by its own name for the set. aws-lc-rs and libcrux have no SLH-DSA.
macro_rules! slh_dsa {
    (
        $bench:ident, $id:literal, n: $n:literal,
        rind: $rind:ident, $rind_verify:ident,
        rustcrypto: $rustcrypto:ident,
        fips205: $fips205:ident,
        openssl: $openssl:literal $(,)?
    ) => {
        fn $bench(c: &mut Criterion) {
            // RustCrypto's `SigningKey::new` wants a rand_core 0.10 RNG too.
            let rustcrypto_key = || {
                let mut seeds = [[0u8; $n]; 3];
                getrandom::fill(seeds.as_flattened_mut()).unwrap();
                slh_dsa::SigningKey::<slh_dsa::$rustcrypto>::slh_keygen_internal(
                    &seeds[0], &seeds[1], &seeds[2],
                )
            };

            // An s set signs for a tenth of a second or more, so the default
            // hundred samples would take minutes.
            let sample_size = |group: &mut criterion::BenchmarkGroup<'_, _>| {
                if $id.ends_with('s') {
                    group.sample_size(10);
                }
            };

            // Generate a key pair, and its public key.
            let mut group = c.benchmark_group(concat!($id, "-keygen"));
            group.throughput(Throughput::Elements(1));
            sample_size(&mut group);

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            if ossl::available() {
                group.bench_function("openssl", |b| {
                    b.iter(|| {
                        let key = ossl::keygen($openssl);
                        black_box(key.raw_public_key().unwrap());
                    })
                });
            }

            group.bench_function("fips205", |b| {
                b.iter(|| {
                    black_box(fips205::$fips205::try_keygen().unwrap());
                })
            });

            group.bench_function("rustcrypto", |b| {
                b.iter(|| {
                    black_box(rustcrypto_key().as_ref().to_bytes());
                })
            });

            group.bench_function("rind", |b| {
                use rind::signature::sign::{SlhDsaKeyPair, $rind};

                b.iter(|| {
                    let key = SlhDsaKeyPair::<$rind>::generate().unwrap();
                    black_box(key.public_key());
                })
            });
            group.finish();

            // Sign with fresh randomness and the empty context.
            let mut group = c.benchmark_group(concat!($id, "-sign"));
            group.throughput(Throughput::Elements(1));
            sample_size(&mut group);

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

            group.bench_function("fips205", |b| {
                use fips205::traits::Signer;
                let (_, key) = fips205::$fips205::try_keygen().unwrap();

                b.iter(|| {
                    black_box(key.try_sign(MESSAGE, b"", true).unwrap());
                })
            });

            // RustCrypto's `RandomizedSigner` wants a rand_core 0.10 RNG, so
            // this draws the randomness itself, as the ML-DSA benchmark does
            // for libcrux.
            group.bench_function("rustcrypto", |b| {
                let key = rustcrypto_key();

                b.iter(|| {
                    let mut rnd = [0u8; $n];
                    getrandom::fill(&mut rnd).unwrap();
                    black_box(key.try_sign_with_context(MESSAGE, b"", Some(&rnd)).unwrap());
                })
            });

            group.bench_function("rind", |b| {
                use rind::signature::sign::{SlhDsaKeyPair, $rind};
                let key = SlhDsaKeyPair::<$rind>::generate().unwrap();

                b.iter(|| {
                    black_box(key.sign(MESSAGE).unwrap());
                })
            });
            group.finish();

            // Verify one signature. Each library parses the public key once,
            // outside the timed loop, and the signature in it.
            let mut group = c.benchmark_group(concat!($id, "-verify"));
            group.throughput(Throughput::Elements(1));

            let (public_key, spki, signature) = {
                use rind::signature::sign::{SlhDsaKeyPair, $rind};
                let key = SlhDsaKeyPair::<$rind>::generate().unwrap();
                let signature = key.sign(MESSAGE).unwrap();
                let public_key = key.public_key();
                (
                    public_key.as_ref().to_vec(),
                    public_key.to_spki().as_ref().to_vec(),
                    signature.as_ref().to_vec(),
                )
            };

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            if ossl::available() {
                group.bench_function("openssl", |b| {
                    use openssl::pkey::PKey;
                    use openssl::sign::Verifier;
                    let key = PKey::public_key_from_der(&spki).unwrap();

                    b.iter(|| {
                        let mut verifier = Verifier::new_without_digest(&key).unwrap();
                        assert!(verifier.verify_oneshot(&signature, MESSAGE).unwrap());
                    })
                });
            }

            group.bench_function("fips205", |b| {
                use fips205::traits::{SerDes, Verifier};
                let key = fips205::$fips205::PublicKey::try_from_bytes(
                    public_key.as_slice().try_into().unwrap(),
                )
                .unwrap();

                b.iter(|| {
                    assert!(key.verify(MESSAGE, signature.as_slice().try_into().unwrap(), b""));
                })
            });

            group.bench_function("rustcrypto", |b| {
                use slh_dsa::signature::Verifier;
                let key =
                    slh_dsa::VerifyingKey::<slh_dsa::$rustcrypto>::try_from(public_key.as_slice())
                        .unwrap();

                b.iter(|| {
                    let signature = slh_dsa::Signature::try_from(signature.as_slice()).unwrap();
                    key.verify(MESSAGE, &signature).unwrap();
                })
            });

            group.bench_function("rind", |b| {
                use rind::signature::{PublicKey, verify};
                let key = PublicKey::from_spki(&verify::$rind_verify, &spki).unwrap();

                b.iter(|| {
                    key.verify(MESSAGE, &signature).unwrap();
                })
            });
            group.finish();
        }
    };
}

slh_dsa!(
    sha2_128s, "slhdsa-sha2-128s", n: 16,
    rind: SlhDsaSha2_128s, SLH_DSA_SHA2_128S,
    rustcrypto: Sha2_128s,
    fips205: slh_dsa_sha2_128s,
    openssl: c"SLH-DSA-SHA2-128s",
);

slh_dsa!(
    sha2_128f, "slhdsa-sha2-128f", n: 16,
    rind: SlhDsaSha2_128f, SLH_DSA_SHA2_128F,
    rustcrypto: Sha2_128f,
    fips205: slh_dsa_sha2_128f,
    openssl: c"SLH-DSA-SHA2-128f",
);

slh_dsa!(
    shake_128s, "slhdsa-shake-128s", n: 16,
    rind: SlhDsaShake128s, SLH_DSA_SHAKE_128S,
    rustcrypto: Shake128s,
    fips205: slh_dsa_shake_128s,
    openssl: c"SLH-DSA-SHAKE-128s",
);

slh_dsa!(
    shake_128f, "slhdsa-shake-128f", n: 16,
    rind: SlhDsaShake128f, SLH_DSA_SHAKE_128F,
    rustcrypto: Shake128f,
    fips205: slh_dsa_shake_128f,
    openssl: c"SLH-DSA-SHAKE-128f",
);

slh_dsa!(
    sha2_256f, "slhdsa-sha2-256f", n: 32,
    rind: SlhDsaSha2_256f, SLH_DSA_SHA2_256F,
    rustcrypto: Sha2_256f,
    fips205: slh_dsa_sha2_256f,
    openssl: c"SLH-DSA-SHA2-256f",
);

slh_dsa!(
    shake_256f, "slhdsa-shake-256f", n: 32,
    rind: SlhDsaShake256f, SLH_DSA_SHAKE_256F,
    rustcrypto: Shake256f,
    fips205: slh_dsa_shake_256f,
    openssl: c"SLH-DSA-SHAKE-256f",
);

criterion_group!(
    benches, sha2_128s, sha2_128f, shake_128s, shake_128f, sha2_256f, shake_256f
);
criterion_main!(benches);
