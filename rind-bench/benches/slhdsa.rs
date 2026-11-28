#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use std::hint::black_box;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, dit};

#[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
#[cfg(not(target_arch = "xtensa"))]
mod ossl {
    //! The openssl crate does not yet wrap SLH-DSA key generation.

    use std::ffi::CStr;
    use std::ptr;

    use foreign_types::ForeignType;
    use openssl::pkey::{PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;

    /// SLH-DSA requires OpenSSL 3.5 or later at runtime: an older one fails
    /// the row rather than leave it out.
    pub fn require() {
        assert!(
            openssl::version::number() >= 0x3050_0000,
            "openssl's SLH-DSA rows need OpenSSL 3.5 or later, not {}",
            openssl::version::version()
        );
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
#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = b"rind SLH-DSA benchmark message";

/// A RustCrypto key from `N`-byte seeds: its `SigningKey::new` wants a
/// rand_core 0.10 RNG too.
#[cfg(not(target_arch = "xtensa"))]
fn rustcrypto_key<P: slh_dsa::ParameterSet, const N: usize>() -> slh_dsa::SigningKey<P> {
    let mut seeds = [[0u8; N]; 3];
    getrandom::fill(seeds.as_flattened_mut()).unwrap();
    slh_dsa::SigningKey::<P>::slh_keygen_internal(&seeds[0], &seeds[1], &seeds[2])
}

// One parameter set's key generation, signing, and verification, each library
// by its own name for the set. aws-lc-rs and libcrux have no SLH-DSA.
macro_rules! slh_dsa {
    (
        $keygen:ident, $sign:ident, $verify:ident, n: $n:literal,
        rind: $rind:ident,
        rustcrypto: $rustcrypto:ident,
        fips205: $fips205:ident,
        openssl: $openssl:literal $(,)?
    ) => {
        // Generate a key pair, and its public key.
        mod $keygen {
            use swole::bench;

            use super::*;

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            #[bench(setup = ossl::require)]
            fn openssl(_: &()) {
                let key = ossl::keygen($openssl);
                black_box(key.raw_public_key().unwrap());
            }

            #[bench]
            fn fips205() {
                black_box(fips205::$fips205::try_keygen().unwrap());
            }

            #[bench]
            fn rustcrypto() {
                black_box(
                    rustcrypto_key::<slh_dsa::$rustcrypto, $n>()
                        .as_ref()
                        .to_bytes(),
                );
            }

            #[bench(setup = dit)]
            fn rind(_dit: &Dit<()>) {
                use rind::slh_dsa::{KeyPair, $rind};
                let key = KeyPair::<$rind>::generate().unwrap();
                black_box(key.public_key());
            }
        }

        // Sign with fresh randomness and the empty context.
        mod $sign {
            use swole::bench;

            use super::*;

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            fn openssl_key() -> openssl::pkey::PKey<openssl::pkey::Private> {
                ossl::require();
                ossl::keygen($openssl)
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            #[bench(setup = openssl_key)]
            fn openssl(key: &openssl::pkey::PKey<openssl::pkey::Private>) {
                let mut signer = openssl::sign::Signer::new_without_digest(key).unwrap();
                black_box(signer.sign_oneshot_to_vec(MESSAGE).unwrap());
            }

            fn fips205_key() -> fips205::$fips205::PrivateKey {
                let (_, key) = fips205::$fips205::try_keygen().unwrap();
                key
            }

            #[bench(setup = fips205_key)]
            fn fips205(key: &fips205::$fips205::PrivateKey) {
                use fips205::traits::Signer;
                black_box(key.try_sign(MESSAGE, b"", true).unwrap());
            }

            // RustCrypto's `RandomizedSigner` wants a rand_core 0.10 RNG, so
            // this draws the randomness itself, as the ML-DSA benchmark does
            // for libcrux.
            #[bench(setup = rustcrypto_key::<slh_dsa::$rustcrypto, $n>)]
            fn rustcrypto(key: &slh_dsa::SigningKey<slh_dsa::$rustcrypto>) {
                let mut rnd = [0u8; $n];
                getrandom::fill(&mut rnd).unwrap();
                black_box(key.try_sign_with_context(MESSAGE, b"", Some(&rnd)).unwrap());
            }

            fn rind_key() -> Dit<rind::slh_dsa::KeyPair<rind::slh_dsa::$rind>> {
                use rind::slh_dsa::{KeyPair, $rind};
                Dit::hold(KeyPair::<$rind>::generate().unwrap())
            }

            #[bench(setup = rind_key)]
            fn rind(key: &Dit<rind::slh_dsa::KeyPair<rind::slh_dsa::$rind>>) {
                black_box(key.sign(MESSAGE).unwrap());
            }
        }

        // Verify one signature. Each library parses the public key once,
        // outside the timed call, and the signature in it.
        mod $verify {
            use swole::bench;

            use super::*;

            /// A rind public key, raw and as an SPKI, and a signature it
            /// verifies.
            struct Signed {
                public_key: Vec<u8>,
                spki: Vec<u8>,
                signature: Vec<u8>,
            }

            fn signed() -> Signed {
                use rind::slh_dsa::{KeyPair, $rind};
                let key = KeyPair::<$rind>::generate().unwrap();
                let signature = key.sign(MESSAGE).unwrap();
                let public_key = key.public_key();
                Signed {
                    public_key: public_key.as_ref().to_vec(),
                    spki: public_key.to_spki().as_ref().to_vec(),
                    signature: signature.as_ref().to_vec(),
                }
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            fn openssl_key() -> (openssl::pkey::PKey<openssl::pkey::Public>, Vec<u8>) {
                ossl::require();
                let signed = signed();
                (
                    openssl::pkey::PKey::public_key_from_der(&signed.spki).unwrap(),
                    signed.signature,
                )
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            #[bench(setup = openssl_key)]
            fn openssl((key, signature): &(openssl::pkey::PKey<openssl::pkey::Public>, Vec<u8>)) {
                let mut verifier = openssl::sign::Verifier::new_without_digest(key).unwrap();
                assert!(verifier.verify_oneshot(signature, MESSAGE).unwrap());
            }

            fn fips205_key() -> (fips205::$fips205::PublicKey, Vec<u8>) {
                use fips205::traits::SerDes;
                let signed = signed();
                let key = fips205::$fips205::PublicKey::try_from_bytes(
                    signed.public_key.as_slice().try_into().unwrap(),
                )
                .unwrap();
                (key, signed.signature)
            }

            #[bench(setup = fips205_key)]
            fn fips205((key, signature): &(fips205::$fips205::PublicKey, Vec<u8>)) {
                use fips205::traits::Verifier;
                assert!(key.verify(MESSAGE, signature.as_slice().try_into().unwrap(), b""));
            }

            fn rustcrypto_key() -> (slh_dsa::VerifyingKey<slh_dsa::$rustcrypto>, Vec<u8>) {
                let signed = signed();
                let key = slh_dsa::VerifyingKey::<slh_dsa::$rustcrypto>::try_from(
                    signed.public_key.as_slice(),
                )
                .unwrap();
                (key, signed.signature)
            }

            #[bench(setup = rustcrypto_key)]
            fn rustcrypto(
                (key, signature): &(slh_dsa::VerifyingKey<slh_dsa::$rustcrypto>, Vec<u8>),
            ) {
                use slh_dsa::signature::Verifier;
                let signature = slh_dsa::Signature::try_from(signature.as_slice()).unwrap();
                key.verify(MESSAGE, &signature).unwrap();
            }

            fn rind_key() -> Dit<(rind::slh_dsa::PublicKey<rind::slh_dsa::$rind>, Vec<u8>)> {
                use rind::slh_dsa::{PublicKey, $rind};
                let signed = signed();
                Dit::hold((
                    PublicKey::<$rind>::from_spki(&signed.spki).unwrap(),
                    signed.signature,
                ))
            }

            #[bench(setup = rind_key)]
            fn rind(fixture: &Dit<(rind::slh_dsa::PublicKey<rind::slh_dsa::$rind>, Vec<u8>)>) {
                let (key, signature) = &**fixture;
                key.verify(MESSAGE, signature).unwrap();
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
slh_dsa!(
    slhdsa_sha2_128s_keygen, slhdsa_sha2_128s_sign, slhdsa_sha2_128s_verify, n: 16,
    rind: SlhDsaSha2_128s,
    rustcrypto: Sha2_128s,
    fips205: slh_dsa_sha2_128s,
    openssl: c"SLH-DSA-SHA2-128s",
);

#[cfg(not(target_arch = "xtensa"))]
slh_dsa!(
    slhdsa_sha2_128f_keygen, slhdsa_sha2_128f_sign, slhdsa_sha2_128f_verify, n: 16,
    rind: SlhDsaSha2_128f,
    rustcrypto: Sha2_128f,
    fips205: slh_dsa_sha2_128f,
    openssl: c"SLH-DSA-SHA2-128f",
);

#[cfg(not(target_arch = "xtensa"))]
slh_dsa!(
    slhdsa_shake_128s_keygen, slhdsa_shake_128s_sign, slhdsa_shake_128s_verify, n: 16,
    rind: SlhDsaShake128s,
    rustcrypto: Shake128s,
    fips205: slh_dsa_shake_128s,
    openssl: c"SLH-DSA-SHAKE-128s",
);

#[cfg(not(target_arch = "xtensa"))]
slh_dsa!(
    slhdsa_shake_128f_keygen, slhdsa_shake_128f_sign, slhdsa_shake_128f_verify, n: 16,
    rind: SlhDsaShake128f,
    rustcrypto: Shake128f,
    fips205: slh_dsa_shake_128f,
    openssl: c"SLH-DSA-SHAKE-128f",
);

#[cfg(not(target_arch = "xtensa"))]
slh_dsa!(
    slhdsa_sha2_256f_keygen, slhdsa_sha2_256f_sign, slhdsa_sha2_256f_verify, n: 32,
    rind: SlhDsaSha2_256f,
    rustcrypto: Sha2_256f,
    fips205: slh_dsa_sha2_256f,
    openssl: c"SLH-DSA-SHA2-256f",
);

#[cfg(not(target_arch = "xtensa"))]
slh_dsa!(
    slhdsa_shake_256f_keygen, slhdsa_shake_256f_sign, slhdsa_shake_256f_verify, n: 32,
    rind: SlhDsaShake256f,
    rustcrypto: Shake256f,
    fips205: slh_dsa_shake_256f,
    openssl: c"SLH-DSA-SHAKE-256f",
);

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
