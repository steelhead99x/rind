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
    //! The openssl crate does not yet wrap ML-DSA key generation.

    use std::ffi::CStr;
    use std::ptr;

    use foreign_types::ForeignType;
    use openssl::pkey::{PKey, Private};
    use openssl::pkey_ctx::PkeyCtx;

    /// ML-DSA requires OpenSSL 3.5 or later at runtime: an older one fails
    /// the row rather than leave it out.
    pub fn require() {
        assert!(
            openssl::version::number() >= 0x3050_0000,
            "openssl's ML-DSA rows need OpenSSL 3.5 or later, not {}",
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

// The message every library signs. Each signature draws fresh randomness, so
// the number of rejected attempts, and with it the time, varies alike.
#[cfg(not(target_arch = "xtensa"))]
const MESSAGE: &[u8] = b"rind ML-DSA benchmark message";

// The longest signature, ML-DSA-87's.
#[cfg(not(target_arch = "xtensa"))]
const MAX_SIGNATURE_LEN: usize = 4627;

// One parameter set's key generation, signing, and verification, each library
// by its own name for the set.
macro_rules! ml_dsa {
    (
        $keygen:ident, $sign:ident, $verify:ident, $load_verify:ident,
        rind: $rind:ident,
        aws_lc_rs: $aws_signing:ident, $aws_verify:ident,
        libcrux: $libcrux:ident, $libcrux_pair:ident, $libcrux_key:ident,
        rustcrypto: $rustcrypto:ident,
        verified_garbage: $vg:ident, $vg_signing:ident, $vg_verifying:ident,
        openssl: $openssl:literal, $openssl_type:ident $(,)?
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
            fn aws_lc_rs() {
                use aws_lc_rs::signature::{KeyPair, PqdsaKeyPair, $aws_signing};
                let key = PqdsaKeyPair::generate(&$aws_signing).unwrap();
                black_box(key.public_key().as_ref());
            }

            #[bench]
            fn libcrux() {
                let mut seed = [0u8; 32];
                getrandom::fill(&mut seed).unwrap();
                black_box(libcrux_ml_dsa::$libcrux::generate_key_pair(seed));
            }

            // RustCrypto's key computes its public key as it is made.
            #[bench]
            fn rustcrypto() {
                use ml_dsa::{Generate, SigningKey, $rustcrypto};
                black_box(SigningKey::<$rustcrypto>::generate());
            }

            #[bench(setup = dit)]
            fn rind(_dit: &Dit<()>) {
                use rind::ml_dsa::{KeyPair, $rind};
                let key = KeyPair::<$rind>::generate().unwrap();
                black_box(key.public_key());
            }

            /// Checks verified-garbage expands a seed as rind does.
            fn vg_checked() {
                use rind::ml_dsa::{KeyPair, $rind};
                use verified_garbage::$vg::$vg_signing;
                let seed = [7u8; 32];
                assert_eq!(
                    $vg_signing::from_seed(&seed)
                        .unwrap()
                        .verifying_key()
                        .as_bytes(),
                    KeyPair::<$rind>::from_seed(&seed)
                        .unwrap()
                        .public_key()
                        .as_ref()
                );
            }

            // verified-garbage generates a key only from a seed: drawn here,
            // as rind draws its own.
            #[bench(setup = vg_checked)]
            fn verified_garbage(_: &()) {
                use verified_garbage::$vg::$vg_signing;
                let mut seed = [0u8; 32];
                getrandom::fill(&mut seed).unwrap();
                let key = $vg_signing::from_seed(&seed).unwrap();
                black_box(key.verifying_key().as_bytes());
            }
        }

        // Sign with hedged randomness and the empty context.
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

            fn aws_key() -> (aws_lc_rs::signature::PqdsaKeyPair, [u8; MAX_SIGNATURE_LEN]) {
                use aws_lc_rs::signature::{PqdsaKeyPair, $aws_signing};
                (
                    PqdsaKeyPair::generate(&$aws_signing).unwrap(),
                    [0; MAX_SIGNATURE_LEN],
                )
            }

            #[bench(setup = aws_key)]
            fn aws_lc_rs(
                (key, signature): &mut (
                    aws_lc_rs::signature::PqdsaKeyPair,
                    [u8; MAX_SIGNATURE_LEN],
                ),
            ) {
                black_box(key.sign(MESSAGE, signature).unwrap());
            }

            fn libcrux_key() -> libcrux_ml_dsa::$libcrux::$libcrux_pair {
                let mut seed = [0u8; 32];
                getrandom::fill(&mut seed).unwrap();
                libcrux_ml_dsa::$libcrux::generate_key_pair(seed)
            }

            #[bench(setup = libcrux_key)]
            fn libcrux(key: &libcrux_ml_dsa::$libcrux::$libcrux_pair) {
                let mut rnd = [0u8; 32];
                getrandom::fill(&mut rnd).unwrap();
                black_box(
                    libcrux_ml_dsa::$libcrux::sign(&key.signing_key, MESSAGE, b"", rnd).unwrap(),
                );
            }

            fn rustcrypto_key() -> ml_dsa::SigningKey<ml_dsa::$rustcrypto> {
                use ml_dsa::{Generate, SigningKey, $rustcrypto};
                SigningKey::<$rustcrypto>::generate()
            }

            // RustCrypto's `Signer` is deterministic, so this signs through the
            // expanded key with randomness, as the others do.
            #[bench(setup = rustcrypto_key)]
            fn rustcrypto(key: &ml_dsa::SigningKey<ml_dsa::$rustcrypto>) {
                black_box(
                    key.expanded_key()
                        .sign_randomized(MESSAGE, b"", &mut getrandom::SysRng)
                        .unwrap(),
                );
            }

            fn rind_key() -> Dit<rind::ml_dsa::KeyPair<rind::ml_dsa::$rind>> {
                use rind::ml_dsa::{KeyPair, $rind};
                Dit::hold(KeyPair::<$rind>::generate().unwrap())
            }

            #[bench(setup = rind_key)]
            fn rind(key: &Dit<rind::ml_dsa::KeyPair<rind::ml_dsa::$rind>>) {
                black_box(key.sign(b"", MESSAGE).unwrap());
            }

            /// A random key, after checking rind verifies its signature.
            fn vg_key() -> verified_garbage::$vg::$vg_signing {
                use rind::ml_dsa::{PublicKey, $rind};
                use verified_garbage::$vg::$vg_signing;
                let mut seed = [0u8; 32];
                getrandom::fill(&mut seed).unwrap();
                let key = $vg_signing::from_seed(&seed).unwrap();
                PublicKey::<$rind>::new(key.verifying_key().as_bytes())
                    .unwrap()
                    .verify(b"", MESSAGE, &key.sign(MESSAGE, b"").unwrap())
                    .unwrap();
                key
            }

            // The key as rind holds it, the expanded private key encoding,
            // not the larger one `prepare` makes for many signatures.
            #[bench(setup = vg_key)]
            fn verified_garbage(key: &verified_garbage::$vg::$vg_signing) {
                black_box(key.sign(MESSAGE, b"").unwrap());
            }
        }

        // Verify one signature. Each library parses the public key once,
        // outside the timed call, and the signature in it.
        mod $verify {
            use swole::bench;

            use super::*;

            /// A rind public key's encoding and a signature it verifies.
            fn signed() -> (Vec<u8>, Vec<u8>) {
                use rind::ml_dsa::{KeyPair, $rind};
                let key = KeyPair::<$rind>::generate().unwrap();
                let signature = key.sign(b"", MESSAGE).unwrap();
                (
                    key.public_key().as_ref().to_vec(),
                    signature.as_ref().to_vec(),
                )
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            fn openssl_key() -> (openssl::pkey::PKey<openssl::pkey::Public>, Vec<u8>) {
                use openssl::pkey::{KeyType, PKey};
                ossl::require();
                let (public_key, signature) = signed();
                let key = PKey::public_key_from_raw_bytes_ex(
                    None,
                    KeyType::$openssl_type,
                    None,
                    &public_key,
                )
                .unwrap();
                (key, signature)
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            #[bench(setup = openssl_key)]
            fn openssl((key, signature): &(openssl::pkey::PKey<openssl::pkey::Public>, Vec<u8>)) {
                let mut verifier = openssl::sign::Verifier::new_without_digest(key).unwrap();
                assert!(verifier.verify_oneshot(signature, MESSAGE).unwrap());
            }

            fn aws_key() -> (aws_lc_rs::signature::ParsedPublicKey, Vec<u8>) {
                use aws_lc_rs::signature::{ParsedPublicKey, $aws_verify};
                let (public_key, signature) = signed();
                (
                    ParsedPublicKey::new(&$aws_verify, &public_key).unwrap(),
                    signature,
                )
            }

            #[bench(setup = aws_key)]
            fn aws_lc_rs((key, signature): &(aws_lc_rs::signature::ParsedPublicKey, Vec<u8>)) {
                key.verify_sig(MESSAGE, signature).unwrap();
            }

            fn libcrux_key() -> (libcrux_ml_dsa::$libcrux::$libcrux_key, Vec<u8>) {
                use libcrux_ml_dsa::MLDSAVerificationKey;
                let (public_key, signature) = signed();
                (
                    MLDSAVerificationKey::new(public_key.as_slice().try_into().unwrap()),
                    signature,
                )
            }

            #[bench(setup = libcrux_key)]
            fn libcrux((key, signature): &(libcrux_ml_dsa::$libcrux::$libcrux_key, Vec<u8>)) {
                use libcrux_ml_dsa::MLDSASignature;
                let signature = MLDSASignature::new(signature.as_slice().try_into().unwrap());
                libcrux_ml_dsa::$libcrux::verify(key, MESSAGE, b"", &signature).unwrap();
            }

            fn rustcrypto_key() -> (ml_dsa::VerifyingKey<ml_dsa::$rustcrypto>, Vec<u8>) {
                use ml_dsa::{EncodedVerifyingKey, VerifyingKey, $rustcrypto};
                let (public_key, signature) = signed();
                let key = VerifyingKey::<$rustcrypto>::decode(
                    &EncodedVerifyingKey::<$rustcrypto>::try_from(public_key.as_slice()).unwrap(),
                );
                (key, signature)
            }

            #[bench(setup = rustcrypto_key)]
            fn rustcrypto((key, signature): &(ml_dsa::VerifyingKey<ml_dsa::$rustcrypto>, Vec<u8>)) {
                use ml_dsa::{Signature, Verifier, $rustcrypto};
                let signature = Signature::<$rustcrypto>::try_from(signature.as_slice()).unwrap();
                key.verify(MESSAGE, &signature).unwrap();
            }

            fn rind_key() -> Dit<(rind::ml_dsa::PublicKey<rind::ml_dsa::$rind>, Vec<u8>)> {
                use rind::ml_dsa::{PublicKey, $rind};
                let (public_key, signature) = signed();
                Dit::hold((PublicKey::<$rind>::new(&public_key).unwrap(), signature))
            }

            #[bench(setup = rind_key)]
            fn rind(fixture: &Dit<(rind::ml_dsa::PublicKey<rind::ml_dsa::$rind>, Vec<u8>)>) {
                let (key, signature) = &**fixture;
                key.verify(b"", MESSAGE, signature).unwrap();
            }

            fn vg_key() -> (verified_garbage::$vg::$vg_verifying, Vec<u8>) {
                use verified_garbage::$vg::$vg_verifying;
                let (public_key, signature) = signed();
                (
                    $vg_verifying::from_bytes(public_key.as_slice().try_into().unwrap()),
                    signature,
                )
            }

            // Not `prepare`d, as signing's row is not.
            #[bench(setup = vg_key)]
            fn verified_garbage(
                (key, signature): &(verified_garbage::$vg::$vg_verifying, Vec<u8>),
            ) {
                let signature = signature.as_slice().try_into().unwrap();
                key.verify(MESSAGE, b"", signature).unwrap();
            }
        }

        // Load a public key and verify one signature with it, as a TLS
        // handshake does with its peer's certificate.
        mod $load_verify {
            use swole::bench;

            use super::*;

            /// A rind public key's encoding and a signature it verifies.
            fn signed() -> (Vec<u8>, Vec<u8>) {
                use rind::ml_dsa::{KeyPair, $rind};
                let key = KeyPair::<$rind>::generate().unwrap();
                let signature = key.sign(b"", MESSAGE).unwrap();
                (
                    key.public_key().as_ref().to_vec(),
                    signature.as_ref().to_vec(),
                )
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            fn openssl_signed() -> (Vec<u8>, Vec<u8>) {
                ossl::require();
                signed()
            }

            #[cfg(all(feature = "__bench_openssl", target_family = "unix"))]
            #[bench(setup = openssl_signed)]
            fn openssl((public_key, signature): &(Vec<u8>, Vec<u8>)) {
                use openssl::pkey::{KeyType, PKey};
                let key = PKey::public_key_from_raw_bytes_ex(
                    None,
                    KeyType::$openssl_type,
                    None,
                    public_key,
                )
                .unwrap();
                let mut verifier = openssl::sign::Verifier::new_without_digest(&key).unwrap();
                assert!(verifier.verify_oneshot(signature, MESSAGE).unwrap());
            }

            #[bench(setup = signed)]
            fn aws_lc_rs((public_key, signature): &(Vec<u8>, Vec<u8>)) {
                use aws_lc_rs::signature::{ParsedPublicKey, $aws_verify};
                let key = ParsedPublicKey::new(&$aws_verify, public_key).unwrap();
                key.verify_sig(MESSAGE, signature).unwrap();
            }

            #[bench(setup = signed)]
            fn libcrux((public_key, signature): &(Vec<u8>, Vec<u8>)) {
                use libcrux_ml_dsa::{MLDSASignature, MLDSAVerificationKey};
                let key = MLDSAVerificationKey::new(public_key.as_slice().try_into().unwrap());
                let signature = MLDSASignature::new(signature.as_slice().try_into().unwrap());
                libcrux_ml_dsa::$libcrux::verify(&key, MESSAGE, b"", &signature).unwrap();
            }

            #[bench(setup = signed)]
            fn rustcrypto((public_key, signature): &(Vec<u8>, Vec<u8>)) {
                use ml_dsa::{EncodedVerifyingKey, Signature, Verifier, VerifyingKey, $rustcrypto};
                let key = VerifyingKey::<$rustcrypto>::decode(
                    &EncodedVerifyingKey::<$rustcrypto>::try_from(public_key.as_slice()).unwrap(),
                );
                let signature = Signature::<$rustcrypto>::try_from(signature.as_slice()).unwrap();
                key.verify(MESSAGE, &signature).unwrap();
            }

            fn rind_signed() -> Dit<(Vec<u8>, Vec<u8>)> {
                Dit::hold(signed())
            }

            #[bench(setup = rind_signed)]
            fn rind(fixture: &Dit<(Vec<u8>, Vec<u8>)>) {
                use rind::ml_dsa::{PublicKey, $rind};
                let (public_key, signature) = &**fixture;
                let key = PublicKey::<$rind>::new(public_key).unwrap();
                key.verify(b"", MESSAGE, signature).unwrap();
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
ml_dsa!(
    mldsa44_keygen, mldsa44_sign, mldsa44_verify, mldsa44_load_verify,
    rind: MlDsa44,
    aws_lc_rs: ML_DSA_44_SIGNING, ML_DSA_44,
    libcrux: ml_dsa_44, MLDSA44KeyPair, MLDSA44VerificationKey,
    rustcrypto: MlDsa44,
    verified_garbage: mldsa44, SigningKey44, VerifyingKey44,
    openssl: c"ML-DSA-44", ML_DSA_44,
);

#[cfg(not(target_arch = "xtensa"))]
ml_dsa!(
    mldsa65_keygen, mldsa65_sign, mldsa65_verify, mldsa65_load_verify,
    rind: MlDsa65,
    aws_lc_rs: ML_DSA_65_SIGNING, ML_DSA_65,
    libcrux: ml_dsa_65, MLDSA65KeyPair, MLDSA65VerificationKey,
    rustcrypto: MlDsa65,
    verified_garbage: mldsa65, SigningKey65, VerifyingKey65,
    openssl: c"ML-DSA-65", ML_DSA_65,
);

#[cfg(not(target_arch = "xtensa"))]
ml_dsa!(
    mldsa87_keygen, mldsa87_sign, mldsa87_verify, mldsa87_load_verify,
    rind: MlDsa87,
    aws_lc_rs: ML_DSA_87_SIGNING, ML_DSA_87,
    libcrux: ml_dsa_87, MLDSA87KeyPair, MLDSA87VerificationKey,
    rustcrypto: MlDsa87,
    verified_garbage: mldsa87, SigningKey87, VerifyingKey87,
    openssl: c"ML-DSA-87", ML_DSA_87,
);

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
