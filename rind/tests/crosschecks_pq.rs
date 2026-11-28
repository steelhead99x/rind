//! Differential tests of ML-KEM, ML-DSA, and SLH-DSA against aws-lc and
//! independent oracles, which Miri cannot run.
#![cfg(not(any(miri, target_family = "wasm")))]

mod common;
use common::der;

mod mlkem {
    use aws_lc_rs::kem::{
        Algorithm, AlgorithmId, Ciphertext, DecapsulationKey, ML_KEM_512, ML_KEM_768, ML_KEM_1024,
    };
    use proptest::prelude::*;
    use rind::kem;

    // aws-lc-rs decapsulates what we encapsulate to its key.
    fn encapsulated_by_ours<A: kem::Algorithm>(
        algorithm: &'static Algorithm<AlgorithmId>,
    ) -> Result<(), TestCaseError> {
        let theirs = DecapsulationKey::generate(algorithm).unwrap();
        let theirs_public = theirs.encapsulation_key().unwrap().key_bytes().unwrap();
        let (ciphertext, secret) = kem::EncapsulationKey::<A>::new(theirs_public.as_ref())
            .unwrap()
            .encapsulate()
            .unwrap();
        let theirs_secret = theirs
            .decapsulate(Ciphertext::from(ciphertext.as_ref()))
            .unwrap();
        prop_assert_eq!(secret.as_ref(), theirs_secret.as_ref());
        Ok(())
    }

    // Each case generates a key, which is slow under emulation.
    proptest! {
        #![proptest_config(ProptestConfig::with_cases(32))]

        #[test]
        fn encapsulated_by_ours_512(_case in any::<u8>()) {
            encapsulated_by_ours::<kem::MlKem512>(&ML_KEM_512)?;
        }

        #[test]
        fn encapsulated_by_ours_768(_case in any::<u8>()) {
            encapsulated_by_ours::<kem::MlKem768>(&ML_KEM_768)?;
        }

        #[test]
        fn encapsulated_by_ours_1024(_case in any::<u8>()) {
            encapsulated_by_ours::<kem::MlKem1024>(&ML_KEM_1024)?;
        }
    }
}

/// aws-lc's ML-DSA under a context string, which aws-lc-rs does not expose,
/// through aws-lc-sys's `EVP_DigestSign` and `EVP_DigestVerify`.
mod aws_lc_context {
    use core::ptr::{null, null_mut};

    use aws_lc_sys::{
        EVP_DigestSign, EVP_DigestSignInit, EVP_DigestVerify, EVP_DigestVerifyInit, EVP_MD_CTX,
        EVP_MD_CTX_free, EVP_MD_CTX_new, EVP_PKEY, EVP_PKEY_CTX,
        EVP_PKEY_CTX_set1_signature_context_string, EVP_PKEY_free,
        EVP_PKEY_pqdsa_new_raw_private_key,
    };

    pub struct Key(*mut EVP_PKEY);

    impl Key {
        /// The key aws-lc expands from `seed`, under parameter set `nid`.
        pub fn from_seed(nid: i32, seed: &[u8]) -> Self {
            // SAFETY: `seed` is readable for its length.
            let key = unsafe { EVP_PKEY_pqdsa_new_raw_private_key(nid, seed.as_ptr(), seed.len()) };
            assert!(!key.is_null());
            Self(key)
        }

        /// Runs `operation` on a context bound to this key and `context`,
        /// or `None` where aws-lc refuses the context.
        fn with<T>(
            &self,
            context: &[u8],
            init: unsafe extern "C" fn(
                *mut EVP_MD_CTX,
                *mut *mut EVP_PKEY_CTX,
                *const aws_lc_sys::EVP_MD,
                *mut aws_lc_sys::ENGINE,
                *mut EVP_PKEY,
            ) -> core::ffi::c_int,
            operation: impl FnOnce(*mut EVP_MD_CTX) -> T,
        ) -> Option<T> {
            // SAFETY: each pointer is live for the call it is passed to, and
            // the context is freed once.
            unsafe {
                let ctx = EVP_MD_CTX_new();
                let mut pkey_ctx = null_mut();
                let mut result = None;
                if init(ctx, &mut pkey_ctx, null(), null_mut(), self.0) == 1
                    && EVP_PKEY_CTX_set1_signature_context_string(
                        pkey_ctx,
                        context.as_ptr(),
                        context.len(),
                    ) == 1
                {
                    result = Some(operation(ctx));
                }
                EVP_MD_CTX_free(ctx);
                result
            }
        }

        /// Signs `message` under `context`, or `None` if aws-lc refuses.
        pub fn sign(&self, context: &[u8], message: &[u8]) -> Option<Vec<u8>> {
            self.with(context, EVP_DigestSignInit, |ctx| {
                let mut len = 0;
                // SAFETY: a null output asks for the length, and the buffer
                // is as long as that says.
                unsafe {
                    assert_eq!(
                        EVP_DigestSign(ctx, null_mut(), &mut len, message.as_ptr(), message.len()),
                        1
                    );
                    let mut signature = vec![0; len];
                    assert_eq!(
                        EVP_DigestSign(
                            ctx,
                            signature.as_mut_ptr(),
                            &mut len,
                            message.as_ptr(),
                            message.len()
                        ),
                        1
                    );
                    signature.truncate(len);
                    signature
                }
            })
        }

        /// Whether `signature` verifies over `message` under `context`.
        pub fn verify(&self, context: &[u8], message: &[u8], signature: &[u8]) -> bool {
            self.with(context, EVP_DigestVerifyInit, |ctx| {
                // SAFETY: each slice is readable for its length.
                unsafe {
                    EVP_DigestVerify(
                        ctx,
                        signature.as_ptr(),
                        signature.len(),
                        message.as_ptr(),
                        message.len(),
                    ) == 1
                }
            })
            .unwrap_or(false)
        }
    }

    impl Drop for Key {
        fn drop(&mut self) {
            // SAFETY: the key is live, and freed once.
            unsafe { EVP_PKEY_free(self.0) };
        }
    }
}

/// ML-DSA against aws-lc-rs, which runs mldsa-native with the same
/// s2n-bignum kernels, and against RustCrypto's, which shares no code with
/// rind.
macro_rules! ml_dsa_crosschecks {
    ($set:ident, $signing:ident, $verify:ident, $rustcrypto:ident, $nid:ident) => {
        use aws_lc_rs::encoding::{AsDer, AsRawBytes};
        use aws_lc_rs::signature::{KeyPair, PqdsaKeyPair, UnparsedPublicKey, $signing};
        use proptest::collection::vec;
        use proptest::prelude::*;
        use proptest::sample::Index;
        use rind::ml_dsa::{KeyPair as MlDsaKeyPair, PublicKey, $set};

        // Each case makes several signatures, which are slow in a debug
        // build and under emulation.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(16))]

            #[test]
            fn sign_verify(
                seed in any::<[u8; 32]>(),
                message in vec(any::<u8>(), 0..300),
                flip in any::<Option<Index>>(),
            ) {
                // One seed gives both sides the same key and encodings.
                let theirs = PqdsaKeyPair::from_seed(&$signing, &seed).unwrap();
                let ours = MlDsaKeyPair::<$set>::from_seed(&seed).unwrap();
                let public = theirs.public_key().as_ref();
                let ours_public = ours.public_key();
                prop_assert_eq!(ours_public.as_ref(), public);
                let spki = theirs.public_key().as_der().unwrap();
                let ours_spki = ours_public.to_spki();
                prop_assert_eq!(ours_spki.as_ref(), spki.as_ref());
                let (ours_pkcs8, theirs_pkcs8) = (ours.to_pkcs8(), theirs.to_pkcs8v1().unwrap());
                prop_assert_eq!(ours_pkcs8.as_ref(), theirs_pkcs8.as_ref());

                // Signing is hedged, so each verifies the other's signature
                // rather than matching its bytes.
                let ours_signature = ours.sign(&[], &message).unwrap();
                UnparsedPublicKey::new(&aws_lc_rs::signature::$verify, public)
                    .verify(&message, ours_signature.as_ref())
                    .unwrap();
                let mut signature = vec![0; $signing.signature_len()];
                theirs.sign(&message, &mut signature).unwrap();
                let verifier = PublicKey::<$set>::from_spki(spki.as_ref()).unwrap();
                verifier.verify(&[], &message, &signature).unwrap();

                // Both refuse it with any one bit flipped.
                if let Some(flip) = flip {
                    let bit = flip.index(signature.len() * 8);
                    signature[bit / 8] ^= 1 << (bit % 8);
                    prop_assert!(verifier.verify(&[], &message, &signature).is_err());
                    prop_assert!(
                        UnparsedPublicKey::new(&aws_lc_rs::signature::$verify, public)
                            .verify(&message, &signature)
                            .is_err()
                    );
                }
            }

            /// RustCrypto derives the same public key from the seed, and
            /// each verifies the other's signature and refuses it altered.
            #[test]
            fn oracle(
                seed in any::<[u8; 32]>(),
                context in vec(any::<u8>(), 0..=255),
                message in vec(any::<u8>(), 0..300),
                flip in any::<Index>(),
            ) {
                let ours = MlDsaKeyPair::<$set>::from_seed(&seed).unwrap();
                let theirs = ml_dsa::ExpandedSigningKey::<ml_dsa::$rustcrypto>::from_seed(&seed.into());
                let their_public = theirs.verifying_key();
                prop_assert_eq!(ours.public_key().as_ref(), &their_public.encode()[..]);

                let ours_signature = ours.sign(&context, &message).unwrap();
                let decoded = ml_dsa::Signature::try_from(ours_signature.as_ref()).unwrap();
                prop_assert!(their_public.verify_with_context(&message, &context, &decoded));
                let mut signature = theirs.sign_deterministic(&message, &context).unwrap().encode().to_vec();
                let verifier = ours.public_key();
                verifier.verify(&context, &message, &signature).unwrap();

                let bit = flip.index(signature.len() * 8);
                signature[bit / 8] ^= 1 << (bit % 8);
                prop_assert!(verifier.verify(&context, &message, &signature).is_err());
                let refused = ml_dsa::Signature::try_from(signature.as_slice())
                    .is_ok_and(|signature| their_public.verify_with_context(&message, &context, &signature));
                prop_assert!(!refused);
            }

            /// aws-lc signs and verifies under a context as rind does, and
            /// neither takes a context past 255 bytes or verifies under a
            /// different one.
            #[test]
            fn context(
                seed in any::<[u8; 32]>(),
                context in vec(any::<u8>(), 0..=255),
                message in vec(any::<u8>(), 0..300),
            ) {
                let theirs = super::aws_lc_context::Key::from_seed(aws_lc_sys::$nid, &seed);
                let ours = MlDsaKeyPair::<$set>::from_seed(&seed).unwrap();
                let public = ours.public_key();

                let signature = ours.sign(&context, &message).unwrap();
                prop_assert!(theirs.verify(&context, &message, signature.as_ref()));
                let signature = theirs.sign(&context, &message).unwrap();
                public.verify(&context, &message, &signature).unwrap();

                // Dropping its first byte, or adding one to the empty
                // context, makes another context.
                let other = if context.is_empty() { vec![0] } else { context[1..].to_vec() };
                prop_assert!(public.verify(&other, &message, &signature).is_err());
                prop_assert!(!theirs.verify(&other, &message, &signature));

                let long = [&context[..], &[0; 256][..]].concat();
                prop_assert!(ours.sign(&long, &message).is_err());
                prop_assert!(theirs.sign(&long, &message).is_none());
                prop_assert!(public.verify(&long, &message, &signature).is_err());
                prop_assert!(!theirs.verify(&long, &message, &signature));
            }

            /// Both load the other's expanded key, which has no seed, and
            /// sign alike with it.
            #[test]
            fn expanded(seed in any::<[u8; 32]>(), message in vec(any::<u8>(), 0..300)) {
                let theirs = PqdsaKeyPair::from_seed(&$signing, &seed).unwrap();
                let expanded = theirs.private_key().as_raw_bytes().unwrap();
                let expanded = expanded.as_ref();
                let ours = MlDsaKeyPair::<$set>::from_pkcs8(&expanded_pkcs8(
                    theirs_pkcs8_prefix(&theirs),
                    expanded,
                ))
                .unwrap();
                prop_assert!(ours.to_seed().is_none());
                let ours_public = ours.public_key();
                prop_assert_eq!(ours_public.as_ref(), theirs.public_key().as_ref());

                // Ours writes the expanded form, which theirs loads.
                let ours_pkcs8 = ours.to_pkcs8();
                let reloaded = PqdsaKeyPair::from_pkcs8(&$signing, ours_pkcs8.as_ref()).unwrap();
                prop_assert_eq!(reloaded.public_key().as_ref(), theirs.public_key().as_ref());
                let signature = ours.sign(&[], &message).unwrap();
                UnparsedPublicKey::new(&aws_lc_rs::signature::$verify, theirs.public_key().as_ref())
                    .verify(&message, signature.as_ref())
                    .unwrap();
            }
        }

        /// The PKCS#8 v1 header up to the private key, from the seed form
        /// aws-lc writes: version and algorithm identifier.
        fn theirs_pkcs8_prefix(theirs: &PqdsaKeyPair) -> Vec<u8> {
            let pkcs8 = theirs.to_pkcs8v1().unwrap();
            // SEQUENCE { INTEGER 0, AlgorithmIdentifier (13 bytes), ... }
            pkcs8.as_ref()[2..2 + 3 + 13].to_vec()
        }

        /// A PKCS#8 v1 key in RFC 9881's expanded form.
        fn expanded_pkcs8(prefix: Vec<u8>, expanded: &[u8]) -> Vec<u8> {
            let inner = super::der(0x04, expanded);
            let body = [prefix, super::der(0x04, &inner)].concat();
            super::der(0x30, &body)
        }
    };
}

mod ml_dsa_44 {
    ml_dsa_crosschecks!(MlDsa44, ML_DSA_44_SIGNING, ML_DSA_44, MlDsa44, NID_MLDSA44);
}

mod ml_dsa_65 {
    ml_dsa_crosschecks!(MlDsa65, ML_DSA_65_SIGNING, ML_DSA_65, MlDsa65, NID_MLDSA65);
}

mod ml_dsa_87 {
    ml_dsa_crosschecks!(MlDsa87, ML_DSA_87_SIGNING, ML_DSA_87, MlDsa87, NID_MLDSA87);
}

// aws-lc-rs has no SLH-DSA, so RustCrypto's and integritychain's `fips205`
// stand in for it. Signing is randomized, so each verifies the others'
// signatures rather than matching their bytes; the ACVP vectors match bytes.
macro_rules! slh_dsa_crosschecks {
    ($set:ident, $rustcrypto:ident, $fips205:ident, $n:literal) => {
        use fips205::traits::{KeyGen, SerDes, Signer as _, Verifier as _};
        use pkcs8::{EncodePrivateKey, EncodePublicKey};
        use proptest::collection::vec;
        use proptest::prelude::*;
        use proptest::sample::Index;
        use rind::slh_dsa::{KeyPair, PublicKey, $set};
        use slh_dsa::signature::Verifier;

        type Theirs = slh_dsa::SigningKey<slh_dsa::$rustcrypto>;

        // RustCrypto's is generic, so it compiles into this test at the
        // test's own optimisation level, and unoptimised it signs for
        // minutes. The release run, which every tier makes, takes these.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(4))]

            #[test]
            #[cfg_attr(debug_assertions, ignore = "RustCrypto signs for minutes unoptimised")]
            fn sign_verify(
                seeds in any::<[[u8; $n]; 3]>(),
                addrnd in any::<[u8; $n]>(),
                message in vec(any::<u8>(), 0..300),
                flip in any::<Option<Index>>(),
            ) {
                // The same seeds give all three the same key and encodings.
                let [sk_seed, sk_prf, pk_seed] = seeds;
                let theirs = Theirs::slh_keygen_internal(&sk_seed, &sk_prf, &pk_seed);
                let (fips_public, fips_private) =
                    fips205::$fips205::KG::keygen_from_seed(&sk_seed, &sk_prf, &pk_seed);
                prop_assert_eq!(
                    &fips_private.clone().into_bytes()[..],
                    &theirs.to_bytes()[..]
                );
                let pkcs8 = theirs.to_pkcs8_der().unwrap();
                let ours = KeyPair::<$set>::from_pkcs8(pkcs8.as_bytes()).unwrap();
                let ours_pkcs8 = ours.to_pkcs8();
                prop_assert_eq!(ours_pkcs8.as_ref(), pkcs8.as_bytes());
                let spki = theirs.as_ref().to_public_key_der().unwrap();
                let ours_spki = ours.public_key().to_spki();
                prop_assert_eq!(ours_spki.as_ref(), spki.as_bytes());

                // Each verifies the others' signatures.
                let ours_signature = ours.sign(&message).unwrap();
                let parsed = slh_dsa::Signature::try_from(ours_signature.as_ref()).unwrap();
                theirs.as_ref().verify(&message, &parsed).unwrap();
                prop_assert!(fips_public.verify(
                    &message,
                    ours_signature.as_ref().try_into().unwrap(),
                    b""
                ));
                let verifier = PublicKey::<$set>::from_spki(spki.as_bytes()).unwrap();
                let mut signature = theirs
                    .try_sign_with_context(&message, b"", Some(&addrnd))
                    .unwrap()
                    .to_vec();
                verifier.verify(&message, &signature).unwrap();
                let fips_signature = fips_private.try_sign(&message, b"", true).unwrap();
                verifier.verify(&message, &fips_signature).unwrap();

                // All refuse it with any one bit flipped.
                if let Some(flip) = flip {
                    let bit = flip.index(signature.len() * 8);
                    signature[bit / 8] ^= 1 << (bit % 8);
                    prop_assert!(verifier.verify(&message, &signature).is_err());
                    let parsed = slh_dsa::Signature::try_from(signature.as_slice()).unwrap();
                    prop_assert!(theirs.as_ref().verify(&message, &parsed).is_err());
                    prop_assert!(!fips_public.verify(
                        &message,
                        signature.as_slice().try_into().unwrap(),
                        b""
                    ));
                }
            }
        }
    };
}

mod slh_dsa_sha2_128s {
    slh_dsa_crosschecks!(SlhDsaSha2_128s, Sha2_128s, slh_dsa_sha2_128s, 16);
}

mod slh_dsa_sha2_128f {
    slh_dsa_crosschecks!(SlhDsaSha2_128f, Sha2_128f, slh_dsa_sha2_128f, 16);
}

mod slh_dsa_sha2_192s {
    slh_dsa_crosschecks!(SlhDsaSha2_192s, Sha2_192s, slh_dsa_sha2_192s, 24);
}

mod slh_dsa_sha2_192f {
    slh_dsa_crosschecks!(SlhDsaSha2_192f, Sha2_192f, slh_dsa_sha2_192f, 24);
}

mod slh_dsa_sha2_256s {
    slh_dsa_crosschecks!(SlhDsaSha2_256s, Sha2_256s, slh_dsa_sha2_256s, 32);
}

mod slh_dsa_sha2_256f {
    slh_dsa_crosschecks!(SlhDsaSha2_256f, Sha2_256f, slh_dsa_sha2_256f, 32);
}

mod slh_dsa_shake_128s {
    slh_dsa_crosschecks!(SlhDsaShake128s, Shake128s, slh_dsa_shake_128s, 16);
}

mod slh_dsa_shake_128f {
    slh_dsa_crosschecks!(SlhDsaShake128f, Shake128f, slh_dsa_shake_128f, 16);
}

mod slh_dsa_shake_192s {
    slh_dsa_crosschecks!(SlhDsaShake192s, Shake192s, slh_dsa_shake_192s, 24);
}

mod slh_dsa_shake_192f {
    slh_dsa_crosschecks!(SlhDsaShake192f, Shake192f, slh_dsa_shake_192f, 24);
}

mod slh_dsa_shake_256s {
    slh_dsa_crosschecks!(SlhDsaShake256s, Shake256s, slh_dsa_shake_256s, 32);
}

mod slh_dsa_shake_256f {
    slh_dsa_crosschecks!(SlhDsaShake256f, Shake256f, slh_dsa_shake_256f, 32);
}
