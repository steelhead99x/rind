// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! A signing key pair of whichever type a PKCS#8 document holds.

use core::fmt;

#[cfg(feature = "ml-dsa")]
use super::ml_dsa;
#[cfg(feature = "slh-dsa")]
use super::slh_dsa;
use super::{ecdsa, ed25519, rsa};
use crate::error::{Error, KeyFormatError};
use crate::high::asn1::{self, Type, oid, pkix};
use crate::low;
#[cfg(feature = "ml-dsa")]
use crate::mid::mldsa::{MlDsa44, MlDsa65, MlDsa87};
#[cfg(feature = "slh-dsa")]
use crate::mid::slhdsa::{
    SlhDsaSha2_128f, SlhDsaSha2_128s, SlhDsaSha2_192f, SlhDsaSha2_192s, SlhDsaSha2_256f,
    SlhDsaSha2_256s, SlhDsaShake128f, SlhDsaShake128s, SlhDsaShake192f, SlhDsaShake192s,
    SlhDsaShake256f, SlhDsaShake256s,
};

/// Declares [`KeyPair`] with one variant per ML-DSA and SLH-DSA parameter
/// set built in, each named after its Cargo feature, and the table that loads
/// each by its OID.
macro_rules! key_pair {
    ($($feature:literal $variant:ident($module:ident::<$set:ident>) = $oid:ident,)*) => {
        /// A signing key pair of whichever type a PKCS#8 document holds, as
        /// [`KeyPair::from_pkcs8`] loads it.
        ///
        /// Each variant holds that type's own key pair, which a caller moves
        /// out to sign with. Each wipes itself on drop.
        ///
        /// ```
        /// # fn main() -> Result<(), rind::Error> {
        /// let pkcs8 = rind::ed25519::KeyPair::generate()?.to_pkcs8();
        /// let signature = match rind::KeyPair::from_pkcs8(pkcs8.as_ref())? {
        ///     rind::KeyPair::Ed25519(key) => key.sign(b"hello"),
        ///     _ => return Err(rind::Error::Unsupported),
        /// };
        /// # Ok(())
        /// # }
        /// ```
        #[non_exhaustive]
        #[allow(clippy::large_enum_variant)]
        pub enum KeyPair {
            /// An ECDSA key on P-256, which signs with
            /// [`P256_SHA256_ASN1`](crate::ecdsa::sign::P256_SHA256_ASN1).
            EcdsaP256(ecdsa::KeyPair),
            /// An ECDSA key on P-384, which signs with
            /// [`P384_SHA384_ASN1`](crate::ecdsa::sign::P384_SHA384_ASN1).
            EcdsaP384(ecdsa::KeyPair),
            /// An ECDSA key on P-521, which signs with
            /// [`P521_SHA512_ASN1`](crate::ecdsa::sign::P521_SHA512_ASN1).
            EcdsaP521(ecdsa::KeyPair),
            /// An Ed25519 key.
            Ed25519(ed25519::KeyPair),
            /// An RSA key.
            Rsa(rsa::KeyPair),
            $(
                #[cfg(feature = $feature)]
                #[doc = concat!("A key of parameter set [`", stringify!($set), "`](crate::", stringify!($module), "::", stringify!($set), ").")]
                $variant($module::KeyPair<$set>),
            )*
        }

        /// The ML-DSA and SLH-DSA OIDs, each with its loader.
        static POST_QUANTUM: &[(&asn1::ObjectId, fn(&[u8]) -> Result<KeyPair, Error>)] = &[$(
            #[cfg(feature = $feature)]
            (
                $module::KeyPair::<$set>::oid(),
                |der| $module::KeyPair::<$set>::from_pkcs8(der).map(KeyPair::$variant),
            ),
        )*];

        /// The OIDs of the parameter sets this build leaves out, each with
        /// the Cargo feature that builds it in.
        #[cfg(not(all(feature = "ml-dsa", feature = "slh-dsa")))]
        static LEFT_OUT: &[(&asn1::ObjectId, &str)] = &[$(
            #[cfg(not(feature = $feature))]
            (&oid::$oid, $feature),
        )*];

        impl fmt::Debug for KeyPair {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                let (variant, key): (_, &dyn fmt::Debug) = match self {
                    Self::EcdsaP256(key) => ("EcdsaP256", key),
                    Self::EcdsaP384(key) => ("EcdsaP384", key),
                    Self::EcdsaP521(key) => ("EcdsaP521", key),
                    Self::Ed25519(key) => ("Ed25519", key),
                    Self::Rsa(key) => ("Rsa", key),
                    $(
                        #[cfg(feature = $feature)]
                        Self::$variant(key) => (stringify!($variant), key),
                    )*
                };
                f.debug_tuple(variant).field(key).finish()
            }
        }
    };
}

key_pair! {
    "ml-dsa" MlDsa44(ml_dsa::<MlDsa44>) = id_ml_dsa_44,
    "ml-dsa" MlDsa65(ml_dsa::<MlDsa65>) = id_ml_dsa_65,
    "ml-dsa" MlDsa87(ml_dsa::<MlDsa87>) = id_ml_dsa_87,
    "slh-dsa" SlhDsaSha2_128s(slh_dsa::<SlhDsaSha2_128s>) = id_slh_dsa_sha2_128s,
    "slh-dsa" SlhDsaSha2_128f(slh_dsa::<SlhDsaSha2_128f>) = id_slh_dsa_sha2_128f,
    "slh-dsa" SlhDsaSha2_192s(slh_dsa::<SlhDsaSha2_192s>) = id_slh_dsa_sha2_192s,
    "slh-dsa" SlhDsaSha2_192f(slh_dsa::<SlhDsaSha2_192f>) = id_slh_dsa_sha2_192f,
    "slh-dsa" SlhDsaSha2_256s(slh_dsa::<SlhDsaSha2_256s>) = id_slh_dsa_sha2_256s,
    "slh-dsa" SlhDsaSha2_256f(slh_dsa::<SlhDsaSha2_256f>) = id_slh_dsa_sha2_256f,
    "slh-dsa" SlhDsaShake128s(slh_dsa::<SlhDsaShake128s>) = id_slh_dsa_shake_128s,
    "slh-dsa" SlhDsaShake128f(slh_dsa::<SlhDsaShake128f>) = id_slh_dsa_shake_128f,
    "slh-dsa" SlhDsaShake192s(slh_dsa::<SlhDsaShake192s>) = id_slh_dsa_shake_192s,
    "slh-dsa" SlhDsaShake192f(slh_dsa::<SlhDsaShake192f>) = id_slh_dsa_shake_192f,
    "slh-dsa" SlhDsaShake256s(slh_dsa::<SlhDsaShake256s>) = id_slh_dsa_shake_256s,
    "slh-dsa" SlhDsaShake256f(slh_dsa::<SlhDsaShake256f>) = id_slh_dsa_shake_256f,
}

impl KeyPair {
    /// Loads a PKCS#8 private key of any type rind signs with, read from its
    /// algorithm identifier.
    ///
    /// Each type accepts what its own `from_pkcs8` does. An ECDSA key's
    /// curve picks its hash, with ASN.1 signatures, since PKCS#8 names no
    /// hash; load it with [`ecdsa::KeyPair::from_pkcs8`] to name another
    /// algorithm. A key of another algorithm, such as X25519, is refused,
    /// naming it if rind knows it, as is an ML-DSA or SLH-DSA key in a build
    /// without its Cargo feature, naming the feature.
    ///
    /// Calling this links every signing algorithm's code, so a program that
    /// loads no ML-DSA or SLH-DSA keys this way shrinks by leaving out the
    /// `ml-dsa` and `slh-dsa` features.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        let key = pkix::OneAsymmetricKey::from_bytes(der).map_err(KeyFormatError::Asn1)?;
        let algorithm = &key.privateKeyAlgorithm;
        let id = &algorithm.algorithm;

        if *id == oid::id_ecPublicKey {
            let Some(asn1::Any::ObjectId(curve)) = &algorithm.parameters else {
                return Err(KeyFormatError::MismatchedPkcs8Parameters.into());
            };
            let (signing, variant): (_, fn(_) -> _) = if *curve == oid::id_prime256v1 {
                (&ecdsa::sign::P256_SHA256_ASN1, Self::EcdsaP256)
            } else if *curve == oid::secp384r1 {
                (&ecdsa::sign::P384_SHA384_ASN1, Self::EcdsaP384)
            } else if *curve == oid::secp521r1 {
                (&ecdsa::sign::P521_SHA512_ASN1, Self::EcdsaP521)
            } else {
                return Err(KeyFormatError::UnsupportedCurve.into());
            };
            return ecdsa::KeyPair::from_pkcs8(signing, der).map(variant);
        }
        if *id == oid::id_ed25519 {
            return ed25519::KeyPair::from_pkcs8(der).map(Self::Ed25519);
        }
        if crate::high::rsa::KEY_ALGORITHMS.contains(&id) {
            return rsa::KeyPair::from_pkcs8(der).map(Self::Rsa);
        }
        if let Some((_, load)) = POST_QUANTUM.iter().find(|(oid, _)| *oid == id) {
            return load(der);
        }
        #[cfg(not(all(feature = "ml-dsa", feature = "slh-dsa")))]
        if let Some(&(_, feature)) = LEFT_OUT.iter().find(|(oid, _)| *oid == id) {
            return Err(KeyFormatError::FeatureDisabled(feature).into());
        }
        if *id == oid::id_X25519 {
            return Err(KeyFormatError::X25519CannotSign.into());
        }
        Err(KeyFormatError::UnknownPkcs8Algorithm.into())
    }
}

// The tests load every key type.
#[cfg(all(test, feature = "ml-dsa", feature = "slh-dsa"))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::high::agreement;
    use crate::high::pkcs8;

    /// The variant's name and its public key's bytes.
    fn describe(key: &KeyPair) -> (&'static str, Vec<u8>) {
        match key {
            KeyPair::EcdsaP256(key) => ("EcdsaP256", key.public_key().as_ref().to_vec()),
            KeyPair::EcdsaP384(key) => ("EcdsaP384", key.public_key().as_ref().to_vec()),
            KeyPair::EcdsaP521(key) => ("EcdsaP521", key.public_key().as_ref().to_vec()),
            KeyPair::Ed25519(key) => ("Ed25519", key.public_key().as_ref().to_vec()),
            KeyPair::Rsa(key) => ("Rsa", key.public_key().as_ref().to_vec()),
            KeyPair::MlDsa44(key) => ("MlDsa44", key.public_key().as_ref().to_vec()),
            KeyPair::MlDsa65(key) => ("MlDsa65", key.public_key().as_ref().to_vec()),
            KeyPair::MlDsa87(key) => ("MlDsa87", key.public_key().as_ref().to_vec()),
            KeyPair::SlhDsaSha2_128f(key) => {
                ("SlhDsaSha2_128f", key.public_key().as_ref().to_vec())
            }
            KeyPair::SlhDsaShake128f(key) => {
                ("SlhDsaShake128f", key.public_key().as_ref().to_vec())
            }
            other => panic!("no test key for {other:?}"),
        }
    }

    /// One key of each type: its PKCS#8, the variant it loads as, and its
    /// own loader's public key.
    type Own = fn(&[u8]) -> Result<Vec<u8>, Error>;

    fn keys() -> Vec<(Vec<u8>, &'static str, Own)> {
        fn ecdsa(signing: &'static ecdsa::SigningAlgorithm, der: &[u8]) -> Result<Vec<u8>, Error> {
            ecdsa::KeyPair::from_pkcs8(signing, der).map(|k| k.public_key().as_ref().to_vec())
        }
        vec![
            (
                include_bytes!("../ecdsa/secp256r1.pkcs8.der").to_vec(),
                "EcdsaP256",
                |der| ecdsa(&ecdsa::sign::P256_SHA256_ASN1, der),
            ),
            (
                include_bytes!("../ecdsa/secp384r1.pkcs8.der").to_vec(),
                "EcdsaP384",
                |der| ecdsa(&ecdsa::sign::P384_SHA384_ASN1, der),
            ),
            (
                include_bytes!("../ecdsa/secp521r1.pkcs8.der").to_vec(),
                "EcdsaP521",
                |der| ecdsa(&ecdsa::sign::P521_SHA512_ASN1, der),
            ),
            (
                include_bytes!("../asn1/testdata/ed25519-p8v2.bin").to_vec(),
                "Ed25519",
                |der| ed25519::KeyPair::from_pkcs8(der).map(|k| k.public_key().as_ref().to_vec()),
            ),
            (
                include_bytes!("../rsa/rsa2048.pkcs8.der").to_vec(),
                "Rsa",
                |der| rsa::KeyPair::from_pkcs8(der).map(|k| k.public_key().as_ref().to_vec()),
            ),
            (
                ml_dsa::KeyPair::<MlDsa44>::generate()
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                "MlDsa44",
                |der| {
                    ml_dsa::KeyPair::<MlDsa44>::from_pkcs8(der)
                        .map(|k| k.public_key().as_ref().to_vec())
                },
            ),
            (
                ml_dsa::KeyPair::<MlDsa65>::generate()
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                "MlDsa65",
                |der| {
                    ml_dsa::KeyPair::<MlDsa65>::from_pkcs8(der)
                        .map(|k| k.public_key().as_ref().to_vec())
                },
            ),
            (
                ml_dsa::KeyPair::<MlDsa87>::generate()
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                "MlDsa87",
                |der| {
                    ml_dsa::KeyPair::<MlDsa87>::from_pkcs8(der)
                        .map(|k| k.public_key().as_ref().to_vec())
                },
            ),
            (
                slh_dsa::KeyPair::<SlhDsaSha2_128f>::generate()
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                "SlhDsaSha2_128f",
                |der| {
                    slh_dsa::KeyPair::<SlhDsaSha2_128f>::from_pkcs8(der)
                        .map(|k| k.public_key().as_ref().to_vec())
                },
            ),
            (
                slh_dsa::KeyPair::<SlhDsaShake128f>::generate()
                    .unwrap()
                    .to_pkcs8()
                    .as_ref()
                    .to_vec(),
                "SlhDsaShake128f",
                |der| {
                    slh_dsa::KeyPair::<SlhDsaShake128f>::from_pkcs8(der)
                        .map(|k| k.public_key().as_ref().to_vec())
                },
            ),
        ]
    }

    #[test]
    fn loads_each_type_as_its_own_loader_does() {
        for (der, variant, own) in keys() {
            let key = KeyPair::from_pkcs8(&der).unwrap();
            assert_eq!(describe(&key), (variant, own(&der).unwrap()));
        }
    }

    // Every one-byte change to a key either leaves its algorithm identifier
    // naming the same type, so the result is that type's own loader's, or
    // makes the identifier name no type rind signs with.
    #[test]
    fn accepts_exactly_what_each_type_does() {
        for (der, variant, own) in keys() {
            // Each SLH-DSA load costs a key generation, which ctgrind's debug
            // build runs too slowly to repeat per byte.
            if crate::test::CTGRIND_DEBUG && variant.starts_with("SlhDsa") {
                continue;
            }
            // Every byte up to the key's first 32 bytes, which cover the
            // algorithm identifier, and a stride past it, so RSA and
            // SLH-DSA stay quick.
            let positions = (0..der.len()).filter(|&i| i < 48 || i % 7 == 0);
            for i in positions {
                for flip in [0x01, 0x80] {
                    let mut der = der.clone();
                    der[i] ^= flip;
                    let any = KeyPair::from_pkcs8(&der);
                    let own = own(&der);
                    match (&any, &own) {
                        (Ok(key), Ok(public)) => {
                            assert_eq!(describe(key), (variant, public.clone()), "{variant} {i}")
                        }
                        (Err(any), Err(own)) => {
                            let renamed = [
                                KeyFormatError::MismatchedPkcs8Algorithm.into(),
                                KeyFormatError::MismatchedPkcs8Parameters.into(),
                            ];
                            assert!(
                                any == own || renamed.contains(own),
                                "{variant} {i}: {any} {own}"
                            );
                        }
                        // The identifier now names another type, which
                        // took the key.
                        (Ok(key), Err(own)) => assert!(
                            *own == KeyFormatError::MismatchedPkcs8Algorithm.into()
                                && describe(key).0 != variant,
                            "{variant} {i}: {key:?} {own}"
                        ),
                        (Err(any), Ok(_)) => panic!("{variant} {i}: refused {any}"),
                    }
                }
            }
        }
    }

    /// A PKCS#8 v1 document naming `algorithm` and `parameters`.
    fn document(algorithm: &asn1::ObjectId, parameters: Option<asn1::Any<'_>>) -> Vec<u8> {
        let mut out = [0; 128];
        pkcs8::Key::construct(&[0x04, 0x00], None, algorithm.clone(), parameters)
            .encode(&mut out)
            .unwrap()
            .to_vec()
    }

    #[test]
    fn refuses_other_algorithms_saying_why() {
        let x25519 = agreement::PrivateKey::generate(&agreement::X25519).unwrap();
        let p256 = asn1::Any::ObjectId(oid::id_prime256v1.clone());
        for (der, error) in [
            (
                x25519.to_pkcs8().as_ref().to_vec(),
                KeyFormatError::X25519CannotSign,
            ),
            (
                document(&oid::id_X25519, None),
                KeyFormatError::X25519CannotSign,
            ),
            (
                document(&oid::id_ecDH, Some(p256)),
                KeyFormatError::UnknownPkcs8Algorithm,
            ),
            (
                document(&oid::id_sha256, None),
                KeyFormatError::UnknownPkcs8Algorithm,
            ),
            (
                document(
                    &oid::id_ecPublicKey,
                    Some(asn1::Any::ObjectId(oid::id_sha256.clone())),
                ),
                KeyFormatError::UnsupportedCurve,
            ),
            (
                document(&oid::id_ecPublicKey, None),
                KeyFormatError::MismatchedPkcs8Parameters,
            ),
            (
                document(&oid::id_ecPublicKey, Some(asn1::Any::Null(asn1::Null))),
                KeyFormatError::MismatchedPkcs8Parameters,
            ),
        ] {
            assert_eq!(KeyPair::from_pkcs8(&der).unwrap_err(), error.into());
        }
    }

    #[test]
    fn keys_stay_secret() {
        // Under `admin/ctgrind`, nothing may branch on or index by a key's
        // scalar or seed while it is told apart and loaded.
        let ml_dsa = ml_dsa::KeyPair::<MlDsa44>::generate().unwrap();
        let ml_dsa_pkcs8 = ml_dsa.to_pkcs8();
        let ml_dsa_seed = ml_dsa.to_seed().unwrap();
        for (der, secret) in [
            (
                &include_bytes!("../ecdsa/secp256r1.pkcs8.der")[..],
                hex::decode("c5a5d2ad8c56caf961268432dff55f66e4da0beb4924587870cda834bf6c6456")
                    .unwrap(),
            ),
            (
                &include_bytes!("../asn1/testdata/ed25519-p8v1.bin")[..],
                include_bytes!("../asn1/testdata/ed25519-p8v1.bin")[16..].to_vec(),
            ),
            (ml_dsa_pkcs8.as_ref(), ml_dsa_seed.as_ref().to_vec()),
        ] {
            // ML-DSA's encodings come out secret, so this finds the seed in
            // public copies, then marks it alone.
            let der = der.to_vec();
            low::ct::public_slice(&der);
            low::ct::public_slice(&secret);
            let at = der.windows(secret.len()).position(|w| w == secret).unwrap();
            low::ct::secret_slice(&der[at..at + secret.len()]);
            let key = KeyPair::from_pkcs8(&der).unwrap();
            low::ct::public_slice(&der);
            drop(key);
        }
    }

    #[test]
    fn refuses_malformed_documents() {
        let ed25519 = include_bytes!("../asn1/testdata/ed25519-p8v2.bin");
        for len in 0..ed25519.len() {
            assert!(KeyPair::from_pkcs8(&ed25519[..len]).is_err(), "{len}");
        }
        for der in [&[0u8; 1024][..], &[0xff; 16], &[0x30, 0x80]] {
            assert!(matches!(
                KeyPair::from_pkcs8(der),
                Err(Error::KeyRejected(_))
            ));
        }
    }
}

#[cfg(all(test, not(all(feature = "ml-dsa", feature = "slh-dsa"))))]
#[cfg_attr(coverage_nightly, coverage(off))]
mod left_out_tests {
    use super::*;
    use crate::high::pkcs8;

    // A key of a parameter set this build leaves out is refused by the name
    // of its feature, and the other types still load.
    #[test]
    fn names_the_feature_of_a_key_left_out() {
        for &(algorithm, feature) in LEFT_OUT {
            let mut out = [0; 128];
            let der = pkcs8::Key::construct(&[0x04, 0x00], None, algorithm.clone(), None)
                .encode(&mut out)
                .unwrap();
            assert_eq!(
                KeyPair::from_pkcs8(der).unwrap_err(),
                KeyFormatError::FeatureDisabled(feature).into()
            );
        }
        let sets = [("ml-dsa", 3), ("slh-dsa", 12)];
        let left_out: usize = sets
            .iter()
            .filter(|(feature, _)| !POST_QUANTUM_FEATURES.contains(feature))
            .map(|(_, sets)| sets)
            .sum();
        assert_eq!(LEFT_OUT.len(), left_out);
        assert_eq!(POST_QUANTUM.len(), 15 - left_out);

        let ed25519 = include_bytes!("../asn1/testdata/ed25519-p8v2.bin");
        assert!(matches!(
            KeyPair::from_pkcs8(ed25519),
            Ok(KeyPair::Ed25519(_))
        ));
    }

    /// The post-quantum features this build has.
    const POST_QUANTUM_FEATURES: &[&str] = &[
        #[cfg(feature = "ml-dsa")]
        "ml-dsa",
        #[cfg(feature = "slh-dsa")]
        "slh-dsa",
    ];
}
