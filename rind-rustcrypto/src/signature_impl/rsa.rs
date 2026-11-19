//! RSA as `signature`'s `Signer` and `Verifier`, under `rsa`'s module paths
//! (`rsa::pkcs1v15`, `rsa::pss`) with its key and signature types.
//!
//! Both schemes sign and verify through `Signer` and `Verifier`. PSS signing is
//! `Signer` and `MultipartSigner`, which draw on the system's random number
//! generator in `rsa` as in rind, and not `RandomizedSigner`, whose caller-chosen
//! generator rind cannot use. rind refuses a modulus under 2048 bits, which `rsa`
//! accepts.

use core::marker::PhantomData;

use ::rsa::pkcs1::{EncodeRsaPrivateKey, EncodeRsaPublicKey};
use ::signature::{Error, MultipartSigner, MultipartVerifier, Signer, Verifier};

use crate::sha2::{Sha256, Sha384, Sha512};

mod sealed {
    pub trait Sealed {}
}

/// A hash rind signs RSA with: [`Sha256`], [`Sha384`], and [`Sha512`].
pub trait Hash: sealed::Sealed {
    #[doc(hidden)]
    fn sign() -> &'static rind::rsa::SigningAlgorithm;
    #[doc(hidden)]
    fn sign_pss() -> &'static rind::rsa::SigningAlgorithm;
    #[doc(hidden)]
    fn verify() -> &'static rind::rsa::VerificationAlgorithm;
    #[doc(hidden)]
    fn pss() -> &'static rind::rsa::VerificationAlgorithm;
    #[doc(hidden)]
    fn pss_any_salt() -> &'static rind::rsa::VerificationAlgorithm;
}

macro_rules! hash {
    ($($hash:ident: $pkcs1:ident, $pss:ident, $any:ident;)*) => {$(
        impl sealed::Sealed for $hash {}
        impl Hash for $hash {
            fn sign() -> &'static rind::rsa::SigningAlgorithm {
                &rind::rsa::sign::$pkcs1
            }
            fn sign_pss() -> &'static rind::rsa::SigningAlgorithm {
                &rind::rsa::sign::$pss
            }
            fn verify() -> &'static rind::rsa::VerificationAlgorithm {
                &rind::rsa::verify::$pkcs1
            }
            fn pss() -> &'static rind::rsa::VerificationAlgorithm {
                &rind::rsa::verify::$pss
            }
            fn pss_any_salt() -> &'static rind::rsa::VerificationAlgorithm {
                &rind::rsa::verify::$any
            }
        }
    )*};
}

hash! {
    Sha256: PKCS1_SHA256, PSS_SHA256, PSS_SHA256_ANY_SALT;
    Sha384: PKCS1_SHA384, PSS_SHA384, PSS_SHA384_ANY_SALT;
    Sha512: PKCS1_SHA512, PSS_SHA512, PSS_SHA512_ANY_SALT;
}

/// The PKCS#1 `RSAPublicKey` DER of a key, which rind parses.
fn public_key_der(key: &::rsa::PublicKey) -> rind::rsa::PublicKey {
    let der = key.to_pkcs1_der().expect("a public key encodes");
    rind::rsa::PublicKey::new(der.as_bytes()).expect("rsa's keys are well formed")
}

/// RSASSA-PKCS1-v1_5, as `rsa::pkcs1v15`.
pub mod pkcs1v15 {
    pub use ::rsa::pkcs1v15::Signature;

    use super::*;

    /// A public key that verifies PKCS#1 v1.5 signatures over `D`.
    pub struct VerifyingKey<D: Hash> {
        key: rind::rsa::PublicKey,
        hash: PhantomData<D>,
    }

    impl<D: Hash> Clone for VerifyingKey<D> {
        fn clone(&self) -> Self {
            Self {
                key: self.key.clone(),
                hash: PhantomData,
            }
        }
    }

    impl<D: Hash> VerifyingKey<D> {
        /// A verifying key for `key`.
        pub fn new(key: ::rsa::PublicKey) -> Self {
            Self {
                key: public_key_der(&key),
                hash: PhantomData,
            }
        }
    }

    impl<D: Hash> From<::rsa::PublicKey> for VerifyingKey<D> {
        fn from(key: ::rsa::PublicKey) -> Self {
            Self::new(key)
        }
    }

    impl<D: Hash> core::fmt::Debug for VerifyingKey<D> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("VerifyingKey { .. }")
        }
    }

    impl<D: Hash> Verifier<Signature> for VerifyingKey<D> {
        fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), Error> {
            use ::rsa::signature::SignatureEncoding;
            self.key
                .verify(D::verify(), msg, &signature.to_bytes())
                .map_err(|_| Error::new())
        }
    }

    impl<D: Hash> MultipartVerifier<Signature> for VerifyingKey<D> {
        fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature) -> Result<(), Error> {
            self.verify(&msg.concat(), signature)
        }
    }

    /// A private key that signs PKCS#1 v1.5 over `D`: rind's key pair, which
    /// wipes itself on drop. The wrapper holds no other copy of the key; rsa's
    /// key is encoded into a zeroizing document that rind parses, then dropped.
    pub struct SigningKey<D: Hash> {
        pair: rind::rsa::KeyPair,
        verifying: VerifyingKey<D>,
    }

    impl<D: Hash> SigningKey<D> {
        /// A signing key for `key`, which rind refuses if its modulus is under
        /// 2048 bits or it is otherwise not one it signs with.
        pub fn try_new(key: ::rsa::PrivateKey) -> Result<Self, Error> {
            let der = key.to_pkcs1_der().map_err(|_| Error::new())?;
            let pair = rind::rsa::KeyPair::from_pkcs1(der.as_bytes()).map_err(|_| Error::new())?;
            let verifying = VerifyingKey {
                key: pair.public_key().clone(),
                hash: PhantomData,
            };
            Ok(Self { pair, verifying })
        }

        /// The public key.
        pub fn verifying_key(&self) -> VerifyingKey<D> {
            self.verifying.clone()
        }
    }

    impl<D: Hash> core::fmt::Debug for SigningKey<D> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("SigningKey { .. }")
        }
    }

    impl<D: Hash> Signer<Signature> for SigningKey<D> {
        fn try_sign(&self, msg: &[u8]) -> Result<Signature, Error> {
            let signature = self.pair.sign(D::sign(), msg).map_err(|_| Error::new())?;
            Signature::try_from(signature.as_ref())
        }
    }

    impl<D: Hash> MultipartSigner<Signature> for SigningKey<D> {
        fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<Signature, Error> {
            self.try_sign(&msg.concat())
        }
    }
}

/// RSASSA-PSS with a salt as long as the hash, as `rsa::pss`.
pub mod pss {
    pub use ::rsa::pss::Signature;

    use super::*;

    /// A public key that verifies PSS signatures over `D`.
    pub struct VerifyingKey<D: Hash> {
        key: rind::rsa::PublicKey,
        any_salt: bool,
        hash: PhantomData<D>,
    }

    impl<D: Hash> Clone for VerifyingKey<D> {
        fn clone(&self) -> Self {
            Self {
                key: self.key.clone(),
                any_salt: self.any_salt,
                hash: PhantomData,
            }
        }
    }

    impl<D: Hash> VerifyingKey<D> {
        /// A verifying key whose signatures carry a salt as long as the hash.
        pub fn new(key: ::rsa::PublicKey) -> Self {
            Self {
                key: public_key_der(&key),
                any_salt: false,
                hash: PhantomData,
            }
        }

        /// A verifying key that takes a signature's salt of any length.
        pub fn new_with_auto_salt_len(key: ::rsa::PublicKey) -> Self {
            Self {
                key: public_key_der(&key),
                any_salt: true,
                hash: PhantomData,
            }
        }
    }

    impl<D: Hash> From<::rsa::PublicKey> for VerifyingKey<D> {
        fn from(key: ::rsa::PublicKey) -> Self {
            Self::new(key)
        }
    }

    impl<D: Hash> core::fmt::Debug for VerifyingKey<D> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("VerifyingKey { .. }")
        }
    }

    impl<D: Hash> Verifier<Signature> for VerifyingKey<D> {
        fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), Error> {
            use ::rsa::signature::SignatureEncoding;
            let algorithm = if self.any_salt {
                D::pss_any_salt()
            } else {
                D::pss()
            };
            self.key
                .verify(algorithm, msg, &signature.to_bytes())
                .map_err(|_| Error::new())
        }
    }

    impl<D: Hash> MultipartVerifier<Signature> for VerifyingKey<D> {
        fn multipart_verify(&self, msg: &[&[u8]], signature: &Signature) -> Result<(), Error> {
            self.verify(&msg.concat(), signature)
        }
    }

    /// A private key that signs PSS over `D`: rind's key pair, which wipes
    /// itself on drop, as the PKCS#1 v1.5 key does.
    pub struct SigningKey<D: Hash> {
        pair: rind::rsa::KeyPair,
        verifying: VerifyingKey<D>,
    }

    impl<D: Hash> SigningKey<D> {
        /// A signing key for `key`, refused as [`super::pkcs1v15::SigningKey::try_new`] does.
        pub fn try_new(key: ::rsa::PrivateKey) -> Result<Self, Error> {
            let der = key.to_pkcs1_der().map_err(|_| Error::new())?;
            let pair = rind::rsa::KeyPair::from_pkcs1(der.as_bytes()).map_err(|_| Error::new())?;
            let verifying = VerifyingKey {
                key: pair.public_key().clone(),
                any_salt: false,
                hash: PhantomData,
            };
            Ok(Self { pair, verifying })
        }

        /// The public key.
        pub fn verifying_key(&self) -> VerifyingKey<D> {
            self.verifying.clone()
        }
    }

    impl<D: Hash> core::fmt::Debug for SigningKey<D> {
        fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
            f.write_str("SigningKey { .. }")
        }
    }

    impl<D: Hash> Signer<Signature> for SigningKey<D> {
        fn try_sign(&self, msg: &[u8]) -> Result<Signature, Error> {
            let signature = self
                .pair
                .sign(D::sign_pss(), msg)
                .map_err(|_| Error::new())?;
            Signature::try_from(signature.as_ref())
        }
    }

    impl<D: Hash> MultipartSigner<Signature> for SigningKey<D> {
        fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<Signature, Error> {
            self.try_sign(&msg.concat())
        }
    }
}
