//! ECDSA on P-256, P-384, and P-521 as `signature`'s `Signer` and `Verifier`,
//! under the module paths RustCrypto's curve crates use (`p256::ecdsa` and so
//! on) and with their `Signature` and `DerSignature` types.
//!
//! Each key signs with its curve's own hash (SHA-256, SHA-384, SHA-512), as
//! RustCrypto's does. rind signs with a random nonce where `ecdsa`'s `Signer`
//! uses RFC 6979's, so a signature differs from RustCrypto's for the same key
//! and message, and verifies under it.

macro_rules! curve {
    ($module:ident, $curve:ty, $field:ty, $sign:ident, $verify:ident, $ecdh:ident) => {
        /// ECDSA on this curve.
        pub mod $module {
            /// The module path RustCrypto's curve crate puts its ECDSA types in.
            pub mod ecdsa {
                use alloc::boxed::Box;
                use core::fmt;

                pub use ::signature::{self, Error};
                use ::signature::{
                    KeypairRef, MultipartSigner, MultipartVerifier, Signer, Verifier,
                };

                /// A fixed-size signature, `r || s`.
                pub type Signature = ::ecdsa::Signature<$curve>;
                /// An ASN.1 DER signature.
                pub type DerSignature = ::ecdsa::der::Signature<$curve>;

                /// A public key.
                #[derive(Clone)]
                #[repr(transparent)]
                pub struct VerifyingKey {
                    key: ::rind::ecdsa::PublicKey,
                }

                impl VerifyingKey {
                    /// A public key from its SEC1 encoding, compressed or not, refused
                    /// as rind refuses one that is not a point on the curve.
                    ///
                    /// rind's ECDSA key takes only the uncompressed point, so a
                    /// compressed one is decompressed by rind's key agreement public
                    /// key on the same curve, which checks it is on the curve.
                    pub fn from_sec1_bytes(bytes: &[u8]) -> Result<Self, Error> {
                        let point =
                            ::rind::agreement::PublicKey::new(&::rind::agreement::$ecdh, bytes)
                                .map_err(|_| Error::new())?;
                        ::rind::ecdsa::PublicKey::new(
                            &::rind::ecdsa::verify::$verify,
                            point.as_ref(),
                        )
                        .map(|key| Self { key })
                        .map_err(|_| Error::new())
                    }

                    /// rind's public key as this wrapper, borrowed rather than
                    /// copied, so a signing key's public key is the one inside rind's
                    /// key pair, which that pair wipes on drop.
                    fn from_rind(key: &::rind::ecdsa::PublicKey) -> &Self {
                        // SAFETY: `VerifyingKey` is `repr(transparent)` over rind's
                        // public key, so the two share a layout and the borrow's
                        // lifetime carries over.
                        unsafe { &*(key as *const ::rind::ecdsa::PublicKey).cast::<Self>() }
                    }

                    /// The uncompressed SEC1 encoding.
                    pub fn to_sec1_bytes(&self) -> Box<[u8]> {
                        self.key.as_ref().into()
                    }
                }

                impl TryFrom<&[u8]> for VerifyingKey {
                    type Error = Error;

                    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
                        Self::from_sec1_bytes(bytes)
                    }
                }

                impl PartialEq for VerifyingKey {
                    fn eq(&self, other: &Self) -> bool {
                        self.key.as_ref() == other.key.as_ref()
                    }
                }

                impl Eq for VerifyingKey {}

                impl fmt::Debug for VerifyingKey {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        write!(f, "VerifyingKey({:02x?})", self.key.as_ref())
                    }
                }

                impl Verifier<Signature> for VerifyingKey {
                    fn verify(&self, msg: &[u8], signature: &Signature) -> Result<(), Error> {
                        self.key
                            .verify(msg, &signature.to_bytes())
                            .map_err(|_| Error::new())
                    }
                }

                impl MultipartVerifier<Signature> for VerifyingKey {
                    fn multipart_verify(
                        &self,
                        msg: &[&[u8]],
                        signature: &Signature,
                    ) -> Result<(), Error> {
                        self.verify(&msg.concat(), signature)
                    }
                }

                impl Verifier<DerSignature> for VerifyingKey {
                    fn verify(&self, msg: &[u8], signature: &DerSignature) -> Result<(), Error> {
                        let fixed = Signature::from_der(signature.as_bytes())?;
                        self.verify(msg, &fixed)
                    }
                }

                impl MultipartVerifier<DerSignature> for VerifyingKey {
                    fn multipart_verify(
                        &self,
                        msg: &[&[u8]],
                        signature: &DerSignature,
                    ) -> Result<(), Error> {
                        self.verify(&msg.concat(), signature)
                    }
                }

                /// A signing key: rind's key pair, which wipes its whole value,
                /// public key included, on drop. The wrapper is only that pair: it
                /// holds no other copy of the scalar or the public key.
                #[repr(transparent)]
                pub struct SigningKey {
                    pair: ::rind::ecdsa::KeyPair,
                }

                impl SigningKey {
                    /// The key a big-endian scalar makes, refused if it is zero or not
                    /// below the curve's order.
                    pub fn from_bytes(bytes: &$field) -> Result<Self, Error> {
                        Self::from_slice(bytes.as_slice())
                    }

                    /// As [`Self::from_bytes`], for a slice that must be exactly the
                    /// scalar's length.
                    pub fn from_slice(bytes: &[u8]) -> Result<Self, Error> {
                        // rind derives the public point from the scalar through its
                        // key agreement key, which wipes itself on drop.
                        let private = ::rind::agreement::PrivateKey::from_scalar(
                            &::rind::agreement::$ecdh,
                            bytes,
                        )
                        .map_err(|_| Error::new())?;
                        let pair = ::rind::ecdsa::KeyPair::from_scalar_and_public_key(
                            &::rind::ecdsa::sign::$sign,
                            bytes,
                            private.public_key().as_ref(),
                        )
                        .map_err(|_| Error::new())?;
                        Ok(Self { pair })
                    }

                    /// The big-endian scalar, the bytes [`Self::from_bytes`] takes.
                    pub fn to_bytes(&self) -> $field {
                        <$field>::try_from(self.pair.to_scalar().as_ref())
                            .expect("rind's scalar is the field's length")
                    }

                    /// The public key.
                    pub fn verifying_key(&self) -> &VerifyingKey {
                        VerifyingKey::from_rind(self.pair.public_key())
                    }
                }

                impl TryFrom<&[u8]> for SigningKey {
                    type Error = Error;

                    fn try_from(bytes: &[u8]) -> Result<Self, Error> {
                        Self::from_slice(bytes)
                    }
                }

                impl fmt::Debug for SigningKey {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.debug_struct("SigningKey")
                            .field("verifying_key", self.verifying_key())
                            .finish_non_exhaustive()
                    }
                }

                impl AsRef<VerifyingKey> for SigningKey {
                    fn as_ref(&self) -> &VerifyingKey {
                        self.verifying_key()
                    }
                }

                impl KeypairRef for SigningKey {
                    type VerifyingKey = VerifyingKey;
                }

                impl Signer<Signature> for SigningKey {
                    fn try_sign(&self, msg: &[u8]) -> Result<Signature, Error> {
                        let signature = self.pair.sign(msg).map_err(|_| Error::new())?;
                        Signature::from_slice(signature.as_ref())
                    }
                }

                impl MultipartSigner<Signature> for SigningKey {
                    fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<Signature, Error> {
                        self.try_sign(&msg.concat())
                    }
                }

                impl Signer<DerSignature> for SigningKey {
                    fn try_sign(&self, msg: &[u8]) -> Result<DerSignature, Error> {
                        let fixed: Signature = self.try_sign(msg)?;
                        Ok(fixed.to_der())
                    }
                }

                impl MultipartSigner<DerSignature> for SigningKey {
                    fn try_multipart_sign(&self, msg: &[&[u8]]) -> Result<DerSignature, Error> {
                        Signer::<DerSignature>::try_sign(self, &msg.concat())
                    }
                }
            }
        }
    };
}

curve!(
    p256,
    ::p256::NistP256,
    ::p256::FieldBytes,
    P256_SHA256_FIXED,
    P256_SHA256_FIXED,
    ECDH_P256
);
curve!(
    p384,
    ::p384::NistP384,
    ::p384::FieldBytes,
    P384_SHA384_FIXED,
    P384_SHA384_FIXED,
    ECDH_P384
);
curve!(
    p521,
    ::p521::NistP521,
    ::p521::FieldBytes,
    P521_SHA512_FIXED,
    P521_SHA512_FIXED,
    ECDH_P521
);
