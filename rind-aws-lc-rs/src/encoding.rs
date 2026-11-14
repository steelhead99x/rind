//! Serialization formats.

use crate::buffer::generated_encodings;
use crate::error::Unspecified;

/// Serializes into a DER format.
pub trait AsDer<T> {
    /// Serializes into a DER format.
    fn as_der(&self) -> Result<T, Unspecified>;
}

/// Serializes into a big-endian format.
pub trait AsBigEndian<T> {
    /// Serializes into a big-endian format.
    fn as_be_bytes(&self) -> Result<T, Unspecified>;
}

/// Serializes into a raw format.
pub trait AsRawBytes<T> {
    /// Serializes into a raw format.
    fn as_raw_bytes(&self) -> Result<T, Unspecified>;
}

generated_encodings!(
    (Curve25519SeedBin, Curve25519SeedBinType, true),
    (EcPrivateKeyBin, EcPrivateKeyBinType, true),
    (EcPrivateKeyRfc5915Der, EcPrivateKeyRfc5915DerType, true),
    (
        EcPublicKeyCompressedBin,
        EcPublicKeyCompressedBinType,
        false
    ),
    (
        EcPublicKeyUncompressedBin,
        EcPublicKeyUncompressedBinType,
        false
    ),
    (Pkcs8V1Der, Pkcs8V1DerType, true),
    (Pkcs8V2Der, Pkcs8V2DerType, true),
    (PqdsaSeedRaw, PqdsaSeedRawType, true),
    (PublicKeyX509Der, PublicKeyX509DerType, false),
);
