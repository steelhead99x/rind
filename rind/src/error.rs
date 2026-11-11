// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// Why a rind call failed.
///
/// Each variant comes from one kind of call, so a caller can tell, say, a bad
/// key from a bad signature.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// An input or output of fixed length, such as a symmetric key, a nonce,
    /// or a derived key, was another length.
    WrongLength,

    /// A private, public, or peer's key was refused, for any reason including
    /// its length; its `Display` says why.
    KeyRejected(KeyRejected),

    /// A signature, MAC tag, or PBKDF2 output did not verify.
    BadSignature,

    /// An AEAD ciphertext, its tag, or its associated data did not
    /// authenticate, or an RSA-OAEP ciphertext did not decrypt.
    DecryptFailed,

    /// The system random source failed.
    RngFailed,

    /// Values compared in constant time were not equal.
    NotEqual,

    /// An internal consistency check failed, from a hardware fault or a rind
    /// bug, which the caller cannot fix.
    Fault,

    /// An HPKE context sealed or opened as many messages as its sequence
    /// number counts.
    MessageLimitReached,

    /// A call was given an algorithm it does not take, such as a SHA-1
    /// digest to sign, or a digest for a key that verifies only messages.
    Unsupported,

    /// A parameter was outside the range its algorithm allows, or named more
    /// memory than this call can allocate.
    OutOfRange,
}

/// Why a key was refused, which its `Display` describes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct KeyRejected(KeyFormatError);

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum KeyFormatError {
    Asn1(crate::high::asn1::Error),
    WrongLength,
    LeadingZero,
    Compressed,
    PointEncoding,
    NotOnCurve,
    SmallOrder,
    ScalarOutOfRange,
    RsaModulus,
    RsaExponent,
    RsaPrimes,
    MultiPrimeRsa,
    MlKemModulus,
    UnsupportedPkcs8Version,
    MismatchedPkcs8Algorithm,
    MismatchedPkcs8Parameters,
    MismatchedPkcs8PublicKey,
    MismatchedPublicKey,
    MismatchedRsaComponents,
    MismatchedSec1Curve,
    MismatchedSec1PublicKey,
    MismatchedSpkiAlgorithm,
}

impl From<KeyFormatError> for Error {
    fn from(kfe: KeyFormatError) -> Self {
        Self::KeyRejected(KeyRejected(kfe))
    }
}

impl core::fmt::Display for KeyRejected {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self.0 {
            KeyFormatError::Asn1(e) => write!(f, "an ASN.1 decoding error: {e}"),
            KeyFormatError::WrongLength => write!(f, "an encoding of the wrong length"),
            KeyFormatError::LeadingZero => write!(f, "an integer with a leading zero byte"),
            KeyFormatError::Compressed => write!(f, "a compressed point"),
            KeyFormatError::PointEncoding => {
                write!(f, "a point neither compressed nor uncompressed")
            }
            KeyFormatError::NotOnCurve => write!(f, "a point not on the curve"),
            KeyFormatError::SmallOrder => write!(f, "a small-order point"),
            KeyFormatError::ScalarOutOfRange => {
                write!(f, "a private scalar of zero, or not below the group order")
            }
            KeyFormatError::RsaModulus => {
                write!(
                    f,
                    "an RSA modulus that is negative, even, or of unsupported size"
                )
            }
            KeyFormatError::RsaExponent => {
                write!(
                    f,
                    "an RSA public exponent that is even, one, or over 33 bits"
                )
            }
            KeyFormatError::RsaPrimes => write!(f, "unsupported RSA primes"),
            KeyFormatError::MultiPrimeRsa => write!(f, "a multi-prime RSA key"),
            KeyFormatError::MlKemModulus => write!(f, "an ML-KEM key failing the modulus check"),
            KeyFormatError::UnsupportedPkcs8Version => write!(f, "unsupported PKCS#8 version"),
            KeyFormatError::MismatchedPkcs8Algorithm => write!(f, "mismatched PKCS#8 algorithm"),
            KeyFormatError::MismatchedPkcs8Parameters => {
                write!(f, "mismatched PKCS#8 parameters")
            }
            KeyFormatError::MismatchedPkcs8PublicKey => write!(f, "mismatched PKCS#8 public key"),
            KeyFormatError::MismatchedPublicKey => write!(f, "mismatched public key"),
            KeyFormatError::MismatchedRsaComponents => {
                write!(f, "mismatched RSA private key components")
            }
            KeyFormatError::MismatchedSec1Curve => write!(f, "mismatched SEC1 curve"),
            KeyFormatError::MismatchedSec1PublicKey => write!(f, "mismatched SEC1 public key"),
            KeyFormatError::MismatchedSpkiAlgorithm => {
                write!(f, "a SubjectPublicKeyInfo of another algorithm")
            }
        }
    }
}

impl core::fmt::Display for Error {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::WrongLength => write!(f, "an input or output was the wrong length"),
            Self::KeyRejected(e) => write!(f, "a key was rejected: {e}"),
            Self::BadSignature => write!(f, "a signature did not verify"),
            Self::DecryptFailed => write!(f, "a ciphertext did not authenticate"),
            Self::RngFailed => write!(f, "the system random source failed"),
            Self::NotEqual => write!(f, "values compared in constant time were not equal"),
            Self::Fault => write!(f, "an internal consistency check failed"),
            Self::MessageLimitReached => write!(f, "a context reached its message limit"),
            Self::Unsupported => write!(f, "an algorithm the call does not take"),
            Self::OutOfRange => write!(
                f,
                "a parameter was outside the range the algorithm allows, or named more memory than this call can allocate"
            ),
        }
    }
}

impl core::error::Error for KeyRejected {}
impl core::error::Error for Error {}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn key_rejected_displays_its_reason() {
        assert_eq!(
            format!(
                "{}",
                Error::from(KeyFormatError::Asn1(
                    crate::high::asn1::Error::UnexpectedTag
                ))
            ),
            "a key was rejected: an ASN.1 decoding error: unexpected tag"
        );
    }
}
