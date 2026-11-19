//! Error reporting.

use core::fmt;

/// An error with no details, as ring returns from most calls.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Unspecified;

impl fmt::Display for Unspecified {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ring::error::Unspecified")
    }
}

#[cfg(feature = "std")]
impl std::error::Error for Unspecified {}

impl From<untrusted::EndOfInput> for Unspecified {
    fn from(_: untrusted::EndOfInput) -> Self {
        Self
    }
}

impl From<core::array::TryFromSliceError> for Unspecified {
    fn from(_: core::array::TryFromSliceError) -> Self {
        Self
    }
}

impl From<KeyRejected> for Unspecified {
    fn from(_: KeyRejected) -> Self {
        Self
    }
}

/// A key was refused; its `Display` says why, in words that may change between releases.
#[derive(Clone, Copy, Debug)]
pub struct KeyRejected(Reason);

#[derive(Clone, Copy, Debug)]
enum Reason {
    /// rind's own reason.
    Rind(rind::KeyRejected),
    /// A rule ring has and rind does not, named as ring names it.
    Ring(&'static str),
}

impl KeyRejected {
    pub(crate) fn invalid_encoding() -> Self {
        Self(Reason::Ring("InvalidEncoding"))
    }

    #[cfg(feature = "alloc")]
    pub(crate) fn too_small() -> Self {
        Self(Reason::Ring("TooSmall"))
    }

    #[cfg(feature = "alloc")]
    pub(crate) fn too_large() -> Self {
        Self(Reason::Ring("TooLarge"))
    }

    pub(crate) fn inconsistent_components() -> Self {
        Self(Reason::Ring("InconsistentComponents"))
    }

    pub(crate) fn wrong_algorithm() -> Self {
        Self(Reason::Ring("WrongAlgorithm"))
    }

    pub(crate) fn public_key_is_missing() -> Self {
        Self(Reason::Ring("PublicKeyIsMissing"))
    }

    pub(crate) fn version_not_supported() -> Self {
        Self(Reason::Ring("VersionNotSupported"))
    }

    #[cfg(feature = "alloc")]
    pub(crate) fn private_modulus_len_not_multiple_of_512_bits() -> Self {
        Self(Reason::Ring("PrivateModulusLenNotMultipleOf512Bits"))
    }
}

impl KeyRejected {
    /// Keeps rind's reason for a refused key.
    pub(crate) fn rind(error: rind::Error) -> Self {
        Self(match error {
            rind::Error::KeyRejected(reason) => Reason::Rind(reason),
            rind::Error::WrongLength => Reason::Ring("InvalidEncoding"),
            rind::Error::RngFailed => Reason::Ring("RNG failed"),
            _ => Reason::Ring("UnexpectedError"),
        })
    }
}

impl fmt::Display for KeyRejected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Reason::Rind(reason) => reason.fmt(f),
            Reason::Ring(reason) => f.write_str(reason),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for KeyRejected {}
