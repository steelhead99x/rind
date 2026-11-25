//! Error reporting.

use core::fmt;
use core::num::TryFromIntError;

/// An error with no details, as aws-lc-rs returns from most calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Unspecified;

impl fmt::Display for Unspecified {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Unspecified")
    }
}

// aws-lc-rs overrides the deprecated `description` and `cause`, so a caller
// still on them gets its answers.
#[allow(deprecated)]
impl std::error::Error for Unspecified {
    fn description(&self) -> &str {
        "Unspecified"
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        None
    }
}

impl From<core::array::TryFromSliceError> for Unspecified {
    fn from(_: core::array::TryFromSliceError) -> Self {
        Self
    }
}

#[cfg(any(feature = "ring-sig-verify", feature = "ring-io"))]
impl From<untrusted::EndOfInput> for Unspecified {
    fn from(_: untrusted::EndOfInput) -> Self {
        Self
    }
}

impl From<TryFromIntError> for Unspecified {
    fn from(_: TryFromIntError) -> Self {
        Self
    }
}

impl From<KeyRejected> for Unspecified {
    fn from(_: KeyRejected) -> Self {
        Self
    }
}

impl From<()> for Unspecified {
    fn from((): ()) -> Self {
        Self
    }
}

impl From<Unspecified> for () {
    fn from(_: Unspecified) -> Self {}
}

/// A key was refused; its `Display` says why, in words that may change between releases.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct KeyRejected(Reason);

#[derive(Clone, Copy, Debug, PartialEq)]
enum Reason {
    /// rind's own reason.
    Rind(rind::KeyRejected),
    /// A rule aws-lc-rs has and rind does not, named as aws-lc-rs names it.
    Named(&'static str),
}

impl KeyRejected {
    /// The reason's name, as aws-lc-rs gives it.
    ///
    /// A key rind itself refused is named `"InvalidEncoding"`, as aws-lc-rs
    /// names most refusals; its `Display` gives rind's reason.
    pub fn description_(&self) -> &'static str {
        match self.0 {
            Reason::Rind(_) => "InvalidEncoding",
            Reason::Named(name) => name,
        }
    }

    pub(crate) fn invalid_encoding() -> Self {
        Self(Reason::Named("InvalidEncoding"))
    }

    pub(crate) fn inconsistent_components() -> Self {
        Self(Reason::Named("InconsistentComponents"))
    }

    pub(crate) fn too_small() -> Self {
        Self(Reason::Named("TooSmall"))
    }

    pub(crate) fn too_large() -> Self {
        Self(Reason::Named("TooLarge"))
    }

    pub(crate) fn wrong_algorithm() -> Self {
        Self(Reason::Named("WrongAlgorithm"))
    }

    pub(crate) fn unspecified() -> Self {
        Self(Reason::Named("Unspecified"))
    }

    pub(crate) fn unexpected_error() -> Self {
        Self(Reason::Named("UnexpectedError"))
    }

    /// Keeps rind's reason for a refused key.
    pub(crate) fn rind(error: rind::Error) -> Self {
        match error {
            rind::Error::KeyRejected(reason) => Self(Reason::Rind(reason)),
            rind::Error::WrongLength => Self::invalid_encoding(),
            _ => Self::unexpected_error(),
        }
    }
}

impl fmt::Display for KeyRejected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.0 {
            Reason::Rind(reason) => reason.fmt(f),
            Reason::Named(name) => f.write_str(name),
        }
    }
}

#[allow(deprecated)]
impl std::error::Error for KeyRejected {
    fn description(&self) -> &str {
        self.description_()
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        None
    }
}

impl From<()> for KeyRejected {
    fn from((): ()) -> Self {
        Self::unexpected_error()
    }
}

impl From<TryFromIntError> for KeyRejected {
    fn from(_: TryFromIntError) -> Self {
        Self::unexpected_error()
    }
}

impl From<Unspecified> for KeyRejected {
    fn from(_: Unspecified) -> Self {
        Self::unspecified()
    }
}

/// Maps any rind error to [`Unspecified`], as `.map_err(unspecified)`.
pub(crate) fn unspecified<E>(_: E) -> Unspecified {
    Unspecified
}

#[cfg(test)]
mod tests {
    use super::*;

    // rind's wrong-length refusal is aws-lc-rs's `InvalidEncoding`.
    #[test]
    fn wrong_length_is_invalid_encoding() {
        assert_eq!(
            KeyRejected::rind(rind::Error::WrongLength).description_(),
            "InvalidEncoding"
        );
    }
}
