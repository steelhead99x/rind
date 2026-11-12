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

    pub(crate) fn too_small() -> Self {
        Self(Reason::Ring("TooSmall"))
    }

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

impl std::error::Error for KeyRejected {}

#[cfg(test)]
mod tests {
    use super::KeyRejected;

    #[test]
    fn rind_errors_keep_ring_names() {
        // Deleting any arm of `KeyRejected::rind` sends that error through the
        // catch-all, which ring calls `UnexpectedError`.
        assert_eq!(
            KeyRejected::rind(rind::Error::WrongLength).to_string(),
            "InvalidEncoding"
        );
        assert_eq!(
            KeyRejected::rind(rind::Error::RngFailed).to_string(),
            "RNG failed"
        );
        assert_eq!(
            KeyRejected::rind(rind::Error::Fault).to_string(),
            "UnexpectedError"
        );

        let rejected = rind::agreement::PrivateKey::from_pkcs8(&rind::agreement::X25519, &[0x30])
            .expect_err("a one-byte sequence is not a key");
        let rind::Error::KeyRejected(reason) = rejected else {
            panic!("expected a rejected key, got {rejected}");
        };
        assert_eq!(KeyRejected::rind(rejected).to_string(), reason.to_string());
    }
}
