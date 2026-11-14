// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::ffi::{self, Status, ids};

/// Why a call failed.
///
/// Each variant comes from one kind of call, so a caller can tell, say, a bad
/// key from a bad signature.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    /// An input or output of fixed length, such as a symmetric key, a nonce,
    /// or a derived key, was another length, or a parameter was outside what
    /// FIPS 140-3 approves, such as a PBKDF2 salt shorter than 16 bytes.
    WrongLength,

    /// A private, public, or peer's key was refused, for any reason including
    /// its length; its `Display` says why.
    KeyRejected(KeyRejected),

    /// A signature, MAC tag, or PBKDF2 output did not verify.
    BadSignature,

    /// An AEAD ciphertext, its tag, or its associated data did not
    /// authenticate.
    DecryptFailed,

    /// The module's random generator failed.
    RngFailed,

    /// Values compared in constant time were not equal.
    NotEqual,

    /// An internal consistency check failed, from a hardware fault or a rind
    /// bug, which the caller cannot fix.
    Fault,

    /// A call was given an algorithm it does not take, such as a digest for
    /// a key that verifies only messages.
    Unsupported,
}

impl Error {
    pub(crate) fn from_status(status: Status) -> Self {
        match status & 0xff {
            ids::error::WRONG_LENGTH => Self::WrongLength,
            ids::error::KEY_REJECTED => Self::KeyRejected(KeyRejected(status)),
            ids::error::BAD_SIGNATURE => Self::BadSignature,
            ids::error::DECRYPT_FAILED => Self::DecryptFailed,
            ids::error::RNG_FAILED => Self::RngFailed,
            ids::error::NOT_EQUAL => Self::NotEqual,
            ids::error::UNSUPPORTED => Self::Unsupported,
            _ => Self::Fault,
        }
    }
}

/// Why a key was refused, which its `Display` describes.
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct KeyRejected(Status);

impl fmt::Display for KeyRejected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&message(self.0))
    }
}

impl fmt::Debug for KeyRejected {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("KeyRejected")
            .field(&message(self.0))
            .finish()
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::KeyRejected(reason) => write!(f, "a key was rejected: {reason}"),
            Self::WrongLength => f.write_str("an input or output was the wrong length"),
            Self::BadSignature => f.write_str("a signature did not verify"),
            Self::DecryptFailed => f.write_str("a ciphertext did not authenticate"),
            Self::RngFailed => f.write_str("the system random source failed"),
            Self::NotEqual => f.write_str("values compared in constant time were not equal"),
            Self::Fault => f.write_str("an internal consistency check failed"),
            Self::Unsupported => f.write_str("an algorithm the call does not take"),
        }
    }
}

impl core::error::Error for KeyRejected {}
impl core::error::Error for Error {}

/// The module's description of the error with `status`.
fn message(status: Status) -> String {
    let mut buf = [0u8; 128];
    // SAFETY: `buf` is 128 writable bytes.
    let len = unsafe { ffi::rind_fips_error_message(status, buf.as_mut_ptr(), buf.len()) };
    String::from_utf8_lossy(&buf[..len.min(buf.len())]).into_owned()
}
