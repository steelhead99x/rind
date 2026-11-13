// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::ffi::{Handle, ids, opaque};

opaque! {
    DigestContext => rind_fips_digest_free,
}

unsafe extern "C" {
    fn rind_fips_digest(id: u32, data: *const u8, len: usize, out: *mut u8) -> usize;
    fn rind_fips_digest_new(id: u32) -> *mut DigestContext;
    fn rind_fips_digest_update(context: *mut DigestContext, data: *const u8, len: usize);
    fn rind_fips_digest_finish(context: *mut DigestContext, out: *mut u8) -> usize;
    fn rind_fips_digest_clone(context: *const DigestContext) -> *mut DigestContext;
}

/// A hash function, chosen by one of this module's constants.
pub struct Algorithm {
    pub(crate) id: u32,
    name: &'static str,
    output_len: usize,
}

impl Algorithm {
    /// The length of this algorithm's digest, in bytes.
    pub fn output_len(&self) -> usize {
        self.output_len
    }
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Algorithm")
            .field("id", &format_args!("{}", self.name))
            .field("output_len", &self.output_len)
            .finish()
    }
}

/// SHA-256, from FIPS 180-4.
pub static SHA256: Algorithm = Algorithm {
    id: ids::hash::SHA256,
    name: "Sha256",
    output_len: 32,
};

/// SHA-384, from FIPS 180-4.
pub static SHA384: Algorithm = Algorithm {
    id: ids::hash::SHA384,
    name: "Sha384",
    output_len: 48,
};

/// SHA-512, from FIPS 180-4.
pub static SHA512: Algorithm = Algorithm {
    id: ids::hash::SHA512,
    name: "Sha512",
    output_len: 64,
};

/// SHA-512/256, from FIPS 180-4.
pub static SHA512_256: Algorithm = Algorithm {
    id: ids::hash::SHA512_256,
    name: "Sha512_256",
    output_len: 32,
};

/// SHA3-256, from FIPS 202.
pub static SHA3_256: Algorithm = Algorithm {
    id: ids::hash::SHA3_256,
    name: "Sha3_256",
    output_len: 32,
};

/// SHA3-384, from FIPS 202.
pub static SHA3_384: Algorithm = Algorithm {
    id: ids::hash::SHA3_384,
    name: "Sha3_384",
    output_len: 48,
};

/// SHA3-512, from FIPS 202.
pub static SHA3_512: Algorithm = Algorithm {
    id: ids::hash::SHA3_512,
    name: "Sha3_512",
    output_len: 64,
};

/// Hashes `data` in one go.
#[must_use]
pub fn digest(algorithm: &'static Algorithm, data: &[u8]) -> Digest {
    let mut digest = Digest::zeroed(algorithm);
    // SAFETY: `data` is readable, and `digest.value` is 64 writable bytes.
    unsafe {
        rind_fips_digest(
            algorithm.id,
            data.as_ptr(),
            data.len(),
            digest.value.as_mut_ptr(),
        )
    };
    digest
}

/// An in-progress hash computation.
///
/// A clone forks the computation, so messages sharing a prefix hash it once.
pub struct Context {
    algorithm: &'static Algorithm,
    handle: Handle<DigestContext>,
}

impl Context {
    /// Starts hashing with `algorithm`.
    pub fn new(algorithm: &'static Algorithm) -> Self {
        // SAFETY: no pointers.
        let handle = Handle::new(unsafe { rind_fips_digest_new(algorithm.id) });
        Self { algorithm, handle }
    }

    /// Adds `data` to the message.
    pub fn update(&mut self, data: &[u8]) {
        // SAFETY: the handle is live, and `data` readable.
        unsafe { rind_fips_digest_update(self.handle.ptr(), data.as_ptr(), data.len()) }
    }

    /// Returns the digest of the message, and starts a new one with the same algorithm.
    pub fn finish(&mut self) -> Digest {
        let mut digest = Digest::zeroed(self.algorithm);
        // SAFETY: the handle is live, and `digest.value` is 64 writable bytes.
        unsafe { rind_fips_digest_finish(self.handle.ptr(), digest.value.as_mut_ptr()) };
        digest
    }
}

impl Clone for Context {
    fn clone(&self) -> Self {
        // SAFETY: the handle is live.
        let handle = Handle::new(unsafe { rind_fips_digest_clone(self.handle.ptr()) });
        Self {
            algorithm: self.algorithm,
            handle,
        }
    }
}

impl fmt::Debug for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Context")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .finish_non_exhaustive()
    }
}

/// The output of a hash function.
#[derive(Clone, Copy)]
pub struct Digest {
    pub(crate) algorithm: &'static Algorithm,
    value: [u8; 64],
}

impl Digest {
    fn zeroed(algorithm: &'static Algorithm) -> Self {
        Self {
            algorithm,
            value: [0; 64],
        }
    }
}

impl AsRef<[u8]> for Digest {
    fn as_ref(&self) -> &[u8] {
        &self.value[..self.algorithm.output_len]
    }
}

impl fmt::Debug for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Digest")
            .field("algorithm", &format_args!("{}", self.algorithm.name))
            .field("value", &self.as_ref())
            .finish()
    }
}
