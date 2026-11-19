use rustls::crypto;
#[cfg(not(feature = "fips"))]
use rustls::crypto::tls13::HkdfUsingHmac;
#[cfg(feature = "fips")]
use rustls::crypto::tls13::OutputLengthError;
use rustls::crypto::tls13::{Hkdf as RustlsHkdf, HkdfExpander, OkmBlock};

#[cfg(feature = "fips")]
use crate::backend::hkdf;
use crate::backend::hmac;

pub struct Hmac(&'static hmac::Algorithm);

pub static SHA256: Hmac = Hmac(&hmac::HMAC_SHA256);

pub static SHA384: Hmac = Hmac(&hmac::HMAC_SHA384);

/// TLS 1.3's HKDF over [`SHA256`] or [`SHA384`]. Under `fips` it runs in the
/// module, which keeps each extracted key inside it, as rustls's aws-lc-rs
/// provider does with AWS-LC; rustls's `HkdfUsingHmac` would extract and
/// expand in rustls's own code and hold the keys there.
pub struct Hkdf {
    #[cfg(not(feature = "fips"))]
    inner: HkdfUsingHmac<'static>,
    #[cfg(feature = "fips")]
    algorithm: &'static hkdf::Algorithm,
    /// rind's HKDF, for the empty `info` the module refuses.
    #[cfg(feature = "fips")]
    rind: &'static rind::hkdf::Algorithm,
    #[cfg(feature = "fips")]
    hmac: &'static hmac::Algorithm,
}

#[cfg(not(feature = "fips"))]
pub static HKDF_SHA256: Hkdf = Hkdf {
    inner: HkdfUsingHmac(&SHA256),
};

#[cfg(not(feature = "fips"))]
pub static HKDF_SHA384: Hkdf = Hkdf {
    inner: HkdfUsingHmac(&SHA384),
};

#[cfg(feature = "fips")]
pub static HKDF_SHA256: Hkdf = Hkdf {
    algorithm: &hkdf::HKDF_SHA256,
    rind: &rind::hkdf::HKDF_SHA256,
    hmac: &hmac::HMAC_SHA256,
};

#[cfg(feature = "fips")]
pub static HKDF_SHA384: Hkdf = Hkdf {
    algorithm: &hkdf::HKDF_SHA384,
    rind: &rind::hkdf::HKDF_SHA384,
    hmac: &hmac::HMAC_SHA384,
};

#[cfg(not(feature = "fips"))]
impl RustlsHkdf for Hkdf {
    fn extract_from_zero_ikm(&self, salt: Option<&[u8]>) -> Box<dyn HkdfExpander> {
        self.inner.extract_from_zero_ikm(salt)
    }

    fn extract_from_secret(&self, salt: Option<&[u8]>, secret: &[u8]) -> Box<dyn HkdfExpander> {
        self.inner.extract_from_secret(salt, secret)
    }

    fn expander_for_okm(&self, okm: &OkmBlock) -> Box<dyn HkdfExpander> {
        self.inner.expander_for_okm(okm)
    }

    fn hmac_sign(&self, key: &OkmBlock, message: &[u8]) -> crypto::hmac::Tag {
        self.inner.hmac_sign(key, message)
    }
}

#[cfg(feature = "fips")]
impl Hkdf {
    /// HKDF-Extract in the module. An absent or empty salt is `HashLen` zero
    /// bytes (RFC 5869 section 2.2), as the trait asks and as aws-lc-rs does;
    /// the module refuses an empty one.
    fn extract(&self, salt: Option<&[u8]>, secret: &[u8]) -> Box<dyn HkdfExpander> {
        let zeroes = [0u8; OkmBlock::MAX_LEN];
        let salt = match salt {
            Some(salt) if !salt.is_empty() => salt,
            _ => &zeroes[..self.hmac.tag_len()],
        };
        let prk = hkdf::Salt::new(self.algorithm, salt)
            .extract(secret)
            .expect("a non-empty salt is approved");
        // The empty-`info` copy is the same extraction in rind.
        let copy = rind::hkdf::Salt::new(self.rind, salt)
            .extract(secret)
            .expect("rind extracts with any salt");
        Box::new(Expander {
            prk,
            copy,
            len: self.hmac.tag_len(),
        })
    }
}

#[cfg(feature = "fips")]
impl RustlsHkdf for Hkdf {
    fn extract_from_zero_ikm(&self, salt: Option<&[u8]>) -> Box<dyn HkdfExpander> {
        let zeroes = [0u8; OkmBlock::MAX_LEN];
        self.extract(salt, &zeroes[..self.hmac.tag_len()])
    }

    fn extract_from_secret(&self, salt: Option<&[u8]>, secret: &[u8]) -> Box<dyn HkdfExpander> {
        self.extract(salt, secret)
    }

    fn expander_for_okm(&self, okm: &OkmBlock) -> Box<dyn HkdfExpander> {
        Box::new(Expander {
            prk: hkdf::Prk::new(self.algorithm, okm.as_ref()),
            copy: rind::hkdf::Prk::new(self.rind, okm.as_ref()),
            len: self.hmac.tag_len(),
        })
    }

    fn hmac_sign(&self, key: &OkmBlock, message: &[u8]) -> crypto::hmac::Tag {
        let key = hmac::Key::new(self.hmac, key.as_ref());
        crypto::hmac::Tag::new(hmac::sign(&key, message).as_ref())
    }

    /// HKDF runs in the module, which holds each key it extracts.
    fn fips(&self) -> bool {
        true
    }
}

/// A pseudorandom key held in the module.
///
/// rustls's aws-lc-rs provider derives an empty `info` too (its
/// `expand_slice(&[], ..)` succeeds; AWS-LC's FIPS build leaves the service
/// indicator unset for it), and this follows it. The module refuses an empty
/// `info`, so the key keeps a second copy in rind, wiped on drop, and derives
/// an empty `info` there. That copy means the key is not held only inside the
/// module, and an empty-`info` derivation is not a module service. TLS 1.3's
/// labels are never empty, so the handshake always derives in the module.
#[cfg(feature = "fips")]
struct Expander {
    prk: hkdf::Prk,
    copy: rind::hkdf::Prk,
    len: usize,
}

#[cfg(feature = "fips")]
impl Expander {
    fn fill(&self, info: &[&[u8]], output: &mut [u8]) -> Result<(), OutputLengthError> {
        if info.iter().all(|part| part.is_empty()) {
            self.copy.fill(info, output).map_err(|_| OutputLengthError)
        } else {
            self.prk.fill(info, output).map_err(|_| OutputLengthError)
        }
    }
}

#[cfg(feature = "fips")]
impl HkdfExpander for Expander {
    fn expand_slice(&self, info: &[&[u8]], output: &mut [u8]) -> Result<(), OutputLengthError> {
        self.fill(info, output)
    }

    fn expand_block(&self, info: &[&[u8]]) -> OkmBlock {
        let mut buf = [0u8; OkmBlock::MAX_LEN];
        let output = &mut buf[..self.len];
        // One block is far under the 255-block limit.
        self.fill(info, output).unwrap();
        OkmBlock::new(output)
    }

    fn hash_len(&self) -> usize {
        self.len
    }
}

impl crypto::hmac::Hmac for Hmac {
    fn with_key(&self, key: &[u8]) -> Box<dyn crypto::hmac::Key> {
        Box::new(Key(hmac::Key::new(self.0, key)))
    }

    fn hash_output_len(&self) -> usize {
        self.0.tag_len()
    }

    /// HMAC runs in the module under `fips`.
    fn fips(&self) -> bool {
        cfg!(feature = "fips")
    }
}

struct Key(hmac::Key);

impl crypto::hmac::Key for Key {
    fn sign_concat(&self, first: &[u8], middle: &[&[u8]], last: &[u8]) -> crypto::hmac::Tag {
        let mut ctx = hmac::Context::with_key(&self.0);
        ctx.update(first);
        for m in middle {
            ctx.update(m);
        }
        ctx.update(last);
        crypto::hmac::Tag::new(ctx.sign().as_ref())
    }

    fn tag_len(&self) -> usize {
        self.0.algorithm().tag_len()
    }
}
