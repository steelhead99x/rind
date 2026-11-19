use rustls::crypto;
use rustls::crypto::tls13::{Hkdf as RustlsHkdf, HkdfExpander, HkdfUsingHmac, OkmBlock};

use crate::backend::hmac;

pub struct Hmac(&'static hmac::Algorithm);

pub static SHA256: Hmac = Hmac(&hmac::HMAC_SHA256);

pub static SHA384: Hmac = Hmac(&hmac::HMAC_SHA384);

/// TLS 1.3's HKDF over [`SHA256`] or [`SHA384`]: rustls's, over the HMAC here,
/// which says what runs in the module, where rustls's own does not.
pub struct Hkdf(HkdfUsingHmac<'static>);

pub static HKDF_SHA256: Hkdf = Hkdf(HkdfUsingHmac(&SHA256));

pub static HKDF_SHA384: Hkdf = Hkdf(HkdfUsingHmac(&SHA384));

impl RustlsHkdf for Hkdf {
    fn extract_from_zero_ikm(&self, salt: Option<&[u8]>) -> Box<dyn HkdfExpander> {
        self.0.extract_from_zero_ikm(salt)
    }

    fn extract_from_secret(&self, salt: Option<&[u8]>, secret: &[u8]) -> Box<dyn HkdfExpander> {
        self.0.extract_from_secret(salt, secret)
    }

    fn expander_for_okm(&self, okm: &OkmBlock) -> Box<dyn HkdfExpander> {
        self.0.expander_for_okm(okm)
    }

    fn hmac_sign(&self, key: &OkmBlock, message: &[u8]) -> crypto::hmac::Tag {
        self.0.hmac_sign(key, message)
    }

    /// HMAC runs in the module under `fips`.
    fn fips(&self) -> bool {
        cfg!(feature = "fips")
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
