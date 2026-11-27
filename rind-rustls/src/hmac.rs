use alloc::boxed::Box;

use rind::hmac;
use rustls::crypto;

pub struct Hmac(&'static hmac::Algorithm);

pub static SHA256: Hmac = Hmac(&hmac::HMAC_SHA256);

pub static SHA384: Hmac = Hmac(&hmac::HMAC_SHA384);

impl crypto::hmac::Hmac for Hmac {
    fn with_key(&self, key: &[u8]) -> Box<dyn crypto::hmac::Key> {
        Box::new(Key(hmac::Key::new(self.0, key)))
    }

    fn hash_output_len(&self) -> usize {
        self.0.tag_len()
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
