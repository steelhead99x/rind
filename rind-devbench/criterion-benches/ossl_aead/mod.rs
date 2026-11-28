//! OpenSSL's AEADs through EVP, one context per key and direction, as a
//! connection keeps them: each message only resets the nonce.

use openssl::cipher::CipherRef;
use openssl::cipher_ctx::CipherCtx;

pub struct Sealer(CipherCtx);

impl Sealer {
    pub fn new(cipher: &CipherRef, key: &[u8]) -> Self {
        let mut ctx = CipherCtx::new().unwrap();
        ctx.encrypt_init(Some(cipher), Some(key), None).unwrap();
        Self(ctx)
    }

    pub fn seal(&mut self, nonce: &[u8; 12], aad: &[u8], buf: &mut [u8]) -> [u8; 16] {
        self.0.encrypt_init(None, None, Some(nonce)).unwrap();
        self.0.cipher_update(aad, None).unwrap();
        let len = buf.len();
        self.0.cipher_update_inplace(buf, len).unwrap();
        self.0.cipher_final(&mut []).unwrap();
        let mut tag = [0u8; 16];
        self.0.tag(&mut tag).unwrap();
        tag
    }
}

#[allow(dead_code)]
pub struct Opener(CipherCtx);

#[allow(dead_code)]
impl Opener {
    pub fn new(cipher: &CipherRef, key: &[u8]) -> Self {
        let mut ctx = CipherCtx::new().unwrap();
        ctx.decrypt_init(Some(cipher), Some(key), None).unwrap();
        Self(ctx)
    }

    pub fn open(&mut self, nonce: &[u8; 12], aad: &[u8], tag: &[u8], buf: &mut [u8]) {
        self.0.decrypt_init(None, None, Some(nonce)).unwrap();
        self.0.set_tag(tag).unwrap();
        self.0.cipher_update(aad, None).unwrap();
        let len = buf.len();
        self.0.cipher_update_inplace(buf, len).unwrap();
        self.0.cipher_final(&mut []).unwrap();
    }
}
