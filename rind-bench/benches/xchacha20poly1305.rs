#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use common::{AEAD_ROWS, Aead, Dit};

/// Each seal draws a fresh random nonce, as a randomized-nonce key must.
#[cfg(not(target_arch = "xtensa"))]
const KEY: [u8; 32] = [0; 32];

/// aws-lc's XChaCha20-Poly1305, which aws-lc-rs does not expose.
#[cfg(not(target_arch = "xtensa"))]
struct AwsXChaCha(*mut aws_lc_sys::EVP_AEAD_CTX);

#[cfg(not(target_arch = "xtensa"))]
impl AwsXChaCha {
    fn new(key: &[u8; 32]) -> Self {
        // SAFETY: the key pointer and length describe `key`, and aws-lc copies it.
        let ctx = unsafe {
            aws_lc_sys::EVP_AEAD_CTX_new(
                aws_lc_sys::EVP_aead_xchacha20_poly1305(),
                key.as_ptr(),
                key.len(),
                16,
            )
        };
        assert!(!ctx.is_null());
        Self(ctx)
    }

    fn seal(&self, aad: &[u8], buf: &mut [u8]) {
        let mut nonce = [0u8; 24];
        rind::rand::fill(&mut nonce).unwrap();
        let mut tag = [0u8; 16];
        let mut tag_len = 0;
        // SAFETY: each pointer and length describes a live buffer, and aws-lc
        // allows `out` to equal `in`.
        let ok = unsafe {
            aws_lc_sys::EVP_AEAD_CTX_seal_scatter(
                self.0,
                buf.as_mut_ptr(),
                tag.as_mut_ptr(),
                &mut tag_len,
                tag.len(),
                nonce.as_ptr(),
                nonce.len(),
                buf.as_ptr(),
                buf.len(),
                std::ptr::null(),
                0,
                aad.as_ptr(),
                aad.len(),
            )
        };
        assert_eq!(ok, 1);
    }
}

#[cfg(not(target_arch = "xtensa"))]
impl Drop for AwsXChaCha {
    fn drop(&mut self) {
        // SAFETY: `self.0` came from `EVP_AEAD_CTX_new` and is freed once.
        unsafe { aws_lc_sys::EVP_AEAD_CTX_free(self.0) }
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rc_chacha(key: &chacha20poly1305::XChaCha20Poly1305, aad: &[u8], buf: &mut [u8]) {
    use chacha20poly1305::AeadInOut;
    let mut nonce = [0u8; 24];
    rind::rand::fill(&mut nonce).unwrap();
    let nonce = &nonce;
    let _tag = key
        .encrypt_inout_detached(nonce.into(), aad, buf.into())
        .unwrap();
}

#[cfg(not(target_arch = "xtensa"))]
fn test_rind_chacha(
    key: &rind::aead::RandomizedNonceKey,
    aad: &[u8],
    buf: &mut Vec<u8>,
    len: usize,
) {
    // Drops the last iteration's tag; the capacity holds the next one.
    buf.truncate(len);
    let _nonce = key.seal_in_place_append_tag(aad, buf).unwrap();
}

/// A key and the buffer it seals in place each call: the same buffer, so a
/// call times the cipher alone, without an allocation or a copy of the
/// input. Its room for rind's appended tag keeps sealing from reallocating.
#[cfg(not(target_arch = "xtensa"))]
struct Seal<K> {
    key: K,
    aad: &'static [u8],
    buf: Vec<u8>,
}

#[cfg(not(target_arch = "xtensa"))]
impl<K> Seal<K> {
    fn new(key: K, row: Aead) -> Self {
        let mut buf = Vec::with_capacity(row.len() + 16);
        buf.resize(row.len(), 0);
        Self {
            key,
            aad: row.aad,
            buf,
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
mod xchacha20poly1305 {
    use swole::bench;

    use super::*;

    fn aws_seal(row: Aead) -> Seal<AwsXChaCha> {
        Seal::new(AwsXChaCha::new(&KEY), row)
    }

    #[bench(args = AEAD_ROWS, setup = aws_seal)]
    fn aws_lc_rs(s: &mut Seal<AwsXChaCha>) {
        s.key.seal(s.aad, &mut s.buf);
    }

    fn rustcrypto_seal(row: Aead) -> Seal<chacha20poly1305::XChaCha20Poly1305> {
        use chacha20poly1305::KeyInit;
        Seal::new(
            chacha20poly1305::XChaCha20Poly1305::new_from_slice(&KEY).unwrap(),
            row,
        )
    }

    #[bench(args = AEAD_ROWS, setup = rustcrypto_seal)]
    fn rustcrypto(s: &mut Seal<chacha20poly1305::XChaCha20Poly1305>) {
        test_rc_chacha(&s.key, s.aad, &mut s.buf);
    }

    fn rind_seal(row: Aead) -> Dit<(Seal<rind::aead::RandomizedNonceKey>, usize)> {
        let key = rind::aead::RandomizedNonceKey::new(&KEY);
        Dit::hold((Seal::new(key, row), row.len()))
    }

    #[bench(args = AEAD_ROWS, setup = rind_seal)]
    fn rind(s: &mut Dit<(Seal<rind::aead::RandomizedNonceKey>, usize)>) {
        let (s, len) = &mut **s;
        test_rind_chacha(&s.key, s.aad, &mut s.buf, *len);
    }

    #[cfg(graviola)]
    fn graviola_seal(row: Aead) -> Seal<(graviola::aead::XChaCha20Poly1305, [u8; 16])> {
        Seal::new((graviola::aead::XChaCha20Poly1305::new(KEY), [0; 16]), row)
    }

    #[cfg(graviola)]
    #[bench(args = AEAD_ROWS, setup = graviola_seal)]
    fn graviola(s: &mut Seal<(graviola::aead::XChaCha20Poly1305, [u8; 16])>) {
        let (key, tag) = &mut s.key;
        let mut nonce = [0u8; 24];
        rind::rand::fill(&mut nonce).unwrap();
        key.encrypt(&nonce, s.aad, &mut s.buf, tag);
    }

    /// libcrux seals out of place, appending the tag.
    fn libcrux_seal(row: Aead) -> Seal<Vec<u8>> {
        Seal::new(vec![0; row.len() + 16], row)
    }

    #[bench(args = AEAD_ROWS, setup = libcrux_seal)]
    fn libcrux(s: &mut Seal<Vec<u8>>) {
        use libcrux_chacha20poly1305::xchacha20_poly1305::encrypt;
        let mut nonce = [0u8; 24];
        rind::rand::fill(&mut nonce).unwrap();
        encrypt(&KEY, &s.buf, &mut s.key, s.aad, &nonce).unwrap();
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
