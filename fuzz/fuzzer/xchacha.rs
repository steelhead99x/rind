#![no_main]

//! XChaCha20-Poly1305 opening what aws-lc seals, tampered with, against
//! aws-lc and RustCrypto opening it. aws-lc-rs has no XChaCha20-Poly1305, so
//! this calls aws-lc directly.

use chacha20poly1305::XChaCha20Poly1305;
use chacha20poly1305::aead::{AeadInOut, KeyInit};
use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use rind::aead::{RandomNonce, RandomizedNonceKey};

mod edit;

#[derive(Arbitrary, Debug)]
struct Input {
    key: [u8; 32],
    nonce: [u8; 24],
    aad: Vec<u8>,
    plain: Vec<u8>,
    edit: edit::Edit,
}

fuzz_target!(|input: Input| {
    let Input {
        key,
        nonce,
        aad,
        plain,
        edit,
    } = input;
    let mut sealed = aws_lc(Op::Seal, &key, &nonce, &aad, &plain).unwrap();
    assert_eq!(
        sealed,
        rustcrypto(Op::Seal, &key, &nonce, &aad, &plain).unwrap()
    );
    let changed = edit.apply(&mut sealed);

    let theirs = aws_lc(Op::Open, &key, &nonce, &aad, &sealed);
    assert_eq!(theirs, rustcrypto(Op::Open, &key, &nonce, &aad, &sealed));
    let ours = RandomizedNonceKey::new(&key)
        .open_in_place(RandomNonce::from(nonce), &aad, &mut sealed)
        .map(|plain| plain.to_vec());
    assert_eq!(ours.as_ref().ok(), theirs.as_ref());
    match changed {
        true => assert!(ours.is_err()),
        false => assert_eq!(ours.unwrap(), plain),
    }
});

enum Op {
    Seal,
    Open,
}

/// RustCrypto's XChaCha20-Poly1305 output for `input`, or `None` if it
/// refuses it.
fn rustcrypto(
    op: Op,
    key: &[u8; 32],
    nonce: &[u8; 24],
    aad: &[u8],
    input: &[u8],
) -> Option<Vec<u8>> {
    let cipher = XChaCha20Poly1305::new(key.into());
    let mut out = input.to_vec();
    match op {
        Op::Seal => {
            let tag = cipher
                .encrypt_inout_detached(nonce.into(), aad, out.as_mut_slice().into())
                .ok()?;
            out.extend_from_slice(&tag);
        }
        Op::Open => {
            let tag = out.split_off(out.len().checked_sub(16)?);
            cipher
                .decrypt_inout_detached(
                    nonce.into(),
                    aad,
                    out.as_mut_slice().into(),
                    tag.as_slice().try_into().unwrap(),
                )
                .ok()?;
        }
    }
    Some(out)
}

/// aws-lc's XChaCha20-Poly1305 output for `input`, or `None` if it refuses it.
fn aws_lc(op: Op, key: &[u8; 32], nonce: &[u8; 24], aad: &[u8], input: &[u8]) -> Option<Vec<u8>> {
    let mut out = vec![0; input.len() + 16];
    let mut out_len = 0;
    // SAFETY: each pointer and length describes a live buffer, and the
    // context is freed once, after its last use.
    let ok = unsafe {
        let ctx = aws_lc_sys::EVP_AEAD_CTX_new(
            aws_lc_sys::EVP_aead_xchacha20_poly1305(),
            key.as_ptr(),
            key.len(),
            16,
        );
        assert!(!ctx.is_null());
        let f = match op {
            Op::Seal => aws_lc_sys::EVP_AEAD_CTX_seal,
            Op::Open => aws_lc_sys::EVP_AEAD_CTX_open,
        };
        let ok = f(
            ctx,
            out.as_mut_ptr(),
            &mut out_len,
            out.len(),
            nonce.as_ptr(),
            nonce.len(),
            input.as_ptr(),
            input.len(),
            aad.as_ptr(),
            aad.len(),
        );
        aws_lc_sys::EVP_AEAD_CTX_free(ctx);
        ok
    };
    out.truncate(out_len);
    (ok == 1).then_some(out)
}
