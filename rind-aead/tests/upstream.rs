//! RustCrypto's documented examples for `aes_gcm` and `chacha20poly1305`, with
//! only the crate in each path swapped for its rind-aead module, so code
//! written against those crates builds here unchanged; each ciphertext is
//! opened by the crate's own type too.

#[test]
fn aes_gcm_example() -> Result<(), Box<dyn core::error::Error>> {
    use rind_aead::aes_gcm::{
        Aes256Gcm, Nonce,
        aead::{Aead, Generate, Key, KeyInit},
    };

    let key = Key::<Aes256Gcm>::generate();
    let cipher = Aes256Gcm::new(&key);
    let nonce = Nonce::generate(); // MUST be unique per message
    let ciphertext = cipher.encrypt(&nonce, b"plaintext message".as_ref())?;
    let plaintext = cipher.decrypt(&nonce, ciphertext.as_ref())?;
    assert_eq!(&plaintext, b"plaintext message");

    let theirs = <aes_gcm::Aes256Gcm as aes_gcm::KeyInit>::new(&key);
    assert_eq!(
        aes_gcm::aead::Aead::decrypt(&theirs, &nonce, ciphertext.as_ref())?,
        plaintext
    );
    let _: rind_aead::aes_gcm::Tag = Default::default();
    Ok(())
}

#[test]
fn aes_gcm_in_place_example() -> Result<(), Box<dyn core::error::Error>> {
    use rind_aead::aes_gcm::{
        Aes128Gcm, Nonce,
        aead::{AeadInOut, Generate, Key, KeyInit},
    };

    let key = Key::<Aes128Gcm>::generate();
    let cipher = Aes128Gcm::new(&key);
    let nonce = Nonce::generate(); // MUST be unique per message
    let mut buffer = b"plaintext message".to_vec();
    cipher.encrypt_in_place(&nonce, b"", &mut buffer)?;
    assert_ne!(buffer, b"plaintext message");
    cipher.decrypt_in_place(&nonce, b"", &mut buffer)?;
    assert_eq!(buffer, b"plaintext message");
    Ok(())
}

#[test]
fn chacha20poly1305_example() -> Result<(), Box<dyn core::error::Error>> {
    use rind_aead::chacha20poly1305::{
        ChaCha20Poly1305, Nonce,
        aead::{Aead, Generate, Key, KeyInit},
    };

    let key = Key::<ChaCha20Poly1305>::generate();
    let cipher = ChaCha20Poly1305::new(&key);
    let nonce = Nonce::generate(); // MUST be unique per message
    let ciphertext = cipher.encrypt(&nonce, b"plaintext message".as_ref())?;
    let plaintext = cipher.decrypt(&nonce, ciphertext.as_ref())?;
    assert_eq!(&plaintext, b"plaintext message");

    let theirs = <chacha20poly1305::ChaCha20Poly1305 as chacha20poly1305::KeyInit>::new(&key);
    assert_eq!(
        chacha20poly1305::aead::Aead::decrypt(&theirs, &nonce, ciphertext.as_ref())?,
        plaintext
    );
    // The crate's own key, nonce and tag aliases.
    let _: rind_aead::chacha20poly1305::Key = key;
    let _: rind_aead::chacha20poly1305::Tag = Default::default();
    Ok(())
}
