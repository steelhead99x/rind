//! RustCrypto's documented examples for `p256`, `ed25519_dalek` and `ml_dsa`,
//! with only the crate in each path swapped for its rind-signature module, so
//! code written against those crates builds here unchanged; each signature is
//! checked by the crate's own verifier too.

use crypto_common::getrandom::SysRng;
use crypto_common::rand_core::UnwrapErr;

#[test]
fn p256_example() -> Result<(), Box<dyn core::error::Error>> {
    use rind_signature::p256::ecdsa::{Signature, SigningKey, signature::Signer};

    // rind's key from RustCrypto's: `generate` is a gap, `to_bytes` is not.
    let theirs = p256::ecdsa::SigningKey::from_slice(&[0x17; 32])?;
    let signing_key = SigningKey::from_bytes(&theirs.to_bytes())?;
    assert_eq!(signing_key.to_bytes(), theirs.to_bytes());
    let verifying_key_bytes = signing_key.verifying_key().to_sec1_bytes();

    let message = b"ECDSA proves knowledge of a secret number in the context of a single message";
    let signature: Signature = signing_key.sign(message);

    use rind_signature::p256::ecdsa::{VerifyingKey, signature::Verifier};
    let verifying_key = VerifyingKey::from_sec1_bytes(verifying_key_bytes.as_ref())?;
    verifying_key.verify(message, &signature)?;
    theirs.verifying_key().verify(message, &signature)?;

    // The crate's own error, re-exported as `p256::ecdsa::Error`.
    let _: rind_signature::p256::ecdsa::Error = signature::Error::new();
    Ok(())
}

#[test]
fn ed25519_dalek_example() -> Result<(), Box<dyn core::error::Error>> {
    use rind_signature::ed25519::{Signature, Signer, SigningKey, Verifier};

    let mut csprng = UnwrapErr(SysRng);
    let signing_key: SigningKey = SigningKey::generate(&mut csprng);
    let message: &[u8] = b"This is a test of the tsunami alert system.";
    let signature: Signature = signing_key.sign(message);
    assert!(signing_key.verify(message, &signature).is_ok());

    // The same key in RustCrypto's crate, through its byte forms.
    let theirs = ed25519_dalek::SigningKey::from_keypair_bytes(&signing_key.to_keypair_bytes())?;
    assert_eq!(theirs.to_bytes(), signing_key.to_bytes());
    assert_eq!(theirs.sign(message), signature);
    let back = SigningKey::from_keypair_bytes(&theirs.to_keypair_bytes())?;
    assert!(back == signing_key);

    // A public key that is not the seed's is refused, as RustCrypto refuses it.
    let mut mismatched = signing_key.to_keypair_bytes();
    mismatched[63] ^= 1;
    assert!(SigningKey::from_keypair_bytes(&mismatched).is_err());
    assert!(ed25519_dalek::SigningKey::from_keypair_bytes(&mismatched).is_err());
    Ok(())
}

#[test]
fn ml_dsa_example() -> Result<(), signature::Error> {
    use rind_signature::ml_dsa::{Generate, Keypair, MlDsa65, Signer, SigningKey, Verifier};

    let sk = SigningKey::<MlDsa65>::generate();
    let msg = b"Hello world";
    let sig = sk.sign(msg);
    sk.verifying_key().verify(msg, &sig)?;
    let _ = sk.verifying_key();
    let _ = Keypair::verifying_key(&sk);

    // The seed round-trips through RustCrypto's key traits, and RustCrypto's
    // key from it verifies rind's signature.
    use rind_signature::ml_dsa::{KeyExport, KeyInit};
    let seed = sk.to_bytes();
    assert_eq!(seed, sk.to_seed());
    let theirs = ml_dsa::SigningKey::<MlDsa65>::new(&seed);
    theirs.verifying_key().verify(msg, &sig)?;
    assert_eq!(
        <SigningKey<MlDsa65> as KeyInit>::new(&seed)
            .verifying_key()
            .encode(),
        theirs.verifying_key().encode()
    );
    Ok(())
}

/// `rsa`'s own keys take rind-digest's hashes, which carry the OIDs it needs.
#[test]
fn rsa_signs_with_rind_digest() {
    use rsa::pkcs8::DecodePrivateKey;
    use rsa::signature::{SignatureEncoding, Signer};

    let key = rsa::PrivateKey::from_pkcs8_der(include_bytes!("data/rsa2048.pkcs8.der")).unwrap();
    let ours = rsa::pkcs1v15::SigningKey::<rind_digest::sha2::Sha256>::new(key.clone());
    let theirs = rsa::pkcs1v15::SigningKey::<sha2::Sha256>::new(key);
    assert_eq!(
        ours.sign(b"message").to_bytes(),
        theirs.sign(b"message").to_bytes()
    );
}
