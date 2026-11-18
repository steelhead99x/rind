use std::hint::black_box;

use verified_garbage::aead::aes_gcm::AesGcm;
use verified_garbage::ec::{P256, PrivateKey};
use verified_garbage::hashes::sha256::Sha256;
use verified_garbage::x25519;

fn main() {
    let message = black_box(b"build cost".as_slice());

    let hash = Sha256::digest(message);

    let key = AesGcm::new(&[0x42; 16]).unwrap();
    let mut in_out = message.to_vec();
    let tag = key.encrypt_in_place(&[0; 12], b"", &mut in_out).unwrap();
    key.decrypt_in_place(&[0; 12], b"", &mut in_out, &tag)
        .unwrap();

    // No key generation: draw scalars until one is in [1, n - 1].
    let (signing_key, public_key) = loop {
        let mut d = [0; 32];
        getrandom::fill(&mut d).unwrap();
        let key = PrivateKey::<P256>::from_bytes(&d);
        if let Ok(public_key) = key.public_key() {
            break (key, public_key);
        }
    };
    let signature = signing_key.sign::<Sha256>(message).unwrap();
    public_key.verify::<Sha256>(message, &signature).unwrap();

    let alice = x25519::PrivateKey::generate().unwrap();
    let bob = x25519::PrivateKey::generate().unwrap();
    let secret = alice.exchange(&bob.public_key()).unwrap();

    black_box((hash, secret));
}
