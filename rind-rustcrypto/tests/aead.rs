//! Every AEAD here against RustCrypto's own crate: the same ciphertext and tag
//! for the same key, nonce, and data; each opens the other's; and both refuse
//! what is altered.
#![cfg(feature = "aead-0_6")]

use aead::{Aead, AeadInOut, KeyInit, Payload, array::Array};

struct Xorshift(u64);

impl Xorshift {
    fn bytes(&mut self, len: usize) -> Vec<u8> {
        (0..len)
            .map(|_| {
                self.0 ^= self.0 << 13;
                self.0 ^= self.0 >> 7;
                self.0 ^= self.0 << 17;
                (self.0 >> 24) as u8
            })
            .collect()
    }
}

/// Around every block (16) and chunk (64) boundary the ciphers have, empty, and long.
const LENGTHS: &[usize] = &[
    0, 1, 2, 15, 16, 17, 31, 32, 33, 63, 64, 65, 127, 128, 129, 255, 256, 257, 1000, 4096, 10_007,
];

fn compare<Ours, Theirs>(seed: u64)
where
    Ours: Aead + KeyInit,
    Theirs: Aead + KeyInit,
{
    let mut rng = Xorshift(seed);
    let key_len = <Ours as aead::common::KeySizeUser>::key_size();
    for &plain_len in LENGTHS {
        for aad_len in [0usize, 1, 16, 33, 300] {
            let key = rng.bytes(key_len);
            let nonce = rng.bytes(12);
            let aad = rng.bytes(aad_len);
            let plaintext = rng.bytes(plain_len);
            let ours = Ours::new_from_slice(&key).unwrap();
            let theirs = Theirs::new_from_slice(&key).unwrap();
            let (our_nonce, their_nonce) = (
                Array::try_from(nonce.as_slice()).unwrap(),
                Array::try_from(nonce.as_slice()).unwrap(),
            );
            let payload = Payload {
                msg: &plaintext,
                aad: &aad,
            };
            let sealed = ours.encrypt(&our_nonce, payload).unwrap();
            let payload = Payload {
                msg: &plaintext,
                aad: &aad,
            };
            assert_eq!(
                sealed,
                theirs.encrypt(&their_nonce, payload).unwrap(),
                "{plain_len}+{aad_len}"
            );
            assert_eq!(sealed.len(), plain_len + 16);
            // Each opens what the other sealed.
            let by_ours = |ct: &[u8]| ours.decrypt(&our_nonce, Payload { msg: ct, aad: &aad });
            let by_theirs =
                |ct: &[u8]| theirs.decrypt(&their_nonce, Payload { msg: ct, aad: &aad });
            assert_eq!(by_ours(&sealed).unwrap(), plaintext);
            assert_eq!(by_theirs(&sealed).unwrap(), plaintext);

            // Every flipped bit of a short message, or sampled positions of a long one, is refused.
            let stride = (sealed.len() / 40).max(1);
            for i in (0..sealed.len()).step_by(stride) {
                let mut bad = sealed.clone();
                bad[i] ^= 0x01;
                assert!(by_ours(&bad).is_err(), "ours accepted a flip at {i}");
                assert!(by_theirs(&bad).is_err(), "theirs accepted a flip at {i}");
            }
            // Wrong associated data and wrong nonce.
            let other_aad = [aad.as_slice(), b"x"].concat();
            assert!(
                ours.decrypt(
                    &our_nonce,
                    Payload {
                        msg: &sealed,
                        aad: &other_aad
                    }
                )
                .is_err()
            );
            assert!(
                theirs
                    .decrypt(
                        &their_nonce,
                        Payload {
                            msg: &sealed,
                            aad: &other_aad
                        }
                    )
                    .is_err()
            );
            let mut other_nonce = our_nonce.clone();
            other_nonce[0] ^= 1;
            assert!(
                ours.decrypt(
                    &other_nonce,
                    Payload {
                        msg: &sealed,
                        aad: &aad
                    }
                )
                .is_err()
            );
            // Shorter than a tag: both refuse, neither panics.
            for cut in [0usize, 1, 15] {
                let short = &sealed[..cut.min(sealed.len())];
                assert!(by_ours(short).is_err());
                assert!(by_theirs(short).is_err());
            }
        }
    }
}

#[test]
fn aes_128_gcm() {
    compare::<rind_rustcrypto::aes_gcm::Aes128Gcm, aes_gcm::Aes128Gcm>(0x1);
}

#[test]
fn aes_256_gcm() {
    compare::<rind_rustcrypto::aes_gcm::Aes256Gcm, aes_gcm::Aes256Gcm>(0x2);
}

#[test]
fn chacha20_poly1305() {
    compare::<
        rind_rustcrypto::chacha20poly1305::ChaCha20Poly1305,
        chacha20poly1305::ChaCha20Poly1305,
    >(0x3);
}

/// The in-place and detached forms, with separate input and output buffers too.
fn inout_forms<A: AeadInOut + KeyInit>() {
    let mut rng = Xorshift(0xabcd);
    let key = rng.bytes(<A as aead::common::KeySizeUser>::key_size());
    let aead = A::new_from_slice(&key).unwrap();
    let nonce = Array::try_from(rng.bytes(12).as_slice()).unwrap();
    for &len in LENGTHS {
        let plaintext = rng.bytes(len);
        let aad = rng.bytes(7);
        // In place with a growing buffer: the tag is appended.
        let mut buffer = plaintext.clone();
        aead.encrypt_in_place(&nonce, &aad, &mut buffer).unwrap();
        assert_eq!(buffer.len(), len + 16);
        // Detached, in place: the same ciphertext and tag.
        let mut detached = plaintext.clone();
        let tag = aead
            .encrypt_inout_detached(&nonce, &aad, detached.as_mut_slice().into())
            .unwrap();
        assert_eq!(&buffer[..len], detached.as_slice());
        assert_eq!(&buffer[len..], tag.as_slice());
        // Detached into a separate output buffer, leaving the input untouched.
        let mut out = vec![0u8; len];
        let in_buf = aead::inout::InOutBuf::new(&plaintext, &mut out).unwrap();
        let tag2 = aead.encrypt_inout_detached(&nonce, &aad, in_buf).unwrap();
        assert_eq!(out, detached);
        assert_eq!(tag2, tag);
        // Open in place, then detached into a separate buffer.
        let mut opened = buffer.clone();
        aead.decrypt_in_place(&nonce, &aad, &mut opened).unwrap();
        assert_eq!(opened, plaintext);
        let mut clear = vec![0u8; len];
        let in_buf = aead::inout::InOutBuf::new(&detached, &mut clear).unwrap();
        aead.decrypt_inout_detached(&nonce, &aad, in_buf, &tag)
            .unwrap();
        assert_eq!(clear, plaintext);
        // A wrong tag is refused, and no plaintext is left in the buffer.
        if len > 0 {
            let mut bad = tag;
            bad[0] ^= 1;
            let mut data = detached.clone();
            assert!(
                aead.decrypt_inout_detached(&nonce, &aad, data.as_mut_slice().into(), &bad)
                    .is_err()
            );
            assert!(
                data != plaintext,
                "a refused message left its plaintext behind"
            );
        }
    }
}

#[test]
fn the_inout_forms() {
    inout_forms::<rind_rustcrypto::aes_gcm::Aes128Gcm>();
    inout_forms::<rind_rustcrypto::aes_gcm::Aes256Gcm>();
    inout_forms::<rind_rustcrypto::chacha20poly1305::ChaCha20Poly1305>();
}

#[test]
fn a_key_of_the_wrong_length_is_refused() {
    use rind_rustcrypto::aes_gcm::Aes256Gcm;
    for len in [0usize, 1, 15, 16, 31, 33, 64] {
        assert!(Aes256Gcm::new_from_slice(&vec![0; len]).is_err(), "{len}");
    }
    assert!(Aes256Gcm::new_from_slice(&[0; 32]).is_ok());
}

// One generic function per trait, instantiated with rind's types.
fn generic_round_trip<A: Aead + KeyInit>(plaintext: &[u8]) -> Vec<u8> {
    let aead = A::new_from_slice(&vec![7u8; <A as aead::common::KeySizeUser>::key_size()]).unwrap();
    let nonce = Array::try_from([9u8; 12].as_slice()).unwrap();
    let sealed = aead.encrypt(&nonce, plaintext).unwrap();
    assert_eq!(aead.decrypt(&nonce, sealed.as_slice()).unwrap(), plaintext);
    sealed
}

#[test]
fn a_generic_function_runs_on_rind() {
    assert_eq!(
        generic_round_trip::<rind_rustcrypto::aes_gcm::Aes256Gcm>(b"generic over Aead"),
        generic_round_trip::<aes_gcm::Aes256Gcm>(b"generic over Aead")
    );
    assert_eq!(
        generic_round_trip::<rind_rustcrypto::chacha20poly1305::ChaCha20Poly1305>(b"x"),
        generic_round_trip::<chacha20poly1305::ChaCha20Poly1305>(b"x")
    );
}
