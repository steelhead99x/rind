//! Ed25519 against ed25519-dalek: the same key and the same (deterministic)
//! signature for every seed and message, each verifying the other's, and the
//! malformed keys and signatures both refuse.

use ed25519::Signature;
use signature::{Keypair, MultipartSigner, MultipartVerifier, Signer, Verifier};

struct Xorshift(u64);

impl Xorshift {
    fn bytes<const N: usize>(&mut self) -> [u8; N] {
        self.vec(N).try_into().unwrap()
    }

    fn vec(&mut self, len: usize) -> Vec<u8> {
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

use rind_signature::ed25519::{SigningKey, VerifyingKey};

const LENGTHS: &[usize] = &[0, 1, 2, 31, 32, 33, 63, 64, 65, 127, 128, 129, 1000, 65_537];

#[test]
fn the_same_keys_and_signatures_as_dalek() {
    let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
    for _ in 0..24 {
        let seed: [u8; 32] = rng.bytes();
        let ours = SigningKey::from_bytes(&seed);
        let theirs = ed25519_dalek::SigningKey::from_bytes(&seed);
        // The same public key.
        assert_eq!(
            ours.verifying_key().to_bytes(),
            theirs.verifying_key().to_bytes()
        );
        assert_eq!(ours.as_ref().as_bytes(), theirs.verifying_key().as_bytes());
        for &len in LENGTHS {
            let msg = rng.vec(len);
            let our_sig = ours.try_sign(&msg).unwrap();
            let their_sig = theirs.try_sign(&msg).unwrap();
            assert_eq!(our_sig, their_sig, "{len} bytes");
            // Each verifies the other's.
            ours.verifying_key().verify(&msg, &their_sig).unwrap();
            theirs.verifying_key().verify(&msg, &our_sig).unwrap();
            ours.verify(&msg, &our_sig).unwrap();
            // A multipart message signs and verifies as the whole.
            let cut = len / 2;
            let parts: [&[u8]; 3] = [&msg[..cut], &[], &msg[cut..]];
            let multi = ours.try_multipart_sign(&parts).unwrap();
            assert_eq!(multi, our_sig);
            ours.verifying_key()
                .multipart_verify(&parts, &multi)
                .unwrap();
        }
    }
}

#[test]
fn what_is_altered_is_refused_by_both() {
    let mut rng = Xorshift(0xd1b5_4a32_d192_ed03);
    let seed: [u8; 32] = rng.bytes();
    let ours = SigningKey::from_bytes(&seed);
    let theirs = ed25519_dalek::SigningKey::from_bytes(&seed);
    let msg = rng.vec(100);
    let sig = ours.try_sign(&msg).unwrap();
    // Every bit of the signature.
    for byte in 0..64 {
        for bit in 0..8 {
            let mut bytes = sig.to_bytes();
            bytes[byte] ^= 1 << bit;
            let bad = Signature::from_bytes(&bytes);
            assert!(
                ours.verifying_key().verify(&msg, &bad).is_err(),
                "byte {byte} bit {bit}"
            );
            assert!(
                theirs.verifying_key().verify(&msg, &bad).is_err(),
                "byte {byte} bit {bit}"
            );
        }
    }
    // A different message, and a different key.
    let mut other = msg.clone();
    other[0] ^= 1;
    assert!(ours.verifying_key().verify(&other, &sig).is_err());
    assert!(theirs.verifying_key().verify(&other, &sig).is_err());
    let stranger = SigningKey::from_bytes(&rng.bytes());
    assert!(stranger.verifying_key().verify(&msg, &sig).is_err());
    assert!(
        ours.verifying_key()
            .multipart_verify(&[&other], &sig)
            .is_err()
    );
}

#[test]
fn malformed_keys_are_refused() {
    // A seed or public key of the wrong length.
    for len in [0usize, 1, 31, 33, 64] {
        assert!(
            SigningKey::try_from(vec![1u8; len].as_slice()).is_err(),
            "seed {len}"
        );
        assert!(
            VerifyingKey::try_from(vec![1u8; len].as_slice()).is_err(),
            "key {len}"
        );
        assert!(ed25519_dalek::VerifyingKey::try_from(vec![1u8; len].as_slice()).is_err());
    }
    // A y coordinate with no point: both refuse it.
    let mut off_curve = [0u8; 32];
    off_curve[0] = 2;
    assert!(ed25519_dalek::VerifyingKey::from_bytes(&off_curve).is_err());
    assert!(VerifyingKey::from_bytes(&off_curve).is_err());
}

#[test]
fn rind_is_strict_where_dalek_verify_is_lenient() {
    // The identity point is a small-order key. ed25519-dalek's `verify` takes it
    // (its `verify_strict` does not); rind refuses it, as `verify_strict` does.
    let mut identity = [0u8; 32];
    identity[0] = 1;
    assert!(VerifyingKey::from_bytes(&identity).is_err());
    assert!(ed25519_dalek::VerifyingKey::from_bytes(&identity).is_ok());
}

// One generic function per trait, instantiated with rind's type.
fn generic_sign_verify<K: Signer<Signature> + Verifier<Signature>>(
    key: &K,
    msg: &[u8],
) -> Signature {
    let sig = key.sign(msg);
    key.verify(msg, &sig).unwrap();
    sig
}

fn generic_keypair<K: Keypair>(key: &K) -> K::VerifyingKey {
    key.verifying_key()
}

#[test]
fn a_generic_function_runs_on_rind() {
    let seed = [7u8; 32];
    let ours = SigningKey::from_bytes(&seed);
    let theirs = ed25519_dalek::SigningKey::from_bytes(&seed);
    assert_eq!(
        generic_sign_verify(&ours, b"generic"),
        generic_sign_verify(&theirs, b"generic")
    );
    assert_eq!(
        generic_keypair(&ours).to_bytes(),
        generic_keypair(&theirs).to_bytes()
    );
}
