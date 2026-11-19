//! RSA against the `rsa` crate: PKCS#1 v1.5 signatures that are byte for byte
//! the same (the scheme is deterministic), each verifying the other's, PSS
//! signatures from `rsa` verifying under rind's key, and everything altered
//! refused by both.

use rsa::pkcs8::DecodePrivateKey;
use signature::{MultipartSigner, MultipartVerifier, SignatureEncoding, Signer, Verifier};

const KEY: &[u8] = include_bytes!("data/rsa2048.pkcs8.der");

struct Xorshift(u64);

impl Xorshift {
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

fn private_key() -> rsa::PrivateKey {
    rsa::PrivateKey::from_pkcs8_der(KEY).expect("the test key parses")
}

const LENGTHS: &[usize] = &[0, 1, 31, 32, 33, 64, 100, 1000, 10_007];

macro_rules! pkcs1v15_tests {
    ($($test:ident: $ours:ident, $theirs:ty;)*) => {$(
        #[test]
        fn $test() {
            use rind_signature::rsa::pkcs1v15 as rind;
            let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
            let key = private_key();
            let ours = rind::SigningKey::<rind_digest::sha2::$ours>::try_new(key.clone()).unwrap();
            let theirs = rsa::pkcs1v15::SigningKey::<$theirs>::new(key.clone());
            let our_verifier = ours.verifying_key();
            let their_verifier = rsa::pkcs1v15::VerifyingKey::<$theirs>::new(rsa::PublicKey::from(&key));
            for &len in LENGTHS {
                let msg = rng.vec(len);
                let ours_sig = ours.try_sign(&msg).unwrap();
                let theirs_sig = theirs.try_sign(&msg).unwrap();
                // The same bytes: PKCS#1 v1.5 is deterministic.
                assert_eq!(ours_sig.to_bytes(), theirs_sig.to_bytes(), "{len} bytes");
                our_verifier.verify(&msg, &theirs_sig).unwrap();
                their_verifier.verify(&msg, &ours_sig).unwrap();
                // A multipart message is the whole message.
                let cut = len / 2;
                let parts: [&[u8]; 3] = [&msg[..cut], &[], &msg[cut..]];
                let multi = ours.try_multipart_sign(&parts).unwrap();
                assert_eq!(multi.to_bytes(), ours_sig.to_bytes());
                our_verifier.multipart_verify(&parts, &multi).unwrap();
            }
            // Altered signatures and messages, refused by both.
            let msg = rng.vec(100);
            let sig = ours.try_sign(&msg).unwrap();
            let bytes = sig.to_bytes();
            for at in (0..bytes.len()).step_by(7) {
                let mut bad = bytes.to_vec();
                bad[at] ^= 0x01;
                let bad = rsa::pkcs1v15::Signature::try_from(bad.as_slice()).unwrap();
                assert!(our_verifier.verify(&msg, &bad).is_err(), "byte {at}");
                assert!(their_verifier.verify(&msg, &bad).is_err(), "byte {at}");
            }
            let mut other = msg.clone();
            other[0] ^= 1;
            assert!(our_verifier.verify(&other, &sig).is_err());
            assert!(their_verifier.verify(&other, &sig).is_err());
            assert!(our_verifier.multipart_verify(&[&other], &sig).is_err());
            // A signature of the wrong length.
            for len in [0usize, 1, 255, 257, 512] {
                if let Ok(short) = rsa::pkcs1v15::Signature::try_from(vec![1u8; len].as_slice()) {
                    assert!(our_verifier.verify(&msg, &short).is_err(), "{len}");
                    assert!(their_verifier.verify(&msg, &short).is_err(), "{len}");
                }
            }
            // Another hash is another signature.
            let wrong_hash = rind::VerifyingKey::<rind_digest::sha2::Sha512>::try_new(rsa::PublicKey::from(&key)).unwrap();
            if stringify!($ours) != "Sha512" {
                assert!(wrong_hash.verify(&msg, &sig).is_err());
            }
        }
    )*};
}

pkcs1v15_tests! {
    pkcs1v15_sha256: Sha256, sha2::Sha256;
    pkcs1v15_sha384: Sha384, sha2::Sha384;
    pkcs1v15_sha512: Sha512, sha2::Sha512;
}

macro_rules! pss_tests {
    ($($test:ident: $ours:ident, $theirs:ty;)*) => {$(
        #[test]
        fn $test() {
            use rind_signature::rsa::pss as rind;
            let mut rng = Xorshift(0xd1b5_4a32_d192_ed03);
            let key = private_key();
            let theirs = rsa::pss::SigningKey::<$theirs>::new(key.clone());
            let public = rsa::PublicKey::from(&key);
            let ours = rind::VerifyingKey::<rind_digest::sha2::$ours>::try_new(public.clone()).unwrap();
            let any_salt = rind::VerifyingKey::<rind_digest::sha2::$ours>::try_new_with_auto_salt_len(public).unwrap();
            let signer = rind::SigningKey::<rind_digest::sha2::$ours>::try_new(key.clone()).unwrap();
            for &len in LENGTHS {
                let msg = rng.vec(len);
                let sig = theirs.try_sign(&msg).unwrap();
                ours.verify(&msg, &sig).unwrap();
                any_salt.verify(&msg, &sig).unwrap();
                // rind's PSS signature verifies under `rsa`'s key, which it did not make.
                let ours_sig = signer.try_sign(&msg).unwrap();
                rsa::pss::VerifyingKey::<$theirs>::new(rsa::PublicKey::from(&key)).verify(&msg, &ours_sig).unwrap();
                signer.verifying_key().verify(&msg, &ours_sig).unwrap();
                let parts_sig = signer.try_multipart_sign(&[&msg[..len / 2], &msg[len / 2..]]).unwrap();
                signer.verifying_key().verify(&msg, &parts_sig).unwrap();
                let parts: [&[u8]; 2] = [&msg[..len / 2], &msg[len / 2..]];
                ours.multipart_verify(&parts, &sig).unwrap();
                // Altered, refused.
                let mut other = msg.clone();
                other.push(0);
                assert!(ours.verify(&other, &sig).is_err());
                let bytes = sig.to_bytes();
                for at in (0..bytes.len()).step_by(11) {
                    let mut bad = bytes.to_vec();
                    bad[at] ^= 0x01;
                    let bad = rsa::pss::Signature::try_from(bad.as_slice()).unwrap();
                    assert!(ours.verify(&msg, &bad).is_err(), "byte {at}");
                }
            }
        }
    )*};
}

pss_tests! {
    pss_sha256: Sha256, sha2::Sha256;
    pss_sha384: Sha384, sha2::Sha384;
    pss_sha512: Sha512, sha2::Sha512;
}

// One generic function per trait, instantiated with rind's type.
fn generic_sign_verify<
    S: Signer<rsa::pkcs1v15::Signature>,
    V: Verifier<rsa::pkcs1v15::Signature>,
>(
    signer: &S,
    verifier: &V,
    msg: &[u8],
) {
    let signature = signer.sign(msg);
    verifier.verify(msg, &signature).unwrap();
}

#[test]
fn a_generic_function_runs_on_rind() {
    use rind_signature::rsa::pkcs1v15 as rind;
    let key = private_key();
    let ours = rind::SigningKey::<rind_digest::sha2::Sha256>::try_new(key).unwrap();
    generic_sign_verify(&ours, &ours.verifying_key(), b"generic over Signer");
}

/// A public key `rsa` holds but rind refuses, as a modulus above 8192 bits: a
/// verifying key from it is an error, never a panic, in both schemes and every
/// constructor.
#[test]
fn a_public_key_rind_refuses_is_an_error() {
    use rind_signature::rsa::{pkcs1v15, pss};
    use rsa::BoxedUint;

    // 2^8999 + 1 is odd and 9000 bits long; rsa takes it once its size limit is raised.
    let modulus =
        (BoxedUint::one_with_precision(9024) << 8999) | BoxedUint::one_with_precision(9024);
    let exponent = BoxedUint::from(65537u64);
    let key = rsa::PublicKey::new_with_max_size(modulus, exponent, 16384).unwrap();

    type Hash = rind_digest::sha2::Sha256;
    assert!(pkcs1v15::VerifyingKey::<Hash>::try_new(key.clone()).is_err());
    assert!(pkcs1v15::VerifyingKey::<Hash>::try_from(key.clone()).is_err());
    assert!(pss::VerifyingKey::<Hash>::try_new(key.clone()).is_err());
    assert!(pss::VerifyingKey::<Hash>::try_new_with_auto_salt_len(key.clone()).is_err());
    assert!(pss::VerifyingKey::<Hash>::try_from(key).is_err());
}
