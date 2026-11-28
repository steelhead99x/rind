//! ML-DSA at each parameter set against the `ml-dsa` crate: the same public key
//! for the same seed, each verifying the other's signatures, and every
//! alteration both refuse.

use ml_dsa::{MlDsa44, MlDsa65, MlDsa87, Signature};
use signature::{Keypair, MultipartSigner, MultipartVerifier, Signer, Verifier};

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

use rind_signature::ml_dsa::{Params, SigningKey as Ours};

fn seed(rng: &mut Xorshift) -> ml_dsa::Seed {
    ml_dsa::Seed::try_from(rng.vec(32).as_slice()).unwrap()
}

fn same_key_and_cross_verification<P: Params>() {
    let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
    for _ in 0..3 {
        let seed = seed(&mut rng);
        let ours = Ours::<P>::from_seed(&seed);
        let theirs = ml_dsa::SigningKey::<P>::from_seed(&seed);
        assert_eq!(
            ours.verifying_key().encode().as_slice(),
            theirs.verifying_key().encode().as_slice()
        );
        for len in [0usize, 1, 32, 33, 1000, 10_007] {
            let msg = rng.vec(len);
            let ours_sig: Signature<P> = ours.try_sign(&msg).unwrap();
            let theirs_sig: Signature<P> = theirs.try_sign(&msg).unwrap();
            // Each verifies the other's.
            ours.verifying_key().verify(&msg, &theirs_sig).unwrap();
            theirs.verifying_key().verify(&msg, &ours_sig).unwrap();
            ours.verifying_key().verify(&msg, &ours_sig).unwrap();
            // A multipart message is the whole message.
            let cut = len / 2;
            let parts: [&[u8]; 3] = [&msg[..cut], &[], &msg[cut..]];
            let multi: Signature<P> = ours.try_multipart_sign(&parts).unwrap();
            ours.verifying_key()
                .multipart_verify(&parts, &multi)
                .unwrap();
            theirs.verifying_key().verify(&msg, &multi).unwrap();
        }
    }
}

fn altered_is_refused_by_both<P: Params>() {
    let mut rng = Xorshift(0xd1b5_4a32_d192_ed03);
    let seed = seed(&mut rng);
    let ours = Ours::<P>::from_seed(&seed);
    let theirs = ml_dsa::SigningKey::<P>::from_seed(&seed);
    let msg = rng.vec(100);
    let sig: Signature<P> = ours.try_sign(&msg).unwrap();
    let encoded = sig.encode();
    // A flipped bit at sampled positions across the whole signature.
    let stride = (encoded.len() / 97).max(1);
    for byte in (0..encoded.len()).step_by(stride) {
        let mut bad = encoded.clone();
        bad[byte] ^= 0x01;
        // A flip can make an encoding that does not decode: also a refusal.
        if let Some(bad) = Signature::<P>::decode(&bad) {
            assert!(
                ours.verifying_key().verify(&msg, &bad).is_err(),
                "byte {byte}"
            );
            assert!(
                theirs.verifying_key().verify(&msg, &bad).is_err(),
                "byte {byte}"
            );
        }
    }
    // Another message, and another key.
    let mut other = msg.clone();
    other[0] ^= 1;
    assert!(ours.verifying_key().verify(&other, &sig).is_err());
    assert!(theirs.verifying_key().verify(&other, &sig).is_err());
    assert!(
        ours.verifying_key()
            .multipart_verify(&[&other], &sig)
            .is_err()
    );
    let stranger = Ours::<P>::from_seed(&self::seed(&mut rng));
    assert!(stranger.verifying_key().verify(&msg, &sig).is_err());
}

// One generic function per trait, instantiated with rind's type.
fn generic_sign_verify<K: Signer<Signature<P>> + Keypair, P: Params>(key: &K, msg: &[u8]) -> bool
where
    K::VerifyingKey: Verifier<Signature<P>>,
{
    let signature = key.sign(msg);
    key.verifying_key().verify(msg, &signature).is_ok()
}

macro_rules! set {
    ($($test:ident: $set:ty;)*) => {$(
        mod $test {
            use super::*;

            #[test]
            fn same_key_and_cross_verification() {
                super::same_key_and_cross_verification::<$set>();
            }

            #[test]
            fn altered_is_refused_by_both() {
                super::altered_is_refused_by_both::<$set>();
            }

            #[test]
            fn a_generic_function_runs_on_rind() {
                let seed = ml_dsa::Seed::try_from([5u8; 32].as_slice()).unwrap();
                let key = Ours::<$set>::from_seed(&seed);
                assert!(generic_sign_verify::<_, $set>(&key, b"generic over Signer"));
            }
        }
    )*};
}

set! {
    ml_dsa_44: MlDsa44;
    ml_dsa_65: MlDsa65;
    ml_dsa_87: MlDsa87;
}
