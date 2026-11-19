//! ECDSA on each curve against RustCrypto's own: the same public key for the
//! same scalar, each verifying the other's signatures in both encodings, and
//! the malformed scalars, points, and signatures both refuse.
#![cfg(feature = "signature-3")]

use signature::{MultipartSigner, MultipartVerifier, Signer, Verifier};

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

/// `n + delta` for a small `delta`, big-endian.
fn add_small(n: &[u8], delta: i8) -> Vec<u8> {
    let mut v = n.to_vec();
    let mut carry = delta as i16;
    for byte in v.iter_mut().rev() {
        let sum = *byte as i16 + carry;
        *byte = sum.rem_euclid(256) as u8;
        carry = sum.div_euclid(256);
        if carry == 0 {
            break;
        }
    }
    v
}

const LENGTHS: &[usize] = &[0, 1, 31, 32, 33, 63, 64, 65, 127, 128, 129, 1000, 10_007];

macro_rules! curve_tests {
    ($mod:ident, $ours:ident, $theirs:ident, $curve:ident, $len:expr) => {
        mod $mod {
            use ::$theirs::ecdsa as rc;
            use rind_rustcrypto::$ours::ecdsa as rind;

            use super::*;

            const SCALAR_LEN: usize = $len;

            fn scalar(rng: &mut Xorshift) -> Vec<u8> {
                // A scalar well below the order: a zero top byte.
                let mut s = rng.vec(SCALAR_LEN);
                s[0] = 0;
                if s.iter().all(|b| *b == 0) {
                    s[SCALAR_LEN - 1] = 1;
                }
                s
            }

            #[test]
            fn the_same_public_key_and_signatures_that_verify_both_ways() {
                let mut rng = Xorshift(0x9e37_79b9_7f4a_7c15);
                for _ in 0..8 {
                    let secret = scalar(&mut rng);
                    let ours = rind::SigningKey::from_slice(&secret).unwrap();
                    let theirs = rc::SigningKey::from_slice(&secret).unwrap();
                    assert_eq!(
                        ours.verifying_key().to_sec1_bytes().as_ref(),
                        theirs.verifying_key().to_sec1_point(false).as_bytes()
                    );
                    for &len in LENGTHS {
                        let msg = rng.vec(len);
                        // rind's signature, in both encodings, verifies under RustCrypto's key.
                        let fixed: rind::Signature = ours.try_sign(&msg).unwrap();
                        let der: rind::DerSignature = ours.try_sign(&msg).unwrap();
                        theirs.verifying_key().verify(&msg, &fixed).unwrap();
                        theirs.verifying_key().verify(&msg, &der).unwrap();
                        ours.verifying_key().verify(&msg, &fixed).unwrap();
                        ours.verifying_key().verify(&msg, &der).unwrap();
                        // RustCrypto's, under rind's.
                        let theirs_fixed: rc::Signature = theirs.sign(&msg);
                        let theirs_der: rc::DerSignature = theirs.sign(&msg);
                        ours.verifying_key().verify(&msg, &theirs_fixed).unwrap();
                        ours.verifying_key().verify(&msg, &theirs_der).unwrap();
                        // A multipart message is the whole message.
                        let cut = len / 3;
                        let parts: [&[u8]; 3] = [&msg[..cut], &[], &msg[cut..]];
                        let multi: rind::Signature = ours.try_multipart_sign(&parts).unwrap();
                        ours.verifying_key()
                            .multipart_verify(&parts, &multi)
                            .unwrap();
                        theirs.verifying_key().verify(&msg, &multi).unwrap();
                    }
                }
            }

            #[test]
            fn what_is_altered_is_refused_by_both() {
                let mut rng = Xorshift(0xd1b5_4a32_d192_ed03);
                let secret = scalar(&mut rng);
                let ours = rind::SigningKey::from_slice(&secret).unwrap();
                let theirs = rc::SigningKey::from_slice(&secret).unwrap();
                let msg = rng.vec(100);
                let sig: rind::Signature = ours.try_sign(&msg).unwrap();
                let bytes = sig.to_bytes();
                // Every bit of the fixed signature.
                for byte in 0..bytes.len() {
                    for bit in 0..8 {
                        let mut bad = bytes.to_vec();
                        bad[byte] ^= 1 << bit;
                        // A flip can make a scalar zero or out of range: then the
                        // signature does not even parse, which is a refusal too.
                        if let Ok(bad) = rind::Signature::from_slice(&bad) {
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
                let stranger = rind::SigningKey::from_slice(&scalar(&mut rng)).unwrap();
                assert!(stranger.verifying_key().verify(&msg, &sig).is_err());
                // A DER signature with its bytes altered or cut.
                let der: rind::DerSignature = ours.try_sign(&msg).unwrap();
                let der_bytes = der.as_bytes().to_vec();
                for at in 0..der_bytes.len() {
                    let mut bad = der_bytes.clone();
                    bad[at] ^= 0x01;
                    if let Ok(bad) = rind::DerSignature::from_bytes(&bad) {
                        assert!(
                            ours.verifying_key().verify(&msg, &bad).is_err(),
                            "der byte {at}"
                        );
                        assert!(
                            theirs.verifying_key().verify(&msg, &bad).is_err(),
                            "der byte {at}"
                        );
                    }
                }
                for cut in [0, 1, 2, der_bytes.len() - 1] {
                    assert!(rind::DerSignature::from_bytes(&der_bytes[..cut]).is_err());
                }
            }

            #[test]
            fn malformed_scalars_are_refused_by_both() {
                use ::$theirs::elliptic_curve::Curve;
                // The order's `Uint` is padded to whole limbs (72 bytes for P-521).
                let wide = <::$theirs::$curve as Curve>::ORDER.to_be_bytes();
                let (pad, order) = wide.as_slice().split_at(wide.len() - SCALAR_LEN);
                assert!(pad.iter().all(|b| *b == 0));
                let order = order.to_vec();
                for (what, bad) in [
                    ("zero", vec![0u8; SCALAR_LEN]),
                    ("n", order.clone()),
                    ("n + 1", add_small(&order, 1)),
                    ("all ones", vec![0xff; SCALAR_LEN]),
                ] {
                    assert!(rind::SigningKey::from_slice(&bad).is_err(), "{what}: ours");
                    assert!(rc::SigningKey::from_slice(&bad).is_err(), "{what}: theirs");
                }
                // n - 1 is the largest valid scalar, for both.
                let largest = add_small(&order, -1);
                let ours = rind::SigningKey::from_slice(&largest).unwrap();
                let theirs = rc::SigningKey::from_slice(&largest).unwrap();
                assert_eq!(
                    ours.verifying_key().to_sec1_bytes().as_ref(),
                    theirs.verifying_key().to_sec1_point(false).as_bytes()
                );
                // A scalar longer than the field, or empty.
                for len in [0usize, SCALAR_LEN + 1, 2 * SCALAR_LEN] {
                    assert!(
                        rind::SigningKey::from_slice(&vec![1u8; len]).is_err(),
                        "{len}"
                    );
                }
            }

            #[test]
            fn malformed_points_are_refused_by_both() {
                let mut rng = Xorshift(0x1234_5678);
                let key = rind::SigningKey::from_slice(&scalar(&mut rng)).unwrap();
                let point = key.verifying_key().to_sec1_bytes().to_vec();
                assert!(rind::VerifyingKey::from_sec1_bytes(&point).is_ok());
                assert!(rc::VerifyingKey::from_sec1_bytes(&point).is_ok());
                // Off the curve (y changed), a bad tag, the point at infinity, truncated.
                let mut off_curve = point.clone();
                *off_curve.last_mut().unwrap() ^= 1;
                let mut bad_tag = point.clone();
                bad_tag[0] = 0x05;
                for (what, bad) in [
                    ("off the curve", off_curve),
                    ("bad tag", bad_tag),
                    ("infinity", vec![0u8]),
                    ("empty", vec![]),
                    ("truncated", point[..point.len() - 1].to_vec()),
                    ("extended", [point.as_slice(), &[0]].concat()),
                ] {
                    assert!(
                        rind::VerifyingKey::from_sec1_bytes(&bad).is_err(),
                        "{what}: ours"
                    );
                    assert!(
                        rc::VerifyingKey::from_sec1_bytes(&bad).is_err(),
                        "{what}: theirs"
                    );
                }
            }

            #[test]
            fn a_generic_function_runs_on_rind() {
                fn sign_verify<K, S>(key: &K, verifying: &impl Verifier<S>, msg: &[u8])
                where
                    K: Signer<S>,
                {
                    let signature = key.sign(msg);
                    verifying.verify(msg, &signature).unwrap();
                }
                let mut secret = vec![0x11; SCALAR_LEN];
                secret[0] = 0;
                let key = rind::SigningKey::from_slice(&secret).unwrap();
                sign_verify::<_, rind::Signature>(
                    &key,
                    key.verifying_key(),
                    b"generic over Signer",
                );
                sign_verify::<_, rind::DerSignature>(
                    &key,
                    key.verifying_key(),
                    b"generic over Signer",
                );
            }
        }
    };
}

curve_tests!(p256, p256, p256, NistP256, 32);
curve_tests!(p384, p384, p384, NistP384, 48);
curve_tests!(p521, p521, p521, NistP521, 66);
