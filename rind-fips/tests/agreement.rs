// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ECDH through the module agrees with rind's, which its own tests check
//! against Wycheproof and aws-lc-rs: keys made on either side work on the
//! other, every encoding round-trips byte for byte, and every malformed key
//! is refused with rind's error.
#![cfg(rind_fips_module)]

use rind_fips::agreement::{self, PrivateKey, PublicKey};

type Curve = (
    &'static agreement::Algorithm,
    &'static rind::agreement::Algorithm,
    usize,
);

/// Each curve, as the module and rind name it, with its scalar's length.
const CURVES: [Curve; 3] = [
    (&agreement::ECDH_P256, &rind::agreement::ECDH_P256, 32),
    (&agreement::ECDH_P384, &rind::agreement::ECDH_P384, 48),
    (&agreement::ECDH_P521, &rind::agreement::ECDH_P521, 66),
];

/// Each curve's ECDSA signing algorithm, which writes SEC1 keys.
fn ecdsa(scalar_len: usize) -> &'static rind::signature::EcdsaSigningAlgorithm {
    match scalar_len {
        32 => &rind::signature::sign::ECDSA_P256_SHA256_ASN1,
        48 => &rind::signature::sign::ECDSA_P384_SHA384_ASN1,
        _ => &rind::signature::sign::ECDSA_P521_SHA512_ASN1,
    }
}

/// Asserts that both succeeded, or failed with the same error.
#[track_caller]
fn same_result<T, U>(
    ours: &Result<T, rind_fips::Error>,
    theirs: &Result<U, rind::Error>,
    what: &str,
) {
    match (ours, theirs) {
        (Ok(_), Ok(_)) => {}
        (Err(ours), Err(theirs)) => assert_eq!(ours.to_string(), theirs.to_string(), "{what}"),
        _ => panic!(
            "{what}: the module {}, rind {}",
            ours.as_ref()
                .map_or_else(|e| e.to_string(), |_| "accepted".into()),
            theirs
                .as_ref()
                .map_or_else(|e| e.to_string(), |_| "accepted".into()),
        ),
    }
}

/// The compressed form of uncompressed point `point`.
fn compress(point: &[u8]) -> Vec<u8> {
    let len = (point.len() - 1) / 2;
    let mut compressed = vec![2 | (point[point.len() - 1] & 1)];
    compressed.extend_from_slice(&point[1..1 + len]);
    compressed
}

#[test]
fn agrees_with_rind_both_ways() {
    for (ours, theirs, _) in CURVES {
        for _ in 0..4 {
            let key = PrivateKey::generate(ours).unwrap();
            let peer = rind::agreement::PrivateKey::generate(theirs).unwrap();
            assert_eq!(key.algorithm(), ours);
            assert_eq!(key.public_key().algorithm(), ours);

            let secret = key.agree(peer.public_key().as_ref()).unwrap();
            let expected = peer.agree(key.public_key().as_ref()).unwrap();
            assert_eq!(secret.as_ref(), expected.as_ref(), "{ours:?}");

            // A key the module generated, loaded by rind, agrees as it did.
            let loaded =
                rind::agreement::PrivateKey::from_pkcs8(theirs, key.to_pkcs8().as_ref()).unwrap();
            assert_eq!(loaded.public_key().as_ref(), key.public_key().as_ref());
            assert_eq!(
                loaded.agree(peer.public_key().as_ref()).unwrap().as_ref(),
                secret.as_ref()
            );
        }
    }
}

#[test]
fn encodings_round_trip_with_rind() {
    for (ours, theirs, scalar_len) in CURVES {
        let reference = rind::agreement::PrivateKey::generate(theirs).unwrap();
        let pkcs8 = reference.to_pkcs8();
        let scalar = reference.to_scalar();
        let sec1 = rind::signature::EcdsaKeyPair::from_pkcs8(ecdsa(scalar_len), pkcs8.as_ref())
            .unwrap()
            .to_sec1();

        let loaded = [
            PrivateKey::from_pkcs8(ours, pkcs8.as_ref()).unwrap(),
            PrivateKey::from_scalar(ours, scalar.as_ref()).unwrap(),
            PrivateKey::from_sec1(ours, sec1.as_ref()).unwrap(),
        ];
        for key in &loaded {
            assert_eq!(key.public_key().as_ref(), reference.public_key().as_ref());
            assert_eq!(key.to_pkcs8().as_ref(), pkcs8.as_ref());
            assert_eq!(key.to_scalar().as_ref(), scalar.as_ref());
            assert_eq!(key.to_scalar().as_ref().len(), scalar_len);
        }

        // Public keys: uncompressed, compressed, and in an SPKI.
        let point = reference.public_key().as_ref();
        let spki = reference.public_key().to_spki();
        let parsed = [
            PublicKey::new(ours, point).unwrap(),
            PublicKey::new(ours, &compress(point)).unwrap(),
            PublicKey::from_spki(ours, spki.as_ref()).unwrap(),
        ];
        for key in &parsed {
            assert_eq!(key.as_ref(), point);
            assert_eq!(key.algorithm(), ours);
            assert_eq!(key.to_spki().as_ref(), spki.as_ref());
            assert_eq!(key.clone().as_ref(), point);
        }
        let compressed_spki = rind::agreement::PublicKey::new(theirs, &compress(point))
            .unwrap()
            .to_spki();
        assert_eq!(compressed_spki.as_ref(), spki.as_ref());
    }
}

#[test]
fn debug_matches_rind() {
    for (ours, theirs, _) in CURVES {
        assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
        let reference = rind::agreement::PrivateKey::generate(theirs).unwrap();
        let key = PrivateKey::from_pkcs8(ours, reference.to_pkcs8().as_ref()).unwrap();
        assert_eq!(format!("{key:?}"), format!("{reference:?}"));
        assert_eq!(
            format!("{:?}", key.public_key()),
            format!("{:?}", reference.public_key())
        );
        assert_eq!(
            format!("{:?}", key.to_scalar()),
            format!("{:?}", reference.to_scalar())
        );
        assert_eq!(
            format!("{:?}", key.to_pkcs8()),
            format!("{:?}", reference.to_pkcs8())
        );
        let peer = reference.public_key().as_ref();
        assert_eq!(
            format!("{:?}", key.agree(peer).unwrap()),
            format!("{:?}", reference.agree(peer).unwrap())
        );
    }
    assert_ne!(agreement::ECDH_P256, agreement::ECDH_P384);
}

#[test]
fn refuses_what_rind_refuses() {
    for (index, (ours, theirs, scalar_len)) in CURVES.into_iter().enumerate() {
        let reference = rind::agreement::PrivateKey::generate(theirs).unwrap();
        let point = reference.public_key().as_ref().to_vec();
        let pkcs8 = reference.to_pkcs8().as_ref().to_vec();
        let spki = reference.public_key().to_spki().as_ref().to_vec();
        let (_, other, _) = CURVES[(index + 1) % CURVES.len()];
        let other_key = rind::agreement::PrivateKey::generate(other).unwrap();

        let mut off_curve = point.clone();
        *off_curve.last_mut().unwrap() ^= 1;
        let mut bad_x = compress(&point);
        bad_x[1..].fill(0xff);
        let mut bad_prefix = point.clone();
        bad_prefix[0] = 5;
        let points: [(&str, Vec<u8>); 9] = [
            ("empty", vec![]),
            ("identity", vec![0]),
            ("off the curve", off_curve),
            ("x out of range", bad_x),
            ("a bad prefix", bad_prefix),
            ("truncated", point[..point.len() - 1].to_vec()),
            ("lengthened", [&point[..], &[0]].concat()),
            ("another curve's", other_key.public_key().as_ref().to_vec()),
            ("all zeros", vec![0; point.len()]),
        ];
        let key = PrivateKey::generate(ours).unwrap();
        for (what, bytes) in &points {
            same_result(
                &PublicKey::new(ours, bytes),
                &rind::agreement::PublicKey::new(theirs, bytes),
                &format!("{ours:?} public key {what}"),
            );
            same_result(
                &key.agree(bytes),
                &reference.agree(bytes),
                &format!("{ours:?} agreeing with {what}"),
            );
        }
        // `agree` takes only an uncompressed point.
        same_result(
            &key.agree(&compress(&point)),
            &reference.agree(&compress(&point)),
            &format!("{ours:?} agreeing with a compressed point"),
        );

        let n_or_more = vec![0xff; scalar_len];
        let scalars: [(&str, Vec<u8>); 5] = [
            ("empty", vec![]),
            ("zero", vec![0; scalar_len]),
            ("n or more", n_or_more),
            ("short", vec![1; scalar_len - 1]),
            ("long", vec![1; scalar_len + 1]),
        ];
        for (what, bytes) in &scalars {
            same_result(
                &PrivateKey::from_scalar(ours, bytes),
                &rind::agreement::PrivateKey::from_scalar(theirs, bytes),
                &format!("{ours:?} scalar {what}"),
            );
        }

        let mut flipped = pkcs8.clone();
        let at = flipped.len() - 1;
        flipped[at] ^= 1;
        let ders: [(&str, Vec<u8>); 5] = [
            ("empty", vec![]),
            ("truncated", pkcs8[..pkcs8.len() - 1].to_vec()),
            ("with its public key changed", flipped),
            ("of another curve", other_key.to_pkcs8().as_ref().to_vec()),
            ("an SPKI", spki.clone()),
        ];
        for (what, der) in &ders {
            same_result(
                &PrivateKey::from_pkcs8(ours, der),
                &rind::agreement::PrivateKey::from_pkcs8(theirs, der),
                &format!("{ours:?} PKCS#8 {what}"),
            );
            same_result(
                &PrivateKey::from_sec1(ours, der),
                &rind::agreement::PrivateKey::from_sec1(theirs, der),
                &format!("{ours:?} SEC1 {what}"),
            );
            same_result(
                &PublicKey::from_spki(ours, der),
                &rind::agreement::PublicKey::from_spki(theirs, der),
                &format!("{ours:?} SPKI {what}"),
            );
        }
        let mut truncated_spki = spki.clone();
        truncated_spki.pop();
        same_result(
            &PublicKey::from_spki(ours, &truncated_spki),
            &rind::agreement::PublicKey::from_spki(theirs, &truncated_spki),
            &format!("{ours:?} SPKI truncated"),
        );
    }

    // rind's own malformed SEC1 keys.
    for (what, der) in [
        (
            "SEC1 with the wrong public key",
            &include_bytes!("../../rind/src/high/ecdsa/secp256r1.wrong-public-key.der")[..],
        ),
        (
            "SEC1 of the wrong version",
            include_bytes!("../../rind/src/high/ecdsa/secp256r1.wrong-version.der"),
        ),
        (
            "SEC1",
            include_bytes!("../../rind/src/high/ecdsa/secp256r1.der"),
        ),
    ] {
        same_result(
            &PrivateKey::from_sec1(&agreement::ECDH_P256, der),
            &rind::agreement::PrivateKey::from_sec1(&rind::agreement::ECDH_P256, der),
            what,
        );
    }
}

/// Dropping a private key wipes the copy of its public key it keeps outside
/// the module, as rind's wipes its whole value.
#[test]
fn drop_wipes_the_public_key() {
    use std::mem::MaybeUninit;

    for algorithm in [
        &agreement::ECDH_P256,
        &agreement::ECDH_P384,
        &agreement::ECDH_P521,
    ] {
        let mut key = MaybeUninit::new(PrivateKey::generate(algorithm).unwrap());
        // SAFETY: initialized just above.
        let held = unsafe { key.assume_init_ref() }.public_key().as_ref();
        let public = held.to_vec();
        // Where the key holds its public key, which it initialized; only
        // those bytes are read after the drop, since its padding may not be.
        let offset = held.as_ptr() as usize - key.as_ptr() as usize;
        // Reads those bytes, deliberately after the drop, as rind's zeroing
        // tests do.
        let read = |key: &MaybeUninit<PrivateKey>| -> Vec<u8> {
            let start = key.as_ptr().cast::<u8>();
            (offset..offset + public.len())
                // SAFETY: within the value's storage, which outlives the
                // read, and initialized, by the key and then by its wipe.
                .map(|i| unsafe { core::ptr::read_volatile(start.add(i)) })
                .collect()
        };
        assert_eq!(read(&key), public);
        // SAFETY: initialized, and dropped only here.
        unsafe { key.assume_init_drop() };
        assert_eq!(read(&key), vec![0; public.len()], "{algorithm:?}");
    }
}
