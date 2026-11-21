// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Known-answer checks for the rind algorithms an ESP32-C6 (riscv32imac) runs.
//!
//! Each check is one function returning whether rind's output equals the
//! published vector, or whether a round trip holds where no deterministic
//! vector exists. The same functions run on the host (`cargo test`) and under
//! qemu-user on riscv32imac (`qemu-kat`), so the vectors are checked on a
//! second CPU and a second word size. Nothing here has run on an ESP32-C6.

#![cfg_attr(not(test), no_std)]

extern crate alloc;

use alloc::vec::Vec;

/// One algorithm's check: its feature name and the function.
pub struct Kat {
    /// The Cargo feature that includes the check.
    pub name: &'static str,
    /// Whether rind agrees with the vector.
    pub run: fn() -> bool,
}

/// Every check the enabled features include, in a fixed order.
pub fn all() -> Vec<Kat> {
    #[allow(unused_mut)]
    let mut v = Vec::new();
    #[cfg(feature = "sha256")]
    v.push(Kat {
        name: "sha256",
        run: sha256,
    });
    #[cfg(feature = "sha512")]
    v.push(Kat {
        name: "sha512",
        run: sha512,
    });
    #[cfg(feature = "sha3-256")]
    v.push(Kat {
        name: "sha3-256",
        run: sha3_256,
    });
    #[cfg(feature = "hmac-sha256")]
    v.push(Kat {
        name: "hmac-sha256",
        run: hmac_sha256,
    });
    #[cfg(feature = "hkdf-sha256")]
    v.push(Kat {
        name: "hkdf-sha256",
        run: hkdf_sha256,
    });
    #[cfg(feature = "chacha20poly1305")]
    v.push(Kat {
        name: "chacha20poly1305",
        run: chacha20poly1305,
    });
    #[cfg(feature = "aes128-gcm")]
    v.push(Kat {
        name: "aes128-gcm",
        run: aes128_gcm,
    });
    #[cfg(feature = "aes256-gcm")]
    v.push(Kat {
        name: "aes256-gcm",
        run: aes256_gcm,
    });
    #[cfg(feature = "x25519")]
    v.push(Kat {
        name: "x25519",
        run: x25519,
    });
    #[cfg(feature = "ed25519")]
    v.push(Kat {
        name: "ed25519",
        run: ed25519,
    });
    #[cfg(feature = "mlkem768")]
    v.push(Kat {
        name: "mlkem768",
        run: mlkem768,
    });
    #[cfg(feature = "mldsa65")]
    v.push(Kat {
        name: "mldsa65",
        run: mldsa65,
    });
    #[cfg(feature = "p256-ecdsa")]
    v.push(Kat {
        name: "p256-ecdsa",
        run: p256_ecdsa,
    });
    v
}

/// Decodes lowercase hex, which every vector below is written in.
pub fn hex(s: &str) -> Vec<u8> {
    let nib = |c: u8| match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        _ => panic!("not lowercase hex"),
    };
    s.as_bytes()
        .chunks(2)
        .map(|p| nib(p[0]) << 4 | nib(p[1]))
        .collect()
}

/// FIPS 180-4 "abc".
#[cfg(feature = "sha256")]
pub fn sha256() -> bool {
    use rind::digest::{SHA256, digest};
    digest(&SHA256, b"abc").as_ref()
        == hex("ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
}

/// FIPS 180-4 "abc".
#[cfg(feature = "sha512")]
pub fn sha512() -> bool {
    use rind::digest::{SHA512, digest};
    digest(&SHA512, b"abc").as_ref()
        == hex(concat!(
            "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a",
            "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
        ))
}

/// FIPS 202 "abc".
#[cfg(feature = "sha3-256")]
pub fn sha3_256() -> bool {
    use rind::digest::{SHA3_256, digest};
    digest(&SHA3_256, b"abc").as_ref()
        == hex("3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532")
}

/// RFC 4231 test case 2.
#[cfg(feature = "hmac-sha256")]
pub fn hmac_sha256() -> bool {
    use rind::hmac::{HMAC_SHA256, Key, sign};
    let key = Key::new(&HMAC_SHA256, b"Jefe");
    sign(&key, b"what do ya want for nothing?").as_ref()
        == hex("5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
}

/// RFC 5869 test case 1.
#[cfg(feature = "hkdf-sha256")]
pub fn hkdf_sha256() -> bool {
    use rind::hkdf::{HKDF_SHA256, Salt};
    let salt = Salt::new(&HKDF_SHA256, &hex("000102030405060708090a0b0c"));
    let mut okm = [0u8; 42];
    let info = hex("f0f1f2f3f4f5f6f7f8f9");
    let ok = salt
        .extract(&[0x0b; 22])
        .and_then(|prk| prk.fill(&[&info], &mut okm))
        .is_ok();
    ok && okm.as_slice()
        == hex(concat!(
            "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf",
            "34007208d5b887185865"
        ))
}

/// RFC 8439 section 2.8.2, sealed and opened.
#[cfg(feature = "chacha20poly1305")]
pub fn chacha20poly1305() -> bool {
    use rind::aead::{CHACHA20_POLY1305, Key, Nonce};
    let key = Key::new(
        &CHACHA20_POLY1305,
        &hex(concat!(
            "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
        )),
    )
    .unwrap();
    let iv: [u8; 12] = hex("070000004041424344454647").try_into().unwrap();
    let aad = hex("50515253c0c1c2c3c4c5c6c7");
    let pt = b"Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it.";
    let mut buf = pt.to_vec();
    let Ok(tag) = key.seal_in_place_separate_tag(Nonce::assume_unique_for_key(iv), &aad, &mut buf)
    else {
        return false;
    };
    let mut sealed = buf.clone();
    sealed.extend_from_slice(tag.as_ref());
    let good = buf[..16] == hex("d31a8d34648e60db7b86afbc53ef7ec2")[..]
        && tag.as_ref() == hex("1ae10b594f09e26a7e902ecbd0600691");
    let opened = key
        .open_in_place(Nonce::assume_unique_for_key(iv), &aad, &mut sealed)
        .map(|p| p.to_vec());
    good && opened.as_deref() == Ok(&pt[..])
}

#[cfg(any(feature = "aes128-gcm", feature = "aes256-gcm"))]
fn gcm(alg: &'static rind::aead::Algorithm, key: &[u8], ct: &str, tag: &str) -> bool {
    use rind::aead::{Key, Nonce};
    let key = Key::new(alg, key).unwrap();
    let mut buf = [0u8; 16];
    let Ok(t) =
        key.seal_in_place_separate_tag(Nonce::assume_unique_for_key([0; 12]), &[], &mut buf)
    else {
        return false;
    };
    buf == hex(ct)[..] && t.as_ref() == hex(tag)
}

/// The GCM specification's test case 2: zero key, zero IV, one zero block.
#[cfg(feature = "aes128-gcm")]
pub fn aes128_gcm() -> bool {
    gcm(
        &rind::aead::AES_128_GCM,
        &[0; 16],
        "0388dace60b6a392f328c2b971b2fe78",
        "ab6e47d42cec13bdf53a67b21257bddf",
    )
}

/// The GCM specification's test case 14: zero key, zero IV, one zero block.
#[cfg(feature = "aes256-gcm")]
pub fn aes256_gcm() -> bool {
    gcm(
        &rind::aead::AES_256_GCM,
        &[0; 32],
        "cea7403d4d606b6e074ec5d3baf39d18",
        "d0d1c8a799996bf0265b98b5d48ab919",
    )
}

/// RFC 7748 section 5.2, first vector.
#[cfg(feature = "x25519")]
pub fn x25519() -> bool {
    use rind::agreement::{PrivateKey, X25519};
    let Ok(k) = PrivateKey::from_scalar(
        &X25519,
        &hex("a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"),
    ) else {
        return false;
    };
    k.agree(&hex(
        "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
    ))
    .is_ok_and(|s| {
        s.as_ref() == hex("c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552")
    })
}

/// RFC 8032 section 7.1, test 1 (empty message): signature equals, verifies.
#[cfg(feature = "ed25519")]
pub fn ed25519() -> bool {
    use rind::ed25519::KeyPair;
    let Ok(kp) = KeyPair::from_seed(&hex(
        "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
    )) else {
        return false;
    };
    let sig = kp.sign(b"");
    kp.public_key().as_ref()
        == hex("d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a")
        && sig.as_ref()
            == hex(concat!(
                "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155",
                "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b"
            ))
        && kp.public_key().verify(b"", sig.as_ref()).is_ok()
}

/// Encapsulate then decapsulate agree. Needs the harness's getrandom source.
#[cfg(feature = "mlkem768")]
pub fn mlkem768() -> bool {
    use rind::kem::{DecapsulationKey, MlKem768};
    let Ok(dk) = DecapsulationKey::<MlKem768>::generate() else {
        return false;
    };
    let Ok((ct, ss)) = dk.public_key().encapsulate() else {
        return false;
    };
    dk.decapsulate(&ct).as_ref() == ss.as_ref()
}

/// Sign then verify, and a changed message fails. Needs the harness's source.
#[cfg(feature = "mldsa65")]
pub fn mldsa65() -> bool {
    use rind::ml_dsa::{KeyPair, MlDsa65, PublicKey};
    let Ok(kp) = KeyPair::<MlDsa65>::generate() else {
        return false;
    };
    let Ok(sig) = kp.sign(b"hello") else {
        return false;
    };
    let Ok(pk) = PublicKey::<MlDsa65>::new(kp.public_key().as_ref()) else {
        return false;
    };
    pk.verify(b"hello", sig.as_ref()).is_ok() && pk.verify(b"hellp", sig.as_ref()).is_err()
}

/// Sign then verify on P-256, and a changed message fails.
#[cfg(feature = "p256-ecdsa")]
pub fn p256_ecdsa() -> bool {
    use rind::ecdsa::{KeyPair, PublicKey, sign, verify};
    let Ok(kp) = KeyPair::generate(&sign::P256_SHA256_FIXED) else {
        return false;
    };
    let Ok(sig) = kp.sign(b"hello") else {
        return false;
    };
    PublicKey::new(&verify::P256_SHA256_FIXED, kp.public_key().as_ref()).is_ok_and(|pk| {
        pk.verify(b"hello", sig.as_ref()).is_ok() && pk.verify(b"hellp", sig.as_ref()).is_err()
    })
}

#[cfg(all(test, feature = "all"))]
mod tests {
    #[test]
    fn every_known_answer_holds_on_the_host() {
        for k in super::all() {
            assert!((k.run)(), "{} failed", k.name);
        }
    }
}
