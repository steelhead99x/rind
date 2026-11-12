// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use crate::Error;
use crate::error::KeyFormatError;
use crate::mid::mlkem768;

/// A key encapsulation mechanism.
pub struct Algorithm {
    id: AlgorithmId,
}

#[derive(Clone, Copy, Debug)]
enum AlgorithmId {
    MlKem768,
}

impl fmt::Debug for Algorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.id.fmt(f)
    }
}

/// ML-KEM-768, as standardised by FIPS-203.
pub static ML_KEM_768: Algorithm = Algorithm {
    id: AlgorithmId::MlKem768,
};

/// A decapsulation key, which decapsulates any number of ciphertexts, wiped on drop under the `wipe` feature.
pub struct DecapsulationKey(mlkem768::DecapKey);

impl DecapsulationKey {
    /// Generates a decapsulation key for `algorithm` from the system random source.
    pub fn generate(algorithm: &'static Algorithm) -> Result<Self, Error> {
        match algorithm.id {
            AlgorithmId::MlKem768 => mlkem768::DecapKey::generate().map(Self),
        }
    }

    /// Returns the encapsulation key to send to the peer.
    pub fn public_key(&self) -> EncapsulationKey {
        let key = self.0.encapsulation_key();
        EncapsulationKey {
            bytes: key.as_bytes(),
            key,
        }
    }

    /// Recovers the secret the peer encapsulated in `ciphertext`.
    ///
    /// A ciphertext of the wrong length is refused. Any other tampering
    /// yields an unrelated secret (FIPS-203's implicit rejection), so the
    /// peer learns nothing until the secret is used.
    pub fn decapsulate(&self, ciphertext: &[u8]) -> Result<SharedSecret, Error> {
        let ciphertext: [u8; 1088] = ciphertext.try_into().map_err(|_| Error::WrongLength)?;
        Ok(SharedSecret(
            self.0.decaps(&mlkem768::Ciphertext::from(ciphertext)),
        ))
    }
}

impl fmt::Debug for DecapsulationKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecapsulationKey").finish_non_exhaustive()
    }
}

/// An encapsulation key, which anyone may encapsulate a secret to.
#[derive(Clone)]
pub struct EncapsulationKey {
    key: mlkem768::EncapKey,
    bytes: [u8; 1184],
}

impl EncapsulationKey {
    /// Parses a peer's encapsulation key for `algorithm`.
    ///
    /// Fails with [`Error::KeyRejected`] for the wrong length, or if it fails
    /// FIPS-203's modulus check.
    pub fn new(algorithm: &'static Algorithm, bytes: &[u8]) -> Result<Self, Error> {
        match algorithm.id {
            AlgorithmId::MlKem768 => {
                let bytes = bytes.try_into().map_err(|_| KeyFormatError::WrongLength)?;
                let key = mlkem768::EncapKey::from_bytes(bytes)?;
                Ok(Self { key, bytes: *bytes })
            }
        }
    }

    /// Encapsulates a fresh random secret, returning the ciphertext to send
    /// to the key's holder and the secret.
    pub fn encapsulate(&self) -> Result<(Ciphertext, SharedSecret), Error> {
        let (secret, ciphertext) = self.key.encaps()?;
        Ok((Ciphertext(ciphertext), SharedSecret(secret)))
    }
}

impl AsRef<[u8]> for EncapsulationKey {
    fn as_ref(&self) -> &[u8] {
        &self.bytes
    }
}

impl fmt::Debug for EncapsulationKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("EncapsulationKey")
            .field(&self.as_ref())
            .finish()
    }
}

// Moving a key calls `memcpy`, which from 8 KiB is glibc's `rep movsb` on
// AVX2 CPUs without FSRM. CodSpeed's simulator charges that per byte, which
// would swamp real changes in the ML-KEM benchmarks.
const _: () = {
    assert!(size_of::<EncapsulationKey>() < 8192);
    assert!(size_of::<Result<EncapsulationKey, Error>>() < 8192);
    assert!(size_of::<DecapsulationKey>() < 8192);
    assert!(size_of::<Result<DecapsulationKey, Error>>() < 8192);
};

/// A ciphertext carrying an encapsulated secret, to send to the key's holder.
#[derive(Clone, Debug)]
pub struct Ciphertext(mlkem768::Ciphertext);

impl AsRef<[u8]> for Ciphertext {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// The secret both parties share, wiped on drop under the `wipe` feature.
pub struct SharedSecret(mlkem768::SharedSecret);

impl AsRef<[u8]> for SharedSecret {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for SharedSecret {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SharedSecret").finish_non_exhaustive()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use serde::Deserialize;

    use super::*;
    use crate::low;
    use crate::test::{Expected, cctv, cctv_records, cctv_value, wycheproof};

    // The seed and message vectors need crate access, so these live here
    // rather than in `tests/wycheproof.rs`.
    #[derive(Deserialize, Debug)]
    struct KemTest {
        #[serde(rename = "tcId")]
        id: usize,
        #[serde(default, with = "hex::serde")]
        seed: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        ek: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        dk: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        m: Vec<u8>,
        #[serde(default, with = "hex::serde")]
        c: Vec<u8>,
        #[serde(default, rename = "K", with = "hex::serde")]
        k: Vec<u8>,
        result: Expected,
    }

    fn secret_bytes(secret: &SharedSecret) -> Vec<u8> {
        let bytes = secret.as_ref().to_vec();
        low::ct::public_slice(&bytes);
        bytes
    }

    #[test]
    fn wycheproof_keygen() {
        for test in wycheproof::<KemTest>("mlkem_768_keygen_seed_test.json") {
            assert_eq!(test.result, Expected::Valid, "{}", test.id);
            let key = mlkem768::DecapKey::keygen_internal(&test.seed.try_into().unwrap());
            assert_eq!(&low::ct::into_public(key.as_bytes())[..], &test.dk);
            let key = DecapsulationKey(key);
            assert_eq!(key.public_key().as_ref(), &test.ek);
        }
    }

    #[test]
    fn wycheproof_encaps() {
        for test in wycheproof::<KemTest>("mlkem_768_encaps_test.json") {
            let m = mlkem768::Message(test.m.try_into().unwrap());
            let result = EncapsulationKey::new(&ML_KEM_768, &test.ek).map(|key| {
                let (secret, ciphertext) = key.key.encaps_internal(m);
                (secret_bytes(&SharedSecret(secret)), ciphertext)
            });
            match (test.result, &result) {
                (Expected::Valid, Ok((secret, ciphertext))) => {
                    assert_eq!(secret, &test.k, "{}", test.id);
                    assert_eq!(&ciphertext.as_ref()[..], &test.c, "{}", test.id);
                }
                (Expected::Invalid, Err(Error::KeyRejected(_))) => {}
                _ => panic!("{}: expected {:?} got {:?}", test.id, test.result, result),
            }
        }
    }

    #[test]
    fn wycheproof_decaps() {
        for test in wycheproof::<KemTest>("mlkem_768_test.json") {
            // Generation never makes a seed of another length.
            let Ok(seed) = test.seed.as_slice().try_into() else {
                assert_eq!(test.result, Expected::Invalid, "{}", test.id);
                continue;
            };

            let key = DecapsulationKey(mlkem768::DecapKey::keygen_internal(&seed));
            assert_eq!(key.public_key().as_ref(), &test.ek, "{}", test.id);
            let result = key.decapsulate(&test.c).map(|secret| secret_bytes(&secret));
            match (test.result, &result) {
                (Expected::Valid, Ok(secret)) => assert_eq!(secret, &test.k, "{}", test.id),
                (Expected::Invalid, Err(Error::WrongLength)) => {}
                _ => panic!("{}: expected {:?} got {:?}", test.id, test.result, result),
            }
        }
    }

    // CCTV's keys come from FIPS 203's draft, whose key generation lacked
    // `k` in `G(d || k)`, so these check encapsulation and decapsulation,
    // which the final standard kept, from the encoded keys.
    fn cctv_encaps_decaps(record: &[(String, Vec<u8>)]) {
        let ek = EncapsulationKey::new(&ML_KEM_768, cctv_value(record, "ek")).unwrap();
        let m = mlkem768::Message(cctv_value(record, "m").try_into().unwrap());
        let (secret, ciphertext) = ek.key.encaps_internal(m);
        assert_eq!(&ciphertext.as_ref()[..], cctv_value(record, "c"));
        assert_eq!(secret_bytes(&SharedSecret(secret)), cctv_value(record, "K"));

        let dk = cctv_value(record, "dk").try_into().unwrap();
        let dk = DecapsulationKey(mlkem768::DecapKey::from_bytes(dk).unwrap());
        assert_eq!(dk.public_key().as_ref(), cctv_value(record, "ek"));
        let secret = dk.decapsulate(cctv_value(record, "c")).unwrap();
        assert_eq!(secret_bytes(&secret), cctv_value(record, "K"));
    }

    // One key's every intermediate value, of which we check the results.
    #[test]
    fn cctv_intermediate() {
        for record in cctv_records("ML-KEM/intermediate/ML-KEM-768.txt") {
            cctv_encaps_decaps(&record);
        }
    }

    // Keys whose matrix needs over 575 bytes of SHAKE-128 to sample.
    #[test]
    fn cctv_unlucky_sample() {
        for record in cctv_records("ML-KEM/unluckysample/ML-KEM-768.txt") {
            cctv_encaps_decaps(&record);
        }
    }

    // A ciphertext that matches the re-encryption up to a zero byte, which a
    // `strcmp` comparison would accept.
    #[test]
    fn cctv_strcmp() {
        for record in cctv_records("ML-KEM/strcmp/ML-KEM-768.txt") {
            let dk = cctv_value(&record, "dk").try_into().unwrap();
            let key = DecapsulationKey(mlkem768::DecapKey::from_bytes(dk).unwrap());
            let secret = key.decapsulate(cctv_value(&record, "c")).unwrap();
            assert_eq!(secret_bytes(&secret), cctv_value(&record, "K"));
        }
    }

    // Encapsulation keys with one coefficient from q to 4095, for every value
    // and position.
    #[test]
    fn cctv_modulus() {
        use std::io::{BufRead, BufReader};

        let path = cctv("ML-KEM/modulus/ML-KEM-768.txt.gz");
        let file = std::fs::File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
        let mut count = 0;
        for line in BufReader::new(flate2::read::GzDecoder::new(file)).lines() {
            let ek = hex::decode(line.unwrap()).unwrap();
            assert_eq!(
                EncapsulationKey::new(&ML_KEM_768, &ek).err(),
                Some(KeyFormatError::MlKemModulus.into())
            );
            count += 1;
        }
        assert_eq!(count, 780);
    }

    // CCTV's pq-crystals vectors, as Go's `crypto/mlkem` updated them for
    // the final FIPS 203 (`TestAccumulated`, golang/go@73de90f): each test
    // draws its inputs from one SHAKE-128 stream and hashes its outputs into
    // another. 10 000 tests run always, and the million SLOW_TESTS asks for.
    #[test]
    fn cctv_accumulated() {
        use crate::mid::sha3::{Shake128, Shake128Sponge};

        let tests = if std::env::var_os("SLOW_TESTS").is_some() {
            1_000_000
        } else {
            10_000
        };
        eprintln!("slow-tests: cctv_accumulated {tests}");

        let mut rng = Shake128::new(&[]);
        let mut acc = Shake128Sponge::new();
        let hash = |acc: &Shake128Sponge| {
            let mut out = [0u8; 32];
            acc.finish().squeeze(&mut out);
            hex::encode(out)
        };
        for i in 1..=tests {
            let mut seed = [0u8; 64];
            let mut m = [0u8; 32];
            let mut ct = [0u8; 1088];
            rng.read(&mut seed);
            rng.read(&mut m);
            rng.read(&mut ct);

            let key = mlkem768::DecapKey::keygen_internal(&seed);
            let (secret, ciphertext) = key
                .encapsulation_key()
                .encaps_internal(mlkem768::Message(m));
            let secret = secret_bytes(&SharedSecret(secret));
            assert_eq!(secret_bytes(&SharedSecret(key.decaps(&ciphertext))), secret);
            let rejected = secret_bytes(&SharedSecret(key.decaps(&ct.into())));

            acc.absorb(&key.encapsulation_key().as_bytes());
            acc.absorb(ciphertext.as_ref());
            acc.absorb(&secret);
            acc.absorb(&rejected);

            match i {
                10_000 => assert_eq!(
                    hash(&acc),
                    "8a518cc63da366322a8e7a818c7a0d63483cb3528d34a4cf42f35d5ad73f22fc"
                ),
                1_000_000 => assert_eq!(
                    hash(&acc),
                    "424bf8f0e8ae99b78d788a6e2e8e9cdaf9773fc0c08a6f433507cb559edfd0f0"
                ),
                _ => {}
            }
        }
    }

    /// Whether every 12-bit coefficient of `poly_bytes` is below q.
    fn reduced(poly_bytes: &[u8]) -> bool {
        poly_bytes.chunks(3).all(|b| {
            let (lo, hi) = (
                u16::from(b[0]) | (u16::from(b[1] & 15) << 8),
                (u16::from(b[1]) >> 4) | (u16::from(b[2]) << 4),
            );
            lo < 3329 && hi < 3329
        })
    }

    // BoringSSL's key generation, encapsulation, and decapsulation vectors,
    // NIST's among them, and its EVP keys' raw encodings.
    #[test]
    fn boringssl() {
        use crate::test::file_test::tests;

        for test in tests("boringssl/crypto/mlkem/mlkem768_keygen_tests.txt") {
            let key = mlkem768::DecapKey::keygen_internal(&test.bytes("seed").try_into().unwrap());
            assert_eq!(
                &key.encapsulation_key().as_bytes()[..],
                test.bytes("public_key"),
                "{test}"
            );
            assert_eq!(
                &low::ct::into_public(key.as_bytes())[..],
                test.bytes("private_key"),
                "{test}"
            );
        }

        for test in tests("boringssl/crypto/mlkem/mlkem768_nist_keygen_tests.txt") {
            let seed = [test.bytes("d"), test.bytes("z")].concat();
            let key = mlkem768::DecapKey::keygen_internal(&seed.try_into().unwrap());
            assert_eq!(
                &key.encapsulation_key().as_bytes()[..],
                test.bytes("ek"),
                "{test}"
            );
            assert_eq!(
                &low::ct::into_public(key.as_bytes())[..],
                test.bytes("dk"),
                "{test}"
            );
        }

        for test in tests("boringssl/crypto/mlkem/mlkem768_encap_tests.txt") {
            let m = mlkem768::Message(test.bytes("entropy").try_into().unwrap());
            let key = EncapsulationKey::new(&ML_KEM_768, &test.bytes("public_key"));
            match test.str("result") {
                "pass" => {
                    let (secret, ciphertext) = key.unwrap().key.encaps_internal(m);
                    assert_eq!(&ciphertext.as_ref()[..], test.bytes("ciphertext"), "{test}");
                    let secret = secret_bytes(&SharedSecret(secret));
                    assert_eq!(secret, test.bytes("shared_secret"), "{test}");
                }
                _ => assert!(matches!(key, Err(Error::KeyRejected(_))), "{test}"),
            }
        }

        // rind imports no decapsulation key, so the vectors of a malformed
        // one have no counterpart.
        for test in tests("boringssl/crypto/mlkem/mlkem768_decap_tests.txt") {
            let dk = test.bytes("private_key");
            let Some(dk) = <&[u8; 2400]>::try_from(&dk[..])
                .ok()
                .filter(|dk| reduced(&dk[..1152]))
                .and_then(mlkem768::DecapKey::from_bytes)
            else {
                assert_eq!(test.str("result"), "fail", "{test}");
                continue;
            };
            let result = DecapsulationKey(dk)
                .decapsulate(&test.bytes("ciphertext"))
                .map(|secret| secret_bytes(&secret));
            match test.str("result") {
                "pass" => assert_eq!(result, Ok(test.bytes("shared_secret")), "{test}"),
                _ => assert_eq!(result, Err(Error::WrongLength), "{test}"),
            }
        }

        for test in tests("boringssl/crypto/mlkem/mlkem768_nist_decap_tests.txt") {
            let dk = mlkem768::DecapKey::from_bytes(&test.bytes("dk").try_into().unwrap());
            let secret = DecapsulationKey(dk.unwrap())
                .decapsulate(&test.bytes("c"))
                .unwrap();
            assert_eq!(secret_bytes(&secret), test.bytes("k"), "{test}");
        }

        // BoringSSL's EVP tests: rind has the raw encodings, not the SPKI or
        // PKCS#8 ones, and imports no key, so of the keys it takes the seeds.
        let mut keys = std::collections::HashMap::new();
        for test in tests("boringssl/crypto/evp/test/mlkem_tests.txt") {
            if test.get("Algorithm") != Some("ML-KEM-768") {
                continue;
            }
            if let Some(name) = test.get("Key") {
                if test.get("Error").is_some() {
                    continue;
                }
                let seed = match test.get("PrivateSeed") {
                    Some(_) => test.bytes("PrivateSeed"),
                    // A seed-only PKCS#8 key ends in its 64-byte seed.
                    None => test.bytes("PKCS8")[22..].to_vec(),
                };
                let key = mlkem768::DecapKey::keygen_internal(&seed.try_into().unwrap());
                let key = DecapsulationKey(key);
                if test.get("RawPublic").is_some() {
                    assert_eq!(key.public_key().as_ref(), test.bytes("RawPublic"), "{test}");
                }
                keys.insert(name.to_string(), key);
            } else if let Some(name) = test.get("Decapsulate") {
                let key = &keys[name.trim_end_matches("/Private")];
                let result = key
                    .decapsulate(&test.bytes("Input"))
                    .map(|secret| secret_bytes(&secret));
                match test.get("DecapsulateFail") {
                    Some(_) => assert_eq!(result, Err(Error::WrongLength), "{test}"),
                    None => assert_eq!(result, Ok(test.bytes("Output")), "{test}"),
                }
            } else if let Some(name) = test.get("Encapsulate") {
                let ek = keys[name].public_key();
                if test.get("Entropy").is_none() {
                    let (ciphertext, secret) = ek.encapsulate().unwrap();
                    let decapsulated = keys[name].decapsulate(ciphertext.as_ref()).unwrap();
                    assert_eq!(secret_bytes(&decapsulated), secret_bytes(&secret), "{test}");
                    continue;
                }
                let m = mlkem768::Message(test.bytes("Entropy").try_into().unwrap());
                let (secret, ciphertext) = ek.key.encaps_internal(m);
                assert_eq!(&ciphertext.as_ref()[..], test.bytes("Ciphertext"), "{test}");
                let secret = secret_bytes(&SharedSecret(secret));
                assert_eq!(secret, test.bytes("Secret"), "{test}");
            } else if let Some(name) = test.get("EncapsulateDecapsulate") {
                let key = &keys[name.trim_end_matches("/Private")];
                let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
                let decapsulated = key.decapsulate(ciphertext.as_ref()).unwrap();
                assert_eq!(secret_bytes(&decapsulated), secret_bytes(&secret), "{test}");
            } else {
                panic!("{test}: unexpected test");
            }
        }
    }

    // Exporting our decapsulation key needs crate access, so this
    // differential test lives here rather than in `tests/crosschecks.rs`.
    #[cfg(not(any(miri, target_family = "wasm")))]
    mod crosscheck {
        use aws_lc_rs::kem::{self, ML_KEM_768};
        use proptest::prelude::*;
        use proptest::sample::Index;

        use super::*;

        // Each case generates a key, which is slow under emulation.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(32))]

            // We decapsulate what aws-lc-rs encapsulates to our key, and so
            // does aws-lc-rs holding our serialized key. With one byte of the
            // ciphertext altered, both give the same implicit-rejection secret.
            #[test]
            fn encapsulated_by_theirs(alter in prop::option::of((any::<Index>(), 1..=255u8))) {
                let ours = DecapsulationKey::generate(&super::ML_KEM_768).unwrap();
                let theirs = kem::DecapsulationKey::new(
                    &ML_KEM_768,
                    &low::ct::into_public(ours.0.as_bytes()),
                )
                .unwrap();
                let (ciphertext, secret) =
                    kem::EncapsulationKey::new(&ML_KEM_768, ours.public_key().as_ref())
                        .unwrap()
                        .encapsulate()
                        .unwrap();

                let mut ciphertext = ciphertext.as_ref().to_vec();
                if let Some((index, xor)) = alter {
                    let index = index.index(ciphertext.len());
                    ciphertext[index] ^= xor;
                }
                let theirs_secret = theirs.decapsulate(kem::Ciphertext::from(&ciphertext[..])).unwrap();
                let ours_secret = secret_bytes(&ours.decapsulate(&ciphertext).unwrap());
                prop_assert_eq!(&ours_secret[..], theirs_secret.as_ref());
                prop_assert_eq!(&ours_secret[..] == secret.as_ref(), alter.is_none());
            }
        }
    }
}
