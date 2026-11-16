// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::marker::PhantomData;

use crate::Error;
use crate::error::KeyFormatError;
use crate::mid::mlkem::{self, Array, Params};
pub use crate::mid::mlkem::{MlKem512, MlKem768, MlKem1024};

/// An ML-KEM parameter set: [`MlKem512`], [`MlKem768`], or [`MlKem1024`].
///
/// Each key, ciphertext, and secret names its set, so a ciphertext of one
/// set fails to compile against a key of another.
pub trait Algorithm: Params {}

impl Algorithm for MlKem512 {}
impl Algorithm for MlKem768 {}
impl Algorithm for MlKem1024 {}

/// A decapsulation key, which decapsulates any number of ciphertexts, wiped on drop under the `wipe` feature.
pub struct DecapsulationKey<A: Algorithm>(mlkem::DecapKey<A>);

impl<A: Algorithm> DecapsulationKey<A> {
    /// Generates a decapsulation key from the system random source.
    pub fn generate() -> Result<Self, Error> {
        mlkem::DecapKey::generate().map(Self)
    }

    /// Returns the encapsulation key to send to the peer.
    pub fn public_key(&self) -> EncapsulationKey<A> {
        let key = self.0.encapsulation_key();
        EncapsulationKey {
            bytes: key.as_bytes(),
            key,
        }
    }

    /// Recovers the secret the peer encapsulated in `ciphertext`.
    ///
    /// A tampered ciphertext yields an unrelated secret (FIPS-203's implicit
    /// rejection), so the peer learns nothing until the secret is used.
    pub fn decapsulate(&self, ciphertext: &Ciphertext<A>) -> SharedSecret<A> {
        SharedSecret::new(self.0.decaps(&ciphertext.0))
    }
}

impl<A: Algorithm> fmt::Debug for DecapsulationKey<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecapsulationKey").finish_non_exhaustive()
    }
}

/// An encapsulation key, which anyone may encapsulate a secret to.
pub struct EncapsulationKey<A: Algorithm> {
    key: mlkem::EncapKey<A>,
    bytes: A::EncapKeyBytes,
}

impl<A: Algorithm> EncapsulationKey<A> {
    /// Parses a peer's encapsulation key.
    ///
    /// Fails with [`Error::KeyRejected`] for the wrong length, or if it fails
    /// FIPS-203's modulus check.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        let bytes = A::EncapKeyBytes::from_slice(bytes).ok_or(KeyFormatError::WrongLength)?;
        let key = mlkem::EncapKey::from_bytes(&bytes)?;
        Ok(Self { key, bytes })
    }

    /// Encapsulates a fresh random secret, returning the ciphertext to send
    /// to the key's holder and the secret.
    pub fn encapsulate(&self) -> Result<(Ciphertext<A>, SharedSecret<A>), Error> {
        let (secret, ciphertext) = self.key.encaps()?;
        Ok((Ciphertext(ciphertext), SharedSecret::new(secret)))
    }
}

impl<A: Algorithm> Clone for EncapsulationKey<A> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
            bytes: self.bytes.clone(),
        }
    }
}

impl<A: Algorithm> AsRef<[u8]> for EncapsulationKey<A> {
    fn as_ref(&self) -> &[u8] {
        self.bytes.as_ref()
    }
}

impl<A: Algorithm> fmt::Debug for EncapsulationKey<A> {
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
    macro_rules! small {
        ($($a:ty),*) => {$(
            assert!(size_of::<EncapsulationKey<$a>>() < 8192);
            assert!(size_of::<Result<EncapsulationKey<$a>, Error>>() < 8192);
            assert!(size_of::<DecapsulationKey<$a>>() < 8192);
            assert!(size_of::<Result<DecapsulationKey<$a>, Error>>() < 8192);
        )*};
    }
    small!(MlKem512, MlKem768, MlKem1024);
};

/// A ciphertext carrying an encapsulated secret, to send to the key's holder.
pub struct Ciphertext<A: Algorithm>(mlkem::Ciphertext<A>);

impl<A: Algorithm> Ciphertext<A> {
    /// Takes a ciphertext the peer sent.
    ///
    /// Fails with [`Error::WrongLength`] unless it is the parameter set's
    /// length.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        mlkem::Ciphertext::from_slice(bytes)
            .map(Self)
            .ok_or(Error::WrongLength)
    }
}

impl<A: Algorithm> Clone for Ciphertext<A> {
    fn clone(&self) -> Self {
        Self(self.0.clone())
    }
}

impl<A: Algorithm> fmt::Debug for Ciphertext<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<A: Algorithm> AsRef<[u8]> for Ciphertext<A> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

/// The secret both parties share, wiped on drop under the `wipe` feature.
pub struct SharedSecret<A: Algorithm>(mlkem::SharedSecret, PhantomData<A>);

impl<A: Algorithm> SharedSecret<A> {
    fn new(secret: mlkem::SharedSecret) -> Self {
        Self(secret, PhantomData)
    }
}

impl<A: Algorithm> AsRef<[u8]> for SharedSecret<A> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<A: Algorithm> fmt::Debug for SharedSecret<A> {
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

    /// Runs the generic test `f` for every parameter set.
    macro_rules! each_set {
        ($f:ident) => {
            $f::<MlKem512>();
            $f::<MlKem768>();
            $f::<MlKem1024>();
        };
    }

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

    /// The parameter set's size, as file names spell it: `512`, `768`, or
    /// `1024`.
    fn size<A: Algorithm>() -> &'static str {
        A::NAME.trim_start_matches("ML-KEM-")
    }

    fn secret_bytes<A: Algorithm>(secret: &SharedSecret<A>) -> Vec<u8> {
        let bytes = secret.as_ref().to_vec();
        low::ct::public_slice(&bytes);
        bytes
    }

    fn keygen<A: Algorithm>(seed: &[u8]) -> mlkem::DecapKey<A> {
        mlkem::DecapKey::keygen_internal(&seed.try_into().unwrap())
    }

    /// The encapsulation of `m` to `key`: its secret and ciphertext.
    fn encaps<A: Algorithm>(key: &EncapsulationKey<A>, m: &[u8]) -> (Vec<u8>, Ciphertext<A>) {
        let (secret, ciphertext) = key
            .key
            .encaps_internal(mlkem::Message(m.try_into().unwrap()));
        (
            secret_bytes(&SharedSecret::<A>::new(secret)),
            Ciphertext(ciphertext),
        )
    }

    /// The expanded decapsulation key `dk`, or `None` where rind would never
    /// hold it: the wrong length, a coefficient of `s` not below q, or the
    /// wrong `H(ek)`.
    fn expanded<A: Algorithm>(dk: &[u8]) -> Option<DecapsulationKey<A>> {
        A::DecapKeyBytes::from_slice(dk)
            .filter(|dk| reduced(&dk.as_ref()[..384 * A::K]))
            .and_then(|dk| mlkem::DecapKey::from_bytes(&dk))
            .map(DecapsulationKey)
    }

    fn decapsulate<A: Algorithm>(key: &DecapsulationKey<A>, c: &[u8]) -> Result<Vec<u8>, Error> {
        Ciphertext::new(c).map(|c| secret_bytes(&key.decapsulate(&c)))
    }

    #[test]
    fn wycheproof_keygen() {
        fn check<A: Algorithm>() {
            let file = format!("mlkem_{}_keygen_seed_test.json", size::<A>());
            for test in wycheproof::<KemTest>(&file) {
                assert_eq!(test.result, Expected::Valid, "{}", test.id);
                let key = keygen::<A>(&test.seed);
                assert_eq!(low::ct::into_public(key.as_bytes()).as_ref(), &test.dk);
                let key = DecapsulationKey(key);
                assert_eq!(key.public_key().as_ref(), &test.ek);
            }
        }
        each_set!(check);
    }

    #[test]
    fn wycheproof_encaps() {
        fn check<A: Algorithm>() {
            let file = format!("mlkem_{}_encaps_test.json", size::<A>());
            for test in wycheproof::<KemTest>(&file) {
                let result = EncapsulationKey::<A>::new(&test.ek).map(|key| encaps(&key, &test.m));
                match (test.result, &result) {
                    (Expected::Valid, Ok((secret, ciphertext))) => {
                        assert_eq!(secret, &test.k, "{}", test.id);
                        assert_eq!(ciphertext.as_ref(), &test.c, "{}", test.id);
                    }
                    (Expected::Invalid, Err(Error::KeyRejected(_))) => {}
                    _ => panic!("{}: expected {:?} got {:?}", test.id, test.result, result),
                }
            }
        }
        each_set!(check);
    }

    #[test]
    fn wycheproof_decaps() {
        fn check<A: Algorithm>() {
            let file = format!("mlkem_{}_test.json", size::<A>());
            for test in wycheproof::<KemTest>(&file) {
                // Generation never makes a seed of another length.
                if test.seed.len() != 64 {
                    assert_eq!(test.result, Expected::Invalid, "{}", test.id);
                    continue;
                }

                let key = DecapsulationKey(keygen::<A>(&test.seed));
                assert_eq!(key.public_key().as_ref(), &test.ek, "{}", test.id);
                let result = decapsulate(&key, &test.c);
                match (test.result, &result) {
                    (Expected::Valid, Ok(secret)) => assert_eq!(secret, &test.k, "{}", test.id),
                    (Expected::Invalid, Err(Error::WrongLength)) => {}
                    _ => panic!("{}: expected {:?} got {:?}", test.id, test.result, result),
                }
            }
        }
        each_set!(check);
    }

    // Decapsulation from the expanded key, which rind holds but imports only
    // here.
    #[test]
    fn wycheproof_semi_expanded_decaps() {
        fn check<A: Algorithm>() {
            let file = format!("mlkem_{}_semi_expanded_decaps_test.json", size::<A>());
            for test in wycheproof::<KemTest>(&file) {
                let Some(key) = expanded::<A>(&test.dk) else {
                    assert_eq!(test.result, Expected::Invalid, "{}", test.id);
                    continue;
                };
                assert_eq!(key.public_key().as_ref(), &test.ek, "{}", test.id);
                let result = decapsulate(&key, &test.c);
                match (test.result, &result) {
                    (Expected::Valid, Ok(secret)) => assert_eq!(secret, &test.k, "{}", test.id),
                    (Expected::Invalid, Err(Error::WrongLength)) => {}
                    _ => panic!("{}: expected {:?} got {:?}", test.id, test.result, result),
                }
            }
        }
        each_set!(check);
    }

    // CCTV's keys come from FIPS 203's draft, whose key generation lacked
    // `k` in `G(d || k)`, so these check encapsulation and decapsulation,
    // which the final standard kept, from the encoded keys.
    fn cctv_encaps_decaps<A: Algorithm>(record: &[(String, Vec<u8>)]) {
        let ek = EncapsulationKey::<A>::new(cctv_value(record, "ek")).unwrap();
        let (secret, ciphertext) = encaps(&ek, cctv_value(record, "m"));
        assert_eq!(ciphertext.as_ref(), cctv_value(record, "c"));
        assert_eq!(secret, cctv_value(record, "K"));

        let dk = expanded::<A>(cctv_value(record, "dk")).unwrap();
        assert_eq!(dk.public_key().as_ref(), cctv_value(record, "ek"));
        let secret = decapsulate(&dk, cctv_value(record, "c")).unwrap();
        assert_eq!(secret, cctv_value(record, "K"));
    }

    // One key's every intermediate value, of which we check the results.
    #[test]
    fn cctv_intermediate() {
        fn check<A: Algorithm>() {
            for record in cctv_records(&format!("ML-KEM/intermediate/{}.txt", A::NAME)) {
                cctv_encaps_decaps::<A>(&record);
            }
        }
        each_set!(check);
    }

    // Keys whose matrix needs over 575 bytes of SHAKE-128 to sample.
    #[test]
    fn cctv_unlucky_sample() {
        fn check<A: Algorithm>() {
            for record in cctv_records(&format!("ML-KEM/unluckysample/{}.txt", A::NAME)) {
                cctv_encaps_decaps::<A>(&record);
            }
        }
        each_set!(check);
    }

    // A ciphertext that matches the re-encryption up to a zero byte, which a
    // `strcmp` comparison would accept.
    #[test]
    fn cctv_strcmp() {
        fn check<A: Algorithm>() {
            for record in cctv_records(&format!("ML-KEM/strcmp/{}.txt", A::NAME)) {
                let key = expanded::<A>(cctv_value(&record, "dk")).unwrap();
                let secret = decapsulate(&key, cctv_value(&record, "c")).unwrap();
                assert_eq!(secret, cctv_value(&record, "K"));
            }
        }
        each_set!(check);
    }

    // Encapsulation keys with one coefficient from q to 4095, for every value
    // and position.
    #[test]
    fn cctv_modulus() {
        fn check<A: Algorithm>(want: usize) {
            use std::io::{BufRead, BufReader};

            let path = cctv(&format!("ML-KEM/modulus/{}.txt.gz", A::NAME));
            let file = std::fs::File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"));
            let mut count = 0;
            for line in BufReader::new(flate2::read::GzDecoder::new(file)).lines() {
                let ek = hex::decode(line.unwrap()).unwrap();
                assert_eq!(
                    EncapsulationKey::<A>::new(&ek).err(),
                    Some(KeyFormatError::MlKemModulus.into())
                );
                count += 1;
            }
            assert_eq!(count, want, "{}", A::NAME);
        }
        check::<MlKem512>(775);
        check::<MlKem768>(780);
        check::<MlKem1024>(1040);
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

        let mut rng = Shake128::new(&Shake128Sponge::new());
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

            let key = DecapsulationKey(keygen::<MlKem768>(&seed));
            let (secret, ciphertext) = encaps(&key.public_key(), &m);
            assert_eq!(decapsulate(&key, ciphertext.as_ref()).unwrap(), secret);
            let rejected = decapsulate(&key, &ct).unwrap();

            acc.absorb(key.public_key().as_ref());
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
    // NIST's among them, for ML-KEM-768 and ML-KEM-1024.
    #[test]
    fn boringssl() {
        use crate::test::file_test::tests;

        fn check<A: Algorithm>() {
            let file =
                |name: &str| format!("boringssl/crypto/mlkem/mlkem{}_{name}.txt", size::<A>());

            for test in tests(&file("keygen_tests")) {
                let key = keygen::<A>(&test.bytes("seed"));
                let public = key.encapsulation_key().as_bytes();
                assert_eq!(public.as_ref(), test.bytes("public_key"), "{test}");
                let private = low::ct::into_public(key.as_bytes());
                assert_eq!(private.as_ref(), test.bytes("private_key"), "{test}");
            }

            for test in tests(&file("nist_keygen_tests")) {
                let key = keygen::<A>(&[test.bytes("d"), test.bytes("z")].concat());
                let public = key.encapsulation_key().as_bytes();
                assert_eq!(public.as_ref(), test.bytes("ek"), "{test}");
                let private = low::ct::into_public(key.as_bytes());
                assert_eq!(private.as_ref(), test.bytes("dk"), "{test}");
            }

            for test in tests(&file("encap_tests")) {
                let key = EncapsulationKey::<A>::new(&test.bytes("public_key"));
                match test.str("result") {
                    "pass" => {
                        let (secret, ciphertext) = encaps(&key.unwrap(), &test.bytes("entropy"));
                        assert_eq!(ciphertext.as_ref(), test.bytes("ciphertext"), "{test}");
                        assert_eq!(secret, test.bytes("shared_secret"), "{test}");
                    }
                    _ => assert!(matches!(key, Err(Error::KeyRejected(_))), "{test}"),
                }
            }

            // rind imports no decapsulation key, so the vectors of a malformed
            // one have no counterpart.
            for test in tests(&file("decap_tests")) {
                let Some(key) = expanded::<A>(&test.bytes("private_key")) else {
                    assert_eq!(test.str("result"), "fail", "{test}");
                    continue;
                };
                let result = decapsulate(&key, &test.bytes("ciphertext"));
                match test.str("result") {
                    "pass" => assert_eq!(result, Ok(test.bytes("shared_secret")), "{test}"),
                    _ => assert_eq!(result, Err(Error::WrongLength), "{test}"),
                }
            }

            for test in tests(&file("nist_decap_tests")) {
                let key = expanded::<A>(&test.bytes("dk")).unwrap();
                let secret = decapsulate(&key, &test.bytes("c")).unwrap();
                assert_eq!(secret, test.bytes("k"), "{test}");
            }
        }
        check::<MlKem768>();
        check::<MlKem1024>();
    }

    // BoringSSL's EVP tests: rind has the raw encodings, not the SPKI or
    // PKCS#8 ones, and imports no key, so of the keys it takes the seeds.
    #[test]
    fn boringssl_evp() {
        use crate::test::file_test::tests;

        fn check<A: Algorithm>() {
            let mut keys = std::collections::HashMap::new();
            for test in tests("boringssl/crypto/evp/test/mlkem_tests.txt") {
                if test.get("Algorithm").is_some_and(|alg| alg != A::NAME) {
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
                    let key = DecapsulationKey(keygen::<A>(&seed));
                    if test.get("RawPublic").is_some() {
                        assert_eq!(key.public_key().as_ref(), test.bytes("RawPublic"), "{test}");
                    }
                    keys.insert(name.to_string(), key);
                } else if let Some(name) = test.get("Decapsulate") {
                    // Each key's tests follow its own `Key` line.
                    let Some(key) = keys.get(name.trim_end_matches("/Private")) else {
                        continue;
                    };
                    let result = decapsulate(key, &test.bytes("Input"));
                    match test.get("DecapsulateFail") {
                        Some(_) => assert_eq!(result, Err(Error::WrongLength), "{test}"),
                        None => assert_eq!(result, Ok(test.bytes("Output")), "{test}"),
                    }
                } else if let Some(name) = test.get("Encapsulate") {
                    let Some(key) = keys.get(name) else {
                        continue;
                    };
                    let ek = key.public_key();
                    if test.get("Entropy").is_none() {
                        let (ciphertext, secret) = ek.encapsulate().unwrap();
                        let decapsulated = key.decapsulate(&ciphertext);
                        assert_eq!(secret_bytes(&decapsulated), secret_bytes(&secret), "{test}");
                        continue;
                    }
                    let (secret, ciphertext) = encaps(&ek, &test.bytes("Entropy"));
                    assert_eq!(ciphertext.as_ref(), test.bytes("Ciphertext"), "{test}");
                    assert_eq!(secret, test.bytes("Secret"), "{test}");
                } else if let Some(name) = test.get("EncapsulateDecapsulate") {
                    let Some(key) = keys.get(name.trim_end_matches("/Private")) else {
                        continue;
                    };
                    let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
                    let decapsulated = key.decapsulate(&ciphertext);
                    assert_eq!(secret_bytes(&decapsulated), secret_bytes(&secret), "{test}");
                } else {
                    panic!("{test}: unexpected test");
                }
            }
            assert!(!keys.is_empty(), "{}", A::NAME);
        }
        check::<MlKem768>();
        check::<MlKem1024>();
    }

    // Exporting our decapsulation key needs crate access, so this
    // differential test lives here rather than in `tests/crosschecks.rs`.
    #[cfg(not(any(miri, target_family = "wasm")))]
    mod crosscheck {
        use aws_lc_rs::kem::{self, AlgorithmId, ML_KEM_512, ML_KEM_768, ML_KEM_1024};
        use proptest::prelude::*;
        use proptest::sample::Index;

        use super::*;

        fn algorithm<A: Algorithm>() -> &'static kem::Algorithm<AlgorithmId> {
            match A::K {
                2 => &ML_KEM_512,
                3 => &ML_KEM_768,
                4 => &ML_KEM_1024,
                _ => unreachable!(),
            }
        }

        // We decapsulate what aws-lc-rs encapsulates to our key, and so
        // does aws-lc-rs holding our serialized key. With one byte of the
        // ciphertext altered, both give the same implicit-rejection secret.
        fn encapsulated_by_theirs<A: Algorithm>(
            alter: Option<(Index, u8)>,
        ) -> Result<(), TestCaseError> {
            let ours = DecapsulationKey::<A>::generate().unwrap();
            let theirs = kem::DecapsulationKey::new(
                algorithm::<A>(),
                low::ct::into_public(ours.0.as_bytes()).as_ref(),
            )
            .unwrap();
            let (ciphertext, secret) =
                kem::EncapsulationKey::new(algorithm::<A>(), ours.public_key().as_ref())
                    .unwrap()
                    .encapsulate()
                    .unwrap();

            let mut ciphertext = ciphertext.as_ref().to_vec();
            if let Some((index, xor)) = alter {
                let index = index.index(ciphertext.len());
                ciphertext[index] ^= xor;
            }
            let theirs_secret = theirs
                .decapsulate(kem::Ciphertext::from(&ciphertext[..]))
                .unwrap();
            let ours_secret = decapsulate(&ours, &ciphertext).unwrap();
            prop_assert_eq!(&ours_secret[..], theirs_secret.as_ref());
            prop_assert_eq!(&ours_secret[..] == secret.as_ref(), alter.is_none());
            Ok(())
        }

        // Each case generates a key, which is slow under emulation.
        proptest! {
            #![proptest_config(ProptestConfig::with_cases(32))]

            #[test]
            fn encapsulated_by_theirs_512(alter in prop::option::of((any::<Index>(), 1..=255u8))) {
                encapsulated_by_theirs::<MlKem512>(alter)?;
            }

            #[test]
            fn encapsulated_by_theirs_768(alter in prop::option::of((any::<Index>(), 1..=255u8))) {
                encapsulated_by_theirs::<MlKem768>(alter)?;
            }

            #[test]
            fn encapsulated_by_theirs_1024(alter in prop::option::of((any::<Index>(), 1..=255u8))) {
                encapsulated_by_theirs::<MlKem1024>(alter)?;
            }
        }
    }
}
