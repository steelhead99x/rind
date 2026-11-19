// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::panic::{RefUnwindSafe, UnwindSafe};

use crate::Error;
use crate::error::KeyFormatError;
use crate::low;
use crate::mid::mlkem::{self, Array, Params};
pub use crate::mid::mlkem::{MlKem512, MlKem768, MlKem1024};
use crate::mid::xwing;

// The marker is defined here rather than in `mid::xwing`, so that its
// `Algorithm` implementation, which names `high` items, stays in `high`, as
// `admin/structure` requires.
/// X-Wing: X25519 and ML-KEM-768, as draft-connolly-cfrg-xwing-kem defines
/// it.
#[derive(Debug)]
pub enum XWing {}

mod sealed {
    pub trait Sealed {}
    impl<P: super::Params> Sealed for P {}
    impl Sealed for super::XWing {}
}

/// A key encapsulation algorithm: an ML-KEM parameter set, [`MlKem512`],
/// [`MlKem768`], or [`MlKem1024`], or [`XWing`], the hybrid of X25519 and
/// ML-KEM-768.
///
/// Each key, ciphertext, and secret names its algorithm, so a ciphertext of
/// one fails to compile against a key of another.
pub trait Algorithm: sealed::Sealed + fmt::Debug + Sized + Plain {
    /// A decapsulation key.
    #[doc(hidden)]
    type DecapKey: Plain;
    /// An encapsulation key.
    #[doc(hidden)]
    type EncapKey: Plain + Clone;
    /// A ciphertext.
    #[doc(hidden)]
    type Ciphertext: Plain + Clone + fmt::Debug + AsRef<[u8]>;
    /// A shared secret.
    #[doc(hidden)]
    type SharedSecret: Plain + AsRef<[u8; 32]>;
    /// A decapsulation key's seed.
    #[doc(hidden)]
    type Seed: Array<u8>;

    // The operations, each taking an `Internal`, which only rind can make, so
    // that no other crate calls them. Each set's compile in rind, not in each
    // generic caller, as `Params`'s do.
    #[doc(hidden)]
    fn generate(_: Internal) -> Result<Self::DecapKey, Error>;
    #[doc(hidden)]
    fn public_key(_: Internal, key: &Self::DecapKey) -> Self::EncapKey;
    #[doc(hidden)]
    fn decapsulate(
        _: Internal,
        key: &Self::DecapKey,
        ciphertext: &Self::Ciphertext,
    ) -> Self::SharedSecret;
    #[doc(hidden)]
    fn parse_encapsulation_key(_: Internal, bytes: &[u8]) -> Result<Self::EncapKey, Error>;
    #[doc(hidden)]
    fn encapsulation_key_bytes(_: Internal, key: &Self::EncapKey) -> &[u8];
    #[doc(hidden)]
    fn encapsulate(
        _: Internal,
        key: &Self::EncapKey,
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), Error>;
    #[doc(hidden)]
    fn parse_ciphertext(_: Internal, bytes: &[u8]) -> Option<Self::Ciphertext>;
    /// Wipes and frees what a key holds only decoded, so that its holder's
    /// drop can wipe the rest of its value.
    #[doc(hidden)]
    fn free_decoded(_: Internal, key: &mut Self::EncapKey);
}

/// The auto traits every key, ciphertext, and secret has, which a generic
/// caller may rely on.
#[doc(hidden)]
pub trait Plain: Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static {}

impl<T: Send + Sync + Unpin + UnwindSafe + RefUnwindSafe + 'static> Plain for T {}

/// Proof that a call to an [`Algorithm`] method comes from rind: no other
/// crate can make one, though a generic caller can name the methods.
#[doc(hidden)]
#[derive(Clone, Copy)]
pub struct Internal(());

// Each ML-KEM parameter set, whose operations run under `Params`'s MXCSR
// mitigation.
impl<P: Params> Algorithm for P {
    type DecapKey = mlkem::DecapKey<P>;
    type EncapKey = mlkem::EncapKey<P>;
    type Ciphertext = mlkem::Ciphertext<P>;
    type SharedSecret = mlkem::SharedSecret;
    // `d || z`, which no key here exports yet.
    type Seed = [u8; 64];

    fn generate(_: Internal) -> Result<Self::DecapKey, Error> {
        mlkem::DecapKey::generate()
    }

    fn public_key(_: Internal, key: &Self::DecapKey) -> Self::EncapKey {
        key.encapsulation_key()
    }

    fn decapsulate(
        _: Internal,
        key: &Self::DecapKey,
        ciphertext: &Self::Ciphertext,
    ) -> Self::SharedSecret {
        key.decaps(ciphertext)
    }

    fn parse_encapsulation_key(_: Internal, bytes: &[u8]) -> Result<Self::EncapKey, Error> {
        let bytes = P::EncapKeyBytes::from_slice(bytes).ok_or(KeyFormatError::WrongLength)?;
        mlkem::EncapKey::from_bytes(&bytes)
    }

    fn encapsulation_key_bytes(_: Internal, key: &Self::EncapKey) -> &[u8] {
        key.as_bytes().as_ref()
    }

    fn encapsulate(
        _: Internal,
        key: &Self::EncapKey,
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), Error> {
        key.encaps()
    }

    fn parse_ciphertext(_: Internal, bytes: &[u8]) -> Option<Self::Ciphertext> {
        mlkem::Ciphertext::from_slice(bytes)
    }

    fn free_decoded(_: Internal, key: &mut Self::EncapKey) {
        key.free_decoded();
    }
}

// X-Wing: the draft's key generation, encapsulation, and decapsulation over
// ML-KEM-768 and X25519, which `mid::xwing` composes.
impl Algorithm for XWing {
    type DecapKey = xwing::DecapKey;
    type EncapKey = xwing::EncapKey;
    type Ciphertext = xwing::Ciphertext;
    type SharedSecret = xwing::SharedSecret;
    type Seed = [u8; xwing::SEED_LEN];

    fn generate(_: Internal) -> Result<Self::DecapKey, Error> {
        xwing::DecapKey::generate()
    }

    fn public_key(_: Internal, key: &Self::DecapKey) -> Self::EncapKey {
        key.encapsulation_key()
    }

    fn decapsulate(
        _: Internal,
        key: &Self::DecapKey,
        ciphertext: &Self::Ciphertext,
    ) -> Self::SharedSecret {
        key.decaps(ciphertext)
    }

    fn parse_encapsulation_key(_: Internal, bytes: &[u8]) -> Result<Self::EncapKey, Error> {
        xwing::EncapKey::from_bytes(bytes)
    }

    fn encapsulation_key_bytes(_: Internal, key: &Self::EncapKey) -> &[u8] {
        key.as_bytes()
    }

    fn encapsulate(
        _: Internal,
        key: &Self::EncapKey,
    ) -> Result<(Self::SharedSecret, Self::Ciphertext), Error> {
        key.encaps()
    }

    fn parse_ciphertext(_: Internal, bytes: &[u8]) -> Option<Self::Ciphertext> {
        xwing::Ciphertext::from_slice(bytes)
    }

    fn free_decoded(_: Internal, key: &mut Self::EncapKey) {
        key.free_decoded();
    }
}

/// A decapsulation key, which decapsulates any number of ciphertexts, and
/// its encapsulation key; wiped on drop.
pub struct DecapsulationKey<A: Algorithm> {
    key: A::DecapKey,
    public: EncapsulationKey<A>,
}

impl<A: Algorithm> DecapsulationKey<A> {
    fn new(key: A::DecapKey) -> Self {
        Self {
            public: EncapsulationKey {
                key: A::public_key(Internal(()), &key),
            },
            key,
        }
    }

    /// Generates a decapsulation key from the system random source.
    pub fn generate() -> Result<Self, Error> {
        A::generate(Internal(())).map(Self::new)
    }

    /// Returns the encapsulation key to send to the peer.
    pub fn public_key(&self) -> &EncapsulationKey<A> {
        &self.public
    }

    /// Recovers the secret the peer encapsulated in `ciphertext`.
    ///
    /// A tampered ciphertext yields an unrelated secret (ML-KEM's implicit
    /// rejection, which X-Wing keeps), so the peer learns nothing until the
    /// secret is used.
    pub fn decapsulate(&self, ciphertext: &Ciphertext<A>) -> SharedSecret<A> {
        SharedSecret(A::decapsulate(Internal(()), &self.key, &ciphertext.0))
    }
}

impl DecapsulationKey<XWing> {
    /// Loads X-Wing's private key, its 32-byte seed, which the key expands
    /// on load: the draft's `GenerateKeyPairDerand`.
    ///
    /// Fails with [`Error::KeyRejected`] unless `seed` is 32 bytes.
    pub fn from_seed(seed: &[u8]) -> Result<Self, Error> {
        let seed: [u8; xwing::SEED_LEN] =
            seed.try_into().map_err(|_| KeyFormatError::WrongLength)?;
        Ok(Self::new(xwing::DecapKey::from_seed(&seed)))
    }

    /// Returns the private key's 32-byte seed, which is what
    /// [`Self::from_seed`] loads and the draft stores as the key.
    pub fn to_seed(&self) -> Seed<XWing> {
        Seed(self.key.seed())
    }
}

impl<A: Algorithm> Drop for DecapsulationKey<A> {
    // The private key's own drop wipes it, so this wipes the encapsulation
    // key, once it frees its decoded form.
    fn drop(&mut self) {
        A::free_decoded(Internal(()), &mut self.public.key);
        low::zeroise_value(&mut self.public);
    }
}

// Bytes, a hash and its flag, and a decoded form that is `None` once freed.
impl<A: Algorithm> low::Zeroable for EncapsulationKey<A> {}

impl<A: Algorithm> fmt::Debug for DecapsulationKey<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecapsulationKey").finish_non_exhaustive()
    }
}

/// A decapsulation key's seed, wiped on drop.
pub struct Seed<A: Algorithm>(A::Seed);

impl<A: Algorithm> AsRef<[u8]> for Seed<A> {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl<A: Algorithm> fmt::Debug for Seed<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Seed").finish_non_exhaustive()
    }
}

impl<A: Algorithm> Drop for Seed<A> {
    fn drop(&mut self) {
        low::zeroise(self.0.as_mut());
    }
}

/// An encapsulation key, which anyone may encapsulate a secret to.
pub struct EncapsulationKey<A: Algorithm> {
    key: A::EncapKey,
}

impl<A: Algorithm> EncapsulationKey<A> {
    /// Parses a peer's encapsulation key.
    ///
    /// Fails with [`Error::KeyRejected`] for the wrong length, or if its
    /// ML-KEM key fails FIPS-203's modulus check.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        A::parse_encapsulation_key(Internal(()), bytes).map(|key| Self { key })
    }

    /// Encapsulates a fresh random secret, returning the ciphertext to send
    /// to the key's holder and the secret.
    pub fn encapsulate(&self) -> Result<(Ciphertext<A>, SharedSecret<A>), Error> {
        let (secret, ciphertext) = A::encapsulate(Internal(()), &self.key)?;
        Ok((Ciphertext(ciphertext), SharedSecret(secret)))
    }
}

impl<A: Algorithm> Clone for EncapsulationKey<A> {
    fn clone(&self) -> Self {
        Self {
            key: self.key.clone(),
        }
    }
}

impl<A: Algorithm> AsRef<[u8]> for EncapsulationKey<A> {
    fn as_ref(&self) -> &[u8] {
        A::encapsulation_key_bytes(Internal(()), &self.key)
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
    small!(MlKem512, MlKem768, MlKem1024, XWing);
};

/// A ciphertext carrying an encapsulated secret, to send to the key's holder.
pub struct Ciphertext<A: Algorithm>(A::Ciphertext);

impl<A: Algorithm> Ciphertext<A> {
    /// Takes a ciphertext the peer sent.
    ///
    /// Fails with [`Error::WrongLength`] unless it is the algorithm's
    /// length.
    pub fn new(bytes: &[u8]) -> Result<Self, Error> {
        A::parse_ciphertext(Internal(()), bytes)
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

/// The secret both parties share, wiped on drop.
pub struct SharedSecret<A: Algorithm>(A::SharedSecret);

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
    fn size<A: Params>() -> &'static str {
        A::NAME.trim_start_matches("ML-KEM-")
    }

    fn secret_bytes<A: Algorithm>(secret: &SharedSecret<A>) -> Vec<u8> {
        let bytes = secret.as_ref().to_vec();
        low::ct::public_slice(&bytes);
        bytes
    }

    fn keygen<A: Params>(seed: &[u8]) -> mlkem::DecapKey<A> {
        mlkem::DecapKey::keygen_internal(&seed.try_into().unwrap())
    }

    /// The encapsulation of `m` to `key`: its secret and ciphertext.
    fn encaps<A: Params>(key: &EncapsulationKey<A>, m: &[u8]) -> (Vec<u8>, Ciphertext<A>) {
        let (secret, ciphertext) = key
            .key
            .encaps_internal(mlkem::Message(m.try_into().unwrap()));
        (
            secret_bytes(&SharedSecret::<A>(secret)),
            Ciphertext(ciphertext),
        )
    }

    /// The expanded decapsulation key `dk`, or `None` where rind would never
    /// hold it: the wrong length, a coefficient of `s` not below q, or the
    /// wrong `H(ek)`.
    fn expanded<A: Params>(dk: &[u8]) -> Option<DecapsulationKey<A>> {
        A::DecapKeyBytes::from_slice(dk)
            .filter(|dk| reduced(&dk.as_ref()[..384 * A::K]))
            .and_then(|dk| mlkem::DecapKey::from_bytes(&dk))
            .map(DecapsulationKey::new)
    }

    fn decapsulate<A: Algorithm>(key: &DecapsulationKey<A>, c: &[u8]) -> Result<Vec<u8>, Error> {
        Ciphertext::new(c).map(|c| secret_bytes(&key.decapsulate(&c)))
    }

    /// A cloned ciphertext decapsulates to the same secret.
    #[test]
    fn cloned_ciphertext_decapsulates() {
        fn check<A: Algorithm>() {
            let key = DecapsulationKey::<A>::generate().unwrap();
            let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
            let clone = ciphertext.clone();
            assert_eq!(clone.as_ref(), ciphertext.as_ref());
            assert_eq!(
                secret_bytes(&key.decapsulate(&clone)),
                secret_bytes(&secret)
            );
        }
        each_set!(check);
    }

    #[test]
    fn wycheproof_keygen() {
        fn check<A: Params>() {
            let file = format!("mlkem_{}_keygen_seed_test.json", size::<A>());
            for test in wycheproof::<KemTest>(&file) {
                assert_eq!(test.result, Expected::Valid, "{}", test.id);
                let key = keygen::<A>(&test.seed);
                assert_eq!(low::ct::into_public(key.as_bytes()).as_ref(), &test.dk);
                let key = DecapsulationKey::<A>::new(key);
                assert_eq!(key.public_key().as_ref(), &test.ek);
            }
        }
        each_set!(check);
    }

    #[test]
    fn wycheproof_encaps() {
        fn check<A: Params>() {
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
        fn check<A: Params>() {
            let file = format!("mlkem_{}_test.json", size::<A>());
            for test in wycheproof::<KemTest>(&file) {
                // Generation never makes a seed of another length.
                if test.seed.len() != 64 {
                    assert_eq!(test.result, Expected::Invalid, "{}", test.id);
                    continue;
                }

                let key = DecapsulationKey::<A>::new(keygen::<A>(&test.seed));
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
        fn check<A: Params>() {
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
    fn cctv_encaps_decaps<A: Params>(record: &[(String, Vec<u8>)]) {
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
        fn check<A: Params>() {
            for record in cctv_records(&format!("ML-KEM/intermediate/{}.txt", A::NAME)) {
                cctv_encaps_decaps::<A>(&record);
            }
        }
        each_set!(check);
    }

    // Keys whose matrix needs over 575 bytes of SHAKE-128 to sample.
    #[test]
    fn cctv_unlucky_sample() {
        fn check<A: Params>() {
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
        fn check<A: Params>() {
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
        fn check<A: Params>(want: usize) {
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

            let key = DecapsulationKey::<MlKem768>::new(keygen::<MlKem768>(&seed));
            let (secret, ciphertext) = encaps(key.public_key(), &m);
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

        fn check<A: Params>() {
            let file =
                |name: &str| format!("boringssl/crypto/mlkem/mlkem{}_{name}.txt", size::<A>());

            for test in tests(&file("keygen_tests")) {
                let key = keygen::<A>(&test.bytes("seed"));
                let public = key.encapsulation_key().as_bytes().clone();
                assert_eq!(public.as_ref(), test.bytes("public_key"), "{test}");
                let private = low::ct::into_public(key.as_bytes());
                assert_eq!(private.as_ref(), test.bytes("private_key"), "{test}");
            }

            for test in tests(&file("nist_keygen_tests")) {
                let key = keygen::<A>(&[test.bytes("d"), test.bytes("z")].concat());
                let public = key.encapsulation_key().as_bytes().clone();
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

        fn check<A: Params>() {
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
                    let key = DecapsulationKey::<A>::new(keygen::<A>(&seed));
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
                    let (secret, ciphertext) = encaps(ek, &test.bytes("Entropy"));
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

    // draft-connolly-cfrg-xwing-kem's Appendix C, as its repository holds it.
    #[derive(Deserialize)]
    struct XWingVector {
        #[serde(with = "hex::serde")]
        seed: Vec<u8>,
        #[serde(with = "hex::serde")]
        sk: Vec<u8>,
        #[serde(with = "hex::serde")]
        pk: Vec<u8>,
        #[serde(with = "hex::serde")]
        eseed: Vec<u8>,
        #[serde(with = "hex::serde")]
        ct: Vec<u8>,
        #[serde(with = "hex::serde")]
        ss: Vec<u8>,
    }

    // draft-ietf-hpke-pq's MLKEM768-X25519 vectors: the KEM's part of each.
    // `ikmR` goes through the draft's `DeriveKeyPair` to `skRm`, which HPKE's
    // quest implements; `ikmE` is the encapsulation's `eseed`.
    #[derive(Deserialize)]
    struct HpkePqVector {
        kem_id: u16,
        #[serde(rename = "ikmE", with = "hex::serde")]
        ikm_e: Vec<u8>,
        #[serde(rename = "skRm", with = "hex::serde")]
        sk_rm: Vec<u8>,
        #[serde(rename = "pkRm", with = "hex::serde")]
        pk_rm: Vec<u8>,
        #[serde(with = "hex::serde")]
        enc: Vec<u8>,
        #[serde(with = "hex::serde")]
        shared_secret: Vec<u8>,
    }

    /// The draft's `EncapsulateDerand` of `eseed` to `key`: its secret and
    /// ciphertext.
    fn xwing_encaps(key: &EncapsulationKey<XWing>, eseed: &[u8]) -> (Vec<u8>, Ciphertext<XWing>) {
        // A copy, since encapsulation marks its randomness secret in place.
        let eseed: [u8; 64] = eseed.try_into().unwrap();
        let (secret, ciphertext) = key.key.encaps_internal(&eseed);
        (
            secret_bytes(&SharedSecret::<XWing>(secret)),
            Ciphertext(ciphertext),
        )
    }

    /// The bytes of the seed `key` exports.
    fn seed_bytes(key: &DecapsulationKey<XWing>) -> Vec<u8> {
        let bytes = key.to_seed().as_ref().to_vec();
        low::ct::public_slice(&bytes);
        bytes
    }

    fn thirdparty(path: &str) -> std::fs::File {
        let path = format!(
            "{}/../thirdparty/vectors/{path}",
            env!("CARGO_MANIFEST_DIR")
        );
        std::fs::File::open(&path).unwrap_or_else(|_| panic!("cannot open {path}"))
    }

    // The draft's three vectors: key generation from the seed, then
    // encapsulation of the `eseed`, then decapsulation of its ciphertext.
    #[test]
    fn xwing_draft_vectors() {
        let vectors: Vec<XWingVector> =
            serde_json::from_reader(thirdparty("xwing/spec/test-vectors.json")).unwrap();
        assert_eq!(vectors.len(), 3);
        for (i, v) in vectors.iter().enumerate() {
            assert_eq!(v.seed, v.sk, "{i}");
            let key = DecapsulationKey::<XWing>::from_seed(&v.sk).unwrap();
            assert_eq!(key.public_key().as_ref(), v.pk, "{i}");
            assert_eq!(seed_bytes(&key), v.seed, "{i}");

            let ek = EncapsulationKey::<XWing>::new(&v.pk).unwrap();
            let (secret, ciphertext) = xwing_encaps(&ek, &v.eseed);
            assert_eq!(ciphertext.as_ref(), v.ct, "{i}");
            assert_eq!(secret, v.ss, "{i}");
            assert_eq!(decapsulate(&key, &v.ct).unwrap(), v.ss, "{i}");
        }
    }

    // draft-ietf-hpke-pq-05's two vectors for KEM 0x647A: the recipient's key
    // from `skRm`, the encapsulation of `ikmE` to it, and decapsulating `enc`.
    #[test]
    fn xwing_hpke_pq_vectors() {
        let file = std::io::BufReader::new(thirdparty("hpke-pq/test-vectors.json"));
        let mut count = 0;
        for vector in serde_json::Deserializer::from_reader(file).into_iter::<HpkePqVector>() {
            let v = vector.unwrap();
            assert_eq!(v.kem_id, 0x647a);
            count += 1;

            let key = DecapsulationKey::<XWing>::from_seed(&v.sk_rm).unwrap();
            assert_eq!(key.public_key().as_ref(), v.pk_rm);
            assert_eq!(seed_bytes(&key), v.sk_rm);

            let ek = EncapsulationKey::<XWing>::new(&v.pk_rm).unwrap();
            let (secret, ciphertext) = xwing_encaps(&ek, &v.ikm_e);
            assert_eq!(ciphertext.as_ref(), v.enc);
            assert_eq!(secret, v.shared_secret);
            assert_eq!(decapsulate(&key, &v.enc).unwrap(), v.shared_secret);
        }
        assert_eq!(count, 2);
    }

    // What X-Wing refuses: a key, ciphertext, or seed of the wrong length,
    // and an ML-KEM key that fails FIPS 203's modulus check. The X25519 half
    // of a key is any 32 bytes.
    #[test]
    fn xwing_refuses_malformed() {
        let key = DecapsulationKey::<XWing>::from_seed(&[7; 32]).unwrap();
        let pk = key.public_key().as_ref().to_vec();
        let (ciphertext, _) = key.public_key().encapsulate().unwrap();

        for len in [0, 31, 1184, 1215, 1217, 1248] {
            let mut bytes = pk.clone();
            bytes.resize(len, 0);
            assert_eq!(
                EncapsulationKey::<XWing>::new(&bytes).err(),
                Some(KeyFormatError::WrongLength.into()),
                "{len}"
            );
        }
        let mut bytes = pk.clone();
        bytes[..2].copy_from_slice(&[0xff, 0x0f]);
        assert_eq!(
            EncapsulationKey::<XWing>::new(&bytes).err(),
            Some(KeyFormatError::MlKemModulus.into())
        );
        let mut bytes = pk.clone();
        bytes[1184..].fill(0xff);
        assert!(EncapsulationKey::<XWing>::new(&bytes).is_ok());

        for len in [0, 1088, 1119, 1121] {
            let mut bytes = ciphertext.as_ref().to_vec();
            bytes.resize(len, 0);
            assert_eq!(
                Ciphertext::<XWing>::new(&bytes).err(),
                Some(Error::WrongLength)
            );
        }
        for len in [0, 31, 33, 64] {
            assert_eq!(
                DecapsulationKey::<XWing>::from_seed(&vec![7; len]).err(),
                Some(KeyFormatError::WrongLength.into()),
                "{len}"
            );
        }
    }

    // A ciphertext whose X25519 share has a small order gives the zero X25519
    // secret, which the draft's combiner takes as it is: decapsulation cannot
    // fail, and the secret still binds the ciphertext and both public keys.
    #[test]
    fn xwing_decapsulates_small_order_shares() {
        let key = DecapsulationKey::<XWing>::from_seed(&[9; 32]).unwrap();
        let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
        let secret = secret_bytes(&secret);
        let mut tampered = ciphertext.as_ref().to_vec();
        tampered[1088..].fill(0);
        let rejected = decapsulate(&key, &tampered).unwrap();
        assert_ne!(rejected, secret);
        assert_eq!(decapsulate(&key, &tampered).unwrap(), rejected);
        // u = 1, another small-order point, also gives the zero X25519 secret.
        tampered[1088] = 1;
        assert_ne!(decapsulate(&key, &tampered).unwrap(), rejected);

        // Encapsulating to a key with a zero X25519 half works too.
        let mut zero_half = key.public_key().as_ref().to_vec();
        zero_half[1184..].fill(0);
        let ek = EncapsulationKey::<XWing>::new(&zero_half).unwrap();
        let (ciphertext, secret) = ek.encapsulate().unwrap();
        assert_eq!(ciphertext.as_ref().len(), 1120);
        assert_eq!(secret_bytes(&secret).len(), 32);
    }

    // Under `admin/ctgrind`, memcheck fails this if X-Wing's key generation,
    // seed export and load, encapsulation, or decapsulation (with a ciphertext
    // it accepts and one it rejects) branches on or indexes by the seed or a
    // secret derived from it. Nothing secret is compared until the end.
    #[test]
    fn xwing_stays_secret() {
        let key = DecapsulationKey::<XWing>::generate().unwrap();
        let (ciphertext, secret) = key.public_key().encapsulate().unwrap();
        let decapsulated = key.decapsulate(&ciphertext);

        let seed = key.to_seed();
        let loaded = DecapsulationKey::<XWing>::from_seed(seed.as_ref()).unwrap();
        let again = loaded.decapsulate(&ciphertext);

        let mut bytes = ciphertext.as_ref().to_vec();
        bytes[0] ^= 1;
        let rejected = key.decapsulate(&Ciphertext::new(&bytes).unwrap());
        let mut bytes = ciphertext.as_ref().to_vec();
        bytes[1100] ^= 1;
        let altered = key.decapsulate(&Ciphertext::new(&bytes).unwrap());

        let secret = secret_bytes(&secret);
        assert_eq!(secret_bytes(&decapsulated), secret);
        assert_eq!(secret_bytes(&again), secret);
        assert_ne!(secret_bytes(&rejected), secret);
        assert_ne!(secret_bytes(&altered), secret);
        assert_eq!(loaded.public_key().as_ref(), key.public_key().as_ref());
        assert_eq!(seed_bytes(&loaded), seed_bytes(&key));
    }

    // X-Wing's key pair and secrets agree with each other on random inputs.
    #[test]
    fn xwing_round_trips() {
        for _ in 0..8 {
            let key = DecapsulationKey::<XWing>::generate().unwrap();
            let ek = EncapsulationKey::<XWing>::new(key.public_key().as_ref()).unwrap();
            let (ciphertext, secret) = ek.encapsulate().unwrap();
            let ciphertext = Ciphertext::<XWing>::new(ciphertext.as_ref()).unwrap();
            assert_eq!(
                secret_bytes(&key.decapsulate(&ciphertext)),
                secret_bytes(&secret)
            );
            let again = DecapsulationKey::<XWing>::from_seed(key.to_seed().as_ref()).unwrap();
            assert_eq!(again.public_key().as_ref(), key.public_key().as_ref());
            assert_eq!(
                secret_bytes(&again.decapsulate(&ciphertext)),
                secret_bytes(&secret)
            );
        }
    }

    // Exporting our decapsulation key needs crate access, so this
    // differential test lives here rather than in `tests/crosschecks.rs`.
    #[cfg(not(any(miri, target_family = "wasm")))]
    // X-Wing against the two other Rust implementations of the draft that
    // carry its combiner: libcrux-kem and RustCrypto's x-wing (aws-lc-rs has
    // none). Both are fed our seeds and our `eseed`s, and what each makes of
    // them is compared byte for byte, in both directions.
    #[cfg(not(any(miri, target_family = "wasm")))]
    mod xwing_crosscheck {
        use libcrux_kem::Algorithm as LibcruxAlgorithm;
        use x_wing::{Decapsulate, Decapsulator, KeyExport, TryDecapsulate};

        use super::*;

        const ROUNDS: usize = 24;

        fn random_bytes<const N: usize>() -> [u8; N] {
            let mut bytes = [0; N];
            for chunk in bytes.chunks_mut(32) {
                let seed = DecapsulationKey::<XWing>::generate().unwrap().to_seed();
                chunk.copy_from_slice(&seed.as_ref()[..chunk.len()]);
            }
            low::ct::public_slice(&bytes);
            bytes
        }

        fn rustcrypto_ciphertext(bytes: &[u8]) -> x_wing::Ciphertext {
            bytes.try_into().unwrap()
        }

        // Keys, ciphertexts, and secrets from our seed and `eseed` equal
        // libcrux-kem's and x-wing's, and each decapsulates the others'.
        #[test]
        fn xwing_matches_libcrux_and_rustcrypto() {
            for _ in 0..ROUNDS {
                let seed = random_bytes::<32>();
                let eseed = random_bytes::<64>();

                let ours = DecapsulationKey::<XWing>::from_seed(&seed).unwrap();
                let (libcrux_sk, libcrux_pk) =
                    libcrux_kem::key_gen_derand(LibcruxAlgorithm::XWingKemDraft06, &seed).unwrap();
                let rustcrypto = x_wing::DecapsulationKey::from(seed);
                let rustcrypto_pk = rustcrypto.encapsulation_key();

                let pk = ours.public_key().as_ref().to_vec();
                assert_eq!(pk, libcrux_pk.encode());
                assert_eq!(pk, rustcrypto_pk.to_bytes().as_slice());
                assert_eq!(libcrux_sk.encode(), seed);
                assert_eq!(rustcrypto.as_bytes(), &seed);

                let (secret, ciphertext) = xwing_encaps(ours.public_key(), &eseed);
                let (libcrux_ss, libcrux_ct) = libcrux_pk.encapsulate_derand(&eseed).unwrap();
                let (rustcrypto_ct, rustcrypto_ss) =
                    rustcrypto_pk.encapsulate_deterministic(&(&eseed[..]).try_into().unwrap());
                assert_eq!(ciphertext.as_ref(), libcrux_ct.encode());
                assert_eq!(ciphertext.as_ref(), rustcrypto_ct.as_slice());
                assert_eq!(secret, libcrux_ss.encode());
                assert_eq!(secret, rustcrypto_ss.as_slice());

                let theirs =
                    libcrux_kem::Ct::decode(LibcruxAlgorithm::XWingKemDraft06, ciphertext.as_ref())
                        .unwrap();
                assert_eq!(theirs.decapsulate(&libcrux_sk).unwrap().encode(), secret);
                assert_eq!(
                    rustcrypto
                        .decapsulate(&rustcrypto_ciphertext(ciphertext.as_ref()))
                        .as_slice(),
                    secret
                );
                assert_eq!(decapsulate(&ours, ciphertext.as_ref()).unwrap(), secret);
            }
        }

        // The public API in both directions: what libcrux-kem and x-wing
        // encapsulate to our key we decapsulate, and what we encapsulate to
        // their keys they decapsulate.
        #[test]
        fn xwing_interoperates() {
            for _ in 0..ROUNDS {
                let ours = DecapsulationKey::<XWing>::generate().unwrap();
                let seed = seed_bytes(&ours);
                let pk = ours.public_key().as_ref().to_vec();

                // Theirs to ours.
                let libcrux_pk =
                    libcrux_kem::PublicKey::decode(LibcruxAlgorithm::XWingKemDraft06, &pk).unwrap();
                let (ss, ct) = libcrux_pk
                    .encapsulate_derand(&random_bytes::<64>())
                    .unwrap();
                assert_eq!(decapsulate(&ours, &ct.encode()).unwrap(), ss.encode());
                let rustcrypto_pk = x_wing::EncapsulationKey::try_from(&pk[..]).unwrap();
                let (ct, ss) =
                    rustcrypto_pk.encapsulate_deterministic(&random_bytes::<64>().into());
                assert_eq!(decapsulate(&ours, ct.as_slice()).unwrap(), ss.as_slice());

                // Ours to theirs.
                let (ciphertext, secret) = ours.public_key().encapsulate().unwrap();
                let secret = secret_bytes(&secret);
                let (libcrux_sk, _) =
                    libcrux_kem::key_gen_derand(LibcruxAlgorithm::XWingKemDraft06, &seed).unwrap();
                let theirs =
                    libcrux_kem::Ct::decode(LibcruxAlgorithm::XWingKemDraft06, ciphertext.as_ref())
                        .unwrap();
                assert_eq!(theirs.decapsulate(&libcrux_sk).unwrap().encode(), secret);
                let rustcrypto =
                    x_wing::DecapsulationKey::from(<[u8; 32]>::try_from(&seed[..]).unwrap());
                assert_eq!(
                    rustcrypto
                        .decapsulate(&rustcrypto_ciphertext(ciphertext.as_ref()))
                        .as_slice(),
                    secret
                );
            }
        }

        // A ciphertext with one byte altered in its ML-KEM or X25519 part
        // decapsulates to the same secret in all three: the implicit
        // rejection of FIPS 203 for the first, the changed X25519 point for
        // the second.
        #[test]
        fn xwing_matches_on_altered_ciphertexts() {
            for i in 0..ROUNDS {
                let ours = DecapsulationKey::<XWing>::generate().unwrap();
                let seed = seed_bytes(&ours);
                let (ciphertext, _) = ours.public_key().encapsulate().unwrap();
                let (libcrux_sk, _) =
                    libcrux_kem::key_gen_derand(LibcruxAlgorithm::XWingKemDraft06, &seed).unwrap();
                let rustcrypto =
                    x_wing::DecapsulationKey::from(<[u8; 32]>::try_from(&seed[..]).unwrap());

                let mut bytes = ciphertext.as_ref().to_vec();
                // Both ends of each part, and the middle of the first.
                let at = [0, 1, 500, 1087, 1088, 1100, 1118, 1119][i % 8];
                bytes[at] ^= 1 << (i % 8);

                let secret = decapsulate(&ours, &bytes).unwrap();
                let theirs =
                    libcrux_kem::Ct::decode(LibcruxAlgorithm::XWingKemDraft06, &bytes).unwrap();
                assert_eq!(
                    theirs.decapsulate(&libcrux_sk).unwrap().encode(),
                    secret,
                    "{at}"
                );
                assert_eq!(
                    rustcrypto
                        .decapsulate(&rustcrypto_ciphertext(&bytes))
                        .as_slice(),
                    secret,
                    "{at}"
                );
            }
        }

        // A key whose ML-KEM half fails the modulus check is refused by all
        // three; one with any X25519 half (here, zero) is taken by all three,
        // and encapsulating to it agrees with x-wing's.
        #[test]
        fn xwing_matches_on_malformed_keys() {
            let key = DecapsulationKey::<XWing>::generate().unwrap();
            let pk = key.public_key().as_ref().to_vec();

            let mut bad = pk.clone();
            bad[..2].copy_from_slice(&[0xff, 0x0f]);
            assert!(EncapsulationKey::<XWing>::new(&bad).is_err());
            assert!(
                libcrux_kem::PublicKey::decode(LibcruxAlgorithm::XWingKemDraft06, &bad).is_err()
            );
            assert!(x_wing::EncapsulationKey::try_from(&bad[..]).is_err());

            let mut zero = pk.clone();
            zero[1184..].fill(0);
            assert!(EncapsulationKey::<XWing>::new(&zero).is_ok());
            assert!(
                libcrux_kem::PublicKey::decode(LibcruxAlgorithm::XWingKemDraft06, &zero).is_ok()
            );
            assert!(x_wing::EncapsulationKey::try_from(&zero[..]).is_ok());
            // Encapsulating to it gives x-wing's ciphertext and secret, the
            // latter from the zero X25519 secret.
            let eseed = random_bytes::<64>();
            let (secret, ciphertext) =
                xwing_encaps(&EncapsulationKey::<XWing>::new(&zero).unwrap(), &eseed);
            let (theirs_ct, theirs_ss) = x_wing::EncapsulationKey::try_from(&zero[..])
                .unwrap()
                .encapsulate_deterministic(&eseed.into());
            assert_eq!(ciphertext.as_ref(), theirs_ct.as_slice());
            assert_eq!(secret, theirs_ss.as_slice());

            for len in [0, 1215, 1217] {
                let mut wrong = pk.clone();
                wrong.resize(len, 0);
                assert!(EncapsulationKey::<XWing>::new(&wrong).is_err());
                assert!(
                    libcrux_kem::PublicKey::decode(LibcruxAlgorithm::XWingKemDraft06, &wrong)
                        .is_err()
                );
                assert!(x_wing::EncapsulationKey::try_from(&wrong[..]).is_err());
            }
        }

        // The draft leaves a ciphertext whose X25519 share gives the zero
        // secret open. We follow its text as x-wing's plain key does: the
        // secret is derived with the zero. libcrux-kem and x-wing's
        // `RejectNonContrib` key refuse it instead.
        #[test]
        fn xwing_non_contributory_shares() {
            let ours = DecapsulationKey::<XWing>::generate().unwrap();
            let seed = seed_bytes(&ours);
            let (ciphertext, _) = ours.public_key().encapsulate().unwrap();
            let mut bytes = ciphertext.as_ref().to_vec();
            bytes[1088..].fill(0);

            let plain = x_wing::DecapsulationKey::from(<[u8; 32]>::try_from(&seed[..]).unwrap());
            assert_eq!(
                decapsulate(&ours, &bytes).unwrap(),
                plain.decapsulate(&rustcrypto_ciphertext(&bytes)).as_slice()
            );

            let strict = x_wing::DecapsulationKeyRejectNonContrib::from(
                <[u8; 32]>::try_from(&seed[..]).unwrap(),
            );
            assert!(
                strict
                    .try_decapsulate(&rustcrypto_ciphertext(&bytes))
                    .is_err()
            );
            let (libcrux_sk, _) =
                libcrux_kem::key_gen_derand(LibcruxAlgorithm::XWingKemDraft06, &seed).unwrap();
            let theirs =
                libcrux_kem::Ct::decode(LibcruxAlgorithm::XWingKemDraft06, &bytes).unwrap();
            assert!(theirs.decapsulate(&libcrux_sk).is_err());
        }
    }

    mod crosscheck {
        use aws_lc_rs::kem::{self, AlgorithmId, ML_KEM_512, ML_KEM_768, ML_KEM_1024};
        use proptest::prelude::*;
        use proptest::sample::Index;

        use super::*;

        fn algorithm<A: Params>() -> &'static kem::Algorithm<AlgorithmId> {
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
        fn encapsulated_by_theirs<A: Params>(
            alter: Option<(Index, u8)>,
        ) -> Result<(), TestCaseError> {
            let ours = DecapsulationKey::<A>::generate().unwrap();
            let theirs = kem::DecapsulationKey::new(
                algorithm::<A>(),
                low::ct::into_public(ours.key.as_bytes()).as_ref(),
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
