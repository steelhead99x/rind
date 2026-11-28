//! Every ML-KEM set here against RustCrypto's `ml-kem`: the same keys from a
//! seed, the same ciphertext and secret from the same randomness, each
//! decapsulating the other's ciphertext, the same implicit-rejection secret
//! for an altered ciphertext, and both refusing a ciphertext of the wrong
//! length and an encapsulation key that fails FIPS 203's modulus check.

use core::convert::Infallible;

use kem::common::rand_core::{TryCryptoRng, TryRng};
use kem::{
    Decapsulate, Decapsulator, Encapsulate, Generate, Kem, KeyExport, KeyInit, TryDecapsulate,
    TryKeyInit,
};

/// A deterministic random source, so both crates draw the same bytes.
#[derive(Clone)]
struct Xorshift(u64);

impl TryRng for Xorshift {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        Ok(self.try_next_u64()? as u32)
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        Ok(self.0)
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        for byte in dst {
            *byte = (self.try_next_u64()? >> 24) as u8;
        }
        Ok(())
    }
}

impl TryCryptoRng for Xorshift {}

fn compare<Ours, Theirs>(seed: u64)
where
    Ours: Kem,
    Theirs: Kem,
    Ours::DecapsulationKey: KeyInit + KeyExport + Decapsulate,
    Theirs::DecapsulationKey: KeyInit + KeyExport + Decapsulate,
{
    let mut rng = Xorshift(seed);
    for round in 0..8 {
        // The same keys from one seed, and the seed back.
        let mut key_seed = [0u8; 64];
        rng.try_fill_bytes(&mut key_seed).unwrap();
        let ours = Ours::DecapsulationKey::new_from_slice(&key_seed).unwrap();
        let theirs = Theirs::DecapsulationKey::new_from_slice(&key_seed).unwrap();
        assert_eq!(ours.to_bytes().as_slice(), key_seed, "round {round}");
        let ek = ours.encapsulation_key().to_bytes();
        assert_eq!(
            ek.as_slice(),
            theirs.encapsulation_key().to_bytes().as_slice()
        );

        // The same ciphertext and secret from the same 32 random bytes.
        let (ours_c, ours_k) = ours
            .encapsulation_key()
            .encapsulate_with_rng(&mut rng.clone());
        let (theirs_c, theirs_k) = theirs
            .encapsulation_key()
            .encapsulate_with_rng(&mut rng.clone());
        assert_eq!(ours_c.as_slice(), theirs_c.as_slice());
        assert_eq!(ours_k.as_slice(), theirs_k.as_slice());
        rng.try_fill_bytes(&mut [0; 32]).unwrap();

        // Each decapsulates the other's ciphertext.
        let (c, k) = ours.encapsulation_key().encapsulate_with_rng(&mut rng);
        let c_theirs = c.as_slice().try_into().unwrap();
        assert_eq!(theirs.decapsulate(&c_theirs).as_slice(), k.as_slice());
        let (c, k) = theirs.encapsulation_key().encapsulate_with_rng(&mut rng);
        let c_ours = c.as_slice().try_into().unwrap();
        assert_eq!(ours.decapsulate(&c_ours).as_slice(), k.as_slice());

        // An altered ciphertext of the right length is not refused: both
        // give FIPS 203's implicit-rejection secret, which differs from the
        // real one.
        let mut altered = c.as_slice().to_vec();
        let at = round * 37 % altered.len();
        altered[at] ^= 1 << (round % 8);
        let ours_rejected = ours.decapsulate(&altered.as_slice().try_into().unwrap());
        let theirs_rejected = theirs.decapsulate(&altered.as_slice().try_into().unwrap());
        assert_eq!(ours_rejected.as_slice(), theirs_rejected.as_slice());
        assert_ne!(ours_rejected.as_slice(), k.as_slice());

        // Only a ciphertext of the wrong length is an error, for both.
        for len in [0, c.len() - 1, c.len() + 1] {
            let bytes = vec![0u8; len];
            assert!(ours.decapsulate_slice(&bytes).is_err(), "{len}");
            assert!(theirs.decapsulate_slice(&bytes).is_err(), "{len}");
        }
    }
}

/// An encapsulation key whose first coefficient is `q` or more fails FIPS
/// 203's modulus check, in both crates; the key it came from loads in both.
fn refuse_malformed_key<Ours, Theirs>()
where
    Ours: Kem,
    Theirs: Kem,
    Ours::DecapsulationKey: KeyInit,
{
    let dk = Ours::DecapsulationKey::new_from_slice(&[7; 64]).unwrap();
    let good = dk.encapsulation_key().to_bytes();
    assert!(Ours::EncapsulationKey::new_from_slice(good.as_slice()).is_ok());
    assert!(Theirs::EncapsulationKey::new_from_slice(good.as_slice()).is_ok());
    let mut bad = good.as_slice().to_vec();
    // The first 12-bit coefficient is 0xfff, above q = 3329.
    bad[0] = 0xff;
    bad[1] |= 0x0f;
    assert!(Ours::EncapsulationKey::new_from_slice(&bad).is_err());
    assert!(Theirs::EncapsulationKey::new_from_slice(&bad).is_err());
    // And the wrong length.
    assert!(Ours::EncapsulationKey::new_from_slice(&good.as_slice()[1..]).is_err());
}

/// Generating takes the 64-byte seed from the random source, as `ml-kem`'s
/// does, and gives the key that seed makes.
fn generate_draws_the_seed<Ours: Kem>()
where
    Ours::DecapsulationKey: KeyInit + KeyExport,
{
    let rng = Xorshift(99);
    let mut seed = [0u8; 64];
    rng.clone().try_fill_bytes(&mut seed).unwrap();
    let generated = Ours::DecapsulationKey::generate_from_rng(&mut rng.clone());
    assert_eq!(generated.to_bytes().as_slice(), seed);
    assert_eq!(
        generated.encapsulation_key().to_bytes().as_slice(),
        Ours::DecapsulationKey::new_from_slice(&seed)
            .unwrap()
            .encapsulation_key()
            .to_bytes()
            .as_slice()
    );
}

/// Code generic over `Kem` runs on rind's types.
fn generic_roundtrip<K: Kem>() {
    let mut rng = Xorshift(5);
    let (dk, ek) = K::generate_keypair_from_rng(&mut rng);
    let (c, k) = ek.encapsulate_with_rng(&mut rng);
    assert_eq!(dk.try_decapsulate(&c).unwrap().as_slice(), k.as_slice());
    assert!(dk.encapsulation_key() == &ek);
    // The system's random source, through kem's `getrandom` feature.
    let (c, k) = ek.encapsulate();
    assert_eq!(dk.try_decapsulate(&c).unwrap().as_slice(), k.as_slice());
}

#[test]
fn ml_kem_512() {
    compare::<rind_kem::MlKem512, ml_kem::MlKem512>(1);
    refuse_malformed_key::<rind_kem::MlKem512, ml_kem::MlKem512>();
    generate_draws_the_seed::<rind_kem::MlKem512>();
    generic_roundtrip::<rind_kem::MlKem512>();
}

#[test]
fn ml_kem_768() {
    compare::<rind_kem::MlKem768, ml_kem::MlKem768>(2);
    refuse_malformed_key::<rind_kem::MlKem768, ml_kem::MlKem768>();
    generate_draws_the_seed::<rind_kem::MlKem768>();
    generic_roundtrip::<rind_kem::MlKem768>();
}

#[test]
fn ml_kem_1024() {
    compare::<rind_kem::MlKem1024, ml_kem::MlKem1024>(3);
    refuse_malformed_key::<rind_kem::MlKem1024, ml_kem::MlKem1024>();
    generate_draws_the_seed::<rind_kem::MlKem1024>();
    generic_roundtrip::<rind_kem::MlKem1024>();
}

/// The aliases name the same types `ml-kem`'s modules do.
#[test]
fn aliases() {
    let dk = rind_kem::ml_kem_768::DecapsulationKey::new_from_slice(&[1; 64]).unwrap();
    let ek: &rind_kem::ml_kem_768::EncapsulationKey = dk.encapsulation_key();
    let (c, _): (rind_kem::ml_kem_768::Ciphertext, _) = ek.encapsulate_with_rng(&mut Xorshift(8));
    assert_eq!(c.len(), 1088);
    assert!(format!("{dk:?}").starts_with("DecapsulationKey"));
}
