//! Constant-time checks for the secret paths this crate adds over rind, run
//! under valgrind by `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. `Generate` draws its seed into a
//! stack buffer rind loads the key from, and `Encapsulate` its 32 random
//! bytes into rind's `kem::Message`, which zeroes them: both are new paths,
//! checked here.

use core::convert::Infallible;

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use kem::common::rand_core::{TryCryptoRng, TryRng};
use kem::{Decapsulate, Decapsulator, Encapsulate, Generate, Kem, KeyExport};

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

/// A random source whose every byte it hands out is marked secret.
struct SecretRng(u8);

impl TryRng for SecretRng {
    type Error = Infallible;

    fn try_next_u32(&mut self) -> Result<u32, Infallible> {
        let mut b = [0; 4];
        self.try_fill_bytes(&mut b)?;
        Ok(u32::from_le_bytes(b))
    }

    fn try_next_u64(&mut self) -> Result<u64, Infallible> {
        let mut b = [0; 8];
        self.try_fill_bytes(&mut b)?;
        Ok(u64::from_le_bytes(b))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Infallible> {
        for byte in dst.iter_mut() {
            self.0 = self.0.wrapping_mul(29).wrapping_add(11);
            *byte = self.0;
        }
        secret(dst);
        Ok(())
    }
}

impl TryCryptoRng for SecretRng {}

fn generate_and_encapsulate<K: Kem>()
where
    K::DecapsulationKey: KeyExport + Decapsulate,
{
    let dk = K::DecapsulationKey::generate_from_rng(&mut SecretRng(3));
    // The encapsulation key is public by design.
    let ek = dk.encapsulation_key().to_bytes();
    public(ek.as_slice());
    let (c, k) = dk
        .encapsulation_key()
        .encapsulate_with_rng(&mut SecretRng(9));
    // The ciphertext is public by design; the secret is declassified only to
    // compare it.
    public(c.as_slice());
    let decapsulated = dk.decapsulate(&c);
    public(decapsulated.as_slice());
    public(k.as_slice());
    assert_eq!(decapsulated.as_slice(), k.as_slice());
}

#[test]
fn kem_keys() {
    generate_and_encapsulate::<rind_kem::MlKem512>();
    generate_and_encapsulate::<rind_kem::MlKem768>();
    generate_and_encapsulate::<rind_kem::MlKem1024>();
}
