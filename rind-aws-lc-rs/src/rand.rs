//! Random bytes from the system's secure random source.
//!
//! [`SystemRandom`] is the only [`SecureRandom`], as in aws-lc-rs. Calls that
//! take one to generate a key or sign draw from the same source inside rind.

use crate::error;

/// A secure source of random bytes; only [`SystemRandom`] is one.
pub trait SecureRandom: sealed::SecureRandom {
    /// Fills `dest` with random bytes.
    fn fill(&self, dest: &mut [u8]) -> Result<(), error::Unspecified>;

    /// Fills `dest` with random bytes, as [`Self::fill`] does.
    #[cfg(feature = "dev-tests-only")]
    fn mut_fill(&mut self, dest: &mut [u8]) -> Result<(), error::Unspecified>;
}

impl<T: sealed::SecureRandom> SecureRandom for T {
    fn fill(&self, dest: &mut [u8]) -> Result<(), error::Unspecified> {
        self.fill_impl(dest)
    }

    #[cfg(feature = "dev-tests-only")]
    fn mut_fill(&mut self, dest: &mut [u8]) -> Result<(), error::Unspecified> {
        self.fill_impl(dest)
    }
}

/// A type [`generate`] can fill with random bytes: a byte array.
pub trait RandomlyConstructable: sealed::RandomlyConstructable {}

impl<T: sealed::RandomlyConstructable> RandomlyConstructable for T {}

/// A randomly generated value, taken out with [`Random::expose`].
pub struct Random<T: RandomlyConstructable>(T);

impl<T: RandomlyConstructable> Random<T> {
    /// Returns the random value.
    pub fn expose(self) -> T {
        self.0
    }
}

/// Generates a random `T` from `rng`.
pub fn generate<T: RandomlyConstructable>(
    rng: &dyn SecureRandom,
) -> Result<Random<T>, error::Unspecified> {
    let mut value = T::zero();
    rng.fill(value.as_mut_bytes())?;
    Ok(Random(value))
}

/// The operating system's secure random source.
#[derive(Clone, Debug, Default)]
pub struct SystemRandom(());

impl SystemRandom {
    /// Returns the system random source.
    pub fn new() -> Self {
        Self(())
    }
}

impl sealed::SecureRandom for SystemRandom {
    fn fill_impl(&self, dest: &mut [u8]) -> Result<(), error::Unspecified> {
        fill(dest)
    }
}

/// Fills `dest` with random bytes from the system random source.
pub fn fill(dest: &mut [u8]) -> Result<(), error::Unspecified> {
    rind::rand::fill(dest).map_err(error::unspecified)
}

mod sealed {
    use crate::error;

    pub trait SecureRandom: core::fmt::Debug {
        fn fill_impl(&self, dest: &mut [u8]) -> Result<(), error::Unspecified>;
    }

    pub trait RandomlyConstructable: Sized {
        fn zero() -> Self;
        fn as_mut_bytes(&mut self) -> &mut [u8];
    }

    impl<const N: usize> RandomlyConstructable for [u8; N] {
        fn zero() -> Self {
            [0; N]
        }

        fn as_mut_bytes(&mut self) -> &mut [u8] {
            &mut self[..]
        }
    }
}
