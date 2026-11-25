#![doc = include_str!("../README.md")]
#![no_std]
#![forbid(unsafe_code)]

/// [`rind::rand::fill`] as a `rand_core` RNG, for crates generic over one.
///
/// It fails as `fill` does, so it is a `TryCryptoRng`; wrap it in
/// `rand_core::UnwrapErr` where a crate takes an infallible `CryptoRng`.
#[derive(Debug, Default, Clone, Copy)]
pub struct SystemRandom;

impl rand_core::TryRng for SystemRandom {
    type Error = rind::Error;

    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        let mut out = [0u8; 4];
        rind::rand::fill(&mut out)?;
        Ok(u32::from_le_bytes(out))
    }

    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        let mut out = [0u8; 8];
        rind::rand::fill(&mut out)?;
        Ok(u64::from_le_bytes(out))
    }

    fn try_fill_bytes(&mut self, dst: &mut [u8]) -> Result<(), Self::Error> {
        rind::rand::fill(dst)
    }
}

impl rand_core::TryCryptoRng for SystemRandom {}
