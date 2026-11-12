# [M] An SP 800-90A DRBG seeded from the OS

## Goal

rind's FIPS module draws every random value from an SP 800-90A DRBG, seeded
and reseeded with entropy the OS supplies from outside the boundary, with the
CAST and health tests SP 800-90A section 11.3 requires.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- Extend rind's HMAC_DRBG (`rind/src/high/hmac_drbg.rs`, today only ECDSA's
  nonces) with reseeding, additional input, and a reseed counter, rather
  than add a CTR_DRBG: it already exists and passes CAVP's vectors, and the
  module draws little randomness (keys, nonces, IVs), so AES-CTR's bulk speed
  buys nothing. HMAC-SHA2-512 gives 256-bit strength; ACVP's `hmacDRBG` sets
  test it.
- Entropy is loaded from `getrandom` by the wrapper crate, outside the
  boundary: IG 9.3.A scenario 2(b), with the caveat aws-lc 3's certificate
  carries. A failed read is an error, never a fallback.
- One DRBG per thread, seeded from a process-wide one, as aws-lc's tree-DRBG
  does, so threads never contend; its state is zeroized at exit.
- Lives in the module's source only: `rind` keeps calling `getrandom`
  directly, which is faster and needs no DRBG.

