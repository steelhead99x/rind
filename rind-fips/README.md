# rind-fips

rind's approved algorithms from a FIPS 140-3 Level 1 cryptographic module.

The module is a shared library, `librind_fips_module.so`, which this
crate's build script builds from rind's source with pinned flags and links.
Its API is rind's, less what FIPS 140-3 does not approve, so code that uses
only approved algorithms switches with `use rind_fips as rind`.

The module has no certificate: it is built to pass validation, ready for a
lab to test.

## What the module does

- **Integrity.** As it loads, it runs the HMAC-SHA-256 and SHA-256
  self-tests, then compares an HMAC-SHA-256 over its code, constants, and
  relocated data with the value the build wrote into it.
- **Self-tests.** Each algorithm's known-answer test runs before its first
  use, and a pairwise consistency test follows every key pair generation.
  [`self_test`] runs them all on demand.
- **Error state.** A failed test prints its name and aborts the process.
- **Approved services only.** A successful call is the service indicator:
  what is not approved, such as X25519, ChaCha20-Poly1305, SHA-1 hashing,
  or a PBKDF2 salt under 16 bytes, is absent or refused.
- **Zeroization.** Keys live only behind the module's handles and never
  move. Every service that handles a secret zeroes the stack it used, and
  the module's allocator zeroes every block it frees. So a thread calling
  the module needs up to 160 KiB of stack free beyond its own: what RSA,
  ML-DSA, and the self-tests reach, which Rust's 2 MiB default and glibc's
  8 MiB leave room for.
- **Random.** Every random value comes from an SP 800-90A HMAC_DRBG seeded
  from the OS, outside the module's boundary: one per thread, which wipes
  itself as its thread exits, and as the process exits, the module wipes
  those of threads still running. A forked child wipes its copies of the
  DRBGs of its parent's other threads, which it does not run.

## Running

A program that depends on `rind-fips` links `librind_fips_module.so`
dynamically. `cargo run` and `cargo test` find it in the build's output;
a program deployed elsewhere needs the library on its loader's path, such
as beside it with an `$ORIGIN` run path.

The module builds only for glibc Linux on x86_64 and aarch64, its tested
environments' kind. On x86_64 it requires AES-NI, PCLMULQDQ, and the AVX2
generation's integer instructions (BMI1, BMI2, ADX, MOVBE), and on aarch64
the crypto extension; it refuses to load without them, naming the first
missing. `RIND_CPU_DISABLE_<feature>` masks a feature at load, which is how
each CPU path is reached for its ACVP run.

## What it does not offer

These are in `rind` but not here, since FIPS 140-3 does not approve them:

- X25519, ChaCha20-Poly1305, XChaCha20-Poly1305, and ChaCha20
- MD5 and SHA-1 hashing; SHA-1 remains for HMAC, HKDF, PBKDF2, and
  verifying legacy signatures
- HPKE, RSA-OAEP, RSA blind signatures, and ECVRF
- RSA-PSS verification of any salt length (`RSA_PSS_*_ANY_SALT`)
- AES-GCM sealing with a caller's nonce. Sealing is
  `aead::RandomizedNonceKey`, a random 96-bit IV from the module DRBG, and
  `aead::TlsRecordSealingKey`, TLS 1.3 with the module's sequence counter.
  TLS 1.2's explicit nonce is not offered
