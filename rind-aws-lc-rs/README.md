<h1 align="center">rind-aws-lc-rs</h1>
<img width="40%" align="right" src="https://raw.githubusercontent.com/kixel-ai/rind/main/admin/logo.png">

[![Latest release](https://img.shields.io/crates/v/rind-aws-lc-rs)](https://crates.io/crates/rind-aws-lc-rs)
[![Documentation](https://img.shields.io/docsrs/rind-aws-lc-rs)](https://docs.rs/rind-aws-lc-rs/)

This crate offers [aws-lc-rs](https://github.com/aws/aws-lc-rs) 1.x's API, name for name, for every item [rind](https://github.com/kixel-ai/rind/) backs.
rind is a pure-Rust fork of [Graviola](https://github.com/ctz/graviola/), so this needs no C compiler, CMake, or NASM.
A crate on aws-lc-rs swaps it in by renaming its dependency, with no code changes:

```toml
[dependencies]
aws-lc-rs = { package = "rind-aws-lc-rs", version = "1" }
```

The rename reaches only the crate that makes it, not dependencies that use aws-lc-rs themselves.

It panics wherever aws-lc-rs panics, such as `pbkdf2::derive` asked for more than PBKDF2 allows, so its signatures stay aws-lc-rs's, as rind-ring's stay ring's.

Every aws-lc-rs feature is accepted. `ring-io` and `ring-sig-verify` gate the items they gate in aws-lc-rs, `fips` is described below, and the rest change nothing.

## FIPS

With the `fips` feature, `aead::TlsRecordSealingKey` and `aead::TlsRecordOpeningKey` hold their keys in [rind-fips](../rind-fips)'s FIPS 140-3 module: sealing through the module's TLS 1.3 IV construction, opening through its AES-GCM key. `try_fips_mode()` still fails, with a message naming the services that run in rind, until every service the module approves runs in it, as aws-lc-rs's FIPS build answers `Ok` only when its operations run in AWS-LC's module.
Without it, `try_fips_mode()` fails with "FIPS mode not enabled!" and every key runs in rind.

- The feature builds only for glibc Linux on little-endian x86_64 and aarch64, where rind-fips builds its module, and is a compile error elsewhere, as aws-lc-rs's FIPS build is off its supported platforms.
- The module seals only TLS 1.3 records, so `TlsRecordSealingKey::new` with `TlsProtocolId::TLS12` fails. Opening takes either version.
- Every other operation the module approves (digests, HMAC, HKDF, PBKDF2, the other AEAD keys, random bytes, key agreement, signatures, RSA, ML-KEM, ML-DSA) still runs in rind and is being moved into the module family by family; this list shrinks as each moves. X25519, ChaCha20-Poly1305, and the other algorithms the module leaves out stay callable, as in aws-lc-rs's FIPS build.
- `fips_version()` is `None`: the module has no AWS-LC module number to return. `try_fips_cpu_jitter_entropy()` fails, since the module takes OS entropy. `awslc_version` and `try_fips_self_test` are not offered; the module's self-test aborts instead of returning a `Result`.
- rind-fips is unpublished, so a rind-aws-lc-rs release cannot yet carry the feature.

## Wiping keys

Keys, and the adapter's own copies of secrets such as PKCS#8 documents, Ed25519 seeds, and ML-KEM shared secrets, are wiped on drop, as aws-lc-rs wipes them.

## What rind cannot back

These items are left out, so code using them fails to build:

- `signature::PqdsaPrivateKey::as_raw_bytes` and `encoding::PqdsaPrivateKeyRaw`: rind does not export an ML-DSA key's expanded form. `to_pkcs8v1` encodes its seed.
- `kem::DecapsulationKey::new`, `kem::DecapsulationKey::key_bytes`, and `kem::DecapsulationKeyBytes`: rind neither imports nor exports an ML-KEM private key.
- SHA-224 (`digest::SHA224*`, `hmac::HMAC_SHA224`, `signature::ECDSA_P521_SHA224_*`), ECDSA with SHA-1 or SHA-3 (`signature::ECDSA_*_SHA1_*`, `signature::ECDSA_*_SHA3_*`), and ECDSA on secp256k1 (`signature::ECDSA_P256K1_*`).
- AES-GCM-SIV (`aead::AES_*_GCM_SIV`); AES in ECB, CFB, or OFB mode (`cipher::*::ecb`, `cipher::*::ecb_pkcs7`, `cipher::*::cfb*`, `cipher::*::ofb`, `cipher::OperatingMode::ECB`, `cipher::OperatingMode::CFB*`, `cipher::OperatingMode::OFB`, `cipher::AES_CFB_IV_LEN`, `cipher::AES_OFB_IV_LEN`); ISO 10126 padding (`cipher::PaddedBlockDecryptingKey::cbc_iso10126`); DES under `legacy-des` (`cipher::DES_*`, `cipher::AlgorithmId::Des*`, `cipher::*Context::Iv64`); CMAC (`cmac`); the KBKDF and SSKDF key derivations (`kdf`); the TLS 1.2 PRF (`tls_prf`); and the streaming cipher contexts (`cipher::Streaming*`, `cipher::BufferUpdate`).
- `aead::chacha20_poly1305_openssh`: rind has no SSH consumer.
- `rsa::KeyPair::from_components`, `signature::RsaKeyPair::from_components`, and `rsa::KeyPairComponents`: building a key from its private components means encoding them as DER here, which branches on their secret leading bytes. Load the key as PKCS#1 or PKCS#8.
- `rsa::KeyPair::sign_digest`, `signature::RsaKeyPair::sign_digest`, `digest::Digest::import_less_safe`, and the PKCS#1 v1.5 encryption keys (`rsa::Pkcs1*`): rind signs only digests it computed, and refuses PKCS#1 v1.5 encryption, which invites padding-oracle attacks.
- `io::der`, `test`, `test_file`, `unstable`, `awslc_version`, `try_fips_self_test`, the FIPS-only functions it cannot back (see FIPS above), and the items aws-lc-rs's `dev-tests-only` feature exposes to supply a key or randomness (`agreement::*::generate_for_test`, `rand::unsealed`), since rind draws its own; under that feature rind-aws-lc-rs adds only `rand::SecureRandom::mut_fill`.

## Behaves differently

- Where aws-lc-rs takes a [`rand::SecureRandom`] to generate a key or sign, rind draws from the system random source itself, as [`rand::SystemRandom`], the only `SecureRandom`, does.
- A [`error::KeyRejected`] from rind's own checks gives rind's reason in its `Display`, and `"InvalidEncoding"` from `description_()`.
- `VerificationAlgorithm::verify_digest_sig` and `verify_digest` fail for RSA, as they do for Ed25519: rind verifies RSA only over a message it hashes itself.
- An Ed25519 public key of small order verifies no signature, and a PKCS#8 v2 Ed25519 key whose public key does not match is refused.
- ECDSA and ECDH public keys in the X9.62 hybrid form are refused.
- An RSA public key, from `rsa::PublicKey::from_der` or elsewhere, must have a modulus of 1024 to 8192 bits, the range rind verifies with.
- An RSA-OAEP private key is bound to one algorithm in rind, so a `rsa::PrivateDecryptingKey` loads the key again the first time it decrypts with each other algorithm, and keeps it.

## WebAssembly

It builds for `wasm32-wasip2` and `wasm32-unknown-unknown`, the browser, for
neither of which aws-lc-rs builds. In the browser, rind needs its JavaScript random source, `getrandom = { version = "0.4",
features = ["wasm_js"] }`. [PLATFORMS.md](https://github.com/kixel-ai/rind/blob/main/PLATFORMS.md) lists what each adapter's
upstream needs there too, and why rind's constant-time checks do not cover wasm.

License: Apache-2.0 OR ISC OR MIT-0
