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

Every aws-lc-rs feature but `fips` is accepted. `ring-io` and `ring-sig-verify` gate the items they gate in aws-lc-rs, and the rest change nothing.
`fips` is refused, since rind is not FIPS validated: `try_fips_mode()` always fails and `fips_version()` is `None`.

## Wiping keys

Keys, and the adapter's own copies of secrets such as PKCS#8 documents, Ed25519 seeds, and ML-KEM shared secrets, are wiped on drop only under the `wipe` feature, which aws-lc-rs lacks since it always wipes.
It turns on rind's own `wipe` feature too. Leaving it off skips the wipe, which is faster.
It is the one item this crate adds to aws-lc-rs's API.

## Not offered

These items are left out, so code using them fails to build:

- ML-KEM-512 and ML-KEM-1024 (`kem::ML_KEM_512`, `kem::ML_KEM_1024`): rind has only ML-KEM-768 so far.
  rustls's `aws_lc_rs` provider does not build on this crate yet: it names `tls_prf`, and rustls 0.23.46 also names `kem::ML_KEM_1024`.
  rustls-webpki's `aws-lc-rs` feature and rcgen's `aws_lc_rs` feature do build.
- `signature::PqdsaPrivateKey::as_raw_bytes` and `encoding::PqdsaPrivateKeyRaw`: rind does not export an expanded ML-DSA private key. `PqdsaKeyPair::from_raw_private_key` still loads one.
- `kem::DecapsulationKey::new` and `key_bytes`: rind neither imports nor exports an ML-KEM private key.
- SHA-224 (`digest::SHA224`, `hmac::HMAC_SHA224`, and the ECDSA algorithms with it), ECDSA with SHA-1 or SHA-3, and ECDSA on secp256k1 (`ECDSA_P256K1_*`).
- AES-GCM-SIV, AES in ECB, CFB, or OFB mode, ISO 10126 padding, DES (`legacy-des`), CMAC (`cmac`), the KBKDF and SSKDF key derivations (`kdf`), the TLS 1.2 PRF (`tls_prf`), and the streaming cipher contexts (`cipher::StreamingEncryptingKey` and the others).
- `aead::chacha20_poly1305_openssh`: rind has no SSH consumer.
- `rsa::KeyPair::from_components` and `rsa::KeyPairComponents`: building a key from its private components means encoding them as DER here, which branches on their secret leading bytes. Load the key as PKCS#1 or PKCS#8.
- `rsa::KeyPair::sign_digest`, `digest::Digest::import_less_safe`, and the PKCS#1 v1.5 encryption keys (`rsa::Pkcs1PublicEncryptingKey`, `rsa::Pkcs1PrivateDecryptingKey`): rind signs only digests it computed, and refuses PKCS#1 v1.5 encryption, which invites padding-oracle attacks.
- `io::der`, `test`, `awslc_version`, `try_fips_self_test`, the FIPS-only functions, and `rand::unsealed`, which aws-lc-rs's `dev-tests-only` feature exposes; rind-aws-lc-rs accepts that feature but adds nothing for it.
- `unstable`: the deprecated aliases (`unstable::signature::ML_DSA_*`, `MLDSA_*`, and the `Pqdsa*` names that module re-exports) are left out. The feature does enable `PqdsaKeyPair::to_pkcs8`, the deprecated alias of `to_pkcs8v1`.

## Behaves differently

- Where aws-lc-rs takes a [`rand::SecureRandom`] to generate a key or sign, rind draws from the system random source itself, as [`rand::SystemRandom`], the only `SecureRandom`, does.
- A [`error::KeyRejected`] from rind's own checks gives rind's reason in its `Display`, and `"InvalidEncoding"` from `description_()`.
- `VerificationAlgorithm::verify_digest_sig` and `verify_digest` fail for RSA, as they do for Ed25519 and ML-DSA: rind verifies RSA only over a message it hashes itself, and pure ML-DSA has no digest verification.
- An Ed25519 public key of small order verifies no signature, and a PKCS#8 v2 Ed25519 key whose public key does not match, or is missing, is refused. An ML-DSA key whose public key does not match is refused.
- An ML-DSA `SubjectPublicKeyInfo` followed by more bytes is refused.
- An ML-DSA PKCS#8 document followed by more bytes is refused.
- An `id-ecPublicKey` PKCS#8 key on secp224r1, secp256k1, or a Brainpool curve is `InvalidEncoding` when loaded as ML-DSA. aws-lc-rs parses that key and reports `WrongAlgorithm`.
- A DSA PKCS#8 key is `InvalidEncoding` when loaded as ML-DSA. aws-lc-rs parses one whose parameters and private key are in range and reports `WrongAlgorithm`.
- An RSASSA-PSS PKCS#8 key whose parameters name a hash or a mask generation function is `InvalidEncoding` when loaded as ML-DSA. aws-lc-rs parses it and reports `WrongAlgorithm`.
- ECDSA and ECDH public keys in the X9.62 hybrid form are refused.
- An RSA public key, from `rsa::PublicKey::from_der` or elsewhere, must have a modulus of 1024 to 8192 bits, the range rind verifies with.
- An RSA-OAEP private key is bound to one algorithm in rind, so a `rsa::PrivateDecryptingKey` loads the key again the first time it decrypts with each other algorithm, and keeps it.

License: Apache-2.0 OR ISC OR MIT-0
