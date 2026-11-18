# aws-lc-rs's tests

These are [aws-lc-rs](https://github.com/aws/aws-lc-rs) 1.19.0's own API tests
and their vectors, from tag `v1.19.0` (commit
`5d496f88b40f327e28315deecc1a5a1fd1e81e95`), run against rind-aws-lc-rs renamed
to `aws_lc_rs`. They keep aws-lc-rs's licenses: see `LICENSE` and each file's
header. They are excluded from the published crate.

The files directly here are aws-lc-rs's `tests/`. Under `unit/` are the
`#[cfg(test)]` tests aws-lc-rs keeps beside its code in `src/`, each at its
path there, with a file holding only module declarations where aws-lc-rs's
holds no tests; `data/agreement_tests.txt` is its `src/agreement/data/`
file.

`test.rs` is aws-lc-rs's `src/test.rs` test harness, with its `src/hex.rs`
inlined, without its fixed random sources, and with its failure logging always
on; rind-aws-lc-rs offers none of them. The SHA-1, SHA-2, and SHA-3 SHAVS
vectors aws-lc-rs keeps in `third_party/NIST` are rind's copies of the same
files, under `thirdparty/`, read when the test runs since the published crate
leaves them out.

## What is left out

Tests of what rind-aws-lc-rs does not offer, which its
[README](../../README.md#what-rind-cannot-back) lists under "What rind cannot back", are removed,
or skip those cases where a test covers more:

- `basic_openssh_test.rs`, `src/aead/chacha20_poly1305_openssh.rs`, and the
  OpenSSH ChaCha20-Poly1305 AEAD test.
- `cmac_tests.rs` and `src/cmac.rs` (CMAC), `kdf_test.rs` and `src/kdf.rs`
  (KBKDF and SSKDF), and `src/tls_prf.rs` (the TLS 1.2 PRF).
- ML-DSA's `PqdsaPrivateKey::as_raw_bytes`, and the tests that need it:
  `test_mldsa_seed_functional_equivalence`, and `src/pqdsa/key_pair.rs`'s
  `test_private_key_serialization`, `test_from_seed_raw_private_key_roundtrip`,
  `test_from_seed_pkcs8_is_seed_form`, and `test_expanded_key_pkcs8_unavailable`.
- `unsealed_rand_test.rs`, which needs the `dev-tests-only` feature's
  `rand::unsealed`.
- AES-GCM-SIV; AES in ECB, CFB, and OFB modes; ISO 10126 padding; DES
  (`legacy-des`); and the streaming cipher contexts (`src/cipher/streaming.rs`).
- SHA-224, Keccak-256 (`unstable`), ECDSA with SHA-1, SHA-224, or SHA-3, and
  ECDSA on secp256k1.
- `RsaKeyPair::sign_digest`, `Digest::import_less_safe`,
  `rsa::KeyPair::from_components` and `KeyPairComponents`, and PKCS#1 v1.5
  encryption.
- ML-KEM-512 and ML-KEM-1024, and `kem::DecapsulationKey::new` and
  `key_bytes`, which every test in `src/kem.rs` but `ciphertext` and
  `test_kem_wrong_sizes` needs.
- `awslc_version` and `try_fips_self_test`, and everything under the `fips`
  feature.

Tests of aws-lc-rs's private code, which no public item reaches the same way,
are left out too:

- The tests in `src/buffer.rs`, `src/cbb.rs`, `src/endian.rs`,
  `src/evp_pkey.rs`, `src/pqdsa.rs`, `src/ptr.rs`, `src/io/der.rs`,
  `src/aead/poly1305.rs`, `src/cipher/aes.rs`, `src/cipher/block.rs`,
  `src/cipher/chacha.rs`, and `src/cipher/key.rs`, and those of the harness
  itself in `src/test.rs`.
- `src/digest.rs`'s `max_input` tests, which build a `Context` from its
  private fields; `src/hmac.rs`'s `hmac_internal_sign_too_small_buffer`;
  `src/lib.rs`'s `test_dump`; `src/kem.rs`'s `shared_secret`; and
  `src/agreement/parsed_public_key_tests.rs`'s
  `test_parsed_public_key_invalid_nid`.

## What changed

Changes to what a test checks are marked `rind-aws-lc-rs:` where they are made.
Each follows from a difference the README lists under
["Behaves differently"](../../README.md#behaves-differently), or reaches a
private item through the public one that calls it or holds the same value:

- A comparison of `KeyRejected`'s text only checks that the key is refused,
  since a `KeyRejected` from rind's own checks gives rind's reason.
- RSA `verify_digest` is expected to fail.
- An RSA key outside an algorithm's modulus range is expected to be refused
  when it is parsed for that algorithm, not when verifying.
- A known ECDH private key is loaded with `PrivateKey::from_private_key`, and
  agrees with `agree`, rather than coming from a fixed random source through
  `generate_for_test`.
- A private constructor or field is replaced with its public counterpart, such
  as `UnboundKey::seal_combined` with `LessSafeKey::seal_in_place_append_tag`,
  `EncryptingKey::new` with `EncryptingKey::cbc` or `ctr`,
  `ParsedPublicKey::new` with `ParsedPublicKey::try_from`, or a private
  constant with its value.

Otherwise, imports name this harness, the modules are gathered under
`main.rs`, `std::sync::LazyLock` stands in for the `lazy_static` crate, string
checks stand in for the `regex` crate, test names are spelled out where the
`paste` crate built them, one `assert_eq!` against an empty slice is typed,
`cargo fmt` and `cargo clippy --fix` reformatted the code, and `main.rs` and
`unit/error.rs` allow the lints clippy cannot fix.

## Updating

On an aws-lc-rs release, copy its `aws-lc-rs/tests/*.rs`, `src/test.rs`, and
`src/hex.rs`, the test modules of its `src/` files to `unit/`, and the
`tests/data/` and `src/agreement/data/` files the tests name, from the
release's tag. Re-apply the changes above, triaging each new failure as a
divergence to fix in rind-aws-lc-rs or a difference its README records, and
update the version above and the `aws-lc-rs` dev-dependency together.
