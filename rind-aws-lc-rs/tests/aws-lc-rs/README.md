# aws-lc-rs's tests

These are [aws-lc-rs](https://github.com/aws/aws-lc-rs) 1.19.0's own API tests
and their vectors, from tag `v1.19.0` (commit
`5d496f88b40f327e28315deecc1a5a1fd1e81e95`), run against rind-aws-lc-rs renamed
to `aws_lc_rs`. They keep aws-lc-rs's licenses: see `LICENSE` and each file's
header. They are excluded from the published crate.

`test.rs` is aws-lc-rs's `src/test.rs` test harness, with its `src/hex.rs`
inlined, without its fixed random sources, and with its failure logging always
on; rind-aws-lc-rs offers none of them. The SHA-1, SHA-2, and SHA-3 SHAVS
vectors aws-lc-rs keeps in `third_party/NIST` are rind's copies of the same
files, under `thirdparty/`, read when the test runs since `thirdparty/cavp` is a
submodule a build need not check out.

## What is left out

Tests of what rind-aws-lc-rs does not offer, which its
[README](../../README.md#not-offered) lists under "Not offered", are removed,
or skip those cases where a test covers more:

- `basic_openssh_test.rs` and the OpenSSH ChaCha20-Poly1305 AEAD test.
- `cmac_tests.rs` (CMAC) and `kdf_test.rs` (KBKDF and SSKDF).
- `pqdsa_test.rs` (ML-DSA).
- `unsealed_rand_test.rs`, which needs the `dev-tests-only` feature's
  `rand::unsealed`.
- AES-GCM-SIV; AES in ECB, CFB, and OFB modes; DES (`legacy-des`); and the
  streaming cipher contexts.
- SHA-224, Keccak-256 (`unstable`), ECDSA with SHA-1, SHA-224, or SHA-3, and
  ECDSA on secp256k1.
- `RsaKeyPair::sign_digest`, `Digest::import_less_safe`,
  `rsa::KeyPair::from_components` and `KeyPairComponents`, and PKCS#1 v1.5
  encryption.
- Everything under the `fips` feature.

## What changed

Changes to what a test checks are marked `rind-aws-lc-rs:` where they are made.
Each follows from a difference the README lists under
["Behaves differently"](../../README.md#behaves-differently):

- A comparison of `KeyRejected`'s text only checks that the key is refused,
  since a `KeyRejected` from rind's own checks gives rind's reason.
- RSA `verify_digest` is expected to fail.
- An RSA key outside an algorithm's modulus range is expected to be refused
  when it is parsed for that algorithm, not when verifying.
- A PKCS#8 v2 Ed25519 key without its public key is expected to be refused.

Otherwise, imports name this harness, the modules are gathered under
`main.rs`, `std::sync::LazyLock` stands in for the `lazy_static` crate, one
`assert_eq!` against an empty slice is typed, `cargo fmt` and `cargo clippy
--fix` reformatted the code, and `main.rs` allows the one lint clippy cannot
fix.

## Updating

On an aws-lc-rs release, copy its `aws-lc-rs/tests/*.rs`, `src/test.rs`, and
`src/hex.rs`, and the `tests/data/` files the tests name, from the release's
tag. Re-apply the changes above, triaging each new failure as a divergence to
fix in rind-aws-lc-rs or a difference its README records, and update the
version above and the `aws-lc-rs` dev-dependency together.
