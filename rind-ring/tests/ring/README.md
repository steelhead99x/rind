# ring's tests

These are [ring](https://github.com/briansmith/ring) 0.17.14's own API tests
and their vectors, from commit `2723abbca9e83347d82b056d5b239c6604f786df`,
run against rind-ring renamed to `ring`. They keep ring's licenses: see
`LICENSE`. They are excluded from the published crate.

`test.rs` is ring's `src/testutil.rs` test harness, without its fixed
random sources and with its failure logging always on, which rind-ring
does not offer. `ecdsa_sign_*_tests.txt` and
`signature_rsa_example_private_key.der` come from ring's `src/`.

Changes to what a test checks are marked `rind-ring:` where they are made:

- A comparison of `KeyRejected`'s text only checks that the key is refused:
  ring documents the text as changing between releases, and rind-ring gives
  rind's reason.
- Known answers that need ring's fixed random sources, which rind-ring
  cannot honor since rind draws its own randomness, become checks that do
  not: Ed25519 loads the seed instead of generating from it, ECDH checks
  only that a valid peer key is accepted, and RSA-PSS signs with a random
  salt and verifies.

Otherwise, imports name this harness, paths to the moved files are local,
the `std`-only error test always runs, `cargo fmt` reordered the imports,
and clippy's lints on ring's code are allowed in `main.rs`. The iterated
X25519 test, which needs fixed private keys, and the OpenSSH
ChaCha20-Poly1305 test are removed.
