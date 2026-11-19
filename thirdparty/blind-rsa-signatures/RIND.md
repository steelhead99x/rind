# rind's fork of blind-rsa-signatures

This directory is rind's fork of
[blind-rsa-signatures](https://github.com/jedisct1/rust-blind-rsa-signatures),
the RFC 9474 implementation `rind/tests/crosschecks.rs` checks rind's blind RSA
against. The workspace's `[patch.crates-io]` builds it in place of crates.io's
0.18.0, which does not build on `rsa` 0.10.0.

Base: `45d0abfa829c3623389daae30bc35e9b2f3b550c`

Every file here is upstream's at that commit, its tag `0.18.0`, unchanged, except this one and
those listed under "Changed files", so each change can be offered upstream.

## Moving the base

The fork holds upstream's whole tree, so moving the base is a merge: apply
upstream's changes from the base to the new commit, which
`admin/upstream blind-rsa-signatures <commit>` checks out into
`.tmp/upstream/blind-rsa-signatures@<commit>`, resolve them against each change
below, delete a change upstream has made, and set the base above. Once
upstream releases a version that builds on `rsa` 0.10, delete the fork and
its `[patch.crates-io]` entry instead.

## Changed files

Each bullet names one file.

- `Cargo.toml`: requires `rsa` 0.10 and `crypto-bigint` 0.7.11, the version
  `rsa` 0.10.0 requires.
- `src/pbrsa.rs`: `PrivateKeyParts` for the derived-key `PbrsaRawKey` follows
  `rsa` 0.10.0's trait: the primes are `Odd<BoxedUint>`, and `p`/`q` replace
  `p_params`/`q_params`, still `None`, so a derived key signs without CRT as
  before. Also `rsa`'s renamed `PrivateKey`/`PublicKey` and crypto-bigint's
  `bit_width`, for their deprecated names.
- `src/lib.rs`: the same renames.
- `tests/vectors.rs`: decodes the vectors' byte strings as hex instead of
  through a `BoxedUint`, which since crypto-bigint 0.7.11 turns an empty
  string, such as the PSSZERO salt, into eight zero bytes and fails the RFC
  9474 vectors. Also `rsa::PrivateKey`, for the deprecated name.
