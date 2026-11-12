feat(blind-rsa): add RSABSSA-SHA384

## Problem

rind has no RSA blind signatures. RFC 9474's four RSABSSA-SHA384 variants are what Privacy Pass's publicly verifiable token (RFC 9578 type `0x0002`) uses: the client blinds a message, the server signs that integer, and the client turns the result into an ordinary RSASSA-PSS signature. A randomized caller must not be able to verify the unprepared message.

## Approach

`blind_rsa` uses rind's public exponentiation, a multiplication mod n, and the existing CRT private operation, which already checks its result against the public key. The blinding factor's inverse is `bignum_modinv`. Each variant is its own `&'static Algorithm`. `PublicKey` loads a SubjectPublicKeyInfo or modulus and exponent. An `id-RSASSA-PSS` key is parsed here, and its hash, MGF1 hash, and salt length must match the chosen variant; the shared RSA parser still accepts only `rsaEncryption`. `blind` returns a `BlindedMessage` and a `Blinding`; `finalize` consumes the blinding and returns a signature only after it verifies. `KeyPair` loads PKCS#8, can generate a key, and `blind_sign` signs a blinded message. A randomized message is a `PreparedMessage` holding the 32-byte prefix and the message, and only that type verifies. Blinding stores the SHA-384 digest, so there is no message-length cap. `Blinding` and `KeyPair` wipe their whole value under `wipe`.

`rsa::MAX_SPKI_LEN` is gone on current main (it moved onto the signature module for ML-DSA). The test that round-trips an RSA SPKI sizes its buffer as `MAX_PUBLIC_KEY_LEN + 32`.

The quest file `quest/m4/protocols/blind-rsa.md` is removed. The work it described is this module.

## Impact

New `blind_rsa` module: `Algorithm`, `RSABSSA_SHA384_PSS_RANDOMIZED`, `RSABSSA_SHA384_PSSZERO_RANDOMIZED`, `RSABSSA_SHA384_PSS_DETERMINISTIC`, `RSABSSA_SHA384_PSSZERO_DETERMINISTIC`, `PreparedMessage`, `PublicKey`, `Components`, `SubjectPublicKeyInfo`, `BlindedMessage`, `BlindSignature`, `Signature`, `Blinding`, `KeyPair`.

`PublicKey` and `KeyPair` export the SPKI and the modulus and exponent.

## Alternatives

One message type for every variant would let a randomized caller pass the original bytes to verify. Partially blind RSA (draft-ietf-privacypass-public-metadata-issuance) is a different construction. aws-lc-rs has no blind RSA, so there is no benchmark against it.

## Follow-ups

- Partially blind RSA stays out until a consumer asks.
- Draft #624 (RSA verification proofs) edits `pkcs1.rs`, `rsa.rs`, `posint.rs`, and `rsa_pub.rs`, the same files this branch extends.
- #614, which is marked to merge, edits `quest/m4/protocols/blind-rsa.md` (a line number in the plan). This branch deletes that file, so the two will conflict on it.

## Testing

Head `1ee546e035f2da7a105b0ccade965c8b9a4fbbd1`.

`nix develop --command just ci upstream/main` exited 0. That run covers fmt, clippy, nextest, structure, MSRV, the cross builds (aarch64, armv7, portable, wasm32), `admin/ct-vartime`, `cargo deny`, the license scan, `admin/testing`, fixtures, the patch build, and the quest, shell, and nix checks.

`nix develop .#ctgrind --command admin/ctgrind unit --release -- blind_rsa::tests::secrets_stay_secret`:

```
test high::blind_rsa::tests::secrets_stay_secret ... ok
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 643 filtered out; finished in 6.05s
ERROR SUMMARY: 0 errors from 0 contexts (suppressed: 0 from 0)
```

`cargo test -p rind --lib matches_blind_rsa_signatures -- --exact high::blind_rsa::tests::matches_blind_rsa_signatures`:

```
test high::blind_rsa::tests::matches_blind_rsa_signatures ... ok
test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 650 filtered out; finished in 0.39s
```

The same `just ci` run includes RFC 9474 Appendix A (`rfc9474`), Wycheproof `rsa_pss_2048_sha384_mgf1_48_test.json` (`wycheproof_pss_sha384`), `zeroing::blind_rsa` under `wipe`, `accepts_openssl_rsassa_pss_spki`, `rejects_nonzero_octet_above_em_len`, and `rejects_a_bare_pkcs1_key`.

## Review

Rounds by a model from a second vendor, different from the one that wrote the code. The SHAs are this branch's commits of those changes.

| Round | Head reviewed | Base | Score | Findings |
| --- | --- | --- | --- | --- |
| 1 (low effort) | `b55cc286` | f5f82bca | 7/10 | 3 low |
| 1 (deep) | `db60925e` | f5f82bca | 7/10 | 5 medium, 5 low |
| 2 | `034a4dfe` | f5f82bca | 9/10 | 1 low |

Every round-1 finding was fixed and confirmed in round 2. The main changes: the PSS salt is bound to the key, the PSS BIT STRING is parsed as PKCS#1 only, blinding state keeps the digest instead of the message, the key can be exported (`to_spki`, `components`), and malformed-DER tests were added.

The round-2 low finding is fixed at `64450392`: `from_spki`'s non-PSS path calls `VerifyingKey::from_spki_der`, and `rejects_a_bare_pkcs1_key` checks that a bare PKCS#1 key is refused. A low finding needs no further round.

`1ee546e0` is not part of those rounds. It only replaces the removed `rsa::MAX_SPKI_LEN` in that test.
