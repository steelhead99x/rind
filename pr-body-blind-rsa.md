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

Partially blind RSA stays out until a consumer asks.

This branch rebases cleanly on upstream main (`62b17d67`). It conflicts with #614 in the docs, the quest files, and `rind/src/low/mod.rs`, and with #624 in `rind/src/high/pkcs1.rs` and `rind/src/high/rsa.rs`. It will be updated by merge after whichever of those lands first.

## Testing

Head `56d288f92c745c95961ee501212bf8624de62c9f`.

`nix develop --command just ci upstream/main` on this head exited 0 (2026-11-12, 00:41–00:50 UTC). That run covers fmt, clippy, nextest, structure, MSRV, the cross builds (aarch64, armv7, portable, wasm32), `admin/ct-vartime`, `cargo deny`, the license scan, `admin/testing`, fixtures, the patch build, and the quest, shell, and nix checks.

The ctgrind run and the `blind-rsa-signatures` differential below are this same series. The last commit only resizes a test buffer, so it does not change the code those two runs execute.

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

The heads in this table are pre-rebuild fork commits. The base of every round is fork main (upstream main as of 2026-11-11 plus fork-only review config).

| Round | Head reviewed | Base | Score | Findings |
| --- | --- | --- | --- | --- |
| 1 (low effort) | `8201a5b5` | fork main | 7/10 | 3 low |
| 1 (deep) | `2ac0ac98` | fork main | 7/10 | 5 medium, 5 low |
| 2 | `72275be4` | fork main | 9/10 | 1 low |

Rebuilt head `56d288f92c745c95961ee501212bf8624de62c9f` carries the same quest commits cherry-picked onto upstream main.

Every round-1 finding was fixed and confirmed in round 2. The main changes: the PSS salt is bound to the key, the PSS BIT STRING is parsed as PKCS#1 only, blinding state keeps the digest instead of the message, the key can be exported (`to_spki`, `components`), and malformed-DER tests were added.

The round-2 low finding is fixed at `3dfc0475`: `from_spki`'s non-PSS path calls `VerifyingKey::from_spki_der`, and `rejects_a_bare_pkcs1_key` checks that a bare PKCS#1 key is refused. A low finding needs no further round.

The tip of the rebuilt head sizes that test's buffer as `MAX_PUBLIC_KEY_LEN + 32` after `rsa::MAX_SPKI_LEN` left `rsa.rs`. That change is mechanical. Checked against REVIEW.md: the buffer holds a public SPKI, so there is no new secret-dependent branch, index, or variable-time instruction; the `unwrap`s stay in the test, on a key the test built, and no library path gained one; the test still refuses a bare PKCS#1 key and reloads the SPKI; no key type or wipe path changes.
