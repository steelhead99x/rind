# [S] rind-aws-lc-rs refuses an RSA key outside an algorithm's range when verifying

## Goal

rind-aws-lc-rs's `ParsedPublicKey::new`, `UnparsedPublicKey::parse`, and `RsaPublicKeyComponents::to_parsed_public_key` accept a well-formed RSA public key whose modulus lies outside the given algorithm's range, such as a 1024-bit key for `RSA_PKCS1_2048_8192_SHA256`, and its verification then fails, as aws-lc-rs's do. rind-aws-lc-rs's README then drops the "refused when parsed for it" line, and `rind-aws-lc-rs/tests/aws-lc-rs/rsa_test.rs`'s `test_rsa_public_key_components_to_parsed_public_key_small_key_fails_at_verify` returns to upstream's checks.

## Plan

- The adapter's `ParsedPublicKey` holds a `rind::signature::PublicKey` parsed for one rind algorithm, whose range rind enforces when parsing. The adapter already reads the modulus length (`RsaParameters::public_modulus_len`), so it can tell an out-of-range key from a malformed one before parsing.
- Recommended: keep a key outside the algorithm's range as one that verifies nothing, after checking it parses for rind's widest range with the same hash and padding, so a malformed key is still refused when parsed. Keys outside rind's own 1024 to 8192 bits stay refused when parsed, as the README already says.
- Test it differentially against aws-lc-rs over modulus sizes on both sides of each algorithm's range.
