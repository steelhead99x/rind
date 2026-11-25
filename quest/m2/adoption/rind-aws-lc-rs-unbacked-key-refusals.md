# [M] rind-aws-lc-rs refuses keys of types it cannot back as aws-lc-rs does

## Goal

Every `rind-aws-lc-rs` loader that refuses a key of another type (`rsa::PublicEncryptingKey::from_der`, `PqdsaKeyPair::from_pkcs8`, and the loaders that share their helpers) returns the same `KeyRejected` kind as aws-lc-rs 1.19 for P-224, secp256k1, brainpoolP256r1, DSA and DH keys, and for EC keys with explicit curve parameters, on valid and invalid keys alike. Today rind decides those keys from their framing, so it says `WrongAlgorithm` for some that aws-lc-rs refuses as `InvalidEncoding`, and the reverse for explicit parameters. An adapter's divergence from its upstream is a bug under `AGENTS.md`. rind gains no support for these key types: each is still refused, only with aws-lc-rs's reason.

## Plan

Drafted 2026-11-25 (Claude), owner-requested as the follow-up of [steelhead99x/rind#316](https://github.com/steelhead99x/rind/pull/316), which ordered `PublicEncryptingKey::from_der`'s checks as aws-lc-rs does and documents these two approximations on `parses_as_other_public_key` and `ec_private_key` in `rind-aws-lc-rs/src/pqdsa.rs`.

aws-lc-rs parses a key with `EVP_parse_public_key` or `EVP_parse_private_key` and returns `InvalidEncoding` when that fails and `WrongAlgorithm` when the parsed key is not the type asked for (`parse_rfc5280_public_key` and `parse_rfc5208_private_key` in aws-lc-rs 1.19.0 `aws-lc-rs/src/evp_pkey.rs`). So the kind depends on whether aws-lc's decoder for the key's type accepts it, which for these types checks more than the framing. MEASURED on x86_64 against aws-lc-rs 1.19.0, through `PublicEncryptingKey::from_der` (rind at #316's head):

| SPKI | rind | aws-lc-rs |
|---|---|---|
| P-224, secp256k1 or brainpoolP256r1 point not on its curve | WrongAlgorithm | InvalidEncoding |
| P-224 with a 29-byte compressed-looking point of junk | WrongAlgorithm | InvalidEncoding |
| DSA whose parameters are an INTEGER, not `Dss-Parms` | WrongAlgorithm | InvalidEncoding |
| DSA with toy parameters (p = 23, q = 11, g = 4) | WrongAlgorithm | InvalidEncoding |
| DSA whose key is an OCTET STRING, not an INTEGER | WrongAlgorithm | InvalidEncoding |
| DH whose parameters are an INTEGER, not `DHParameter` | WrongAlgorithm | InvalidEncoding |
| DH with toy parameters (p = 23, g = 5) | WrongAlgorithm | WrongAlgorithm |
| P-256 with explicit parameters equal to P-256's, on-curve point | InvalidEncoding | WrongAlgorithm |
| The same, point off the curve | InvalidEncoding | InvalidEncoding |
| Explicit parameters of no built-in curve | InvalidEncoding | InvalidEncoding |

What to match, from aws-lc's decoders in `crypto/evp_extra` and the code they call:

- EC (`eckey_pub_decode`, `eckey_priv_decode`): `EC_KEY_parse_parameters` takes a named curve aws-lc builds in (P-224, P-256, P-384, P-521, secp256k1, and brainpoolP256r1, which the PKCS#8 parity harness in `tests/parity.rs` already shows aws-lc-rs parses), or explicit prime-field parameters only when every field equals a built-in curve's, so the explicit form is that named curve. The public point goes through `EC_POINT_oct2point`, which refuses a point not on the curve and accepts the compressed form. A private key's scalar must be below the order, and a public key it carries must match it.
- DSA (`dsa_pub_decode`, `dsa_priv_decode`): `DSA_parse_parameters` and `DSA_parse_public_key` need a `Dss-Parms` SEQUENCE of three INTEGERs and an INTEGER key, and `dsa_check_key` (`crypto/dsa/dsa.c`) bounds them: q of 160, 224 or 256 bits, p of at most 10,000 bits, and g and the key in range. That is why the toy parameters fail.
- DH (`dh_pub_decode`): `DH_parse_parameters` needs a `DHParameter` SEQUENCE of p and g and an INTEGER key. It checks no size, so the toy parameters parse.

Recommendations, each the agent's call unless review finds otherwise:

- Each check reads public data only (an SPKI, or a PKCS#8's curve, parameters and embedded public key), so plain variable-time code in the adapter is acceptable, as the existing framing checks are. The one secret is a private scalar: compare it with the order without a branch on its bytes, as `padded_ec_scalar`'s callers already handle rind's curves, or leave the scalar-and-public-key agreement check to the curves rind backs and say so in the PR.
- The on-curve check for P-224, secp256k1 and brainpoolP256r1 is `y^2 = x^3 + a x + b mod p` on public coordinates, plus decompressing a compressed point. Prefer reusing a rind type if one exposes modular arithmetic on public values; otherwise a small fixed-width modular multiply in the adapter's `der` helpers, tested against these vectors, is enough. Do not add a dependency for it.
- Explicit parameters: compare the parsed `ECParameters` with P-256's, P-384's and P-521's constants field by field (the seed is optional and ignored, as in aws-lc), then hand the key to rind under that named curve. For the unbacked curves, compare with their constants and run the same on-curve check.
- Keep one helper per key type shared by the public and the PKCS#8 paths, so the two cannot drift again.

The differential test: extend `rsa_encrypting_key_refusals` in `rind-aws-lc-rs/tests/keys.rs`, which asserts each case's kind equal to aws-lc-rs's, with every row of the table above plus the same with the point compressed, and for each unbacked curve a valid point both uncompressed and compressed. Extend `tests/parity.rs`'s PKCS#8 checks the same way: a scalar at and above the order, a public key that does not match the scalar, and explicit parameters, for each curve. The test must fail on #316's head on the rows the table marks as differing, and pass after.

Out of scope: accepting any of these key types, and loaders whose refusal kind for these keys already matches.

## Related

- [Adapter mutants](/quest/m2/23-adapter-mutants.md) - the quest whose PR found these approximations
- [rind-ring sizes RSA keys by their primes](/quest/m2/adoption/rind-ring-rsa-prime-length.md) - the same kind of adapter divergence, in rind-ring
