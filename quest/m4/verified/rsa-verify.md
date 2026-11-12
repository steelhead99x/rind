# [L] RSA verification is proven

## Goal

RSA PKCS#1 v1.5 and PSS verification, the signatures most certificate chains carry, are proven from the signature API to the Montgomery products, so `rsa2048-pkcs1-sha256-verify` and `rsa2048-pss-sha256-verify` earn the ✓ on x86_64 with BMI2 and ADX, where RSA-2048's products are s2n-bignum's proven Karatsuba routines, and on every path whose products a later quest proves.

## Plan

- Runs: `mid::rsa_pub`'s public square-and-multiply, `pub_montifier` (Knuth D) and `mont_neg_inverse`, `high::pkcs1`'s EMSA-PKCS1-v1_5 encoding check, PSS's EMSA-PSS-VERIFY with MGF1, and the key-load checks, over `low::mont`'s products: on x86_64 with BMI2 and ADX at 16 and 32 words, `bignum_kmul_16_32`, `bignum_kmul_32_64`, their squarings, `bignum_emontredc_8n`, `bignum_cmp_lt`, and `bignum_optsub`, all proven in HOL Light.
- Route: Aeneas to Lean, under the epic's composition rule, against RFC 8017 transliterated in `proofs/`, composing with the hash proofs for the message digest's row and the MGF1 hash inside the scheme.
- Products elsewhere (aws-lc's on aarch64, at other widths, and without ADX) enter as a hypothesis, as `ShaBlocks` does for SHA-256, so each later proof of them drops it: [aarch64's](/quest/m4/verified/rsa-aarch64-mont.md) and [x86_64's](/quest/m4/verified/rsa-x86-mont.md).
- armv7's portable bignum Rust is the same tool's work; include it if the translation covers it without a separate model.
