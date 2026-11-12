# [XL] RSA signing, decryption, and key generation are proven

## Goal

RSA's private operation and everything around it, PKCS#1 v1.5 and PSS signing, OAEP encryption and decryption, key loading, and key generation, are proven from the API to the Montgomery products and table gathers, so RSA-2048 signing earns the ✓ on x86_64 with BMI2 and ADX but without AVX-512 IFMA, and on every path whose products a later quest proves.

## Plan

- Runs: `mid::rsa_priv`'s CRT private operation with the verify-after-sign check, the 5-bit fixed-window exponentiation (`low::x86_64::mont_exp`, a port of aws-lc's C) gathering each entry by s2n-bignum's proven `bignum_copy_row_from_table` or by masking all 32 with AVX2, EMSA-PSS and EMSA-PKCS1-v1_5 encoding, OAEP's encoding and its constant-time decoding, `exponents_agree` and the other key-load checks, and `rsa_priv::generate`, over the same products as [RSA verification](/quest/m4/verified/rsa-verify.md).
- Route: Aeneas to Lean against RFC 8017. The AVX2 gather is intrinsics, modelled as `Rind/X86_64/Simd.lean` models AES-GCM's.
- Key generation's spec is the key it returns, not how it found it: the components satisfy RFC 8017's relations at the requested size with e = 65537, and d is reduced mod lcm(p - 1, q - 1). Primality is probabilistic and outside a functional spec, as randomness is.
- Products elsewhere enter as a hypothesis, as in [RSA verification](/quest/m4/verified/rsa-verify.md).

## Required

- [RSA verification is proven](/quest/m4/verified/rsa-verify.md) - its spec, public operation, and key-load checks are what signing reuses
