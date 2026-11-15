# [XL] RSA signing, decryption, and key generation are proven

## Goal

RSA's private operation and everything around it, PKCS#1 v1.5 and PSS signing, OAEP encryption and decryption, key loading, and key generation, are proven from the API to the Montgomery products and table gathers, so RSA-2048 signing earns the ✓ on x86_64 with BMI2 and ADX but without AVX-512 IFMA, and on every path whose products a later quest proves.

## Plan

- Runs: `mid::rsa_priv`'s CRT private operation with the verify-after-sign check, the 5-bit fixed-window exponentiation (`low::x86_64::mont_exp`, a port of aws-lc's C) gathering each entry by s2n-bignum's proven `bignum_copy_row_from_table` or by masking all 32 with AVX2, EMSA-PSS and EMSA-PKCS1-v1_5 encoding, OAEP's encoding and its constant-time decoding, `exponents_agree` and the other key-load checks, and `rsa_priv::generate`, over the same products as RSA verification, whose proof in `proofs/Rind/X86_64/RsaDispatch.lean` gives the spec (`Rind/Rsa.lean`), public operation, and key-load checks signing reuses.
- Route: Aeneas to Lean against RFC 8017. The AVX2 gather is intrinsics, modelled as `Rind/X86_64/Simd.lean` models AES-GCM's.
- Key generation's spec is the key it returns, not how it found it: the components satisfy RFC 8017's relations at the requested size with e = 65537, and d is reduced mod lcm(p - 1, q - 1). Primality is probabilistic and outside a functional spec, as randomness is.
- Products elsewhere enter as a hypothesis, as `MontProducts` and `AwsLcMont` in `proofs/Rind/X86_64/RsaMont.lean` do for verification.
- pyca/verified-garbage (VG) measured slower on 2026-11-13 for the private operation with ADX but without IFMA (1.02 to 1.65: every size on the no-AVX-512 tier, and 2048, 2056, 2560, and 4096 bits on the no-IFMA tier) and without ADX (1.4 to 2.2), so rind keeps this code ([the m2 VG epic](/quest/m2/verified-garbage/README.md)). With IFMA, VG won at the sizes the dual RSAZ runs (2048, 3072, and 4096 bits, 0.96 to 0.99) but lost 6144 and 8192 (1.06 and 1.07); on the no-IFMA tier it won 3072, 6144, and 8192 bits but lost the rest. Where [its switch](/quest/m2/verified-garbage/rsa-avx512.md) replaces the dual RSAZ exponentiation, it keeps the CRT and padding glue this quest proves.
