# [M] ML-DSA's SHAKE calls rest on the proven sponge

## Goal

ML-DSA's SHAKE readers, `Shake256::new` and `read` and the four-way `Shake4x`, are proven against FIPS 202 as ML-KEM's are in `proofs/Rind/X86_64/Sha3.lean`, so an ML-DSA construction proof can build on them.

## Plan

- `admin/prove` leaves them out of the translation: `Sponge::new_for_message` loops over a `&[&[u8]]`, a nested borrow, and `Shake4x` zips iterators, neither of which Aeneas translates. Restructure them as `shake256_batch` and `SqueezingSponge4xShake128` were (absorb each piece through `Sponge::absorb`, index rather than zip), keeping their speed against aws-lc-rs.
- Prove them with the sponge's lemmas: `squeezing_squeeze_spec` for the reader, and the `sbl_states` and `Shake128Out` shape of `shake128x4_squeeze_spec` for `Shake4x`, whose lane count reaches `sha3_keccak_nof4_f1600` as `shake256_batch`'s does.
