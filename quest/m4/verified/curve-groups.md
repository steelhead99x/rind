# [S] Ed25519 verification drops its group-closure assumption

## Goal

Ed25519's `ed25519_key_pair_verify` drops its assumption that a multiple of the base point is a point of the group.

## Plan

P-256's half of this quest has landed: `proofs/Rind/P256Order.lean` proves `P256Order`, every finite point has order n, and `p256_ecdsa_public_key_new` no longer takes that hypothesis. `benchmarks/verified.toml`'s P-256 ECDSA entry states no order assumption. The counting lemmas (`nist_card_le`, `nist_order`) are stated for any odd prime field and any curve constant b, so P-384 and P-521 reuse them with their own certificates that x³ − 3x + b has no root.

What remains is Ed25519. `edPow` and `edMul` in `proofs/Rind/Ed25519.lean` are opaque stand-ins for HOL Light's `group_pow` and `group_mul` of `edwards25519_group`. Replace them with the twisted Edwards addition, transliterated as `P256Group.lean` transliterates the Weierstrass law, and prove the base point's multiples stay on the curve. That needs 2^255 − 19 prime, which this tree does not yet prove: a Lucas certificate needs the factorization of 2^255 − 20, and trial division to 2·10^6 leaves a 236-bit cofactor. `ed25519_key_pair_verify` keeps `edOnCurve (edPow edB (ed25519Scalar seed))` until that closure is proved.
