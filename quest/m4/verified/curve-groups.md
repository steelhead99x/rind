# [S] Ed25519 verification drops its group-closure assumption

## Goal

Ed25519's `ed25519_key_pair_verify` drops its assumption that a multiple of the base point is a point of the group.

## Plan

P-256's half of this quest has landed. `nist.card_le` and `nist.order` in `Rind/NistGroup.lean` count the points of y² = x³ − 3x + b: at most 2p + 1, and the order is n when n is prime, 2p + 1 < 3n, and the cubic has no root. `proofs/Rind/P256Order.lean` is P-256's no-root certificate, so `P256Order` holds and `p256_ecdsa_public_key_new` no longer takes it. `benchmarks/verified.toml`'s P-256 ECDSA entry states no order assumption. P-384 and P-521 reuse `nist.order` with their own certificates.

What remains is Ed25519. `edPow` and `edMul` in `proofs/Rind/Ed25519.lean` are opaque stand-ins for HOL Light's `group_pow` and `group_mul` of `edwards25519_group`. Replace them with the twisted Edwards addition, transliterated as `P256Group.lean` transliterates the Weierstrass law, and prove the base point's multiples stay on the curve. That needs 2^255 − 19 prime, which this tree does not yet prove: a Lucas certificate needs the factorization of 2^255 − 20, and trial division to 2·10^6 leaves a 236-bit cofactor. `ed25519_key_pair_verify` keeps `edOnCurve (edPow edB (ed25519Scalar seed))` until that closure is proved.

Moving P-256's own copies in `Rind/Spec.lean` and `Rind/P256Group.lean` onto `Rind/Nist.lean` so one law remains is still open, and is not required for the count.
