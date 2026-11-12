# [M] The curve proofs' group assumptions are proven

## Goal

The elliptic-curve theorems stop assuming group facts: P-256 ECDSA verification with a parsed public key drops `P256Order`, that every finite point has order n, and Ed25519's `ed25519_key_pair_verify` drops its assumption that a multiple of the base point is a point of the group. `benchmarks/verified.toml`'s P-256 ECDSA entry then states no assumption.

## Plan

- `P256Order` (`proofs/Rind/P256Multiples.lean:33`) follows from the group having n points. HOL Light's `P256_GROUP_ELEMENT_ORDER` proves it from the group's size, which Mathlib cannot count.
- Route to the count (maintainer, 2026-11-09): ✅ the elementary counting argument (rejected: prove Hasse's bound; describe both and let the implementer pick). Mathlib has no Hasse bound for elliptic curves (searched 2026-11-09), and formalizing one is far more than this quest. The argument, for the curve y^2 = x^3 - 3x + b over the field of p elements:
  1. Each x gives at most two points, so with the point at infinity the group has at most 2p + 1.
  2. 2p + 1 is under 3n: p and n are both just under 2^256, a comparison of two literals.
  3. n divides the group's order, by Lagrange, because G has order n: `Rind/P256Multiples.lean` proves n·G = O with G finite, and `Rind/N256Prime.lean` that n is prime.
  4. So the order is n or 2n.
  5. 2n is even, so by Cauchy the group would hold a point of order 2. Such a point is its own negative, so its y is 0 and its x is a root of x^3 - 3x + b in the field.
  6. A kernel-checked computation shows the cubic has no root there: for example that gcd(x^p - x, x^3 - 3x + b) is 1, with x^p reduced modulo the cubic by square-and-multiply as `P256Multiples.lean` checks its doubling chain, or whatever certificate Lean's kernel checks cheapest.
  7. So the order is n, a prime, and every finite point has order n.
- This argument was checked on paper during the 2026-11-09 audit, not in Lean. Hasse's bound is the fallback only if step 6's certificate proves impractical; say so in the PR before taking it. Offering either to Mathlib is optional, with no standing approval: stop and ask the maintainer before posting there or anywhere outside the moq-dev and kixelated orgs (decided with the maintainer on 2026-11-07 on [moq-dev/rind#448](https://github.com/moq-dev/rind/pull/448)).
- Ed25519's fact is closure of `edwards25519_group` under its power, from the group's definition transliterated under the composition rule, as `P256Group.lean` does for P-256.
- Shape the lemmas over the curve's p, n, b, and G, so [P-384](/quest/m4/verified/p384.md) and [P-521](/quest/m4/verified/p521.md) reuse them: both have a = -3, a prime n, and cofactor 1, so the same seven steps apply with their own certificates. `Rind/Nist.lean` and `Rind/NistGroup.lean` ([moq-dev/rind#628](https://github.com/moq-dev/rind/pull/628)) already state the group law and its Mathlib group over p and b, with P-384 on them; prove the count there, and move P-256's copies in `Rind/Spec.lean` and `Rind/P256Group.lean` onto them so one law remains.
