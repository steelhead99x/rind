# [S] rind-ring sizes RSA keys by their primes, as ring does

## Goal

rind-ring's `rsa::KeyPair` loaders (`from_pkcs8`, `from_der`, and
`from_components`) accept and refuse a key's size exactly as ring 0.17 does.
ring requires each prime to be `ceil(n_bits / 2)` bits long and a multiple of
512 bits (`src/rsa/keypair.rs`, `PrivatePrime::new`). rind-ring instead
requires the modulus to be a multiple of 512 bits. So it refuses a 3071-bit
modulus with two 1536-bit primes, or a 4095-bit one with two 2048-bit primes,
which ring loads, and a 2047-bit one with two 1024-bit primes, which ring
also loads (its 2048-bit floor counts the modulus's bytes, not its bits).
It also loads a 3072-bit key with unbalanced primes, which ring refuses.

## Plan

- Check both primes' bit lengths in rind-ring's shared `KeyPair::new`.
  Revealing only the verdict, whether each prime has the expected length, is
  acceptable, as ring and aws-lc check it too. Read the length without a
  branch or variable-time instruction on the prime's bytes.
- Recommendation: give `rind::rsa::KeyPair` a way to report whether its
  primes are balanced at a given width, rather than re-parse its PKCS#8 in
  the adapter, since rind already holds the primes and its `ct` tools.
- The 2047-bit key also meets rind's own floor: `rind::rsa::KeyPair` refuses
  a modulus under 2048 bits (`MIN_MODULUS_BITS` in `rind/src/mid/rsa_priv.rs`),
  as aws-lc-rs does, so rind-ring cannot accept it alone.
- Decided 2026-11-24 (maintainer, /quest-run): ✅ lower rind's private-key
  floor to 2047 bits, whose 1024-bit primes give the strength of 2048, so
  rind-ring loads 2047-bit keys as ring does, and have rind-aws-lc-rs refuse
  under 2048 bits as aws-lc-rs does (rejected: keep rind's 2048-bit floor and
  list 2047-bit keys as refused in rind-ring's README). An adapter's
  divergence from its upstream is a bug under AGENTS.md.
- Test against ring with 2047-, 3071-, 3072-, 4095-, and 4096-bit keys whose
  primes are each `ceil(n / 2)` bits, an unbalanced 3072-bit key, and a
  2560-bit key (1280-bit primes, refused), under `rind-ring/tests/rsa.rs`. Update the
  `KeyPair` doc comment in `rind-ring/src/rsa.rs`.

