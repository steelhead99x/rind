# [M] RSA private keys load in constant time to the last byte

## Goal

Loading an RSA private key from DER reads no secret byte through a branch or
a memory index, so `rsa_with_secret` in `rind-fips/tests/ctgrind.rs` marks
every byte of the private integers (d, p, q, dp, dq, and qinv) secret and
`admin/ctgrind fips` still passes. A test in `rind` marks the same bytes and
loads the key under ctgrind, so the check does not depend on the FIPS module.

## Plan

Found by [kixel-ai/rind#704](https://github.com/kixel-ai/rind/pull/704) on
2026-11-13; the maintainer kept it as a follow-up rather than fix it there.
Until it lands, `rsa_with_secret` leaves three bytes of each private integer
public, and its doc comment says why.

- Three checks read those bytes, and memcheck taints a whole byte on any
  read of it, so marking only the bits that carry public facts fails too:
  - `minimum_magnitude_check` in `rind/src/high/asn1.rs` compares the first
    byte with 0x00 and 0xff and tests the second byte's top bit.
  - `trim_leading_zeroes` in `rind/src/low/posint.rs` loops while a byte is
    zero.
  - `RsaPrivateKey::new` in `rind/src/mid/rsa_priv.rs` tests p's and q's
    parity, and `len_bits` reads the top byte.
- The facts these reveal are public in any valid key, as the doc comment
  says: the byte length is in the DER header, p and q are odd, and their bit
  lengths follow from n's. Make each check a mask over the bytes, combine
  the masks, and declassify only the accept-or-refuse verdict and the facts
  that are public anyway, with `low::ct::into_public`. A refused key may
  reveal which check refused it: that names a malformed key, not its secret.
- `trim_leading_zeroes` is shared with public integers, so give the private
  path its own constant-time trim rather than slow the public one.
- Benchmark RSA key loading against aws-lc-rs before and after, as
  AGENTS.md asks of performance-sensitive changes.
