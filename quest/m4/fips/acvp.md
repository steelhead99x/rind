# [S] rind-acvp answers every ACVP set the module needs

## Goal

[rind-acvp](/rind-acvp/README.md) answers ACVP test sets for every
algorithm in rind's FIPS module, including the ones the module does not
offer yet, on the sample sets `admin/sync-acvp` keeps.

## Plan

The wrapper, its registration (ML-KEM at all three parameter sets), and its
offline run on each CPU path landed in
[kixel-ai/rind#789](https://github.com/kixel-ai/rind/pull/789). What
remains:

- Register and answer AES-GCM sealing with internal IVs (`ivGen:
  internal`), which the module offers since
  [kixel-ai/rind#771](https://github.com/kixel-ai/rind/pull/771): aws-lc's `acvptool` asks `AES-GCM/seal` with an empty nonce, and
  reads the ciphertext, tag, and 12-byte IV back in one string.
  The kept `ACVP-AES-GCM-1.0.json` sample holds only `ivGen: external`
  groups, and the offline test keeps only decrypt groups, so add an offline
  check that sends a synthetic `ivGen: internal` request with an empty
  nonce and checks the returned ciphertext, tag, and 12-byte IV, by
  decrypting them, before the lab's run is the first to seal.
- Decided 2026-11-24 (maintainer, /quest-run): ✅ no NIST ACVP demo
  server credentials (rejected: request them now; defer the request). The
  offline sample runs cover the wrapper; the lab's production run is the
  first against NIST's server.
