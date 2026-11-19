# [S] rind-acvp answers every ACVP set the module needs

## Goal

[rind-acvp](/rind-acvp/README.md) answers ACVP test sets for every
algorithm in rind's FIPS module, including the ones the module does not
offer yet, and answers fresh sets from NIST's demo server, not only the
sample sets `admin/sync-acvp` keeps.

## Plan

The wrapper, its registration (ML-KEM at all three parameter sets), and its
offline run on each CPU path landed in
[kixel-ai/rind#789](https://github.com/kixel-ai/rind/pull/789). AES-GCM
sealing with internal IVs (`ivGen: internal`), which the module offers since
[kixel-ai/rind#771](https://github.com/kixel-ai/rind/pull/771), is registered
and answered: `AES-GCM/seal` takes an empty nonce, and replies the
ciphertext, tag, and the 12-byte IV the module generated in one string, as
aws-lc's `acvptool` reads it; the offline test checks each IV and tag by
opening. What remains:

- Once a credential exists, run fresh demo sets for every registered
  algorithm, once per CPU mask, in a scheduled job, as the offline test
  runs the samples.

## Waiting

- Maintainer: request ACVP demo server credentials from NIST, which issues a TLS client certificate per organization, so fresh sets run before the lab's production run. An agent cannot contact NIST. Optional until the lab is engaged: the offline runs cover the wrapper meanwhile. Done once a credential is stored as a secret and this item is deleted.
