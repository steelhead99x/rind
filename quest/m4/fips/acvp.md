# [L] An ACVP module wrapper for fresh test sets

## Goal

A `rind-acvp` binary (unpublished, beside rind-bench) answers ACVP test
sets for every algorithm and CPU path in rind's FIPS module, so the lab can
run NIST's production server against it and rind's CI can run fresh demo
sets, not only the sample sets `admin/sync-acvp` keeps.

## Plan

From [the scope](/quest/m4/fips/README.md), 2026-11-11.

- Speak the module wrapper protocol of BoringSSL's and aws-lc's `acvptool`
  (Go, test-only, outside rind), so that tool handles ACVP's sessions,
  authentication, and JSON, and rind writes only the per-algorithm handlers.
  Writing an ACVP client from scratch buys nothing.
- Cover the test types the sample sets skip: ECDH as KAS-ECC-SSC, whose
  sample sets hold no curve rind offers; FIPS 186-5 RSA key generation from
  the server's seeds or candidates, or keep RSA key generation out of the
  module; ECDSA and ML-KEM key generation from given seeds; the DRBG; AES-GCM
  with internal IVs; and the TLS 1.3 KDF if rind-rustls's FIPS build derives
  through it.
- Run once per CPU path, with the module's load-time CPU mask; each path is
  its own CAVP implementation, as aws-lc's certificate lists two dozen.
- Offline first: `acvptool` processes a vector file locally, and the sample
  sets carry their answers, so CI checks the wrapper without NIST's server.

## Waiting

- Maintainer: request ACVP demo server credentials from NIST, which issues a TLS client certificate per organization, so fresh sets run before the lab's production run. An agent cannot contact NIST. Optional until the lab is engaged: the offline runs cover the wrapper meanwhile. Done once a credential is stored as a secret and this item is deleted.
