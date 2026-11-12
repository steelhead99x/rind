# rind builds a FIPS 140-3 module ready for validation

## Goal

A `rind-fips` crate offers rind's approved algorithms from a module built to
pass FIPS 140-3 Level 1 validation, so a consumer that must use validated
cryptography (FedRAMP, FISMA, and the deployments behind
[oven-sh/bun#4869](https://github.com/oven-sh/bun/issues/4869) and
[denoland/deno#36906](https://github.com/denoland/deno/pull/36906)) can run on
rind. The default `rind` build pays nothing for it.

## Plan

Scoped in [moq-dev/rind#638](https://github.com/moq-dev/rind/pull/638)
(2026-11-11), whose body is the report: boundary, changes, lab, cost, and
timeline, against aws-lc's validated module
([cert #5298](https://csrc.nist.gov/projects/cryptographic-module-validation-program/certificate/5298)).

- The module is its own crate, frozen at a tagged snapshot of rind for the
  certificate's life, as aws-lc freezes its `AWS-LC-FIPS-*` tags: the
  security policy names one source archive by hash, and any change to it
  needs a new submission. `rind` keeps moving; `rind-fips` follows it only
  when a new version is submitted.
- It holds only approved algorithms used in approved ways, enforced by its
  types, so a successful call is the service indicator (IG 2.4.C's implicit
  indicator). X25519, ChaCha20-Poly1305, MD5, HPKE, and RSA-OAEP stay in
  `rind`, outside the boundary, as aws-lc keeps X25519 outside its module.
- Entropy comes from the OS, outside the boundary (IG 9.3.A scenario 2(b)),
  accepting aws-lc 3's caveat "No assurance of the minimum strength of
  generated SSPs". An SP 800-90B entropy source with its own ESV certificate
  waits for a consumer that rejects that caveat.
- The children build the module, ready for a lab to test. The lab contract
  and the CMVP submission are dropped until a consumer needs or funds a
  certificate, as the maintainer decided on 2026-11-12;
  [moq-dev/rind#638](https://github.com/moq-dev/rind/pull/638)'s body keeps
  their cost (about $70k to $100k) and timeline (about 18 to 24 months).
