# rind-fips

The start of rind's FIPS 140-3 module: an SP 800-90A HMAC_DRBG over SHA-512,
one per thread, seeded from a process-wide DRBG, itself seeded from the
operating system. `fill` is the only call. rind's own key generation does
not use it.

This crate is not the module boundary. Load-time integrity, the self-tests,
the approved-service API, and the C ABI are
[quest/m4/fips/module.md](https://github.com/moq-dev/rind/blob/main/quest/m4/fips/module.md).
AES-GCM's internal IVs are
[quest/m4/fips/gcm-iv.md](https://github.com/moq-dev/rind/blob/main/quest/m4/fips/gcm-iv.md).

## What this cannot back

Everything the module will offer besides this DRBG: no approved services, no
self-tests, no integrity check, and no `fips` feature for rind-rustls or
rind-aws-lc-rs. Entropy comes from `getrandom`. A failed read is
`rind::Error::RngFailed`, with no other source tried.

`fill` runs `rind::drbg::health_test` once per process before it draws
(SP 800-90A section 11.3). A mismatch returns `rind::Error::Fault` and no
bytes. `rind::drbg::health_test` is the on-demand run.

The DRBG wipes its state on drop when rind is built with the `wipe` feature.
This crate does not turn that feature on: in a workspace, doing so would turn
it on for every member.
