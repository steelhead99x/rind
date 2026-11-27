# [XS] rind-aws-lc-rs loads and saves ML-KEM decapsulation keys

## Goal

rind-aws-lc-rs backs aws-lc-rs's `kem::DecapsulationKey::new`,
`kem::DecapsulationKey::key_bytes`, and `kem::DecapsulationKeyBytes` with
rind's `kem::DecapsulationKey::new` and `to_bytes`, FIPS 203's expanded
form, and its README stops listing them as unwrapped.

## Plan

- rind gained the API when rind-openssl's ML-KEM needed to move keys
  between OpenSSL's providers; the adapter wraps it as aws-lc-rs 1.x names
  it, with crosschecks against aws-lc-rs on each parameter set.
