# [S] The portable backend passes ctgrind in debug builds

## Goal

`admin/ctgrind unit` passes on the portable backend (`RUSTFLAGS='--cfg rind_portable --cfg curve25519_dalek_backend="serial"'`) in a debug build, as it does in release, and `ctgrind.yml`'s weekly `portable` job runs a debug row beside the release one, as `build` does for x86_64 and aarch64.

## Plan

Found by [kixel-ai/rind#944](https://github.com/kixel-ai/rind/pull/944), which ran both builds: on `main` at `121f4ab45`, 23 debug tests fail memcheck, and none in release. No job runs that build, so nothing caught them.

- 22 X25519 and HPKE tests (`mid::x25519::tests::*`, `high::agreement::tests::*x25519*`, `high::agreement::tests::{agrees, round_trips, loads_in_constant_time}`, `high::hpke::tests::*`) branch inside curve25519-dalek's `MontgomeryPoint::mul_bits_be`, on the scalar's bits, though the workspace's `[profile.dev.package.curve25519-dalek]` already turns off its overflow checks and debug assertions. Find the branch, which release inlines away, and fix it where it lives: rind's call, a dev-profile setting for dalek such as `opt-level`, or upstream.
- `high::rsa::tests::loads_secret_integers_in_constant_time` branches in `high::asn1::Integer::is_negative`, whose `Option<bool>::unwrap_or_default` the debug build does not inline, on the top bit of a secret integer's first byte. Compute the sign bit without an `Option<bool>`, such as `first().copied().unwrap_or(0) >> 7`, whose `Option` holds only the public length.
- Then add the debug row. It adds one hosted job a week.

## Waiting

- Maintainer: say when to start. The maintainer holds this quest; an agent does not pick it up until this item is removed.
