# [S] rind-fips versions its module's C ABI

## Goal

A `rind-fips` executable refuses a `librind_fips_module.so` built with a different C ABI, instead of calling its entry points with the wrong arguments, as a program deployed beside the library on its loader's path could today.

## Plan

Found in [kixel-ai/rind#1126](https://github.com/kixel-ai/rind/pull/1126)'s review, which changed `rind_fips_ml_dsa_sign`'s arguments and added `rind_fips_ml_dsa_public_key_verify`: every change to an entry point's signature has had this hazard, since the module keeps one SONAME (`rind-fips/build.rs`) and the crate never checks the module's identity at load.

- The build script already hashes the module for its integrity test; either carry an ABI hash in the SONAME and link name (`librind_fips_module.<hash>.so`, so the loader finds only the matching one), or export a version symbol the crate checks once before any call, failing loud on a mismatch. Recommended: the version symbol, which leaves the README's "beside it with an `$ORIGIN` run path" unchanged.
- Derive the version from the declarations both sides share, not from a constant someone must remember to bump.
- The module is unpublished and has no certificate, so nothing needs to wait for this.
