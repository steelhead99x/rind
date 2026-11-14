# rind-acvp

Unpublished. A module wrapper for [BoringSSL's and aws-lc's `acvptool`](https://github.com/aws/aws-lc/tree/main/util/fipstools/acvp/acvptool): that tool speaks ACVP's sessions and JSON, and this binary runs the operation.

```shell
# From a checkout of aws-lc. The binary has to be on PATH.
go build -o acvptool ./util/fipstools/acvp/acvptool

admin/acvp
```

`admin/acvp` runs `cargo test -p rind-acvp`, then `acvptool -wrapper target/debug/rind-acvp -json` on every sample set in `thirdparty/acvp` that this wrapper answers, and compares the replies to the published answers. The sample files are `internalProjection.json` and also carry the answers. The script strips fields `acvptool` reads as inputs (AES-GCM's `ct` and `tag` on an encrypt test), gives each HMAC test its own length group, and concatenates a KDA hybrid secret's `t` onto `z` because `acvptool` forwards only `z`. `ACVP_SKIP_TOOL=1` runs the crate tests only. Without `acvptool` on `PATH`, `admin/acvp` stops and prints the build line above.

`prompts.json` for a direct `acvptool` invocation is a JSON array of vector sets, prompts only. `cargo test -p rind-acvp` checks answers by calling the handlers, including the standard Monte Carlo groups the sample files carry. The vendored SHA-256 set has the alternate Monte Carlo, which `acvptool` does not drive. `acvptool` is what checks the byte framing: a reply is written to the stdout fd, because a block-buffered pipe never flushes a reply that has no newline.

A debug build, and a release build with `--cfg rind_cpu_disable`, honours `RIND_CPU_DISABLE_<feature>`, so one process is one CPU path. `rind-fips` applies that mask as the module loads; this binary calls rind, which is where `__acvp` lives. AES-GCM with an internal IV is refused until [that quest](../quest/m4/fips/gcm-iv.md). RSA key generation is not advertised: rind has no FIPS 186-5 generation from the server's seeds or candidates.

rind's `__acvp` feature exists only for this binary. A leading `__` marks it internal, as `__ctgrind` is, and it is not a supported API. The binary enables `wipe` as well, so the decapsulation key, the shared secrets, the expanded ML-DSA private key, an ECDSA private scalar, an Ed25519 seed, an ECDH shared secret, the RSA primitive's output, and `hmacDRBG`'s K and V are wiped on drop.

`hmacDRBG` is rind's `HmacDrbg`.

`admin/ctgrind` checks the secret paths this binary adds. rind's unit suite, built with `__acvp`, runs the `acvp` module's tests: the HMAC_DRBG for every hash ACVP names, seeded ML-KEM-768 key generation, encapsulation, and decapsulation of a parsed key, the RSA primitive's exponent at its public length (including leading zero bytes), and ML-DSA signing with a fixed `rnd`. The adapter suite runs `tests/ctgrind.rs`, which marks the secret arguments `acvptool` sends for ECDH, ECDSA sigGen, hmacDRBG, ML-KEM, ML-DSA sigGen, and the raw RSA exponent. ECDSA signing checks short, field-width, and zero-padded scalars on P-256, P-384, and P-521, and refuses a nonzero excess prefix. Valgrind is Linux-only.
