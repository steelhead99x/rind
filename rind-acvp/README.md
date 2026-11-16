# rind-acvp

Answers ACVP test sets for [rind-fips](../rind-fips/README.md)'s module, as
the module wrapper of aws-lc's `acvptool` (`util/fipstools/acvp/`), so the
lab can run NIST's ACVP server against the module, and rind's CI can run
NIST's sample sets offline. Unpublished: it is a test tool.

`acvptool` handles ACVP's sessions, authentication, and JSON, and asks the
wrapper for each answer over stdin and stdout (aws-lc's
`ACVP.md`). `rind-acvp` answers through `rind-fips`'s API, and through the
deterministic forms of the randomized services, which FIPS 203 and 204 allow
only for testing: the DRBG from given entropy, ML-KEM from given seeds, and
ML-DSA from a given seed and `rnd`. Only the module's ACVP build has those,
which `rind-fips`'s hidden `__acvp` feature builds; a program's module never
does. `rind-acvp`'s `module` feature asks for it, so a workspace build
without it compiles nothing here.

[`src/config.json`](src/config.json) registers the module's capabilities,
which `acvptool -wrapper target/debug/rind-acvp -regcap` prints.

## Running

`nix develop` provides `acvptool`, patched to send ML-DSA's `externalMu`
only for the internal interface; an unpatched one answers ML-DSA's
external-interface tests wrongly (UPSTREAM.md, "acvptool sends ML-DSA's
externalMu for the external interface"). The offline test answers NIST's sample
sets (`thirdparty/acvp/`) and sets it builds from CAVP's and Wycheproof's
vectors for what the samples lack, once for each CPU path this host can
take, by the module's load-time `RIND_CPU_DISABLE_<feature>` mask:

```sh
cargo test -p rind-acvp --features module
SLOW_TESTS=1 cargo test --release -p rind-acvp --features module  # with the 15 GiB large-data hash tests
```

`just ci` runs it when `rind-fips`, `rind-acvp`, or the sample sets change.
build.yml's nightly runs it with the large-data tests on x86_64 and
aarch64. x86-cpu.yml runs it for the AVX-512 paths with
`RIND_ACVP_WRAPPER_RUNNER="sde -dmr --"`, which runs only the wrapper
under Intel SDE's Diamond Rapids, and every CPU mask, while the test and
`acvptool` run natively.

Against NIST's demo server, with a credential in `acvptool`'s
`config.json`, `-run` fetches an algorithm's fresh sets and answers them:

```sh
cargo build -p rind-acvp --features module
acvptool -wrapper target/debug/rind-acvp -run ML-DSA
```

Each CPU path is its own ACVP implementation: run the server's sets once
per `RIND_CPU_DISABLE_<feature>` mask, as the offline test does.

## What it does not answer yet

- AES-GCM sealing with internally generated IVs, which the module offers
  but rind-acvp does not register or answer yet; it registers opening only.
- The TLS 1.3 KDF, which no module service derives through yet.
