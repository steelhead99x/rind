# rind-acvp

Unpublished. A module wrapper for [BoringSSL's and aws-lc's `acvptool`](https://github.com/aws/aws-lc/tree/main/util/fipstools/acvp/acvptool): that tool speaks ACVP's sessions and JSON, and this binary runs the operation.

```shell
cargo build -p rind-acvp
acvptool -wrapper target/debug/rind-acvp -json prompts.json
```

`prompts.json` is a JSON array of vector sets, prompts only. The sample files in `thirdparty/acvp` are `internalProjection.json` and also carry the answers, which `acvptool` rejects when the field is one it reads as an input (AES-GCM's `ct` and `tag` on an encrypt test). Strip those before passing the file. `admin/acvp` does this for the sets the wrapper answers offline.

`cargo test -p rind-acvp` checks those answers directly, including SHA-256's standard Monte Carlo test, and checks the byte framing by running the binary.

A debug build, and a release build with `--cfg rind_cpu_disable`, honours `RIND_CPU_DISABLE_<feature>`, so one process is one CPU path. The FIPS module's load-time mask is still [its quest](../quest/m4/fips/module.md). AES-GCM with an internal IV is refused until [that quest](../quest/m4/fips/gcm-iv.md). RSA key generation is not advertised: rind has no FIPS 186-5 generation from the server's seeds or candidates.

The `acvp` feature of `rind` exists only for this binary. It is not a supported API.
