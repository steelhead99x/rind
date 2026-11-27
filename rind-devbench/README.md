# rind-devbench — RindBench "All" for iPad/iPhone and Android

A standalone crate (own `[workspace]`), not a member of rind's workspace.

rind-bench's own bench files (`../rind-bench/benches/*.rs`) compiled unchanged
as modules of one library, with `criterion` replaced by a tiny shim
(`criterion-shim/`) that either lists each row's criterion ID or times it. So
the app times **every library × every operation bench-report has**, under the
same IDs (`ed25519-verify/aws-lc-rs`, `aes128-gcm/rind/16KB`, …), and gains any
row rind-bench adds with no app change. The op list (`src/ops.rs`) is
generated from `admin/bench-report` by `tools/gen-ops.py` (`--check` reports drift; not wired into CI yet).

Data-driven: the app asks the core for its catalog (rows → op, section,
library), shows libraries and sections as switches, and passes the picks back
as JSON. Report operations are on by default; rind-bench's other rows
(SLH-DSA, PBKDF2, AES-KW/KWP, AES-CBC/CTR, JWT, RSA 3072–8192 loads, extra
sizes, …) are offered as "More: <file>" groups, off by default.

## Output
JSON lines (`start`, `row` per row per round with all samples, `error`,
`round`, `done`/`stopped`, `report`) to an optional TCP collector (plain
`ncat -l -k`, see `tools/listen-devbench.sh`) and to `<app docs>/<run_id>.jsonl`.
The `report` line / `<run_id>.json` is a bench-report host result (schema 1:
host, commit, cpu, os, libraries, results[{operation, library, id, ns, ns_low,
ns_high, throughput}]) plus `device` (model, chip, OS, P/E cores, CPU
features) and `timing`. `ns` = median of per-round medians; `ns_low/high` =
min/max per-round median (not criterion's CI). `tools/import-device.py
CAPTURE --out DIR` splits a collector capture into one JSON per run.

## Build
- iOS (Mac, Xcode, rustup 1.98.1 + aarch64-apple-ios): `ios/build-ipa.sh PORT [HOST]`
  (e.g. 9101 for one iPad, 9102 for another; HOST is the collector's LAN address, left out = results stay on the iPad)
  → `ios/out/RindBenchAll-v14.1-<port>.ipa`, **unsigned**.
  Bundle id `io.github.steelhead99x.rindbench.all` (installs next to v13, not over it).
  OpenSSL is vendored (built from source) by default; `CARGO_FEATURES= ios/build-ipa.sh` leaves it out.
- Android (Linux, SDK build-tools 35 + platform 35 + NDK, JDK 17+, rustup aarch64-linux-android):
  `JAVA_HOME=… CARGO_FEATURES="--features __bench_openssl" [COLLECTOR_HOST=<LAN address>] android/build-apk.sh` →
  `android/out/RindBench-android.apk` (no Gradle; debug-key signed). arm64-v8a only.
- Host smoke: `cargo run --release --example devbench-cli -- catalog|run '<json>'`.

## Run
- iPad: sign + install with your own Apple developer account (e.g. plumesign), start `tools/listen-devbench.sh`
  on the collector computer, open "RindBench All", agree, Start.
- Android: `adb install -r RindBench-android.apk`;
  the collector fills itself in (127.0.0.1:9103 via `adb reverse`, else the LAN address given to build-apk.sh as `COLLECTOR_HOST`); headless:
  `adb shell am start -n io.github.steelhead99x.rindbench/.MainActivity --es preset quick --es libraries rind,ring --es sections AEADs --ez autostart true`;
  results also in `/sdcard/Android/data/io.github.steelhead99x.rindbench/files/`.

## DIT and SHA-3: the A/B/C/D matrix for an iPad

rind's DIT and its SHA-3 instructions both change what a row measures on Apple
CPUs. Every `rind` row is timed holding `rind::cpu::Dit`, so it pays no
per-call toggle, and the `dit-per-call/*` rows time a few of them again without
the guard, paying one enter/exit per call. Neither shows what DIT itself or the
SHA-3 extension costs, so run the same app four times on each iPad, each a
separate build and a fresh app launch (rind reads the CPU's features once per
process):

| Run | Build | rind sees |
|---|---|---|
| A | `ios/build-ipa.sh PORT` | default: DIT set, SHA-3 instructions used |
| B | `RIND_DEVBENCH_DENY=sha3 ios/build-ipa.sh PORT` | no SHA-3 extension (`RIND_CPU_DISABLE_sha3`) |
| C | `RIND_DEVBENCH_DENY=dit ios/build-ipa.sh PORT` | rind sets no DIT, held or per call |
| D | `RIND_DEVBENCH_DENY=sha3,dit ios/build-ipa.sh PORT` | both |

`RIND_DEVBENCH_DENY` must list ids rind reads on the target (`src/deny.rs`;
`sse4.1` may be written with its dot): the build refuses an empty or
malformed entry, an id rind does not read there, or any build without
`--cfg rind_cpu_disable`, and the report's `cpu_denied` is that checked list.
`build-ios.sh` builds rind with `--cfg rind_cpu_disable`, without which rind
may ignore `RIND_CPU_DISABLE_<id>` (it reads it otherwise only with debug
assertions on, which a profile can turn off for rind alone), and the app
sets those variables before its first rind call, from `main` before `UIApplicationMain` starts any thread (`devbench_apply_denies`), because changing the environment is not safe once other threads may read it. A build that denies features and skips that call refuses to list or run. Android has no such point, since its process is multi-threaded before any app code runs, so `android/build-apk.sh` refuses to build with `RIND_DEVBENCH_DENY` set. Each set has its own cargo
target directory and its own `out/RindBenchAll-v..-PORT-deny-<ids>.ipa`. The
report records the denied ids as `cpu_denied`, and every run's `device`
features include `FEAT_DIT` and `FEAT_SB`. Nothing here was built or run on
Apple hardware when it was written.

What to compare, with the same rounds and sample settings in all four:

- A alone, a `dit-per-call/*` row against the held row it repeats: the
  per-call toggle.
- A against C, the `rind` rows: A runs with DIT held on, C without DIT, so A's
  `rind` minus C's is DIT's own slowdown on the instructions, if any; C's
  `dit-per-call/*` rows should match its held ones within noise.
- A against B, the `sha3-*` rows and the SHA-512 rows (rind's SHA-512 compress
  runs on the same `sha3` feature as Keccak): B's `rind` row without
  the SHA-3 extension against A's is what that extension is worth; it also
  shows whether a SHA-3 row's gap is DIT, the instructions, or neither.
  B against D separates the SHA-3 effect without DIT.
- The `dit-toggle/*` rows (run them as "More: dit_toggle") in A:
  `dit-per-call/dit-toggle/verify-empty` minus `dit-toggle/verify-empty`, and
  `hold-drop`, are one toggle with no other work, and `no-entry` is the floor;
  in C the verify-empty rows agree and `hold-drop` is not made.
