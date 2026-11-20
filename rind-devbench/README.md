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
  Bundle id `com.kyledouglas.rindbench.all` (installs next to v13, not over it).
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
  `adb shell am start -n com.kyledouglas.rindbench/.MainActivity --es preset quick --es libraries rind,ring --es sections AEADs --ez autostart true`;
  results also in `/sdcard/Android/data/com.kyledouglas.rindbench/files/`.
