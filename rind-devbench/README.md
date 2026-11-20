# rind-devbench — RindBench "All" for iPad/iPhone and Android

Local work (branch `devbench/all-libs-app` on rind `cce3272`); not pushed.

rind-bench's own bench files (`../rind-bench/benches/*.rs`) compiled unchanged
as modules of one library, with `criterion` replaced by a tiny shim
(`criterion-shim/`) that either lists each row's criterion ID or times it. So
the app times **every library × every operation bench-report has**, under the
same IDs (`ed25519-verify/aws-lc-rs`, `aes128-gcm/rind/16KB`, …), and gains any
row rind-bench adds with no app change. The op list (`src/ops.rs`) is
generated from `admin/bench-report` by `tools/gen-ops.py` (`--check` in CI).

Data-driven: the app asks the core for its catalog (rows → op, section,
library), shows libraries and sections as switches, and passes the picks back
as JSON. Report operations are on by default; rind-bench's other rows
(SLH-DSA, PBKDF2, AES-KW/KWP, AES-CBC/CTR, JWT, RSA 3072–8192 loads, extra
sizes, …) are offered as "More: <file>" groups, off by default.

## Output
JSON lines (`start`, `row` per row per round with all samples, `error`,
`round`, `done`/`stopped`, `report`) to an optional TCP collector (plain
`ncat -l -k`, as the Alienware's :9099/:9100) and to `<app docs>/<run_id>.jsonl`.
The `report` line / `<run_id>.json` is a bench-report host result (schema 1:
host, commit, cpu, os, libraries, results[{operation, library, id, ns, ns_low,
ns_high, throughput}]) plus `device` (model, chip, OS, P/E cores, CPU
features) and `timing`. `ns` = median of per-round medians; `ns_low/high` =
min/max per-round median (not criterion's CI). `tools/import-device.py
CAPTURE --out DIR` splits a collector capture into one JSON per run.

## Build
- iOS (Mac, Xcode, rustup 1.98.1 + aarch64-apple-ios): `ios/build-ipa.sh 9101`
  (M4) / `ios/build-ipa.sh 9102` (A17 mini) → `ios/out/RindBenchAll-v14-<port>.ipa`, **unsigned**.
  Bundle id `com.kyledouglas.rindbench.all` (installs next to v13, not over it).
  OpenSSL is vendored (built from source) by default; `CARGO_FEATURES= ios/build-ipa.sh` leaves it out.
- Android (Linux, SDK build-tools 35 + platform 35 + NDK, JDK 17+, rustup aarch64-linux-android):
  `JAVA_HOME=… CARGO_FEATURES="--features __bench_openssl" android/build-apk.sh` →
  `android/out/RindBench-android.apk` (no Gradle; debug-key signed). arm64-v8a only.
- Host smoke: `cargo run --release --example devbench-cli -- catalog|run '<json>'`.

## Run
- iPad: sign + install with plumesign (Apple ID + 2FA), start `tools/listen-devbench.sh`
  on the Alienware, open "RindBench All", agree, Start.
- Android: `adb install -r RindBench-android.apk`; optional
  `adb reverse tcp:9101 tcp:9101` + a listener; or headless:
  `adb shell am start -n com.kyledouglas.rindbench/.MainActivity --es host 127.0.0.1 --ei port 9101 --es preset quick --es libraries rind,ring --es sections AEADs --ez autostart true`;
  results also in `/sdcard/Android/data/com.kyledouglas.rindbench/files/`.
