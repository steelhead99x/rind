# rind-devbench — RindBench "All" for iPad/iPhone and Android

A standalone crate (own `[workspace]`), not a member of rind's workspace.

rind-bench's bench files as they were written for criterion, compiled
unchanged as modules of one library, with `criterion` replaced by a tiny shim
(`criterion-shim/`) that either lists each row's criterion ID or times it. So
the app times **every library × every operation bench-report has**, under the
same IDs (`ed25519-verify/aws-lc-rs`, `aes128-gcm/rind/16KB`, …).

rind-bench moved its benches to swole (kixel-ai/rind#1141), whose
`#[bench]` functions this shim cannot run, so `criterion-benches/` keeps the
last criterion files: fork main's before that merge (741e32ae), merged with
upstream's last criterion versions (84e2aa83), with their `criterion/`,
`ossl_aead/`, and `ossl_ec/` modules. The swole files keep the
same row IDs. Until the app runs swole's benches itself, a row rind-bench adds
reaches the app only by being copied here. The op list (`src/ops.rs`) is
generated from `admin/bench-report` by `tools/gen-ops.py` (`--check` reports drift; not wired into CI yet).

Data-driven: the app asks the core for its catalog (rows → op, section,
library), shows libraries and sections as chips, and passes the picks back
as JSON. Report operations are on by default; rind-bench's other rows
(SLH-DSA, PBKDF2, AES-KW/KWP, AES-CBC/CTR, JWT, RSA 3072–8192 loads, extra
sizes, …) are its "More: <file>" groups, which share one "+ N more groups"
chip, off by default.

One screen, no scrolling, on both platforms: a header (device, rind commit,
where results go), the picker and run controls, and a run panel with a
progress bar, "rind fastest on X of Y" and the operations where another
library is faster, worst first, as many as fit. Wide screens put the picker
and the run panel side by side. On a phone too short for every chip, iOS or
Android, the picker's chips scroll inside its card, so none is out of reach;
the rest of the screen stays put. Every row's full timings still go to the
collector and to the device's files.

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
  → `ios/out/RindBenchAll-v15.0-<port>.ipa`, **unsigned**.
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
  the collector fills itself in (127.0.0.1:9103 via `adb reverse`, else the LAN address given to build-apk.sh as `COLLECTOR_HOST`); headless, from an APK built with
  `DEVICE_RUNNER=1 android/build-apk.sh` (a normal build ignores `autostart`, `host` and `port`, since any app on the phone can start the launcher):
  `adb shell am start --activity-single-top -n io.github.steelhead99x.rindbench/.MainActivity --es preset quick --es libraries rind,ring --es sections AEADs --ez autostart true`;
  results also in `/sdcard/Android/data/io.github.steelhead99x.rindbench/files/`.
- iPad/iPhone headless (the same choices as Android's extras, as launch arguments):
  `xcrun devicectl device process launch --console --device UDID io.github.steelhead99x.rindbench.all -preset quick -libraries rind,ring -sections AEADs -autostart YES [-host H -port P]`.
  `-host`/`-port` override the collector baked in at build time.

## Device runners
Both apps support an unattended run with no one looking at the screen (on Android, only a `DEVICE_RUNNER=1` build):
- `autostart` waits 3 s after the list of tests loads, so a runner can capture the picker before the run starts.
  On iOS an autostart prints the same `RINDBENCH_RUN` lines on stderr, which `devicectl … --console` shows: `started:true` (with `start`) or `started:false` with the reason, then the `selected` line or a refusal once listed (`after_start`).
  On Android each launch with `autostart` starts one run, also when the app is already open (it arrives as a new intent) or a run has finished (its results are cleared first). Such a launch shows the Bench tab, and one that brings the app back from the background starts once the app is on screen. A launch is dropped, not queued, when a run is going; leaving the app or the Bench tab before the run starts cancels it. Restoring the activity never starts a run. A later autostart launch picks its libraries and groups as a first launch does, so one that names none runs the defaults, not the last run's choice.
- At each screen state (`ready`, `run`, `done`), the app logs one line:
  `RINDBENCH_LAYOUT {"phase":"ready","w":390,"h":844,"wide":false,"folded":false,"fits":true,"clipped":[]}`.
  On Android it goes to logcat with tag `RindBench`. On iOS it goes to stderr (seen with `devicectl … --console`) and the device log.
  `w` and `h` are in points (iOS) or dp (Android).
- `fits` is false when the run controls are cut off or off screen, or when the run panel can't show its status or score. `"picker"` in `clipped` means some chips are out of view (they scroll inside the picker), which a short screen allows.
  On Android the library and group pickers open in sheets, so `folded` is always true and `clipped` never names `"picker"`; `"score"` there is the results preview, and `"status"` the status card, either out of view in its scrolling pane.
- On Android, each run that starts logs `RINDBENCH_RUN {"started":true,"start":N,"preset":…,"libraries":[…],"sections":[…],"host":…,"port":…}` on tag `RindBench` as the start is accepted, with the libraries and groups asked for, so a runner can check that a launch ran its own selection. Once the library has picked the run's rows it logs `RINDBENCH_RUN {"selected":true,"start":N,"libraries":[…],"libraries_missing":[…],"sections":[…],"sections_missing":[…]}` under the same start number: `libraries` and `sections` are the ones the run takes rows from, and the `_missing` ones those asked for that it takes no row from, either because the list has none (a misspelt name, or TLS after a keys copy that failed) or because the libraries and groups picked share none. The process logs that line, not the screen, so it comes once per start even if the activity is gone by then (as with "Don't keep activities"). The native status carries the same as `run_start`, `libraries_run`, `libraries_missing`, `sections_run` and `sections_missing`, and each status a start writes carries its number as `acked_start`. A start that doesn't happen logs `RINDBENCH_RUN {"started":false,"reason":…}`, so each autostart launch gets exactly one outcome: the list hasn't loaded or couldn't be read, consent isn't given, no library or group is picked, the native start refused it, with its reason (as when a launch names no library or group that exists, or the libraries and groups picked, each valid alone, match no test together), a run is going, the Bench tab isn't shown, the app or the Bench tab was left before the run started, or a later launch or a start by hand replaced it while it waited, or a later launch without `autostart` changed its collector.
  `--activity-single-top` delivers a launch to the app when it is already open; without it Android only brings the app forward and the launch is lost. A launch without `host` sends to the USB or built-in collector, not an earlier launch's `host`; one whose `host` is blank or not a string keeps the collector as it is.
  A start the library can only check once it has listed the tests on the run's thread (after a list that failed in part, such as a keys copy that failed) logs `started:true` and, if nothing matched, then `RINDBENCH_RUN {"started":false,"start":N,"reason":…,"after_start":true}` in place of the `selected` line, which ends that launch (the process logs it too, once); no line reaches the collector for it. An autostart passes its launch's `libraries` and `sections` to the native start as given, not as the picker shows them, so a group the picker left out after a list that failed in part still gets that check; a launch without `host` probes the collector again, USB first, and the autostart waits for the probe to answer before it starts.
  A runner launch without `preset` runs Quick, as a fresh process does, whatever the last run picked.
- The run itself ends with a `done` or `stopped` line at the collector; a start refused after `started:true` sends none (see above).

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
