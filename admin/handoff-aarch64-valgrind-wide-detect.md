# Handoff: aarch64 ctgrind detects a narrow core as wide under valgrind

Status: draft handoff for an agent. Written against `perf/aarch64-narrow-dispatch`
at `ea45d7936f3d46b9e3e6ec7b3fe246e86c590881` (fork PR #82). No code is
changed here. Line numbers below are at that commit.

## Problem

On a Raspberry Pi 5 (Cortex-A76, `MIDR_EL1` implementer `0x41`, part `0xd0b`,
`AT_HWCAP` has `HWCAP_CPUID`), `wide_multiplier()` is `false` when run
natively, so the narrow schedules run. Under valgrind it returned `true`, so
`low::aarch64::cpu::tests::detects_the_expected_cpu` failed when
`RIND_TEST_ARM_WIDE_MUL=0` was set. Two consequences:

1. Any ctgrind pass on narrow hardware that does not force the schedule runs
   the `_alt` (wide) schedules, not the narrow ones the CPU runs natively.
2. `admin/ctgrind` runs under `set -e`. When the first `run_suites` fails,
   the script exits before the second, narrow pass at the bottom of the
   script, so the narrow schedules are never reached in that run.

## Environment and exact repro

Host: Raspberry Pi 5, aarch64 Linux, valgrind 3.24.0. Do not reuse
`~/.config/rind-pi5` or the Pi while another task has it; any aarch64 Linux
host with a Cortex-A72, A76, or Neoverse N1 core reproduces it.

The failing run's environment:

```sh
RUSTFLAGS="--cfg rind_cpu_disable"
VALGRIND_BUG_494162=1
RIND_TEST_ARM_CRYPTO_EXT=1
RIND_TEST_ARM_SHA3=0
RIND_TEST_ARM_SVE2=0
RIND_TEST_ARM_WIDE_MUL=0
```

Commands (from a checkout of `ea45d793`, in `nix develop .#ctgrind` where nix
exists; the Pi has no nix on its PATH, so its run used the host's own Rust
toolchain with valgrind 3.24.0):

```sh
# the whole script
admin/ctgrind unit

# or just the failing test, through the same runner
admin/ctgrind unit -- low::aarch64::cpu::tests::detects_the_expected_cpu
```

Control runs on the same Pi:

```sh
# native: passes, 172 tests in `low::aarch64::`
cargo test -p rind --lib --locked -- low::aarch64::
RIND_CPU_DISABLE_wide_mul=1 RIND_TEST_ARM_WIDE_MUL=0 \
    cargo test -p rind --lib --locked -- low::aarch64::   # passes

# under valgrind, forced wide: passes
RIND_CPU_FORCE_wide_mul=1 RIND_TEST_ARM_WIDE_MUL=1 admin/ctgrind unit
```

## Evidence

- Native run (`run1`): 172 `low::aarch64` tests passed, and `wide_multiplier()`
  was `false`.
- Under valgrind: 171 passed, 1 failed, 0 valgrind errors. The failure is
  `low::aarch64::cpu::tests::detects_the_expected_cpu` at
  `rind/src/low/aarch64/cpu.rs:589`, `assert_eq!(wide_multiplier(), expected == "1")`,
  with `left: true, right: false`.
- The forced-wide run under valgrind passed.
- Logs: on the Pi, `~/rind-pr82-hw/logs/ctgrind-a64-native.log` and
  `~/rind-pr82-hw/logs/ctgrind-a64-forcewide.log`. On the PC,
  `/tmp/rind-pr82-pi5/` if it still exists (it did not when this was
  written, so the lines above come from the run notes, not a re-read of the
  logs). First step for the agent: read the native log and check for the two
  discriminators under "Which run failed" below.

## What the code does

`rind/src/low/aarch64/cpu.rs`:

- `wide_multiplier()` (line 180) returns the cached `WIDE` choice, or calls
  `detect_wide_once()` (258) on the first call.
- `detect_wide_once()` applies `wide_toggle()` (252) to
  `detect_wide_multiplier()` (281). `wide_toggle` calls `feature_toggle`
  (460), where `RIND_CPU_DISABLE_wide_mul` wins over `RIND_CPU_FORCE_wide_mul`.
- `detect_wide_multiplier()` on Linux returns
  `read_midr().is_none_or(wide_from_midr)` (after the debug-only
  `midr_fixture()` at 307, which reads `RIND_TEST_MIDR`).
- `read_midr()` (320) returns `None` when `getauxval(AT_HWCAP) & HWCAP_CPUID`
  is 0. Otherwise it executes `mrs {}, midr_el1`, which Linux emulates.
- `wide_from_midr()` (347) is `!narrow_part(implementer, part)`, and
  `narrow_part()` (365) lists A72 `0xd08`, A76 `0xd0b`, N1 `0xd0c`.
- A missing `HWCAP_CPUID`, or any unrecognised part, returns wide on purpose.
  The doc comment on `detect_wide_multiplier` already says the `HWCAP_CPUID`
  gate exists "because valgrind cannot decode the register without it".

Tests: `detects_the_expected_cpu` (581) asserts the schedule only when
`RIND_TEST_ARM_WIDE_MUL` is set; `wide_mul_env_overrides` (640),
`detected_value_matches_midr` (821), `midr_fixture_selects_the_schedule`
(856), and `detection_opens_no_file` (880) cover the rest. The same test
already tolerates valgrind for SHA3 by having CI export
`RIND_TEST_ARM_SHA3=0`.

`admin/ctgrind`:

- Lines 194-221 are an aarch64 second pass. It captures
  `narrow_requested` (196), runs `run_suites` once (197), then, if the caller
  did not set `RIND_CPU_DISABLE_wide_mul` and the target is aarch64 and not
  portable, echoes `ctgrind: narrow multiplier (RIND_CPU_DISABLE_wide_mul=1)`,
  exports `RIND_CPU_DISABLE_wide_mul=1` and `RIND_TEST_ARM_WIDE_MUL=0`, adds
  `--cfg rind_cpu_disable` to `RUSTFLAGS`, and runs `run_suites` again.
- The first pass sets nothing for `wide_mul`. It inherits the caller's
  environment.
- `ctgrind.yml` (`build` job, lines 51-56) exports only
  `RIND_TEST_ARM_CRYPTO_EXT`, `RIND_TEST_ARM_SHA3`, and `RIND_TEST_ARM_SVE2`.
  It never sets `RIND_TEST_ARM_WIDE_MUL`, so CI's first pass asserts no
  schedule.
- `TESTING.md` (aarch64 narrow-multiplier row) documents this second pass as
  the narrow-schedule coverage.

So the "ctgrind checks only the wide schedules" worry is already answered in
part by the second pass at `ea45d793`. The gaps are in how the first pass is
set up and in what happens when it fails.

## Suspected cause, unconfirmed

Hypothesis A: valgrind 3.24.0 does not pass `HWCAP_CPUID` in `AT_HWCAP` (or
does not emulate the `MIDR_EL1` read), so `read_midr()` returns `None` and
`detect_wide_multiplier()` returns `true` by design. This matches the comment
in `detect_wide_multiplier`.

Which run failed. Two readings fit the report, and the log decides:

- Reading 1: the failure is the first pass, with the caller's environment
  exporting `RIND_TEST_ARM_WIDE_MUL=0` and no `RIND_CPU_DISABLE_wide_mul`.
  Then the log has no `ctgrind: narrow multiplier` banner and no
  `DEBUG: denying cpuid "wide_mul"` line. Valgrind returning wide there is
  expected under hypothesis A, and the bug is that the first pass should not
  assert narrow. The script then aborts before the second pass.
- Reading 2: the failure is in the second pass, where the script itself
  exported `RIND_CPU_DISABLE_wide_mul=1`. Then the log shows the banner and
  `DEBUG: denying cpuid "wide_mul"`, and `wide_multiplier()` still returned
  `true`. That would be a real bug in `feature_toggle` or `WIDE`
  caching under valgrind, not a detection problem, and is more serious.
  Look at it first.

## How to confirm

Add a throwaway probe (not committed), for example
`rind/examples/midr_probe.rs` or a standalone `rustc` file:

```rust
fn main() {
    let hwcap = unsafe { libc::getauxval(libc::AT_HWCAP) };
    println!("AT_HWCAP = {hwcap:#x}");
    println!("HWCAP_CPUID set = {}", hwcap & libc::HWCAP_CPUID != 0);
    if hwcap & libc::HWCAP_CPUID != 0 {
        let midr: u64;
        unsafe { core::arch::asm!("mrs {}, midr_el1", out(reg) midr) };
        println!("MIDR_EL1 = {midr:#x} (implementer {:#x}, part {:#x})",
                 (midr >> 24) & 0xff, (midr >> 4) & 0xfff);
    }
}
```

Run it natively and under valgrind with the same flags `admin/ctgrind` uses:

```sh
./midr_probe
valgrind --error-exitcode=99 ./midr_probe
```

Expected natively on a Pi 5: `HWCAP_CPUID set = true`, `MIDR_EL1 = 0x414fd0b1`
(implementer `0x41`, part `0xd0b`). Record the three outcomes under valgrind:

1. `HWCAP_CPUID` clear: valgrind hides the bit (hypothesis A, expected).
2. `HWCAP_CPUID` set and the read returns a value: detection works, so
   reading 2 above is the bug.
3. `HWCAP_CPUID` set and the `mrs` dies with SIGILL: valgrind advertises the
   bit but cannot decode the read, which is worse (a crash, not a wrong
   answer). Commit `fd7f34da` ("check the narrow schedules and survive
   SIGSYS") touched nearby handling; read it first.

Also run the first-pass and second-pass logs through
`grep -n 'narrow multiplier\|denying cpuid\|detects_the_expected_cpu'`.

## Fix options

1. Make detection under valgrind deterministic and documented. Detection
   cannot see the part under valgrind, so say so: add an `UPSTREAM.md` entry
   ("Valgrind hides `HWCAP_CPUID`", with Breaks, Reproduce, Workaround,
   Reported, Goes when, like its neighbours) and a comment on
   `detect_wide_multiplier`. Does not fix the coverage gap by itself.
2. Make `admin/ctgrind` on aarch64 run both families explicitly, regardless
   of what valgrind reports: a forced-wide pass
   (`RIND_CPU_FORCE_wide_mul=1`, `RIND_TEST_ARM_WIDE_MUL=1`) and the existing
   forced-narrow pass (`RIND_CPU_DISABLE_wide_mul=1`,
   `RIND_TEST_ARM_WIDE_MUL=0`), each setting `RIND_TEST_ARM_WIDE_MUL` to the
   schedule it forces, and neither inheriting a caller's value. Each needs
   `--cfg rind_cpu_disable` in `--release` builds. Skip both on
   `rind_portable` as the current pass does, and keep the fips suite on
   disable only (the module honours no force, see `wide_toggle`'s doc
   comment). Make the first pass `unset RIND_TEST_ARM_WIDE_MUL` unless the
   caller passes `RIND_CPU_FORCE_wide_mul`/`RIND_CPU_DISABLE_wide_mul`, so a
   leftover value from a native run cannot fail it. Also make a failure in
   the first pass not skip the second: run both passes and exit non-zero if
   either failed, so one log shows both families.
3. Relax the test under valgrind, as SHA3 is handled. Do it by environment,
   not by sniffing valgrind: CI already exports `RIND_TEST_ARM_SHA3=0` to say
   what valgrind shows, so a first pass that must not assert narrow simply
   leaves `RIND_TEST_ARM_WIDE_MUL` unset, which `detects_the_expected_cpu`
   (581) already tolerates. Do not add `RUNNING_ON_VALGRIND` detection to
   the test, which would let a real detection regression pass.

Recommendation: (2) with the `unset`/run-both-passes details, plus (1) as
documentation once the probe says why. (3) falls out of (2): the test needs
no change if the script stops exporting a stale `RIND_TEST_ARM_WIDE_MUL`. Do
not weaken the assertion at line 589.

## Acceptance criteria

- `admin/ctgrind` passes on a Raspberry Pi 5 (Cortex-A76) and on CI's
  `ubuntu-24.04-arm` row of `ctgrind.yml`.
- Under valgrind, both schedule families run in one invocation: the `_alt`
  schedules (forced wide, `RIND_TEST_ARM_WIDE_MUL=1`) and the narrow ones
  (forced narrow, `RIND_TEST_ARM_WIDE_MUL=0`), each asserted by
  `detects_the_expected_cpu`, and the log names each pass.
- A failure in one pass still runs the other, and the script exits non-zero.
- A stale `RIND_TEST_ARM_WIDE_MUL` in the caller's environment cannot fail an
  unforced pass.
- The probe's results are recorded in `UPSTREAM.md` (or in the PR), naming
  which of the three outcomes happened and the valgrind version.
- `TESTING.md`'s aarch64 narrow-multiplier row still matches the script.
- `just ci` passes, and `low::aarch64::cpu::tests` is unchanged except for
  anything the probe shows is needed.

## Out of scope

Native detection (it is correct on the Pi), the choice of narrow parts in
`narrow_part`, and the Lean composition of the narrow schedules.
