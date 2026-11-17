#!/usr/bin/env bash
# Times rind's Argon2 fills on this machine against the portable permutation
# and RustCrypto's argon2: every fill the CPU can run, 3 rounds interleaved.
# Linux (x86_64 or aarch64), macOS, or Termux on Android. Needs git, python3,
# a C compiler, and Rust (rustup, or Termux: `pkg install rust clang git python`).
#
#   curl -sSfLO https://raw.githubusercontent.com/steelhead99x/rind/wip/argon2-hosts/.github/argon2-measure/host-bench.sh
#   bash host-bench.sh
#
# Env: WORK (default ~/rind-work/argon2-hosts), ROUNDS (3), PIN_CPU (Linux;
# default the core with the highest max clock), BENCH_LOCK (a lock dir to
# take per round), INSTALL_RUST=1 (rustup into $HOME if cargo is missing).
set -euo pipefail
REPO=${REPO:-https://github.com/steelhead99x/rind.git}
WORK=${WORK:-$HOME/rind-work/argon2-hosts}
# The tree before NEON became the default: portable on aarch64, plus the
# gated NEON (SHA3 where the CPU has it) and plain NEON fills.
BASE_REV=52e0ed733b69c14253d1ffb5a8d310cd4c453a8d
PICK=wip/argon2-neon-pick   # aarch64 default: SHA3 on Apple, plain NEON elsewhere
TOOLS=wip/argon2-hosts

if ! command -v cargo >/dev/null; then
  if [ "${INSTALL_RUST:-}" = 1 ]; then
    curl -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal --no-modify-path
  fi
  [ -f "$HOME/.cargo/env" ] && . "$HOME/.cargo/env"
  command -v cargo >/dev/null || { echo "need cargo: rustup, or INSTALL_RUST=1" >&2; exit 1; }
fi
for t in git python3 cc; do command -v $t >/dev/null || { echo "need $t" >&2; exit 1; }; done

mkdir -p "$WORK" && cd "$WORK"
[ -d repo ] || git clone -q --filter=blob:none --no-checkout "$REPO" repo
git -C repo fetch -q origin "$PICK" "$TOOLS" quest/m4/protocols/argon2-simd
tree() {  # tree <dir> <rev>
  if [ -d "$1" ]; then git -C "$1" checkout -q --detach "$2"; else git -C repo worktree add -q --detach "$1" "$2"; fi
}
tree "$WORK/base" "$BASE_REV"
tree "$WORK/pick" origin/$PICK
tree "$WORK/tools" origin/$TOOLS
T=$WORK/tools/.github/argon2-measure

out=$WORK/out-$(date -u +%Y%m%dT%H%M%SZ); mkdir -p "$out"
arch=$(uname -m)
{
  echo "arch: $arch"; echo "os: $(uname -sr)"
  if [ "$(uname -s)" = Darwin ]; then
    echo "cpu: $(sysctl -n machdep.cpu.brand_string)"; echo "cpus: $(sysctl -n hw.ncpu)"
    sysctl hw.optional 2>/dev/null | grep -E 'sha3|sha512|dotprod|i8mm' || true
  else
    command -v getprop >/dev/null && echo "model: $(getprop ro.product.model) / $(getprop ro.soc.model)"
    if command -v lscpu >/dev/null; then lscpu | grep -E 'Model name|Vendor|^CPU\(s\)|MHz'; fi
    grep -m1 -E '^(Features|flags)' /proc/cpuinfo
  fi
  rustc -V
} | tee "$out/host.txt"

has() {
  if [ "$(uname -s)" = Darwin ]; then
    [ "$1" = sha3 ] && [ "$(sysctl -n hw.optional.armv8_2_sha3 2>/dev/null)" = 1 ]
  else grep -m1 -E '^(Features|flags)' /proc/cpuinfo | grep -qw "$1"; fi
}
spec=$out/specs.txt
case $arch in
  aarch64|arm64)
    echo "portable|$WORK/base||" > "$spec"
    if has sha3; then
      echo "plain-neon|$WORK/base|--cfg rind_argon2_neon --cfg rind_cpu_disable|RIND_CPU_DISABLE_sha3=1" >> "$spec"
      echo "sha3-neon|$WORK/base|--cfg rind_argon2_neon|" >> "$spec"
    else
      echo "plain-neon|$WORK/base|--cfg rind_argon2_neon|" >> "$spec"
    fi
    echo "pick|$WORK/pick||" >> "$spec" ;;
  x86_64)
    echo "portable|$WORK/pick|--cfg rind_cpu_disable|RIND_CPU_DISABLE_avx2=1" > "$spec"
    has ssse3 && echo "ssse3|$WORK/pick|--cfg rind_argon2_ssse3 --cfg rind_cpu_disable|RIND_CPU_DISABLE_avx2=1" >> "$spec"
    has avx2 && echo "avx2|$WORK/pick||" >> "$spec"
    has avx512f && echo "avx512|$WORK/pick|--cfg rind_argon2_avx512|" >> "$spec" ;;
  *) echo "unsupported arch $arch" >&2; exit 1 ;;
esac
cat "$spec"

if [ -z "${PIN_CPU+x}" ] && [ -d /sys/devices/system/cpu/cpu0/cpufreq ]; then
  PIN_CPU=$(for f in /sys/devices/system/cpu/cpu[0-9]*/cpufreq/cpuinfo_max_freq; do
    c=${f#/sys/devices/system/cpu/cpu}; echo "$(cat "$f") ${c%%/*}"; done | sort -n | tail -1 | cut -d' ' -f2)
fi
export PIN_CPU=${PIN_CPU:-}
echo "pin: ${PIN_CPU:-none}" | tee -a "$out/host.txt"

TARGET_BASE=$WORK/target "$T/run-specs.sh" "$out/bench" "$spec" 2>&1 | tee "$out/run.log"
python3 "$T/summary.py" "$out/bench" portable | tee "$out/summary.md"
echo; echo "Results: $out (send host.txt and summary.md)"
