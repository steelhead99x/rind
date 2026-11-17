#!/usr/bin/env bash
# Builds each Argon2 fill configuration once, then runs the argon2 bench for
# every configuration, ROUNDS times, rotating the order each round.
# Usage: run.sh <outdir> <config>...   configs: default neon neon-plain
#        portable ssse3 avx512, and base: the default build of $BASE_TREE.  ROUNDS (default 3), PIN_CPU (Linux taskset).
set -euo pipefail
out=$(mkdir -p "$1" && cd "$1" && pwd); shift
configs=("$@")
rounds=${ROUNDS:-3}
tbase=${TARGET_BASE:-target}; [[ $tbase = /* ]] || tbase=$PWD/$tbase
flags() {
  case $1 in
    default|base) echo "" ;;
    neon) echo "--cfg rind_argon2_neon" ;;
    neon-plain) echo "--cfg rind_argon2_neon --cfg rind_cpu_disable" ;;
    portable) echo "--cfg rind_cpu_disable" ;;
    ssse3) echo "--cfg rind_argon2_ssse3 --cfg rind_cpu_disable" ;;
    avx512) echo "--cfg rind_argon2_avx512" ;;
    *) echo "unknown config $1" >&2; exit 1 ;;
  esac
}
envs() {
  case $1 in
    neon-plain) echo "RIND_CPU_DISABLE_sha3=1" ;;
    portable|ssse3) echo "RIND_CPU_DISABLE_avx2=1" ;;
    *) echo "" ;;
  esac
}
declare -A exe
for c in "${configs[@]}"; do
  echo "== build $c: RUSTFLAGS='$(flags "$c")'"
  tree=.; [ "$c" = base ] && tree=${BASE_TREE:?BASE_TREE names the base checkout}
  exe[$c]=$(cd "$tree" && RUSTFLAGS="$(flags "$c")" CARGO_TARGET_DIR="$tbase-$c" \
    cargo bench -p rind-bench --bench argon2 --no-run --message-format=json \
    | python3 -c 'import sys,json
for l in sys.stdin:
    m=json.loads(l)
    if m.get("reason")=="compiler-artifact" and m.get("executable") and m["target"]["name"]=="argon2": print(m["executable"])' | tail -1)
  echo "   -> ${exe[$c]}"
  printf '%s\t%s\t%s\n' "$c" "$(flags "$c")" "$(envs "$c")" >> "$out/configs.tsv"
done
n=${#configs[@]}
for ((r = 1; r <= rounds; r++)); do
  for i in $(seq 0 $((n - 1))); do
    c=${configs[$(( (i + r - 1) % n ))]}
    dir="$out/$c/r$r"; mkdir -p "$dir"
    echo "== round $r: $c ($(date -u +%FT%TZ))"
    pin=(); [ -n "${PIN_CPU:-}" ] && command -v taskset >/dev/null && pin=(taskset -c "$PIN_CPU")
    # shellcheck disable=SC2046
    env CRITERION_HOME="$dir/criterion" $(envs "$c") "${pin[@]}" "${exe[$c]}" --bench --noplot 2>&1 | tee "$dir/log.txt"
  done
done
