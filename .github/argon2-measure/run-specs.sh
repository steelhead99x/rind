#!/usr/bin/env bash
# Builds each config once, then runs the argon2 bench ROUNDS times per config,
# rotating the order each round.
# Usage: run-specs.sh <outdir> <specfile>; spec lines: name|tree|rustflags|env
# (tree relative to the cwd or absolute; env a space-separated VAR=value list).
# SKIP_RUN=1 builds only; EXES=<file> reuses a build's name<TAB>exe list.
set -euo pipefail
out=$(mkdir -p "$1" && cd "$1" && pwd); spec=$2
rounds=${ROUNDS:-3}
tbase=${TARGET_BASE:-target}; [[ $tbase = /* ]] || tbase=$PWD/$tbase
declare -A exe envs
names=()
while IFS='|' read -r name tree flags env; do
  [ -z "$name" ] || [[ $name = \#* ]] && continue
  names+=("$name"); envs[$name]=$env
  printf '%s\t%s\t%s\t%s\n' "$name" "$tree" "$flags" "$env" >> "$out/configs.tsv"
  if [ -n "${EXES:-}" ]; then exe[$name]=$(awk -F'\t' -v n="$name" '$1==n{print $2}' "$EXES"); continue; fi
  echo "== build $name: tree=$tree RUSTFLAGS='$flags'"
  exe[$name]=$(cd "$tree" && RUSTFLAGS="$flags" CARGO_TARGET_DIR="$tbase-$name" \
    cargo bench -p rind-bench --bench argon2 --no-run --message-format=json \
    | python3 -c 'import sys,json
for l in sys.stdin:
    m=json.loads(l)
    if m.get("reason")=="compiler-artifact" and m.get("executable") and m["target"]["name"]=="argon2": print(m["executable"])' | tail -1)
  printf '%s\t%s\n' "$name" "${exe[$name]}" >> "$out/exes.tsv"
  echo "   -> ${exe[$name]}"
done < "$spec"
[ -n "${SKIP_RUN:-}" ] && exit 0
n=${#names[@]}
for ((r = 1; r <= rounds; r++)); do
  for ((i = 0; i < n; i++)); do
    c=${names[$(( (i + r - 1) % n ))]}
    dir="$out/$c/r$r"; mkdir -p "$dir"
    echo "== round $r: $c ($(date -u +%FT%TZ))"
    pin=(); [ -n "${PIN_CPU:-}" ] && command -v taskset >/dev/null && pin=(taskset -c "$PIN_CPU")
    # shellcheck disable=SC2086
    env CRITERION_HOME="$dir/criterion" ${envs[$c]} "${pin[@]}" "${exe[$c]}" --bench --noplot 2>&1 | tee "$dir/log.txt"
  done
done
