#!/usr/bin/env bash
# Build pyrind's wheel and run its tests, or its benchmarks, against it.
#
# Usage: sh/python.sh test|bench [ARGS...]
# The tests need pyca/cryptography, the differential oracle, mypy, pytest,
# and the Wycheproof submodule. They cover pyrind, then pyrind-cryptography,
# then pyjwt's and joserfc's own suites run on pyrind-cryptography, from the
# releases the dev shell pins (PYJWT_SRC and JOSERFC_SRC). The benchmarks
# compare against cryptography, hashlib, and hmac. ARGS go to unittest or
# the benchmark script.
set -euo pipefail

usage="usage: sh/python.sh test|bench [ARGS...]"
action=${1:?$usage}
shift

cd "$(git rev-parse --show-toplevel)"
root=$PWD

out=$(cargo metadata --format-version 1 --no-deps | jq -r .target_directory)/pyrind
rm -rf "$out"
maturin build --release --quiet --manifest-path rind-python/Cargo.toml --out "$out/wheel"
# A wheel is a zip of the installed package, so unpacking it is installing it
# without pip.
python3 -m zipfile -e "$out"/wheel/pyrind-*.whl "$out/site"

# Runs the pytest suite of the project at $2, named $1, on
# pyrind-cryptography: a copy whose `cryptography` imports name it instead,
# skipping the tests rind-python/cryptography/compat/$1.txt lists as needing
# what rind lacks.
compat() {
    local name=$1 src=$2 dir="$out/compat/$1" line args=()
    cp -r "$src" "$dir"
    chmod -R u+w "$dir"
    find "$dir" -name '*.py' -exec sed -i -E \
        -e 's/\bfrom cryptography([. ])/from pyrind_cryptography\1/' \
        -e 's/^(\s*)import cryptography$/\1import pyrind_cryptography as cryptography/' {} +
    while IFS= read -r line; do
        case "$line" in
            '' | '#'*) ;;
            *::*) args+=(--deselect "$line") ;;
            *) args+=(--ignore "$line") ;;
        esac
    done <"rind-python/cryptography/compat/$name.txt"
    (cd "$dir" && PYTHONPATH="$out/site:$root/rind-python/cryptography:$dir:$dir/src" \
        python3 -m pytest --quiet -p no:cacheprovider "${args[@]}" tests)
}

case "$action" in
    test)
        # The tests take pyrind from PYTHONPATH, never resolving
        # pyrind-cryptography's requirement, so a release PR bumping pyrind
        # past it would pass here and only fail release.yml once merged.
        version=$(PYTHONPATH="$out/site" python3 -c 'from importlib.metadata import version; print(version("pyrind"))')
        state=$(python3 rind-python/cryptography/pin.py "$version")
        if [[ "$state" == past ]]; then
            echo "error: pyrind $version is past pyrind-cryptography's pyrind requirement" >&2
            exit 1
        fi
        PYTHONPATH="$out/site" python3 -m unittest discover --start-directory rind-python/tests "$@"
        # Checks the type stubs against the built module.
        (cd "$out/site" && python3 -m mypy.stubtest pyrind)
        PYTHONPATH="$out/site:rind-python/cryptography" python3 -m unittest discover --start-directory rind-python/cryptography/tests
        mkdir "$out/compat"
        compat pyjwt "${PYJWT_SRC:?run in the dev shell}"
        compat joserfc "${JOSERFC_SRC:?run in the dev shell}"
        ;;
    bench) PYTHONPATH="$out/site" python3 rind-python/bench/bench.py "$@" ;;
    *)
        echo "$usage" >&2
        exit 2
        ;;
esac
