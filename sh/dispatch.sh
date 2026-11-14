#!/usr/bin/env bash
# Run `just check`, `just fix`, or `just ci` over one resolved branch diff.
# `--query` prints the selection before CI installs its toolchain and caches.
set -euo pipefail

usage="usage: sh/dispatch.sh check|fix|ci [BASE|--all] [--query]"
action=${1:?$usage}
base=${2:-}
query=${3:-}
if [[ $# -gt 3 || (-n "$query" && "$query" != --query) ]]; then
    echo "$usage" >&2
    exit 2
fi
case "$action" in
    check | fix | ci) ;;
    *)
        echo "$usage" >&2
        exit 2
        ;;
esac

# A host toolchain may differ from CI's pinned one. This flake's dev shell sets
# IN_RIND_DEV_SHELL.
if [[ -z "$query" && -z "${IN_RIND_DEV_SHELL:-}" && -z "${ALLOW_HOST_TOOLCHAIN:-}" ]]; then
    echo "error: run inside the Nix dev shell ('nix develop' or direnv) so tools match CI" >&2
    echo "       or set ALLOW_HOST_TOOLCHAIN=1 to use the host toolchain anyway" >&2
    exit 1
fi

cd "$(git rev-parse --show-toplevel)"

changed=$(mktemp)
trap 'rm -f "$changed"' EXIT

all=
if [[ "$base" == --all ]]; then
    all=1
else
    sh/changed.sh "$base" >"$changed"

    # These files hold the map and the recipes that call it, and match no
    # module, so a change to them would otherwise validate none of it.
    if grep -qE '^(justfile|sh/(dispatch|changed|select)\.sh)$' "$changed"; then
        echo "$action: root orchestration changed; running everything." >&2
        all=1
    fi
fi

# The impact map: a module is in scope when a changed path matches its
# pattern. An empty pattern is a repository-wide lint that runs on every diff.
declare -A scope=(
    # sh/select.sh narrows this to the changed crates and their dependents.
    [rs]='^(rind[^/]*/|fuzz/|thirdparty/|Cargo\.(toml|lock)$|\.rustfmt(\.unstable)?\.toml$)'
    # Advisories, licenses, and sources move with any manifest or the policy.
    # rind's low, mid, and high layers reference only the layers below them.
    [structure]='^(rind/(src/|Cargo\.toml$)|admin/structure$)'
    [deny]='(^|/)Cargo\.(toml|lock)$|^deny\.toml$'
    # An adapter's manifest holds both its version and its upstream requirement.
    [versions]='^(rind-[^/]+/Cargo\.toml$|sh/adapter-versions\.sh$)'
    [license]='^(rind/src/|rind/LICENSE$|rind-python/LICENSE$|admin/scan-license$)'
    # Dependents may build with the workspace's declared rust-version.
    [msrv]='^(rind[^/]*/|fuzz/|Cargo\.(toml|lock)$|flake\.(nix|lock)$)'
    # rind's aarch64, armv7, portable, and wasm32 builds, which the host's
    # own build skips, and which a toolchain bump can break.
    [cross]='^(rind/(src/|tests/|Cargo\.toml$|build\.rs$)|Cargo\.(toml|lock)$|flake\.(nix|lock)$)'
    # Variable-time instructions in rind's release builds, which a change to
    # its code, dependencies, toolchain, or the scan itself can bring.
    [vartime]='^(rind/(src/|Cargo\.toml$|build\.rs$)|Cargo\.(toml|lock)$|flake\.(nix|lock)$|admin/ct-vartime)'
    # s2n-bignum's proofs assume separate input and output, so the kernels
    # rind runs in place are walked, after planting faults in each.
    [inplace]='^(rind/src/low/|admin/parse-asm/)'
    # .cargo/mutants.toml's exclusions name mutants by file, line, and
    # function, so moving code can leave one matching nothing.
    [mutants]='^(rind[^/]*/src/|\.cargo/mutants\.toml$|admin/mutants$)'
    # TESTING.md's table names every export, test, and vector file.
    [testing]='^(TESTING\.md$|admin/testing$|rind/(src|tests)/|fuzz/)'
    # COMPATIBILITY.md is generated from the CPU scans.
    [compat]='^(COMPATIBILITY\.md$|admin/x86-cpus?(/|$))'
    # BENCHMARKS.md is generated from the results, the verified-code table,
    # and the gap decisions, which link the quests that close them.
    [bench]='^(BENCHMARKS\.md$|benchmarks/|admin/bench-report|quest/)'
    # admin/build-cost builds these against rind's API, so they break with it.
    [fixtures]='^(rind/|rind-rustls/|Cargo\.toml$|admin/build-cost-fixtures/(rind|rustls)/)'
    # The fixture builds this checkout's rind-ring under the rind-patch shim.
    [patch]='^(patch/|rind-ring/|(rind/)?Cargo\.toml$|sh/patch\.sh$)'
    # pyrind's Python tests and type stubs, against its built wheel, and
    # pyrind-cryptography's, with pyjwt's and joserfc's suites, which the lock
    # pins. rind's own changes reach them in the nightly wheels workflow
    # instead.
    [py]='^(rind-python/|sh/python\.sh$|flake\.lock$)'
    # rind-dart's Dart package, whose build hook compiles the crate.
    [dart]='^rind-dart/'
    # Quest documents form one graph, so any change validates the whole tree,
    # as does a bump of the flake-pinned validator.
    [quest]='^(quest/|flake\.lock$)'
    # alert.yml must watch every workflow that runs outside a pull request, and
    # every third-party action must be pinned.
    [gh]='^(\.github/|sh/(alert|pins)\.sh$)'
    [shell]=''
    [nix]=''
)

# The tools each module needs, or a `verb:module` entry's tools for that verb.
# A module missing one is skipped locally; under CI_STRICT (CI) it is an error,
# since there a skip is indistinguishable from a pass.
declare -A tools=(
    [rs]='cargo jq'
    [check:rs]='cargo cargo-nextest jq rustfmt-unstable'
    [fix:rs]='cargo jq rustfmt-unstable'
    [structure]='cargo cargo-modules'
    [deny]='cargo-deny'
    [versions]='cargo jq'
    [license]='find grep'
    [msrv]='nix cargo jq'
    [cross]='cargo'
    [vartime]='nix'
    [inplace]='python3'
    [mutants]='cargo-mutants python3'
    [testing]='python3'
    [compat]='python3'
    [bench]='python3'
    [fixtures]='cargo'
    [patch]='cargo jq git'
    [py]='cargo jq maturin python3'
    [dart]='nix'
    [quest]='quest'
    [gh]='actionlint yq jq'
    [shell]='shellcheck'
    [nix]='nixfmt'
)

verb=$action
[[ "$verb" != ci ]] || verb=check

case "$verb" in
    check) modules=(rs structure msrv cross vartime deny versions license inplace mutants testing compat bench fixtures patch py dart quest gh shell nix) ;;
    fix) modules=(rs compat patch dart nix) ;;
esac

selected=()
missing=()
for module in "${modules[@]}"; do
    pattern=${scope[$module]}
    if [[ -z "$all" && -n "$pattern" ]] && ! grep -qE "$pattern" "$changed"; then
        continue
    fi
    # Selection must not depend on the tools setup has yet to install.
    if [[ -n "$query" ]]; then
        selected+=("$module")
        continue
    fi
    absent=()
    for tool in ${tools[$verb:$module]-${tools[$module]}}; do
        command -v "$tool" >/dev/null 2>&1 || absent+=("$tool")
    done
    if ((${#absent[@]} == 0)); then
        selected+=("$module")
    elif [[ -n "${CI_STRICT:-}" ]]; then
        missing+=("${absent[@]}")
    else
        echo "$action: skipping $module; missing ${absent[*]}" >&2
    fi
done

# A query runs on the host before Nix is installed.
if [[ -n "$query" ]]; then
    needed=false
    rust=false
    for module in "${selected[@]}"; do
        needed=true
        [[ "$module" != rs ]] || rust=true
    done
    echo "needed=$needed"
    echo "rust=$rust"
    exit
fi

if ((${#missing[@]} > 0)); then
    echo "error: missing tools under CI_STRICT: ${missing[*]}" >&2
    exit 1
fi

# The portable backend, forced on a target; an explicit target keeps its
# builds apart from the host's, and its build scripts unflagged.
portable='--cfg rind_portable --cfg curve25519_dalek_backend="serial"'

# Tracked files matching a pathspec, NUL-separated.
files() {
    git ls-files -z -- "$@"
}

for module in "${selected[@]}"; do
    echo "==> $action $module" >&2
    case "$verb:$module" in
        check:rs)
            # The tests read these vectors, and otherwise fail partway through.
            # s2n-bignum only feeds admin/parse-asm, so it is not required.
            # Only uninitialized ones, so a local submodule bump stays put.
            mapfile -t unfetched < <(git submodule status -- thirdparty/cavp thirdparty/cctv thirdparty/wycheproof | sed -n 's/^-[0-9a-f]* //p')
            if ((${#unfetched[@]} > 0)); then
                git submodule update --init --depth 1 -- "${unfetched[@]}"
            fi
            mapfile -t packages < <(sh/select.sh "$changed" "$all")
            cargo fmt --all --check
            RUSTFMT=rustfmt-unstable cargo fmt --all --check -- --config-path=.rustfmt.unstable.toml
            cargo clippy "${packages[@]}" --all-targets --locked -- --deny warnings
            # nextest runs the test binaries in parallel but not doc tests. Like
            # `cargo test`, it passes a selection with no tests, such as the
            # benches alone.
            cargo nextest run "${packages[@]}" --locked --no-tests=warn
            # Only the zeroing and heap scratch tests see the opt-in wipe,
            # which the default build turns into no-ops.
            if ((${#packages[@]} == 0)) || printf '%s\n' "${packages[@]}" | grep -qxE 'rind|--workspace'; then
                cargo nextest run -p rind --features wipe,__acvp --test zeroing --test heap_scratch --locked
            fi
            if ((${#packages[@]} == 0)) || printf '%s\n' "${packages[@]}" | grep -qxE 'rind-aws-lc-rs|--workspace'; then
                cargo nextest run -p rind-aws-lc-rs --features wipe --test zeroing --locked
            fi
            # The FIPS module's own code compiles only under its cfg, which a
            # workspace build leaves off, and only for glibc Linux on x86_64
            # and aarch64, where rind-fips is not empty. Its break build
            # checks, on every call, the stack each service zeroes, and fails
            # each self-test.
            if printf '%s\n' "${packages[@]}" | grep -qxE 'rind-fips|--workspace' &&
                [[ "$(rustc -vV | sed -n 's/^host: //p')" =~ ^(x86_64|aarch64)-unknown-linux-gnu$ ]]; then
                RUSTFLAGS='--cfg rind_fips --cfg rind_cpu_disable' cargo clippy -p rind-fips-module \
                    --locked --target-dir target/fips-module -- --deny warnings
                if [[ -n "$all" ]] || grep -q '^rind-fips/' "$changed"; then
                    cargo nextest run -p rind-fips --features __break_tests --locked
                fi
            fi
            # Doc tests need a library. No packages at all means the workspace.
            mapfile -t libs < <(sh/select.sh "$changed" "$all" --lib)
            if ((${#libs[@]} > 0 || ${#packages[@]} == 0)); then
                cargo test "${libs[@]}" --locked --doc
            fi
            ;;
        fix:rs)
            mapfile -t packages < <(sh/select.sh "$changed" "$all")
            cargo fmt --all
            RUSTFMT=rustfmt-unstable cargo fmt --all -- --config-path=.rustfmt.unstable.toml
            cargo clippy "${packages[@]}" --all-targets --fix --allow-dirty --allow-staged
            ;;
        # Plain `cargo check` covers the lib and bin targets, all a dependent
        # builds.
        check:msrv)
            mapfile -t packages < <(sh/select.sh "$changed" "$all")
            # An adapter whose upstream needs a newer Rust declares that
            # rust-version instead, which its users need anyway, so it is
            # left out.
            mapfile -t newer < <(cargo metadata --format-version 1 --no-deps --locked |
                jq -r '(.packages[] | select(.name == "rind") | .rust_version) as $v | .packages[] | select(.rust_version != $v) | .name')
            args=()
            for ((i = 0; i < ${#packages[@]}; i++)); do
                if [[ "${packages[i]}" == -p ]]; then
                    i=$((i + 1))
                    if ! printf '%s\n' "${newer[@]}" | grep -qxF "${packages[i]}"; then
                        args+=(-p "${packages[i]}")
                    fi
                elif [[ "${packages[i]}" == --workspace ]]; then
                    args+=(--workspace)
                    for name in "${newer[@]}"; do
                        args+=(--exclude "$name")
                    done
                fi
            done
            if [[ ${#args[@]} -gt 0 ]]; then
                nix develop .#msrv --command cargo check "${args[@]}" --locked
            fi
            for target in aarch64-unknown-linux-gnu armv7-unknown-linux-gnueabihf i686-unknown-linux-gnu; do
                nix develop .#msrv --command cargo check -p rind -p rind-rustls --lib --locked --target "$target"
            done
            ;;
        check:cross)
            # The tests too, in the shells whose C toolchain builds their
            # aws-lc-rs dev-dependency, so test code that only these targets
            # compile is checked before it lands. aarch64 in release, as
            # sh/qemu.sh explains: nixpkgs' cross gcc fails aws-lc's -O0 probes.
            # Those shells are Linux-only, so elsewhere the library alone.
            if [[ $(uname -s) == Linux ]]; then
                nix develop .#aarch64 --command cargo clippy -p rind --all-targets --locked --release \
                    --target aarch64-unknown-linux-gnu -- --deny warnings
                nix develop .#armv7 --command cargo clippy -p rind --all-targets --locked \
                    --target armv7-unknown-linux-gnueabihf -- --deny warnings
            else
                for target in aarch64-unknown-linux-gnu armv7-unknown-linux-gnueabihf; do
                    cargo clippy -p rind --lib --locked --target "$target" -- --deny warnings
                done
            fi
            # The FIPS module's source rides along: its cfg touches only where
            # randomness comes from, which no backend changes.
            CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="$portable --cfg rind_fips" \
                cargo clippy -p rind --lib --locked --target x86_64-unknown-linux-gnu -- --deny warnings
            # And on a 32-bit target, whose Poly1305 and GHASH differ.
            CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUSTFLAGS="$portable" \
                cargo clippy -p rind --lib --locked --target armv7-unknown-linux-gnueabihf -- --deny warnings
            # wasm32 compiles on the portable backend; the browser target
            # needs getrandom's JavaScript source, WASI has its own.
            for features in "" wipe; do
                cargo clippy -p rind --lib --locked --target wasm32-wasip2 --features "$features" -- --deny warnings
                cargo clippy -p rind --lib --locked --target wasm32-unknown-unknown \
                    --features "$features,getrandom/wasm_js" -- --deny warnings
            done
            ;;
        check:structure) admin/structure ;;
        check:vartime) nix develop .#ct-vartime --command admin/ct-vartime ;;
        check:deny) cargo deny --locked check ;;
        check:versions) sh/adapter-versions.sh ;;
        check:quest) quest check ;;
        check:license) bash admin/scan-license ;;
        check:mutants) admin/mutants --pins ;;
        # It finds the generated kernels relative to its own directory.
        check:inplace) (cd admin/parse-asm && python3 inplace.py) ;;
        check:testing) python3 admin/testing ;;
        check:compat) python3 admin/x86-cpu markdown-table | diff -u COMPATIBILITY.md - ;;
        fix:compat) python3 admin/x86-cpu markdown-table >COMPATIBILITY.md ;;
        check:bench)
            python3 admin/bench-report-test
            python3 admin/bench-report render --check
            ;;
        # Each fixture is its own workspace and resolves its own lockfile.
        check:fixtures)
            cargo check --manifest-path admin/build-cost-fixtures/rind/Cargo.toml --target-dir target
            cargo check --manifest-path admin/build-cost-fixtures/rustls/Cargo.toml --features rind --target-dir target
            ;;
        check:patch) sh/patch.sh ;;
        check:py) sh/python.sh test ;;
        check:dart) nix develop .#dart --command sh/dart.sh check ;;
        fix:dart) nix develop .#dart --command sh/dart.sh fix ;;
        fix:patch) cargo fmt --manifest-path patch/fixture/Cargo.toml ;;
        check:gh)
            actionlint
            # See queue-build.yml: main's copy runs against every group's tree.
            if grep -nE '^[[:space:]]*(-[[:space:]]*)?uses:[[:space:]]*\./' .github/workflows/queue-build.yml; then
                echo "error: queue-build.yml must use no local action; put the setup in \`just ci\`" >&2
                exit 1
            fi
            sh/alert.sh check
            sh/pins.sh
            ;;
        check:shell) files 'sh/*.sh' | xargs -0 shellcheck ;;
        check:nix) files '*.nix' | xargs -0 nixfmt --check ;;
        fix:nix) files '*.nix' | xargs -0 nixfmt ;;
    esac
done
