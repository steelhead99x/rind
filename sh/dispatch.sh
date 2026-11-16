#!/usr/bin/env bash
# Run `just check`, `just fix`, or `just ci` over one resolved branch diff.
# check and ci run CHECK_JOBS lanes of modules at once (default 3); 1 runs
# them in order and streams their output. CHECK_MODULES limits the selection to
# the modules it names, or skips those named with a leading `-`.
# CHECK_FAIL_FAST=1 stops every lane at the first failed module, for the merge
# queue, which ejects a failing group either way and gains nothing from the
# rest.
# CHECK_TIMES=FILE also writes each module's wall seconds, CPU milliseconds,
# and name there, one per line, ending with the whole run's.
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
    if grep -qE '^(justfile|sh/(dispatch|changed|select|backends)\.sh)$' "$changed"; then
        echo "$action: root orchestration changed; running everything." >&2
        all=1
    fi
fi

# The impact map: each module registers once, in the order its lane starts, so
# the slowest come first. A module is in scope when a changed path matches its
# pattern; an empty pattern is a repository-wide lint that runs on every diff.
# After the pattern:
#   tools='...'        The commands it needs, for check and fix. A module
#                      missing one is skipped locally, so an incomplete
#                      toolchain checks less; under CI_STRICT (CI) it is an
#                      error, up front, because there a skip is
#                      indistinguishable from a pass.
#   check-tools='...'  More commands only its check needs.
#   compiles           Its check builds Rust in target/, so CI restores the
#                      Rust build cache when one is selected.
#   lane=NAME          Modules that share mutable state run in one lane, in
#                      module order; every other module is a lane of its own,
#                      and lanes run concurrently. Cargo's build directory
#                      lock already serializes builds sharing a target.
#   fix                `just fix` runs it too; check and ci run every module.
declare -A scope=() tools=() check_tools=() compiles=() lane=()
checks=()
fixes=()
module() {
    local name=$1 option
    scope[$name]=$2
    tools[$name]=
    check_tools[$name]=
    checks+=("$name")
    shift 2
    for option; do
        case "$option" in
            tools=*) tools[$name]=${option#tools=} ;;
            check-tools=*) check_tools[$name]=${option#check-tools=} ;;
            compiles) compiles[$name]=1 ;;
            lane=*) lane[$name]=${option#lane=} ;;
            fix) fixes+=("$name") ;;
            *)
                echo "error: module $name has an unknown option '$option'" >&2
                exit 2
                ;;
        esac
    done
}

# sh/select.sh narrows this to the changed crates and their dependents.
module rs '^(rind[^/]*/|fuzz/|thirdparty/|Cargo\.(toml|lock)$|\.rustfmt(\.unstable)?\.toml$)' \
    tools='cargo jq rustfmt-unstable' check-tools='cargo-nextest' compiles fix
# rind's aarch64, armv7, portable, and wasm32 builds, which the host's own
# build skips, and which a toolchain bump can break. A change under one
# backend's low/ directory checks only the builds of that backend (see
# `reach`), so an x86_64 kernel selects none of them. On Linux its aarch64 and
# armv7 builds run in nix's cross shells.
cross_tools=cargo
[[ $(uname -s) != Linux ]] || cross_tools='cargo nix'
module cross '^(rind/(src/|tests/|Cargo\.toml$|build\.rs$)|Cargo\.(toml|lock)$|flake\.(nix|lock)$)' \
    tools="$cross_tools" compiles
# The published adapters' wasm32 builds, and the tests the nightly runs there.
# rind's manifest picks the random source rind-ring's browser feature reaches.
module wasm '^(rind/Cargo\.toml$|rind-(aws-lc-rs|ring|rustls|rcgen|jsonwebtoken|dimpl|str0m|openmls|object-store)/(src/|tests/|Cargo\.toml$)|admin/wasm-fixture/|Cargo\.(toml|lock)$|flake\.(nix|lock)$)' \
    tools='cargo jq' compiles
# Dependents may build with the workspace's declared rust-version. Plain
# `cargo check` covers the lib and bin targets, all a dependent builds, so a
# crate's tests, benches, and docs cannot break it. A Rust crate nested in
# an adapter, such as rind-fips/module/, counts too.
module msrv '^(rind[^/]*/(src/|build\.rs$|Cargo\.toml$)|rind[^/]*/([^/]+/)+(src/.*\.rs$|build\.rs$|Cargo\.toml$)|fuzz/|Cargo\.(toml|lock)$|flake\.(nix|lock)$)' \
    tools='nix cargo jq' compiles
# Variable-time instructions in rind's release builds, which a change to its
# code, dependencies, toolchain, or the scan itself can bring. A change under
# one backend's low/ directory scans only that backend's targets.
module vartime '^(rind/(src/|Cargo\.toml$|build\.rs$)|Cargo\.(toml|lock)$|flake\.(nix|lock)$|admin/ct-vartime)' \
    tools='nix' compiles
# rind-dart's Dart package, whose build hook compiles the crate into a target
# directory of its own.
module dart '^rind-dart/' \
    tools='nix' fix
# pyrind's Python tests and type stubs, against its built wheel, and
# pyrind-cryptography's, with pyjwt's and joserfc's suites, which the lock
# pins. rind's own changes reach them in the nightly wheels workflow instead.
module py '^(rind-python/|sh/python\.sh$|flake\.lock$)' \
    tools='cargo jq maturin python3' compiles
# OpenSSL's own tests with rind-openssl loaded, against the OpenSSL the flake
# pins. rind's own changes reach the provider through its tests.
module openssl '^(rind-openssl/|sh/openssl\.sh$|flake\.(nix|lock)$)' \
    tools='nix' compiles
# The fixture builds this checkout's rind-ring under the rind-patch shim.
module patch '^(patch/|rind-ring/|(rind/)?Cargo\.toml$|sh/patch\.sh$)' \
    tools='cargo jq git' compiles fix
# rind's low, mid, and high layers reference only the layers below them.
module structure '^(rind/(src/|Cargo\.toml$)|admin/structure$)' \
    tools='cargo cargo-modules'
# admin/build-cost builds these against rind's public API, which nothing
# under rind/src/low/ is part of: rs already compiles that code on the host.
module fixtures '^(rind/(src/([^l]|l[^o]|lo[^w]|low[^/])|Cargo\.toml$|build\.rs$)|rind-rustls/(src/|Cargo\.toml$|build\.rs$)|Cargo\.toml$|admin/build-cost-fixtures/(rind|rustls)/)' \
    tools='cargo' compiles
# Advisories, licenses, and sources move with any manifest or the policy.
module deny '(^|/)Cargo\.(toml|lock)$|^deny\.toml$' \
    tools='cargo-deny'
# .cargo/mutants.toml's exclusions name mutants by file, line, and function,
# so moving code can leave one matching nothing.
module mutants '^(rind[^/]*/src/|\.cargo/mutants\.toml$|admin/mutants$)' \
    tools='cargo-mutants python3'
# An adapter's manifest holds both its version and its upstream requirement.
module versions '^(rind-[^/]+/Cargo\.toml$|sh/adapter-versions\.sh$)' \
    tools='cargo jq'
# Each adapter's API against its upstream's, which reaches rind only through a
# lockfile change, as read by the flake's rustdoc. rind-object-store has none
# to copy.
module adapters '^(rind/(src/|Cargo\.toml$)|rind-(aws-lc-rs|ring|rustls|rcgen|jsonwebtoken|dimpl|str0m|openmls)/(src/|Cargo\.toml$|README\.md$)|Cargo\.lock$|flake\.(nix|lock)$|admin/adapter-api$)' \
    tools='cargo python3' compiles
module license '^(rind/src/|rind/LICENSE$|rind-python/LICENSE$|admin/scan-license$)' \
    tools='find grep'
# TESTING.md's table names every export, test, and vector file.
module testing '^(TESTING\.md$|admin/testing$|rind/(src|tests)/|fuzz/)' \
    tools='python3'
# AUDIT.md's pins table is generated from the files that hold the pins, and
# the quests it links name gaps that finishing them closes.
module audit '^(AUDIT\.md$|admin/(audit|import-[a-z-]+|prove-bytes|sync-(acvp|vectors))$|thirdparty/s2n-bignum/RIND\.md$|(rind/)?Cargo\.(toml|lock)$|quest/)' \
    tools='python3 git' fix
# COMPATIBILITY.md is generated from the CPU scans.
module compat '^(COMPATIBILITY\.md$|admin/x86-cpus?(/|$))' \
    tools='python3' fix
# BENCHMARKS.md and the README's comparison are generated from the results,
# the verified-code table, and the gap decisions, which link the quests that
# close them.
module bench '^(BENCHMARKS\.md$|README\.md$|benchmarks/|admin/bench-report|quest/)' \
    tools='python3'
# The landing page reads and links files across the repository, and its build
# takes seconds, so it runs on every diff rather than keep a list.
module site '' \
    tools='nix'
# Quest documents form one graph, so any change validates the whole tree, as
# does a bump of the flake-pinned validator.
module quest '^(quest/|flake\.lock$)' \
    tools='quest'
# alert.yml must watch every workflow that runs outside a pull request, every
# third-party action must be pinned, and every scheduled workflow must run
# whole when the release check dispatches it.
module gh '^(\.github/|sh/(alert|pins|release-check)\.sh$)' \
    tools='actionlint yq jq'
module shell '' \
    tools='shellcheck'
module nix '' \
    tools='nixfmt' fix

# The rind backends that the changed paths matching a module's pattern compile
# into, one per line, or `all` when one of them lies outside rind/src/, such as
# a manifest, the toolchain, or the module's own script.
reach() {
    local matching
    if [[ -n "$all" ]]; then
        echo all
        return
    fi
    matching=$(grep -E "${scope[$1]}" "$changed" || true)
    if grep -qv '^rind/src/' <<<"$matching"; then
        echo all
    else
        sh/backends.sh - <<<"$matching"
    fi
}

# Whether `reach` printed `all` or any of the backends named after it.
reaches() {
    local backends=$1 name
    shift
    [[ "$backends" != all ]] || return 0
    for name; do
        grep -qxF "$name" <<<"$backends" && return 0
    done
    return 1
}

# The backend this host's native build compiles.
case "$(uname -m)" in
    x86_64) host=x86_64 ;;
    aarch64 | arm64) host=aarch64 ;;
    *) host=portable ;;
esac

verb=$action
[[ "$verb" != ci ]] || verb=check

modules=("${checks[@]}")
[[ "$action" != fix ]] || modules=("${fixes[@]}")

# CHECK_MODULES names the modules to run, or with a leading `-` those to skip.
declare -A only=() skip=()
for word in ${CHECK_MODULES:-}; do
    name=${word#-}
    if [[ " ${modules[*]} " != *" $name "* ]]; then
        echo "error: CHECK_MODULES names '$name', which $action does not run; pick from: ${modules[*]}" >&2
        exit 2
    fi
    if [[ "$word" == -* ]]; then skip[$name]=1; else only[$name]=1; fi
done

selected=()
missing=()
for module in "${modules[@]}"; do
    if [[ -v "skip[$module]" ]] || { ((${#only[@]})) && [[ ! -v "only[$module]" ]]; }; then
        continue
    fi
    pattern=${scope[$module]}
    if [[ -z "$all" && -n "$pattern" ]] && ! grep -qE "$pattern" "$changed"; then
        continue
    fi
    # The host's build already covers its own backend. A plain assignment, so
    # a failing `reach` stops the run instead of reading as no backend.
    if [[ "$verb:$module" == check:cross ]]; then
        cross_reach=$(reach cross)
        reaches "$cross_reach" aarch64 arm portable || continue
    fi
    # Selection must not depend on the tools setup has yet to install.
    if [[ -n "$query" ]]; then
        selected+=("$module")
        continue
    fi
    absent=()
    needs=${tools[$module]}
    [[ "$verb" != check ]] || needs+=" ${check_tools[$module]}"
    for tool in $needs; do
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
        [[ ! -v "compiles[$module]" ]] || rust=true
    done
    echo "needed=$needed"
    echo "rust=$rust"
    echo "modules=${selected[*]}"
    exit
fi

if ((${#missing[@]} > 0)); then
    echo "error: missing tools under CI_STRICT: $(printf '%s\n' "${missing[@]}" | sort -u | tr '\n' ' ')" >&2
    exit 1
fi

# The portable backend, forced on a target; an explicit target keeps its
# builds apart from the host's, and its build scripts unflagged.
portable='--cfg rind_portable --cfg curve25519_dalek_backend="serial"'

# A trapped shell defers its trap while a foreground command runs, and a TERM
# that lands just before the fork never reaches the command, so a cancel would
# wait for the whole module. A lane and its module therefore fork every
# command as a job: `wait` runs the trap at once, and Bash runs a trap left
# pending across the fork as soon as the fork returns. Without job control,
# an async list ignores INT and QUIT, which the job restores for the command,
# and may read /dev/null instead of the caller's stdin, which it redirects
# explicitly.
run() {
    {
        trap - INT QUIT
        exec "$@"
    } <&0 &
    wait "$!"
}

# A TERM trap's body: resend TERM to the lane's process group, which reaches a
# job forked after the first TERM, then return once every job has exited. The
# resend can land while Bash still records `wait` as its builtin, which makes
# the next `wait` return at once (see the EXIT trap below), so it waits again.
stop() {
    trap '' TERM
    kill -TERM 0
    until wait; do :; done
}

# Writes the tracked files matching a pathspec to $listed, NUL-separated.
files() {
    run git ls-files -z -- "$@" >"$listed"
}

# Whether the Cargo arguments after CRATE, as sh/select.sh prints them, name
# it or the whole workspace, which no arguments at all also mean.
names() {
    local crate=$1 arg
    shift
    (($#)) || return 0
    for arg; do
        [[ "$arg" != "$crate" && "$arg" != --workspace ]] || return 0
    done
    return 1
}

# One module's check or fix, run through `run`.
step() {
    local listed=$logs/$2.files packages libs backends target targets
    case "$1:$2" in
        check:rs)
            mapfile -t packages < <(sh/select.sh "$changed" "$all")
            run cargo fmt --all --check
            RUSTFMT=rustfmt-unstable run cargo fmt --all --check -- --config-path=.rustfmt.unstable.toml
            run cargo clippy "${packages[@]}" --all-targets --locked -- --deny warnings
            # nextest runs the test binaries in parallel but not doc tests. Like
            # `cargo test`, it passes a selection with no tests, such as the
            # benches alone.
            run cargo nextest run "${packages[@]}" --locked --no-tests=warn
            # Only the zeroing and heap scratch tests see the opt-in wipe,
            # which the default build turns into no-ops.
            if names rind "${packages[@]}"; then
                run cargo nextest run -p rind --features wipe --test zeroing --test heap_scratch --locked
            fi
            if names rind-aws-lc-rs "${packages[@]}"; then
                run cargo nextest run -p rind-aws-lc-rs --features wipe --test zeroing --locked
            fi
            # The FIPS module's own code compiles only under its cfg, which a
            # workspace build leaves off, and only for glibc Linux on x86_64
            # and aarch64, where rind-fips is not empty. Its break build
            # checks, on every call, the stack each service zeroes, and fails
            # each self-test. Its ACVP build adds the deterministic forms
            # rind-acvp answers ACVP with, and rind-acvp compiles only with
            # the `module` feature that builds it; its offline run answers
            # every vector set on each of this CPU's paths, with the dev
            # shell's acvptool.
            if { names rind-fips "${packages[@]}" || names rind-acvp "${packages[@]}"; } &&
                [[ "$(rustc -vV | sed -n 's/^host: //p')" =~ ^(x86_64|aarch64)-unknown-linux-gnu$ ]]; then
                for features in '' acvp; do
                    RUSTFLAGS='--cfg rind_fips --cfg rind_cpu_disable' run cargo clippy -p rind-fips-module \
                        --features "$features" --locked --target-dir target/fips-module -- --deny warnings
                done
                run cargo clippy -p rind-acvp --features module --all-targets --locked -- --deny warnings
                if [[ -n "$all" ]] || grep -q '^rind-fips/' "$changed"; then
                    run cargo nextest run -p rind-fips --features __break_tests --locked
                fi
                # Selected whenever rind or the module it builds changes,
                # since its answers come from rind's services.
                if names rind-acvp "${packages[@]}"; then
                    run cargo nextest run -p rind-acvp --features module --locked
                fi
            fi
            # Doc tests need a library. No packages at all means the workspace.
            mapfile -t libs < <(sh/select.sh "$changed" "$all" --lib)
            if ((${#libs[@]} > 0 || ${#packages[@]} == 0)); then
                run cargo test "${libs[@]}" --locked --doc
                # A broken or private intra-doc link renders as plain text on
                # docs.rs.
                RUSTDOCFLAGS='--deny warnings' run cargo doc "${libs[@]}" --no-deps --locked
            fi
            ;;
        fix:rs)
            mapfile -t packages < <(sh/select.sh "$changed" "$all")
            run cargo fmt --all
            RUSTFMT=rustfmt-unstable run cargo fmt --all -- --config-path=.rustfmt.unstable.toml
            run cargo clippy "${packages[@]}" --all-targets --fix --allow-dirty --allow-staged
            ;;
        check:msrv)
            backends=$(reach msrv)
            # The host's own check runs only when the change reaches the
            # host's backend: one under another backend's low/ directory
            # compiles nothing here.
            if reaches "$backends" "$host"; then
                mapfile -t packages < <(sh/select.sh "$changed" "$all")
                # A change that selects no crate, such as the flake's, can
                # still change the toolchain.
                ((${#packages[@]} > 0)) || packages=(--workspace)
                # An adapter whose upstream needs a newer Rust declares that
                # rust-version instead, which its users need anyway, so it is
                # left out.
                local newer args=() i name
                mapfile -t newer < <(cargo metadata --format-version 1 --no-deps --locked |
                    jq -r '(.packages[] | select(.name == "rind") | .rust_version) as $v | .packages[] | select(.rust_version != $v) | .name')
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
                if ((${#args[@]} > 0)); then
                    run nix develop .#msrv --command cargo check "${args[@]}" --locked
                fi
            fi
            # rind and rind-rustls on each other backend this change reaches.
            # i686 has only the portable one.
            for target in aarch64:aarch64-unknown-linux-gnu arm:armv7-unknown-linux-gnueabihf portable:i686-unknown-linux-gnu; do
                if reaches "$backends" "${target%%:*}"; then
                    run nix develop .#msrv --command cargo check -p rind -p rind-rustls --lib --locked --target "${target#*:}"
                fi
            done
            ;;
        check:cross)
            backends=$(reach cross)
            # The tests too, in the shells whose C toolchain builds their
            # aws-lc-rs dev-dependency, so test code that only these targets
            # compile is checked before it lands. aarch64 in release, as
            # sh/qemu.sh explains: nixpkgs' cross gcc fails aws-lc's -O0 probes.
            # Those shells are Linux-only, so elsewhere the library alone.
            if reaches "$backends" aarch64; then
                if [[ $(uname -s) == Linux ]]; then
                    run nix develop .#aarch64 --command cargo clippy -p rind --all-targets --locked --release \
                        --target aarch64-unknown-linux-gnu -- --deny warnings
                else
                    run cargo clippy -p rind --lib --locked --target aarch64-unknown-linux-gnu -- --deny warnings
                fi
            fi
            if reaches "$backends" arm; then
                if [[ $(uname -s) == Linux ]]; then
                    run nix develop .#armv7 --command cargo clippy -p rind --all-targets --locked \
                        --target armv7-unknown-linux-gnueabihf -- --deny warnings
                else
                    run cargo clippy -p rind --lib --locked --target armv7-unknown-linux-gnueabihf -- --deny warnings
                fi
            fi
            if reaches "$backends" portable; then
                # The FIPS module's source rides along: its cfg touches only
                # where randomness comes from, which no backend changes, and
                # the CPU check, which only the backends it builds on have.
                CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_RUSTFLAGS="$portable --cfg rind_fips" \
                    run cargo clippy -p rind --lib --locked --target x86_64-unknown-linux-gnu -- --deny warnings
                # And on a 32-bit target, whose Poly1305 and GHASH differ.
                CARGO_TARGET_ARMV7_UNKNOWN_LINUX_GNUEABIHF_RUSTFLAGS="$portable" \
                    run cargo clippy -p rind --lib --locked --target armv7-unknown-linux-gnueabihf -- --deny warnings
                # wasm32 compiles on the portable backend; the browser target
                # needs getrandom's JavaScript source, WASI has its own.
                local features
                for features in "" wipe; do
                    run cargo clippy -p rind --lib --locked --target wasm32-wasip2 --features "$features" -- --deny warnings
                    run cargo clippy -p rind --lib --locked --target wasm32-unknown-unknown \
                        --features "$features,getrandom/wasm_js" -- --deny warnings
                done
            fi
            ;;
        check:wasm)
            # Each published adapter, as sh/adapter-versions.sh finds them.
            local adapters
            mapfile -t adapters < <(cargo metadata --format-version 1 --no-deps --locked |
                jq -r '.packages[] | select((.name | startswith("rind-")) and .publish == null) | "-p", .name')
            run cargo clippy "${adapters[@]}" --lib --locked --target wasm32-wasip2 -- --deny warnings
            # The tests `just wasm` runs, without the differential ones.
            run cargo clippy -p rind-rustls -p rind-ring --lib --tests --locked --target wasm32-wasip2 -- --deny warnings
            # The browser: admin/wasm-fixture adds what a caller adds, and
            # rind-ring also takes ring's own feature for it.
            run cargo clippy -p wasm-fixture "${adapters[@]}" --lib --locked --target wasm32-unknown-unknown -- --deny warnings
            run cargo clippy -p rind-ring --lib --locked --target wasm32-unknown-unknown \
                --features wasm32_unknown_unknown_js -- --deny warnings
            ;;
        check:vartime)
            # Each backend's targets, as admin/ct-vartime names them; no
            # target at all scans every one.
            backends=$(reach vartime)
            targets=()
            if [[ "$backends" != all ]]; then
                ! reaches "$backends" x86_64 || targets+=(x86_64-unknown-linux-gnu)
                ! reaches "$backends" aarch64 || targets+=(aarch64-unknown-linux-gnu)
                ! reaches "$backends" arm || targets+=(armv7-unknown-linux-gnueabihf)
                ! reaches "$backends" portable || targets+=(
                    x86_64-unknown-linux-gnu+portable armv7-unknown-linux-gnueabihf+portable
                    i686-unknown-linux-gnu arm-unknown-linux-gnueabihf loongarch64-unknown-linux-gnu
                    powerpc-unknown-linux-gnu powerpc64-unknown-linux-gnu powerpc64le-unknown-linux-gnu
                    riscv64gc-unknown-linux-gnu s390x-unknown-linux-gnu
                )
            fi
            run nix develop .#ct-vartime --command admin/ct-vartime "${targets[@]}"
            ;;
        check:structure) run admin/structure ;;
        check:deny) run cargo deny --locked check ;;
        check:versions) run sh/adapter-versions.sh ;;
        check:adapters) run python3 admin/adapter-api ;;
        check:quest) run quest check ;;
        check:license) run bash admin/scan-license ;;
        check:mutants)
            run admin/mutants --pins
            run admin/mutants --expand-diff-self-test
            ;;
        check:testing) run python3 admin/testing ;;
        check:audit) run python3 admin/audit check ;;
        fix:audit) run python3 admin/audit fix ;;
        check:compat)
            run python3 admin/x86-cpu markdown-table >"$logs/compat.md"
            run diff -u COMPATIBILITY.md "$logs/compat.md"
            ;;
        fix:compat) run python3 admin/x86-cpu markdown-table >COMPATIBILITY.md ;;
        check:bench)
            run python3 admin/bench-report-test
            run python3 admin/bench-report render --check
            ;;
        # Each fixture is its own workspace and resolves its own lockfile.
        check:fixtures)
            run cargo check --manifest-path admin/build-cost-fixtures/rind/Cargo.toml --target-dir target
            run cargo check --manifest-path admin/build-cost-fixtures/rustls/Cargo.toml --features rind --target-dir target
            ;;
        check:patch) run sh/patch.sh ;;
        fix:patch) run cargo fmt --manifest-path patch/fixture/Cargo.toml ;;
        check:py) run sh/python.sh test ;;
        check:dart) run nix develop .#dart --command sh/dart.sh check ;;
        check:openssl) run nix develop .#openssl --command sh/openssl.sh ;;
        check:site) run nix develop .#site --command sh/site.sh ;;
        fix:dart) run nix develop .#dart --command sh/dart.sh fix ;;
        check:gh)
            run actionlint
            # See queue-build.yml: main's copy runs against every group's tree.
            if grep -nE '^[[:space:]]*(-[[:space:]]*)?uses:[[:space:]]*\./' .github/workflows/queue-build.yml; then
                echo "error: queue-build.yml must use no local action; put the setup in \`just ci\`" >&2
                return 1
            fi
            run sh/alert.sh check
            # Fixtures for the checker. A failure here is the checker, not alert.yml,
            # so it is not part of `sh/alert.sh check`.
            run sh/alert.sh prove
            run sh/pins.sh
            run sh/release-check.sh --check >/dev/null
            ;;
        check:shell)
            files 'sh/*.sh'
            run xargs -0 shellcheck <"$listed"
            ;;
        check:nix)
            files '*.nix'
            run xargs -0 nixfmt --check <"$listed"
            ;;
        fix:nix)
            files '*.nix'
            run xargs -0 nixfmt <"$listed"
            ;;
        *)
            echo "error: $action has no step for $2" >&2
            return 2
            ;;
    esac
}

# Lanes run at most this many at a time. fix stays serial: its fixers rewrite
# files the others read.
limit=${CHECK_JOBS:-3}
[[ "$action" != fix ]] || limit=1
if [[ ! "$limit" =~ ^[1-9][0-9]*$ ]]; then
    echo "error: CHECK_JOBS must be a positive integer, not '$limit'" >&2
    exit 2
fi

lanes=()
declare -A members=()
for module in "${selected[@]}"; do
    name=${lane[$module]:-$module}
    [[ -v "members[$name]" ]] || lanes+=("$name")
    members[$name]+=" $module"
done

github() {
    [[ -n "${GITHUB_ACTIONS:-}" ]]
}

# Sets cpu to the CPU milliseconds, user and system, of every child this shell
# has waited for. `times` must run in this shell, not a command substitution's
# fork, whose children are its own. Bash prints three decimals, with the
# locale's decimal point.
lane_cpu() {
    local user system each minutes seconds
    times >"$times.cpu"
    { read -r _ _ && read -r user system; } <"$times.cpu"
    cpu=0
    for each in "$user" "$system"; do
        minutes=${each%%m*}
        seconds=${each#*m}
        seconds=${seconds%s}
        cpu=$((cpu + minutes * 60000 + 10#${seconds%[.,]*} * 1000 + 10#${seconds#*[.,]}))
    done
}

# Run one lane's modules in order, appending each one's wall seconds and CPU
# milliseconds to the lane's times file and announcing each one's start and
# end on fd 3. A failed module leaves the lane's later ones to run, unless
# CHECK_FAIL_FAST is set. A TERM stops the running module, waits for it, and
# records the module it cut short. CPU counts only processes the module
# waited for, so not the work of a daemon such as Nix's.
run_lane() {
    times=$1
    shift
    current=
    lane_status=0
    trap 'stop; cancelled; exit 143' TERM
    for module in "$@"; do
        current="$verb $module"
        began=$SECONDS
        lane_cpu
        cpu_began=$cpu
        if github; then echo "::group::$current"; else echo "==> $current"; fi
        echo "$action: $current started" >&3
        # A job, as `run` explains; errexit stays on inside it. Untrapped, the
        # module would die on TERM at once, orphaning its commands. Trapped,
        # it exits once they do, so a cancel returns only after the whole
        # tree has exited.
        (
            trap - INT QUIT
            set -e
            trap 'stop; exit 143' TERM
            step "$verb" "$module"
        ) &
        set +e
        wait "$!"
        status=$?
        set -e
        ! github || echo "::endgroup::"
        if ((status)); then
            record failed
            ((lane_status)) || lane_status=$status
            current=
            [[ -z "${CHECK_FAIL_FAST:-}" ]] || return "$lane_status"
            continue
        fi
        record
        current=
    done
    return "$lane_status"
}
record() {
    local seconds=$((SECONDS - began))
    lane_cpu
    echo "$seconds $((cpu - cpu_began)) $current${1:+ ($1)}" >>"$times"
    echo "$action: $current ${1:-passed} in ${seconds}s" >&3
}
cancelled() {
    [[ -n "$current" ]] || return 0
    ! github || echo "::endgroup::"
    record cancelled
}

# Each module's wall and CPU time, printed when the run ends, pass or fail, so
# the slow module of a check or a queue run is named without reading log
# timestamps. GitHub Actions also gets it in the job summary, and CHECK_TIMES
# in its file. Concurrent modules overlap, so the whole run comes last.
report() {
    local name row seconds cpu label total=0 rows=()
    for name in "${lanes[@]:0:next}"; do
        [[ ! -f "$logs/$name.times" ]] || mapfile -t -O "${#rows[@]}" rows <"$logs/$name.times"
    done
    ((${#rows[@]})) || return 0
    for row in "${rows[@]}"; do
        read -r seconds cpu label <<<"$row"
        total=$((total + cpu))
    done
    rows+=("$SECONDS $total whole run")
    [[ -z "${CHECK_TIMES:-}" ]] || printf '%s\n' "${rows[@]}" >"$CHECK_TIMES"
    echo "$action: wall and CPU seconds per module" >&2
    for row in "${rows[@]}"; do
        read -r seconds cpu label <<<"$row"
        printf '%6d %7d  %s\n' "$seconds" "$((cpu / 1000))" "$label" >&2
    done
    [[ -n "${GITHUB_STEP_SUMMARY:-}" ]] || return 0
    {
        printf '| %s module | Wall seconds | CPU seconds |\n| --- | ---: | ---: |\n' "$action"
        for row in "${rows[@]}"; do
            read -r seconds cpu label <<<"$row"
            printf '| %s | %d | %d |\n' "$label" "$seconds" "$((cpu / 1000))"
        done
    } >>"$GITHUB_STEP_SUMMARY"
}

# Stop every running lane, whose process group holds its whole tree. The job
# table also holds a lane a signal interrupted before `running` recorded it.
cancel() {
    local pid
    for pid in $(jobs -pr); do
        kill -TERM -- "-$pid" 2>/dev/null || true
    done
}

logs=$(mktemp -d)
declare -A running=()
next=0
failed=()
failed_status=0
# A trapped signal that lands after `wait -n` returns, before the next builtin
# runs, makes Bash end the exit trap's first wait at once, though that signal's
# trap already ran; the next wait blocks until every lane has exited.
trap 'cancel; until wait; do :; done; report; rm -rf "$logs" "$changed"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM

# Each lane runs in its own process group, so a cancel reaches its whole tree;
# a lane shell stops its running module and waits for it before it exits.
# Concurrent lanes buffer their output and print it whole when they finish; a
# serial run streams instead. A buffered lane still announces each module on
# the run's stderr as it starts and ends, so a run cut off mid-module, such as
# by a job timeout that never reaches this script, names the module it stopped
# in. Every lane completes even when another fails, so one failing check
# cannot hide unrelated failures; under CHECK_FAIL_FAST the first failure
# cancels the running lanes and starts no more.
set -m
stopping=
while true; do
    while [[ -z "$stopping" ]] && ((next < ${#lanes[@]} && ${#running[@]} < limit)); do
        name=${lanes[next]}
        next=$((next + 1))
        read -ra lane_modules <<<"${members[$name]}"
        if ((limit == 1)); then
            run_lane "$logs/$name.times" "${lane_modules[@]}" </dev/null 3>/dev/null &
        else
            run_lane "$logs/$name.times" "${lane_modules[@]}" </dev/null 3>&2 >"$logs/$name.log" 2>&1 &
        fi
        running[$!]=$name
    done
    ((${#running[@]})) || break

    status=0
    wait -n -p pid "${!running[@]}" || status=$?
    name=${running[$pid]}
    unset "running[$pid]"
    if ((status)) && [[ -z "$stopping" ]]; then
        failed+=("$name")
        ((failed_status)) || failed_status=$status
        if [[ -n "${CHECK_FAIL_FAST:-}" ]]; then
            stopping=1
            cancel
        fi
    fi
    ((limit == 1)) || cat "$logs/$name.log"
done

# Name every failed module after all independent work has completed.
if ((${#failed[@]})); then
    for name in "${failed[@]}"; do
        # A lane killed before its first record leaves no times file.
        failed_modules=
        [[ ! -e "$logs/$name.times" ]] ||
            failed_modules=$(sed -n 's/^[0-9]* [0-9]* \(.*\) (failed)$/\1/p' "$logs/$name.times")
        while IFS= read -r module; do
            if github; then echo "::error::$action: $module failed"; else echo "$action: $module failed" >&2; fi
        done <<<"${failed_modules:-${members[$name]# }}"
    done
    exit "$failed_status"
fi
