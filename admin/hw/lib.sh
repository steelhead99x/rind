# shellcheck shell=bash
# Sourced by admin/hw/*.sh: the host checks, checkouts, and builds they share.
# Each measurement script states its host, sources this, and calls hw_setup.
#
# Environment every script reads:
#   HW_REMOTE        where the PR branches live (default the fork on GitHub)
#   HW_TARGET_ROOT   cargo target dirs, one per commit and RUSTFLAGS, kept
#                    between runs (default .tmp/hw/target)
#   RIND_PINNED_CPUS the CPU to pin the timed runs to (admin/bench-report's
#                    variable; default: a P-core on a hybrid CPU, else the
#                    last CPU)

HW_ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
HW_REMOTE=${HW_REMOTE:-https://github.com/steelhead99x/rind.git}
HW_AB=$HW_ROOT/admin/hw/ab
HW_TARGET_ROOT=${HW_TARGET_ROOT:-$HW_ROOT/.tmp/hw/target}

hw_die() {
    echo "error: $*" >&2
    exit 1
}

# Refuses, with the reason, the host a script cannot measure on.
hw_refuse() {
    echo "refused: $*" >&2
    exit 4
}

hw_say() {
    echo "== $*" >&2
}

# Parses the arguments every script takes: --preflight runs the host checks
# only, and exits 0 when this host could run the measurement.
hw_args() {
    HW_PREFLIGHT=0
    for arg in "$@"; do
        case $arg in
            --preflight) HW_PREFLIGHT=1 ;;
            -h | --help)
                awk 'NR > 1 && /^#/ { sub(/^# ?/, ""); print; next } NR > 1 { exit }' "$0"
                exit 0
                ;;
            *) hw_die "unknown argument $arg (only --preflight)" ;;
        esac
    done
}

hw_preflight_done() {
    if ((HW_PREFLIGHT)); then
        echo "preflight passed: this host can run $(basename "$0")" >&2
        exit 0
    fi
}

hw_need_tools() {
    local tool
    for tool in "$@"; do
        command -v "$tool" >/dev/null || hw_refuse "$tool is not installed"
    done
}

hw_require_linux_x86_64() {
    [[ $(uname -s) == Linux ]] || hw_refuse "this measurement runs on Linux, not $(uname -s)"
    [[ $(uname -m) == x86_64 ]] || hw_refuse "this measurement needs an x86_64 CPU, not $(uname -m)"
    hw_need_tools git cargo python3 taskset
}

# The CPU's feature flags as the Linux kernel reports them.
hw_flags() {
    grep -m1 '^flags' /proc/cpuinfo | cut -d: -f2
}

hw_has_flag() {
    [[ " $(hw_flags) " == *" $1 "* ]]
}

hw_cpu_model() {
    grep -m1 '^model name' /proc/cpuinfo | cut -d: -f2 | sed 's/^ *//'
}

# A VM's vCPUs share their cores with other tenants, which admin/bench-report's
# notes give as noise a dedicated host lacks.
hw_refuse_vm() {
    if hw_has_flag hypervisor; then
        hw_refuse "$(hw_cpu_model) is a virtual machine; this measurement needs a dedicated host"
    fi
}

# Sets HW_PIN: RIND_PINNED_CPUS, or a P-core (on a hybrid Intel CPU the
# kernel lists them in /sys/devices/cpu_core/cpus), or the last CPU; never
# CPU 0, which takes most interrupts.
hw_pick_pin() {
    local list=${1:-}
    if [[ -n ${RIND_PINNED_CPUS:-} ]]; then
        HW_PIN=$RIND_PINNED_CPUS
        [[ $HW_PIN =~ ^[0-9]+$ ]] || hw_die "RIND_PINNED_CPUS=$HW_PIN: give one CPU number"
    elif [[ -n $list ]]; then
        HW_PIN=$(hw_expand "$list" | tail -n1)
    else
        HW_PIN=$(($(nproc --all) - 1))
    fi
    ((HW_PIN != 0)) || hw_refuse "this host has one CPU, or RIND_PINNED_CPUS is 0: pin to a CPU other than 0"
    [[ -d /sys/devices/system/cpu/cpu$HW_PIN ]] || hw_die "CPU $HW_PIN does not exist"
}

# Expands a kernel CPU list such as 0-7,16 into one number per line.
hw_expand() {
    local part
    IFS=, read -ra parts <<<"$1"
    for part in "${parts[@]}"; do
        if [[ $part == *-* ]]; then
            seq "${part%-*}" "${part#*-}"
        else
            echo "$part"
        fi
    done
}

# Holds the host's benchmark lease for the rest of the script, as
# admin/bench-report's collect does on a host that has one, or refuses.
hw_lease() {
    local lease=/run/lock/moq-perf.lock
    [[ -e $lease ]] || return 0
    hw_need_tools flock
    exec {HW_LEASE_FD}>>"$lease"
    flock -n "$HW_LEASE_FD" || hw_refuse "other work holds $lease"
    hw_say "holding $lease"
}

# Refuses a host other work keeps busy, by admin/bench-report's limit.
hw_check_idle() {
    local msg
    if ! msg=$("$HW_AB" idle); then
        hw_refuse "busy: $msg. Run it when the host is idle."
    fi
    hw_say "idle: $msg"
}

# Makes this run's directory, and removes its checkouts on exit.
hw_setup() {
    local name
    name=$(basename "$0" .sh)
    HW_RUN=$HW_ROOT/.tmp/hw/$name-$(date -u +%Y%m%dT%H%M%SZ)
    mkdir -p "$HW_RUN/src" "$HW_TARGET_ROOT"
    trap hw_cleanup EXIT
    # Everything the script prints goes to run.log as well.
    exec > >(tee -a "$HW_RUN/run.log") 2>&1
    hw_say "results in $HW_RUN"
}

# Removes this run's checkouts, which hw_worktree makes under $HW_RUN/src.
hw_cleanup() {
    local wt
    for wt in "$HW_RUN"/src/*/; do
        [[ ! -d $wt ]] || git -C "$HW_ROOT" worktree remove --force "$wt" 2>/dev/null || true
    done
    git -C "$HW_ROOT" worktree prune
}

# Prints the commit REF names on HW_REMOTE now (a branch, or pull/N/head),
# or $2 when that is set, so a rerun can name the same commits.
hw_rev() {
    local ref=$1 given=${2:-}
    if [[ -n $given ]]; then
        git -C "$HW_ROOT" rev-parse --verify --quiet "$given^{commit}" >/dev/null ||
            git -C "$HW_ROOT" fetch -q "$HW_REMOTE" "$given" ||
            hw_die "cannot find commit $given"
        git -C "$HW_ROOT" rev-parse --verify "$given^{commit}"
        return
    fi
    git -C "$HW_ROOT" fetch -q --no-tags "$HW_REMOTE" "$ref" || hw_die "cannot fetch $ref from $HW_REMOTE"
    git -C "$HW_ROOT" rev-parse --verify "FETCH_HEAD^{commit}"
}

# Checks out SHA as $HW_RUN/src/NAME and prints its path.
hw_worktree() {
    local name=$1 sha=$2 wt=$HW_RUN/src/$1
    git -C "$HW_ROOT" worktree add -q --detach "$wt" "$sha" >&2 || hw_die "cannot check out $sha"
    echo "$wt"
}

# Runs a build through `quest gate` where the host has it, so it waits for
# room beside other gated work.
hw_gate() {
    if command -v quest >/dev/null; then
        quest gate "$@"
    else
        "$@"
    fi
}

# The target dir for a commit and RUSTFLAGS: one per variant, so cargo never
# reuses one revision's artifacts for another.
hw_target() {
    local sha=$1 flags=${2:-}
    local key=${sha:0:12}
    [[ -z $flags ]] || key+=-$(printf %s "$flags" | sha256sum | cut -c1-8)
    echo "$HW_TARGET_ROOT/$key"
}

# Builds the BENCHes of rind-bench in WORKTREE with RUSTFLAGS, then copies
# their executables to $HW_RUN/bin/NAME/ and prints them comma-separated.
hw_build_benches() {
    local name=$1 wt=$2 sha=$3 flags=$4
    shift 4
    local target json args=() bench out=$HW_RUN/bin/$name exes=()
    target=$(hw_target "$sha" "$flags")
    for bench in "$@"; do
        args+=(--bench "$bench")
    done
    json=$HW_RUN/bin/$name.cargo.json
    mkdir -p "$out"
    hw_say "building $name ($sha) into $target"
    (cd "$wt" && CARGO_TARGET_DIR=$target RUSTFLAGS=$flags hw_gate cargo bench -p rind-bench "${args[@]}" --no-run --message-format=json-render-diagnostics >"$json") ||
        hw_die "the $name build failed"
    local exe
    while read -r exe; do
        cp "$exe" "$out/"
        exes+=("$out/$(basename "$exe")")
    done < <("$HW_AB" executables "$@" <"$json")
    (
        IFS=,
        echo "${exes[*]}"
    )
}

# Checks the CPU features rind itself detects, at WORKTREE's revision, with
# rind-cpuid: FEATURE=0|1 arguments. A second check beside the kernel's flags.
hw_rind_cpuid() {
    local wt=$1 sha=$2 flags=$3
    shift 3
    local json
    json=$(cd "$wt" && CARGO_TARGET_DIR=$(hw_target "$sha" "$flags") RUSTFLAGS=$flags hw_gate cargo run -q --release -p rind-cpuid) ||
        hw_die "rind-cpuid failed"
    echo "$json" >"$HW_RUN/rind-cpuid.json"
    "$HW_AB" cpuid "$@" <<<"$json" || exit
}

# Prints the follow-up: the summary posted on fork PR NUMBER.
hw_follow_up() {
    local pr=$1 file=$2
    cat <<EOF

Next step: review $file, then post it on steelhead99x/rind#$pr:
  gh api repos/steelhead99x/rind/issues/$pr/comments -F body=@$file
EOF
}
