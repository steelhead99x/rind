#!/bin/bash
# Builds librind_devbench.a for iOS (aarch64-apple-ios) at low priority.
set -u
# A relative CARGO_TARGET_DIR is the caller's: resolve it before the cd below,
# so cargo and the caller use the same directory.
case "${CARGO_TARGET_DIR:-}" in
  ""|/*) ;;
  *) export CARGO_TARGET_DIR="$PWD/$CARGO_TARGET_DIR" ;;
esac
cd "$(dirname "$0")" || exit 1
export DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer
export IPHONEOS_DEPLOYMENT_TARGET=17.0 MACOSX_DEPLOYMENT_TARGET=14.0
export PATH=$HOME/.cargo/bin:$PATH
# RIND_DEVBENCH_DENY=sha3,dit builds a variant that denies those CPU features
# (rind's RIND_CPU_DISABLE_<id>): the ids go into the library (see
# `apply_build_denies` in src/lib.rs) and rind is built with `--cfg
# rind_cpu_disable`, without which an optimised rind ignores the denial. Each
# set gets its own target directory, so switching sets rebuilds nothing else.
TAG=${RIND_DEVBENCH_DENY:+-deny-${RIND_DEVBENCH_DENY//,/_}}
if [ -n "${RIND_DEVBENCH_DENY:-}" ]; then
  export RUSTFLAGS="${RUSTFLAGS:-} --cfg rind_cpu_disable"
fi
# RIND_DEVBENCH_DIT picks one of the DIT measuring builds (fork issues #259 to
# #266): sticky (`--cfg rind_dit_sticky`, DIT left on once set), nobarrier
# (`--cfg rind_dit_barrier="none"`), isb (`--cfg rind_dit_barrier="isb"`), or
# both (sticky and nobarrier). Measuring builds only; each gets its own target
# directory and IPA name.
case "${RIND_DEVBENCH_DIT:-}" in
  "") ;;
  sticky) export RUSTFLAGS="${RUSTFLAGS:-} --cfg rind_dit_sticky" ;;
  nobarrier) export RUSTFLAGS="${RUSTFLAGS:-} --cfg rind_dit_barrier=\"none\"" ;;
  isb) export RUSTFLAGS="${RUSTFLAGS:-} --cfg rind_dit_barrier=\"isb\"" ;;
  both) export RUSTFLAGS="${RUSTFLAGS:-} --cfg rind_dit_sticky --cfg rind_dit_barrier=\"none\"" ;;
  *) echo "RIND_DEVBENCH_DIT is sticky, nobarrier, isb or both" >&2; exit 2 ;;
esac
TAG=$TAG${RIND_DEVBENCH_DIT:+-dit-$RIND_DEVBENCH_DIT}
# A runner may set CARGO_TARGET_DIR; each deny/DIT set still gets its own.
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/rind-devbench/target}$TAG
exec nice -n 19 cargo +1.98.1 build --release --lib --target aarch64-apple-ios -j 6 "$@"
