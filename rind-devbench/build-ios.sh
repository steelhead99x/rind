#!/bin/bash
# Builds librind_devbench.a for iOS (aarch64-apple-ios) at low priority.
set -u
cd "$(dirname "$0")"
export DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer
export IPHONEOS_DEPLOYMENT_TARGET=17.0 MACOSX_DEPLOYMENT_TARGET=14.0
export PATH=$HOME/.cargo/bin:$PATH
export CARGO_TARGET_DIR=$HOME/rind-devbench/target
exec nice -n 19 cargo +1.98.1 build --release --lib --target aarch64-apple-ios -j 6 "$@"
