#!/bin/bash
# usage: [RIND_DEVBENCH_DENY=sha3,dit] [RIND_DEVBENCH_DIT=sticky|nobarrier|isb|both] build-ipa.sh PORT [HOST]  -> out/RindBenchAll-v${VER:-15.0}-<PORT>[-deny-<ids>][-dit-<build>].ipa (unsigned; sign it yourself, e.g. with plumesign)
# Ports: 9101 for the iPad Pro M4, 9102 for the iPad mini A17 Pro (new listeners, so v13's 9099/9100 logs stay clean).
set -eu
# A relative CARGO_TARGET_DIR is the caller's: resolve it before the cd below,
# so cargo and Xcode (RIND_DEVBENCH_LIB) use the same directory.
case "${CARGO_TARGET_DIR:-}" in
  ""|/*) ;;
  *) export CARGO_TARGET_DIR="$PWD/$CARGO_TARGET_DIR" ;;
esac
cd "$(dirname "$0")"
PORT=${1:-9101}; HOST=${2:-}  # HOST: the collector's LAN address; empty = results stay on the device
export DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer
# shellcheck disable=SC2086 # CARGO_FEATURES is a list of cargo arguments.
../build-ios.sh ${CARGO_FEATURES---features __bench_openssl}
TAG=${RIND_DEVBENCH_DENY:+-deny-${RIND_DEVBENCH_DENY//,/_}}${RIND_DEVBENCH_DIT:+-dit-$RIND_DEVBENCH_DIT}  # as ../build-ios.sh names it
LIB=${CARGO_TARGET_DIR:-$HOME/rind-devbench/target}$TAG/aarch64-apple-ios/release/librind_devbench.a
rm -rf Resources/keys && cp -R ../../rind-rustls/tests/keys Resources/keys
BENCH_HOST=$HOST BENCH_PORT=$PORT xcodegen generate -q
# BenchPort as an integer, as v13 reads it.
/usr/libexec/PlistBuddy -c "Delete :BenchPort" -c "Add :BenchPort integer $PORT" Info.plist
rm -rf build
nice -n 19 xcodebuild -project RindBenchAll.xcodeproj -target RindBenchAll -configuration Release -sdk iphoneos \
  SYMROOT="$PWD/build" OBJROOT="$PWD/build/obj" ARCHS=arm64 IPHONEOS_DEPLOYMENT_TARGET=17.0 \
  CODE_SIGNING_ALLOWED=NO CODE_SIGNING_REQUIRED=NO CODE_SIGN_IDENTITY= RIND_DEVBENCH_LIB="$LIB" build -quiet
APP=build/Release-iphoneos/RindBenchAll.app
mkdir -p out && rm -rf out/Payload && mkdir out/Payload && cp -R "$APP" out/Payload/
IPA="RindBenchAll-v${VER:-15.0}-$PORT$TAG.ipa"
(cd out && rm -f "$IPA" && zip -q -r "$IPA" Payload && rm -rf Payload)
ls -la "out/$IPA"
