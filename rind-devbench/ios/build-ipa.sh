#!/bin/bash
# usage: build-ipa.sh PORT [HOST]  -> out/RindBenchAll-v${VER:-14.1}-<PORT>.ipa (unsigned; sign with plumesign on the Alienware)
# Ports: 9101 for the iPad Pro M4, 9102 for the iPad mini A17 Pro (new listeners, so v13's 9099/9100 logs stay clean).
set -eu
cd "$(dirname "$0")"
PORT=${1:-9101}; HOST=${2:-192.168.90.75}
export DEVELOPER_DIR=/Applications/Xcode.app/Contents/Developer
../build-ios.sh ${CARGO_FEATURES---features __bench_openssl}
LIB=$HOME/rind-devbench/target/aarch64-apple-ios/release/librind_devbench.a
rm -rf Resources/keys && cp -R ../../rind-rustls/tests/keys Resources/keys
BENCH_HOST=$HOST BENCH_PORT=$PORT xcodegen generate -q
# BenchPort as an integer, as v13 reads it.
/usr/libexec/PlistBuddy -c "Delete :BenchPort" -c "Add :BenchPort integer $PORT" Info.plist
rm -rf build
nice -n 19 xcodebuild -project RindBenchAll.xcodeproj -target RindBenchAll -configuration Release -sdk iphoneos \
  SYMROOT=$PWD/build OBJROOT=$PWD/build/obj ARCHS=arm64 IPHONEOS_DEPLOYMENT_TARGET=17.0 \
  CODE_SIGNING_ALLOWED=NO CODE_SIGNING_REQUIRED=NO CODE_SIGN_IDENTITY= RIND_DEVBENCH_LIB="$LIB" build -quiet
APP=build/Release-iphoneos/RindBenchAll.app
mkdir -p out && rm -rf out/Payload && mkdir out/Payload && cp -R "$APP" out/Payload/
(cd out && rm -f RindBenchAll-v${VER:-14.1}-$PORT.ipa && zip -q -r RindBenchAll-v${VER:-14.1}-$PORT.ipa Payload && rm -rf Payload)
ls -la out/RindBenchAll-v${VER:-14.1}-$PORT.ipa
