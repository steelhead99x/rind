#!/bin/bash
# Builds RindBench-android.apk without Gradle: cargo (NDK clang) -> javac -> d8 -> aapt2 -> zipalign -> apksigner.
# Needs ANDROID_HOME (SDK with build-tools 35, platforms/android-35, ndk), JDK 17+, rustup target aarch64-linux-android.
set -eu
cd "$(dirname "$0")"
HERE=$PWD
SDK=${ANDROID_HOME:-$HOME/Android/Sdk}
BT=$SDK/build-tools/35.0.0
JAR=$SDK/platforms/android-35/android.jar
NDK=${ANDROID_NDK_HOME:-$(ls -d $SDK/ndk/* | sort -V | tail -1)}
TC=$NDK/toolchains/llvm/prebuilt/linux-x86_64/bin
API=30
export CARGO_TARGET_AARCH64_LINUX_ANDROID_LINKER=$TC/aarch64-linux-android$API-clang
export CC_aarch64_linux_android=$TC/aarch64-linux-android$API-clang
export CXX_aarch64_linux_android=$TC/aarch64-linux-android$API-clang++
export AR_aarch64_linux_android=$TC/llvm-ar
export ANDROID_NDK_HOME=$NDK ANDROID_NDK_ROOT=$NDK
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$HOME/rind-devbench/target}
export PATH=$TC:$PATH
OUT=$HERE/out; rm -rf $OUT; mkdir -p $OUT/classes $OUT/apk/lib/arm64-v8a $OUT/apk/assets
(cd .. && nice -n 19 cargo +1.98.1 build --release --lib --target aarch64-linux-android -j ${JOBS:-6} ${CARGO_FEATURES:-})
cp $CARGO_TARGET_DIR/aarch64-linux-android/release/librind_devbench.so $OUT/apk/lib/arm64-v8a/
$TC/llvm-strip --strip-debug $OUT/apk/lib/arm64-v8a/librind_devbench.so
cp -R ../../rind-rustls/tests/keys $OUT/apk/assets/keys
JH=${JAVA_HOME:-}; JAVAC=${JH:+$JH/bin/}javac
$JAVAC --release 11 -cp $JAR -d $OUT/classes $(find src -name '*.java')
$BT/d8 --release --min-api 26 --lib $JAR --output $OUT/apk $(find $OUT/classes -name '*.class')
$BT/aapt2 link -o $OUT/base.apk -I $JAR --manifest AndroidManifest.xml -A $OUT/apk/assets --min-sdk-version 26 --target-sdk-version 35
(cd $OUT/apk && zip -q -r ../base.apk classes.dex lib)
$BT/zipalign -f -p 4 $OUT/base.apk $OUT/aligned.apk
KS=$HOME/.android/rindbench-debug.keystore
[ -f $KS ] || keytool -genkeypair -keystore $KS -storepass android -keypass android -alias rindbench -keyalg RSA -keysize 2048 -validity 10000 -dname "CN=RindBench debug"
$BT/apksigner sign --ks $KS --ks-pass pass:android --key-pass pass:android --out $OUT/RindBench-android.apk $OUT/aligned.apk
$BT/apksigner verify $OUT/RindBench-android.apk && ls -la $OUT/RindBench-android.apk
