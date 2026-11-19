# shellcheck shell=bash
# Source this: NDK and cargo environment for armv7-linux-androideabi.
# The Fire TV Stick (AFTSSS) runs Android 9, API 28; the build targets that API.
# Needs rustup with the target (`rustup target add armv7-linux-androideabi`),
# an Android NDK (r28c was used) and, for vendored OpenSSL, perl and make.
: "${ANDROID_HOME:=$HOME/Android/Sdk}"
: "${ANDROID_NDK_HOME:=$(printf '%s\n' "$ANDROID_HOME"/ndk/* | tail -1)}"
ANDROID_API="${ANDROID_API:-28}"
# The NDK names its host toolchain linux-x86_64 or darwin-x86_64; override with NDK_HOST_TAG.
NDK_HOST_TAG="${NDK_HOST_TAG:-$(uname -s | tr '[:upper:]' '[:lower:]')-x86_64}"
TOOLCHAIN="$ANDROID_NDK_HOME/toolchains/llvm/prebuilt/$NDK_HOST_TAG"
export ANDROID_HOME ANDROID_NDK_HOME ANDROID_NDK_ROOT="$ANDROID_NDK_HOME"
export PATH="$TOOLCHAIN/bin:$PATH"
export CC_armv7_linux_androideabi="$TOOLCHAIN/bin/armv7a-linux-androideabi${ANDROID_API}-clang"
export CXX_armv7_linux_androideabi="$TOOLCHAIN/bin/armv7a-linux-androideabi${ANDROID_API}-clang++"
export AR_armv7_linux_androideabi="$TOOLCHAIN/bin/llvm-ar"
export CARGO_TARGET_ARMV7_LINUX_ANDROIDEABI_LINKER="$CC_armv7_linux_androideabi"
export CARGO_TARGET_ARMV7_LINUX_ANDROIDEABI_AR="$AR_armv7_linux_androideabi"
export ANDROID_PLATFORM="android-${ANDROID_API}"
export LLVM_STRIP="$TOOLCHAIN/bin/llvm-strip"
# Keep the target dir small and out of the checkout: about 2.3 GB for the bench set below.
export CARGO_TARGET_DIR="${CARGO_TARGET_DIR:-$HOME/tmp/rind-armv7-target}"
