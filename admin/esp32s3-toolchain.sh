# Sourced by admin/esp32s3-sha256-layout and admin/esp32s3-sha512-layout:
# the esp toolchain's paths, under $HOME/.espressif where
# .github/actions/esp32s3-toolchain installs it unless RIND_ESP_* or
# RIND_XTENSA_BIN say otherwise, and `esp_toolchain_env`.
# shellcheck shell=sh disable=SC2034 # The sourcing script uses these.

esp=${RIND_ESP_ROOT:-"$HOME/.espressif"}
rustc=${RIND_ESP_RUSTC:-"$esp/rust-nightly-x86_64-unknown-linux-gnu/rustc/bin/rustc"}
cargo=${RIND_ESP_CARGO:-"$esp/rust-nightly-x86_64-unknown-linux-gnu/cargo/bin/cargo"}
xtensa_bin=${RIND_XTENSA_BIN:-"$esp/xtensa-esp-elf/bin"}
objdump=$xtensa_bin/xtensa-esp32s3-elf-objdump
readelf=$xtensa_bin/xtensa-esp32s3-elf-readelf
nm=$xtensa_bin/xtensa-esp32s3-elf-nm
ar=$xtensa_bin/xtensa-esp32s3-elf-ar
gcc=$xtensa_bin/xtensa-esp32s3-elf-gcc
ld=$xtensa_bin/xtensa-esp32s3-elf-ld

# Puts the toolchain first on PATH and CARGO_HOME under directory $1.
#
# cargo's nightly -Z is the esp cargo; rustup's stable cargo must not win.
# -Z build-std resolves the sysroot's proc_macro crate, which depends on
# rustc-literal-escaper. That crate is in the rust-src vendor tree. A
# project .cargo/config is not visible to the std resolution, and --offline
# against an empty registry fails before it looks there. A cargo home that
# only replaces crates.io with that vendor tree resolves it.
esp_toolchain_env() {
  PATH="$xtensa_bin:$(dirname "$cargo"):$(dirname "$rustc"):$PATH"
  export PATH
  hash -r
  sysroot=$("$rustc" --print sysroot)
  vendor="$sysroot/lib/rustlib/src/rust/library/vendor"
  set -- "$1" "$vendor"/rustc-literal-escaper-*
  if [ ! -d "$2" ]; then
    printf 'missing vendored std sources under %s\n' "$vendor" >&2
    exit 1
  fi
  mkdir -p "$1/cargo-home"
  cat >"$1/cargo-home/config.toml" <<CONFIG
[source.crates-io]
replace-with = "vendored-sources"

[source.vendored-sources]
directory = "$vendor"
CONFIG
  CARGO_HOME="$1/cargo-home"
  export CARGO_HOME
}
