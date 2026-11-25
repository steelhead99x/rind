# Ubuntu 24.04's git (2.43) fetches with protocol v2: GitHub refuses the
# shallow protocol v0 fetch that 20.04's git 2.25 makes.
FROM gcr.io/oss-fuzz-base/base-builder-rust:ubuntu-24-04
# The base image's nightly predates fuzz/Cargo.toml's rust-version and is too
# old to build cargo-fuzz, so the image ships without it. The install line is
# the base's own install_rust.sh one. OSS-Fuzz's compile copies the default
# toolchain's rust-src for coverage reports, so the pin is the default too.
ENV RUSTUP_TOOLCHAIN=nightly-2026-01-20
RUN rustup toolchain install $RUSTUP_TOOLCHAIN --profile minimal --component rust-src \
    && rustup default $RUSTUP_TOOLCHAIN \
    && cargo install cargo-fuzz --locked && rm -rf /rust/registry
# jq, zip, and xxd for the seed corpora; aws-lc-sys, the differential oracle, builds C.
RUN apt-get update && apt-get install -y --no-install-recommends jq zip cmake xxd
RUN git clone --depth 1 https://github.com/kixel-ai/rind
WORKDIR $SRC/rind
COPY build.sh $SRC/
