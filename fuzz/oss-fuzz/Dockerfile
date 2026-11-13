FROM gcr.io/oss-fuzz-base/base-builder-rust
# jq, zip, and xxd (vim-common) for the seed corpora; aws-lc-sys, the differential oracle, builds C.
RUN apt-get update && apt-get install -y --no-install-recommends jq zip cmake vim-common
RUN git clone --depth 1 https://github.com/kixel-ai/rind && \
    git -C rind submodule update --init --depth 1 thirdparty/wycheproof
WORKDIR $SRC/rind
COPY build.sh $SRC/
