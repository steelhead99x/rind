#!/bin/bash -eu
# OSS-Fuzz's build script for rind: every cargo-fuzz target, with the seed
# corpora sh/fuzz-seed.sh writes. This directory is what google/oss-fuzz's
# projects/rind copies; check it with that repo's `infra/helper.py check_build`.

cd "$SRC/rind"

# OSS-Fuzz's coverage build fails on debug assertions in std's
# instrumentation, as rustls's build notes.
if [ "$SANITIZER" = "coverage" ]; then
    export RUSTFLAGS="$RUSTFLAGS -C debug-assertions=no"
    export CFLAGS=""
fi

cargo fuzz build -O
sh/fuzz-seed.sh

for target in $(cargo fuzz list); do
    cp "target/x86_64-unknown-linux-gnu/release/$target" "$OUT/"
    if [ -d "fuzz/corpus/$target" ]; then
        zip -qjr "$OUT/${target}_seed_corpus.zip" "fuzz/corpus/$target"
    fi
done
