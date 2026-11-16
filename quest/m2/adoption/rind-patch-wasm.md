# [XS] rind-patch forwards ring's browser feature

## Goal

A binary that patches ring with [rind-patch](https://github.com/kixel-ai/rind-patch) and builds for `wasm32-unknown-unknown` gets the browser's random source when a dependency asks ring for it, as quinn-proto does with `wasm32_unknown_unknown_js`, instead of failing in getrandom's build.

## Plan

rind-ring's `wasm32_unknown_unknown_js` now turns on getrandom's `wasm_js`, as ring's turns on its `js`. rind-patch's shim declares the feature but forwards nothing, so a patched tree loses it.

- In rind-patch's `ring/Cargo.toml`, forward it: `wasm32_unknown_unknown_js = ["rind-ring/wasm32_unknown_unknown_js"]`, and require the rind-ring release that has it, since the shim resolves against crates.io and an older rind-ring lacks the feature.
- Update the comment there that says every feature changes nothing.
- Check it with `sh/patch.sh` here, and by building patch/fixture for `wasm32-unknown-unknown` with the feature on.

## Waiting

- kixel-ai/rind: a rind-ring release after 0.17.4 carries `wasm32_unknown_unknown_js` with its getrandom dependency; `cargo info rind-ring` lists it.
