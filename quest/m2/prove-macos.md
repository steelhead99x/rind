# [S] The Lean proofs translate and build on aarch64 macOS

## Goal

The flake's `prove` dev shell exists on aarch64-darwin, and `nix develop .#prove --command admin/prove lean` on a Mac translates every target's Rust with Charon and Aeneas and builds the Lean proofs, but for the steps that need an x86_64 or Linux host (the intrinsic vectors and `rind_isa`), which it reports as not run and exits nonzero for, so a Mac run never passes as the whole check. An agent on the Mac mini or a laptop iterates on a proof in minutes instead of waiting on a dispatched `prove` run.

## Plan

The maintainer kept this quest when picking #1043 to merge; it has no open decisions.

Found on 2026-11-25 while proving x86_64 ChaCha20-Poly1305 on the Mac mini ([kixel-ai/rind#1043](https://github.com/kixel-ai/rind/pull/1043)):

- The `prove` shell is Linux-only because the flake fetches only Aeneas's Linux tarballs, but Aeneas's nightly release also ships `aeneas-macos-aarch64.tar.gz` (Charon, its driver, and Aeneas, with `libgmp` beside them). With it, the flake's nightly `rust-charon` built for aarch64-darwin, and a `cargo miri setup --target=x86_64-unknown-linux-gnu` sysroot as `charon-sysroots` builds, the x86_64 translation and its KDF slice ran in about 4 minutes, and `lake build Rind.X86_64.Axioms` passed against it. A dispatched `prove` run took about 1.5 hours that day, mostly queued.
- What the manual run needed: the driver links `librustc_driver` and `libLLVM` by bare name, so the wrapper sets `DYLD_FALLBACK_LIBRARY_PATH` (not `DYLD_LIBRARY_PATH`, which made the build scripts' linker load Rust's `libLLVM` and abort); `admin/prove` uses GNU `sed -i`, `realpath -e`, `sha256sum`, and bash 4's `${x,,}`, which the shell must provide on macOS; `charon-sysroots` must build the aarch64 and armv7 sysroots too.
- Decide at setup what the host cannot run (`simd-vectors` needs x86_64 with AVX2, `rind_isa` and the HOL Light steps Linux), build the Lean proofs anyway, then exit nonzero naming the skipped steps.
