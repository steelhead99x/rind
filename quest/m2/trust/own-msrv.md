# [XS] CI checks each crate on the Rust version it declares

## Goal

Every published crate whose `rust-version` differs from rind's, rind-openmls's 1.91 today, is checked on that version wherever `sh/dispatch.sh`'s `msrv` module checks the rest, and the README's Versions section drops "CI does not yet check such a crate on its own `rust-version`".

## Plan

The `msrv` module leaves out every package whose `rust-version` differs from rind's (`sh/dispatch.sh`, the `newer` list), and `devShells.msrv` in `flake.nix` holds only the workspace's toolchain, so nothing checks rind-openmls's declared 1.91. A declared version nothing checks has been false twice: rind-rustls declared 1.85 while rind needed 1.89 (kixel-ai/rind#33), and rind declared 1.89 while its code needed 1.90 (kixel-ai/rind#199).

- Check each left-out package on its own `rust-version` instead of skipping it, with a toolchain for each distinct declared version, so a new adapter with its own `rust-version` needs no edit to the module or the flake.
- Run it whenever the module runs (`sh/dispatch.sh`'s `msrv` scope: any crate, `Cargo.toml`, `Cargo.lock`, or the flake), since a lockfile bump alone can raise an adapter's dependencies past its declared Rust. Say in the PR what the added toolchain costs the gate.
- Maintainer, 2026-11-15 ([comment](https://github.com/kixel-ai/rind/pull/770#issuecomment-6886687863)): ✅ keep this quest (rejected: drop).
