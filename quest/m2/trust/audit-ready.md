# [M] A security reviewer can start from one document

## Goal

One document in the repository gives an outside security reviewer what they need to scope a review of rind without reading the whole tree: what is in scope and what is not, the threat model, where each line of code came from and at which pin, what each automated check does and does not establish, and what has never been checked by anything. The maintainer can hand it to an auditor, or an adopter's security team can read it on their own.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ write the package. No audit is commissioned by this, and none is promised; the point is that the cost of starting one, or of an adopter's own review, drops.

- Collect, don't restate. Nearly all of it exists: AGENTS.md's rules are the security claims, TESTING.md has the checks, ARCHITECTURE.md the layering, UPSTREAM.md and `thirdparty/` the pins, `benchmarks/verified.toml` the proofs with their caveats, `admin/ctgrind`, `admin/ct-vartime`, `admin/ct-sde`, `admin/ct-qemu`, and `admin/ct-binsec` the constant-time checks. The document is the map, with a paragraph per area and a link.
- Threat model: what an attacker is assumed able to do (choose every input, measure time remotely and on the same host) and what is out (faults, power, speculative execution beyond what the constant-time rule gives, a compromised build machine). Draft it from what the checks actually defend, and ask the maintainer to confirm it under `Waiting`, since it is a claim made in their name.
- Provenance per primitive and backend: s2n-bignum, BoringSSL, aws-lc, libcrux and HACL*, fiat-crypto, curve25519-dalek, or written here, with the pinned revision and how the import is regenerated and checked (`admin/import-*`, `admin/parse-asm`). Generate the table from the pins if they are machine-readable, so it cannot go stale.
- For each check, one honest line on its limits, in the manner of PLATFORMS.md's "constant time is unchecked on wasm": what ctgrind's coverage depends on, what a proof's hand model assumes, which code only fuzzing reaches.
- The list an auditor most wants is where the checks are thinnest. Build it from the coverage report and the proofs table, not from memory: hand-written arithmetic with neither a proof nor a differential test, and public functions the unit tests never call. Lacking one check is not lacking all of them, so each entry says what does reach it (Wycheproof vectors, a unit test, a fuzz target), and only code none of them reaches is listed as unchecked.
- The `unsafe` in the tree, counted by area, with what justifies each area (`rind::doc::inline_assembly_safety` for the assembly).
- Link it from SECURITY.md once [that exists](/quest/m2/trust/security-policy.md) and from the README.

## Related

- [The coverage report measures the published code under its own tests](/quest/m2/confidence/coverage-report.md) - the source for what no test reaches
- [rind runs in OSS-Fuzz](/quest/m4/oss-fuzz.md) - continuous fuzzing, which a reviewer will ask about
