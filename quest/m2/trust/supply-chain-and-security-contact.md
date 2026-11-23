# [M] Upgrade supply-chain posture with cargo-vet, SLSA attestations, reproducible builds, OpenSSF Scorecard, and security contact

## Goal

Downstream security teams inspecting `rind` find modern supply-chain hygiene enforced in CI and releases: `cargo-vet` initialized and checked, SLSA build provenance attestations attached to release artifacts, a reproducible-build verification job for prebuilt FFI/binary artifacts, an OpenSSF Scorecard workflow, and complete vulnerability-reporting metadata (GHSA CVE-request note, `security.txt`, and security contact/PGP instructions).

## Plan

Planned with the maintainer on 2026-11-21 (`/quest-plan`): ✅ upgrade supply-chain and vulnerability-reporting posture across `cargo-vet`, SLSA, reproducible builds, OpenSSF Scorecard, and `security.txt`/PGP/CVE documentation (rejected: skip).

- **`cargo-vet`**:
  - Initialize `supply-chain/` (`cargo vet init`), configure trusted upstream criteria/imports (e.g. Mozilla/Google/Bytecode Alliance audit sets where appropriate) for `rind`'s tiny dependency graph (`getrandom`, etc.), and add a CI check so no unvetted dependency can enter the published `rind` crate tree.
- **SLSA build provenance attestations**:
  - Add GitHub artifact attestations (`actions/attest-build-provenance`) to the release workflows (crates/wheels/prebuilt native libraries for `rind-python`, `rind-dart`, `rind-openssl`, etc.) so downloaded binaries carry verifiable SLSA provenance.
- **Reproducible-build verification**:
  - Add a CI check (nightly or release workflow) that builds prebuilt release libraries twice in clean environments (or verifies deterministic flags/timestamps) and asserts bit-for-bit identical output (or documents any platform-specific linker non-determinism such as macOS codesigning).
- **OpenSSF Scorecard**:
  - Add the official `ossf/scorecard-action` workflow, fix low-hanging Scorecard findings (pinned GitHub Action SHAs, minimal `permissions:` blocks, branch protection notes), and badge/link the result where appropriate.
- **Vulnerability reporting & CVE clarity**:
  - Update `SECURITY.md` to explicitly state that GitHub Security Advisories (GHSA) will be used to request CVEs for confirmed vulnerabilities, and add `.well-known/security.txt` (on the website `site/public/.well-known/security.txt` and/or repo root).
  - Leave any external contact address or PGP public key fingerprint as a clear maintainer decision/fill-in in the PR rather than inventing one.
