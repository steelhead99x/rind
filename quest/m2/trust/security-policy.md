# [XS] rind says how to report a vulnerability

## Goal

`SECURITY.md` at the repository's root tells a reporter to use GitHub's private vulnerability reporting, what counts as a vulnerability in rind, and which versions get fixes, and GitHub's Security tab shows it.

## Plan

Decided 2026-11-12 (maintainer, /quest-audit): ✅ write it.

- Private vulnerability reporting is already enabled (`gh api repos/kixel-ai/rind/private-vulnerability-reporting` returned `{"enabled":true}` that day), so the file points at the repository's "Report a vulnerability" button and adds no email address.
- Scope, from AGENTS.md's own rules, which are what rind promises: a panic or unbounded cost on hostile input, a secret-dependent branch, index, or variable-time instruction, a wrong result, and a key, keyed state, or heap scratch derived from a private key left unwiped where AGENTS.md says it is wiped. Say what is out: the unpublished bench, fuzz, and timing crates, and what a wasm engine's compiler does to constant-time code, which PLATFORMS.md says is unchecked. That excludes only the engine: a secret-dependent branch or index in rind's own source is in scope on every target, wasm included.
- Supported versions: the latest release of `rind` and of each adapter, unless [the stability policy](/quest/m2/trust/stability-policy.md) has settled backports by then.
- Make no promise the maintainer has not made: no response time, no bounty, no embargo length. Write the draft without them and ask the maintainer in the PR whether to add any.
- RustSec is where Rust users look. Say that a fixed vulnerability gets a RustSec advisory, if the maintainer confirms that in the PR; filing one is a post outside the org and theirs to approve each time.
- Link it from the README and from CONTRIBUTING.md.
