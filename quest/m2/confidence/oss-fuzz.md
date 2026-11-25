# [XS] rind runs in OSS-Fuzz

## Goal

rind's `fuzz` crate targets run continuously in OSS-Fuzz, with crashes reported to the maintainer, and its coverage shows on OSS-Fuzz's dashboard.

## Plan

- Promoted from m4 to `m2/confidence` on 2026-11-21 (maintainer, /quest-plan): ✅ promote to m2 (rejected: keep in m4). The upstream PR text is already approved and continuous OSS-Fuzz is an immediate assurance and public-trust signal.
- `fuzz/oss-fuzz/` holds `project.yaml`, `Dockerfile`, and `build.sh`; OSS-Fuzz's `helper.py` built all 20 targets of the time under ASan and coverage and passes `check_build`. Keep them in sync with what google/oss-fuzz's `projects/rind` holds once it lands.
- This was one of three children of an assurance epic (maintainer, 2026-11-07). On 2026-11-09 the maintainer chose ✅ ACVP to m2 and cryptofuzz deleted (rejected: retarget cryptofuzz at MozillaSecurity's fork, leave both in m4): ACVP is static vectors that need no outside approval, and cryptofuzz's upstream, guidovranken/cryptofuzz, is gone, with OSS-Fuzz's own cryptofuzz project disabled. Don't plan cryptofuzz again without a maintained upstream.
- Decided 2026-11-18 (maintainer, /quest-complete): ✅ approve the drafted google/oss-fuzz PR below as written (rejected: hold, reject). An agent copies `fuzz/oss-fuzz/*` to `projects/rind/` in a fork of google/oss-fuzz and opens it, now that kixel-ai/rind#639 is on `main` (OSS-Fuzz clones `main`, whose image lacks the `basenc` older `sh/fuzz-seed.sh` used), correcting the text's facts first: its count of 22 predates the 25 `[[bin]]` entries `fuzz/Cargo.toml` holds on 2026-11-18 (recount with `cargo fuzz list`), and its oracle sentence below is wrong for more than `blind_rsa` and `vrf`, since `argon2` compares with RustCrypto, `oprf` checks rind against itself, and `openssl` compares with rind's own API, among others; read each target's oracle in `fuzz/fuzzer/` and say what each group checks against. Such factual corrections keep the approval. `primary_contact` (kixelated@gmail.com) must be a Google account to see crash reports. Check with `gh pr list --repo google/oss-fuzz --search rind`. The approved text:
  > **Add rind**
  > [rind](https://github.com/kixel-ai/rind) is a pure-Rust cryptography library (AES-GCM, ChaCha20-Poly1305, ECDSA/Ed25519/RSA, X25519/ECDH, ML-KEM, HPKE) with x86_64 and aarch64 assembly. It backs TLS (via a rustls provider) and WebRTC (str0m, dimpl) in [MoQ](https://github.com/moq-dev/moq). Its 22 cargo-fuzz targets check rind against aws-lc-rs on the same input, except `blind_rsa` and `vrf`, which aws-lc-rs lacks and which check rind against itself. The project files are maintained upstream in `fuzz/oss-fuzz/`.
