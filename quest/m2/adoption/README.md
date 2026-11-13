# Adoption beyond MoQ

## Goal

Popular projects that gain from rind's pure-Rust build or its ECC speed, and
whose crypto is less security-critical, can choose rind: through upstream
feature or provider-hook PRs, `rind-*` adapters, and rind packages for other
languages, with whatever rind itself lacks for them planned here too.

## Plan

Decided with the maintainer on 2026-11-04, in a planning interview. Settled;
don't ask again (✅ is the chosen option):

- Milestone: m2 ✅ / m3.
- Targets: rind-str0m, opendal's provider-neutral hook, rustls 0.24,
  Python, and Dart ✅. Node, React Native, Go, Java, .NET,
  Swift, Zig, and C libraries are out: they need OpenSSL's breadth or FIPS,
  which [m4](/quest/m4/README.md) holds, and rind wins there only on
  asymmetric ECC.
- opendal needs no quest: it already ships
  `http-transport-reqwest-rustls-no-provider`
  ([apache/opendal#7582](https://github.com/apache/opendal/pull/7582)), which
  the [migration prompt](/MIGRATE.md) can turn on.
- Big names on RustCrypto are marketing wins, since rind is several times
  faster ([BENCHMARKS.md](/BENCHMARKS.md)'s `nixos2`, an i7-8700: RSA-2048
  verify about 4.7x, P-256 sign and ECDH about 5x, ChaCha20-Poly1305 per
  packet about 3x, AES-GCM about 2x). Decided 2026-11-09 (maintainer,
  /quest-unblock): Deno and snow are dropped, Deno because it is
  deprecated and rind-snow by closing
  [#470](https://github.com/kixel-ai/rind/pull/470) on purpose.
  Considered and left out: RustFS
  (already links aws-lc-rs), YARA-X, age, Turso, rustic (needs a raw
  Poly1305 API), Kanidm and Servo (forbid AI-written contributions; Servo
  dropped on 2026-11-07 in [#475](https://github.com/kixel-ai/rind/pull/475)),
  Arti (security bar), and Bitwarden and Matrix (need wasm).
- Patches and issues to downstream projects: drop them and let projects pull
  rind themselves ✅ (rejected: keep preparing them). The maintainer dropped
  llrt, rusty-s3, librespot, Lemmy, tailscale-rs, and Apache Iggy on
  2026-11-07, and Deno and str0m's upstream fixes on 2026-11-09. Decided
  2026-11-11 (maintainer, /quest-unblock): rind files no upstream PRs to get
  itself adopted, so quinn's provider-neutral PR, rustls's provider list, and
  Bun (asymmetric crypto and SHA-3) are dropped too (rejected: keep them).
- No rind-graviola ✅: build it only if big crates use graviola directly.
  None does; every notable graviola user (llrt, rusty-s3, wtx, oxish) picks it
  with an optional feature, and `[patch]` cannot swap in a crate of another
  name, so a `rind` feature beside theirs is the path.
- Upstream PRs, issues, and discussions are outward-facing: each quest
  prepares the change and its text, then asks the maintainer before posting
  ✅ / starting the quest authorizes it. Posts carry the AI marker.
- Core-stack maintainers decline young providers by name
  ([quinn-rs/quinn#2253](https://github.com/quinn-rs/quinn/issues/2253),
  [transact-rs/sqlx#4408](https://github.com/transact-rs/sqlx/issues/4408)),
  so PRs to them are provider-neutral and stand on their own merits.
- Other-language packages live in this workspace as `rind-<consumer>` crates
  released by its CI ✅ / separate repositories; each language gets rind's own
  API and a second package with the popular library's interface ✅.
- rind-rustls's `default_provider()` keeps aws-lc-rs's algorithm list,
  P-521 included ✅ / drop P-521 as ring does (decided 2026-11-05 on
  [#375](https://github.com/kixel-ai/rind/pull/375), which has the sizes): it
  is already smaller than aws-lc-rs's provider.
- Whatever these consumers need from rind itself is planned now: the
  WebCrypto set (AES-192, MD5, RSA-OAEP key labels and SPKI export, AES key
  wrap with padding, all landed) and platform coverage. RSA-2048 signing, which JWT's RS256 needs, is level with the
  fastest library on x86_64 in [BENCHMARKS.md](/BENCHMARKS.md).
- Decided 2026-11-12 (maintainer, /quest-audit), after an audit of what keeps
  a project from choosing rind. The maintainer picked four bets ✅: RustCrypto's
  traits and a `[patch]` spike, which are
  [their own epic](/quest/m2/rustcrypto/README.md), and here
  [a `no_std` build](/quest/m2/adoption/no-std.md) and
  [adapters on wasm32](/quest/m2/adoption/wasm-adapters.md), which Bitwarden
  and Matrix were left out for above. An npm package was offered and not
  picked, so Node stays out as decided on 2026-11-04. Considered and left out,
  so don't raise them again without new evidence:
  - An adapter for rustls's 0.24 pre-releases: the
    [rustls 0.24 adapter](/quest/m2/adoption/rind-rustls-0.24.md) waits for
    the release, and the newest that day was 0.24.0-dev.3, whose provider API
    may still change.
  - SSH (russh, ssh-key): no consumer has asked, and OpenSSH's
    ChaCha20-Poly1305 needs raw ChaCha20 and Poly1305, the API rustic was left
    out for above.
  - X.509 and PKCS#12 for the Python package: `cryptography`'s largest
    surface, and none of it is where rind is faster.
  - The primitives the most-downloaded crates would need next, in the order
    the audit read off crates.io that day: BLAKE3, BLAKE2, secp256k1, scrypt,
    AES-GCM-SIV, and AES-CCM. An algorithm outside the planned set gets a
    quest when a consumer asks, as
    [aws-lc-rs's extras](/quest/m3/parity/aws-lc-extras.md) do, and this
    order is where to start when one does.
  - A watch list of projects that add a provider hook: nothing to build, and
    rind files no upstream PRs.
  - Distribution packages (Debian, Fedora, nixpkgs): no consumer has asked,
    and a library crate reaches them through whatever application ships it.
  - A C ABI, and Go, JVM, Swift, and .NET packages: out on 2026-11-04 for
    needing OpenSSL's breadth, and nothing has changed.
