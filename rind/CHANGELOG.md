# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Other

- *(aarch64)* run s2n-bignum's narrow-multiplier schedules for the elliptic curves and for RSA-2048 on Cortex-A72, Cortex-A76, and Neoverse N1. Other aarch64 cores, including ones this crate does not recognise, keep the `_alt` schedules. The narrow path has per-routine HOL Light proofs and not yet the Lean composition

## [0.3.2](https://github.com/kixel-ai/rind/compare/rind-v0.3.1...rind-v0.3.2) - 2026-11-08

### Other

- *(cpu)* set DIT only on Apple's platforms, and document it ([#503](https://github.com/kixel-ai/rind/pull/503))

## [0.3.1](https://github.com/kixel-ai/rind/compare/rind-v0.3.0...rind-v0.3.1) - 2026-11-08

### Other

- refuse variable-time instructions on rind's secret paths ([#455](https://github.com/kixel-ai/rind/pull/455))

## [0.3.0](https://github.com/kixel-ai/rind/compare/rind-v0.2.1...rind-v0.3.0) - 2026-11-07

### Added

- a portable backend for architectures without rind assembly ([#458](https://github.com/kixel-ai/rind/pull/458))
- *(aws-lc-rs)* rind-aws-lc-rs offers aws-lc-rs 1.x's API backed by rind ([#465](https://github.com/kixel-ai/rind/pull/465))
- *(python)* pyrind, rind's API for Python ([#459](https://github.com/kixel-ai/rind/pull/459))
- *(str0m)* rind-str0m, a str0m CryptoProvider on rind ([#467](https://github.com/kixel-ai/rind/pull/467))
- wiping keys on drop is opt-in, under a `wipe` feature ([#461](https://github.com/kixel-ai/rind/pull/461))
- *(rind-dart)* rind for Dart and Flutter through FFI ([#462](https://github.com/kixel-ai/rind/pull/462))

### Fixed

- *(key_wrap)* fold unwrap_padded's AIV check into the word it reveals ([#489](https://github.com/kixel-ai/rind/pull/489))

### Other

- *(testing)* map every primitive and tier to its checks, and fill the small gaps ([#454](https://github.com/kixel-ai/rind/pull/454))
- Mutation testing ([#482](https://github.com/kixel-ai/rind/pull/482))
- run CCTV's, aws-lc's, and BoringSSL's vectors on every CPU tier ([#481](https://github.com/kixel-ai/rind/pull/481))
- *(aes-gcm)* run aws-lc's eight-way AES-192-GCM on aarch64 with SHA3 ([#460](https://github.com/kixel-ai/rind/pull/460))
- The hash and KDF glue is proven ([#476](https://github.com/kixel-ai/rind/pull/476))

## [0.2.1](https://github.com/kixel-ai/rind/compare/rind-v0.2.0...rind-v0.2.1) - 2026-11-07

### Added

- [**breaking**] each adapter's version matches the upstream it adapts ([#440](https://github.com/kixel-ai/rind/pull/440))
- *(bench)* measure Apple M4 natively in the bench report ([#435](https://github.com/kixel-ai/rind/pull/435))
- *(cpu)* hold DIT across a batch of calls, putting M1 AES-GCM ahead of aws-lc-rs ([#431](https://github.com/kixel-ai/rind/pull/431))
- *(aes)* AES-192 in every AES mode on every backend ([#414](https://github.com/kixel-ai/rind/pull/414))
- *(digest)* MD5 under digest::legacy ([#412](https://github.com/kixel-ai/rind/pull/412))

### Fixed

- *(ctgrind)* type the armv7 key-wrap-with-padding test's lengths ([#426](https://github.com/kixel-ai/rind/pull/426))

### Other

- *(release)* ship rind as 0.2.1, not 0.3.0 ([#457](https://github.com/kixel-ai/rind/pull/457))
- *(aarch64)* run s2n-bignum's faster _alt P-256 and P-384 Montgomery multiplication ([#434](https://github.com/kixel-ai/rind/pull/434))
- *(aes-gcm)* seal under 129 bytes on by-8 on the AVX tier ([#436](https://github.com/kixel-ai/rind/pull/436))
- *(aes-gcm)* pad Vale's partial blocks in registers, and re-set the open crossovers ([#430](https://github.com/kixel-ai/rind/pull/430))
- test iOS in the simulator and Android under cross ([#432](https://github.com/kixel-ai/rind/pull/432))
- *(aes-gcm)* check 16-byte tags as whole words, so by-8 opens no longer trail its seals ([#429](https://github.com/kixel-ai/rind/pull/429))
- *(ed25519)* verify without ADX through curve25519-dalek's AVX2 backend ([#415](https://github.com/kixel-ai/rind/pull/415))
- *(aarch64)* run s2n-bignum's by-8 AES-128-GCM kernels on cores with SHA3 ([#408](https://github.com/kixel-ai/rind/pull/408))
- *(aes-gcm)* hash and cipher partial blocks without memcpy on x86_64, and seal short messages on by-8 on VAES-AVX2 ([#409](https://github.com/kixel-ai/rind/pull/409))
- *(ecdsa)* derive a key pair's public key on its first read (P-256 generation ahead of BoringSSL) ([#407](https://github.com/kixel-ai/rind/pull/407))

## [0.2.0](https://github.com/kixel-ai/rind/compare/rind-v0.1.13...rind-v0.2.0) - 2026-11-06

### Added

- *(key_wrap)* AES key wrap with padding (RFC 5649) ([#418](https://github.com/kixel-ai/rind/pull/418))
- *(rsa)* load RSA keys named id-RSAES-OAEP or id-ea-rsa, as aws-lc-rs does ([#413](https://github.com/kixel-ai/rind/pull/413))
- *(rsa)* RSA public keys export as SPKI ([#411](https://github.com/kixel-ai/rind/pull/411))
- [**breaking**] audit rind's public API, and apply its decisions, before 0.2.0 ([#383](https://github.com/kixel-ai/rind/pull/383))
- *(keys)* SPKI, SEC1, and seed key formats, and compressed ECDH peers, for Bun ([#382](https://github.com/kixel-ai/rind/pull/382))
- *(cipher)* AES-CBC with PKCS#7 padding on every backend ([#381](https://github.com/kixel-ai/rind/pull/381))
- *(agreement)* [**breaking**] store, load, and export agreement keys, agreeing by reference ([#372](https://github.com/kixel-ai/rind/pull/372))
- *(signature)* ECDSA over a precomputed digest ([#379](https://github.com/kixel-ai/rind/pull/379))
- *(signature)* RSA-PSS with any salt length ([#363](https://github.com/kixel-ai/rind/pull/363))
- *(key_wrap)* AES key wrap (RFC 3394) on AES decryption for every backend ([#359](https://github.com/kixel-ai/rind/pull/359))
- *(rsa)* RSA-OAEP encryption and decryption, and RSA SPKI public keys ([#361](https://github.com/kixel-ai/rind/pull/361))
- *(cipher)* [**breaking**] AES-CTR over a 16-byte counter block with a per-key counter width ([#360](https://github.com/kixel-ai/rind/pull/360))
- *(aead)* AES-GCM with any IV length and truncated tags ([#362](https://github.com/kixel-ai/rind/pull/362))
- *(digest)* SHA3-256, SHA3-384, and SHA3-512 ([#358](https://github.com/kixel-ai/rind/pull/358))
- *(proofs)* prove aarch64 P-256 ECDSA end to end with Aeneas and Lean ([#346](https://github.com/kixel-ai/rind/pull/346))

### Fixed

- *(ctgrind)* green the nightly again: PBKDF2's HMAC out of line, and DIT denied under valgrind ([#406](https://github.com/kixel-ai/rind/pull/406))
- *(bench-report)* hold each host with quest gate --host, and measure macOS noise ([#399](https://github.com/kixel-ai/rind/pull/399))
- *(cpu)* run aarch64 Linux with DIT where Hyper-V hides it ([#370](https://github.com/kixel-ai/rind/pull/370))
- *(cpu)* run aarch64 Windows with DIT where the core has it ([#366](https://github.com/kixel-ai/rind/pull/366))
- *(x86_64)* build on the declared 1.90 rust-version, and gate on it ([#365](https://github.com/kixel-ai/rind/pull/365))

### Other

- *(digest)* start and reset a Context from a constant ([#416](https://github.com/kixel-ai/rind/pull/416))
- *(readme)* show how to use rind and link the details ([#410](https://github.com/kixel-ai/rind/pull/410))
- *(aarch64)* seal and open short AES-GCM messages in one pass ([#393](https://github.com/kixel-ai/rind/pull/393))
- *(aes)* header protection reads the sample straight into AES-NI ([#392](https://github.com/kixel-ai/rind/pull/392))
- *(readme)* credit Vale's proven kernel for short AES-GCM on VAES CPUs ([#402](https://github.com/kixel-ai/rind/pull/402))
- *(aes-gcm)* run Vale's kernel for short messages on VAES CPUs ([#391](https://github.com/kixel-ai/rind/pull/391))
- stop wiping anything but keys, keyed state, and private-key heap scratch ([#394](https://github.com/kixel-ai/rind/pull/394))
- *(sha)* pad SHA-1 and SHA-256's last block in registers on the SHA extensions ([#376](https://github.com/kixel-ai/rind/pull/376))
- *(ecdsa)* build a verifying key's multiples on its first verification (P-256 keygen 1.4x) ([#374](https://github.com/kixel-ai/rind/pull/374))
- a prompt has an agent migrate a repo to rind and report the results ([#357](https://github.com/kixel-ai/rind/pull/357))
- *(sha256)* [**breaking**] finish SHA-NI hashes in registers, and digest contexts by reference ([#352](https://github.com/kixel-ai/rind/pull/352))
- *(build)* test aarch64 Windows, x86_64 macOS, and musl ([#356](https://github.com/kixel-ai/rind/pull/356))

## [0.1.13](https://github.com/kixel-ai/rind/compare/rind-v0.1.12...rind-v0.1.13) - 2026-11-05

### Added

- *(proofs)* prove x86_64 AES-GCM on Vale's tier end to end with Aeneas and Lean ([#344](https://github.com/kixel-ai/rind/pull/344))
- *(proofs)* prove SHA-1, SHA-256, and HMAC's glue with Aeneas and Lean ([#338](https://github.com/kixel-ai/rind/pull/338))
- *(proofs)* prove aarch64 P-256's generator table in Lean ([#343](https://github.com/kixel-ai/rind/pull/343))
- *(bench)* publish BENCHMARKS.md from three hosts and the nightly CPU tiers ([#347](https://github.com/kixel-ai/rind/pull/347))
- *(proofs)* prove Ed25519 end to end with Aeneas and Lean ([#339](https://github.com/kixel-ai/rind/pull/339))
- *(proofs)* prove SHA-384 and SHA-512 end to end with Aeneas and Lean ([#337](https://github.com/kixel-ai/rind/pull/337))
- *(proofs)* prove ChaCha20 header protection end to end with Aeneas and Lean ([#335](https://github.com/kixel-ai/rind/pull/335))
- *(proofs)* prove aarch64 P-256 ECDH end to end ([#336](https://github.com/kixel-ai/rind/pull/336))
- *(proofs)* prove X25519 end to end with Aeneas and Lean ([#326](https://github.com/kixel-ai/rind/pull/326))
- *(p256)* run aarch64 ECDH through s2n-bignum's proven p256_scalarmul ([#321](https://github.com/kixel-ai/rind/pull/321))
- *(admin)* render BENCHMARKS.md from the benchmark results ([#316](https://github.com/kixel-ai/rind/pull/316))
- *(bench)* time every library on every host ([#309](https://github.com/kixel-ai/rind/pull/309))

### Fixed

- *(p256, p384, p521)* verify ECDSA without adding equal points ([#324](https://github.com/kixel-ai/rind/pull/324))
- enter the entry guard in hashing, HMAC, HKDF, PBKDF2, and constant-time comparison ([#299](https://github.com/kixel-ai/rind/pull/299))
- *(x86_64)* compute prefetch's stride address with wrapping arithmetic ([#301](https://github.com/kixel-ai/rind/pull/301))
- *(ecdsa)* draw a new nonce when s is zero ([#300](https://github.com/kixel-ai/rind/pull/300))
- *(ed25519)* [**breaking**] refuse public keys of small order ([#298](https://github.com/kixel-ai/rind/pull/298))

### Other

- *(release)* ship rind 0.1.13 and rind-ring 0.1.12 as patch releases ([#355](https://github.com/kixel-ai/rind/pull/355))
- *(sha2)* run OpenSSL's AVX2 and SHA512-instruction SHA-2 routines on x86_64 ([#353](https://github.com/kixel-ai/rind/pull/353))
- *(x86_64)* gather RSA's window entries by AVX2 ([#351](https://github.com/kixel-ai/rind/pull/351))
- *(quest)* plan adoption beyond MoQ, a marketing README, and m4 ([#341](https://github.com/kixel-ai/rind/pull/341))
- *(readme)* open with why to use rind and a generated headline chart ([#350](https://github.com/kixel-ai/rind/pull/350))
- *(quest)* triage the report's speed gaps into quests and recorded reasons ([#348](https://github.com/kixel-ai/rind/pull/348))
- *(quest)* close ECDSA verify speed with the equal-point cost accepted ([#345](https://github.com/kixel-ai/rind/pull/345))
- *(p256, p384, p521)* widen a reused ECDSA key's NAF to width 6 from its second verification ([#334](https://github.com/kixel-ai/rind/pull/334))
- *(p256, p384, p521)* add the public key's multiples to ECDSA verification in affine form ([#331](https://github.com/kixel-ai/rind/pull/331))
- *(aes-gcm)* run HACL*'s Vale AES-GCM on x86_64 with AVX and MOVBE ([#329](https://github.com/kixel-ai/rind/pull/329))
- link only the algorithms a binary names, and never inline assembly routines ([#315](https://github.com/kixel-ai/rind/pull/315))
- mark ✓ only where a current proof covers the code ([#325](https://github.com/kixel-ai/rind/pull/325))
- *(p256)* show rind's aarch64 base-point table meets s2n-bignum's proof ([#319](https://github.com/kixel-ai/rind/pull/319))
- add rind logos and credit upstream projects ([#313](https://github.com/kixel-ai/rind/pull/313))
- *(ctgrind)* check armv7's crypto extension for constant time under qemu ([#311](https://github.com/kixel-ai/rind/pull/311))
- check every import regenerates exactly at its pin, and write generated files atomically ([#304](https://github.com/kixel-ai/rind/pull/304))
- *(chacha20)* run HACL*'s verified rounds where x86_64 ran aws-lc's integer ChaCha20 ([#293](https://github.com/kixel-ai/rind/pull/293))
- *(chacha20)* run one block in general-purpose registers on x86_64 ([#287](https://github.com/kixel-ai/rind/pull/287))

## [0.1.12](https://github.com/kixel-ai/rind/compare/rind-v0.1.11...rind-v0.1.12) - 2026-11-03

### Other

- *(xchacha20poly1305)* run HChaCha20 in general-purpose registers ([#285](https://github.com/kixel-ai/rind/pull/285))
- *(sha256)* compress a message's whole blocks in place with SHA-NI ([#282](https://github.com/kixel-ai/rind/pull/282))
- README's Algorithms table shows current numbers and the reason for each accepted gap ([#283](https://github.com/kixel-ai/rind/pull/283))
- *(p384)* multiply armv7 P-384 with rind's Montgomery multiplication ([#273](https://github.com/kixel-ai/rind/pull/273))
- *(x86_64)* check VAES-AVX2 AES-GCM and SHA-NI HMAC's constant time under SDE ([#279](https://github.com/kixel-ai/rind/pull/279))
- *(mlkem)* run rind's ML-KEM on armv7 over OpenSSL's Keccak-f ([#254](https://github.com/kixel-ai/rind/pull/254))
- *(x86_64)* check AVX-512 AES-GCM's constant time under SDE ([#276](https://github.com/kixel-ai/rind/pull/276))

## [0.1.11](https://github.com/kixel-ai/rind/compare/rind-v0.1.10...rind-v0.1.11) - 2026-11-03

### Fixed

- *(rsa)* bound x86_64 power5's secret window by a mask, not a check ([#275](https://github.com/kixel-ai/rind/pull/275))
- *(x86_64)* wipe RSA's heap power tables before freeing them ([#267](https://github.com/kixel-ai/rind/pull/267))

### Other

- *(x86_64,aarch64)* start imported routines at aws-lc's alignment ([#274](https://github.com/kixel-ai/rind/pull/274))
- *(x86_64)* sign RSA by aws-lc's dual AVX-512 IFMA RSAZ ([#263](https://github.com/kixel-ai/rind/pull/263))
- *(quest)* close the AES-GCM key setup quest with the bench numbers ([#272](https://github.com/kixel-ai/rind/pull/272))
- *(p256)* run armv7 P-256 on the shared code with rind's Montgomery multiplication ([#253](https://github.com/kixel-ai/rind/pull/253))
- *(x86_64)* keep aws-lc's alignment of carried routines ([#262](https://github.com/kixel-ai/rind/pull/262))
- *(rsa)* exponentiate by a 5-bit window on aarch64 and armv7 ([#261](https://github.com/kixel-ai/rind/pull/261))
- *(aead)* build AES-GCM keys in place, check CPU features inline, and keep one aarch64 GHASH table ([#260](https://github.com/kixel-ai/rind/pull/260))
- *(rsa)* load keys faster and multiply odd-width moduli at their own width on armv7 ([#259](https://github.com/kixel-ai/rind/pull/259))
- *(hash)* compress the last whole block with the padding in one call ([#255](https://github.com/kixel-ai/rind/pull/255))

## [0.1.10](https://github.com/kixel-ai/rind/compare/rind-v0.1.9...rind-v0.1.10) - 2026-11-02

### Other

- *(aes-gcm)* set up keys and GHASH tables without serial chains or repeated work ([#239](https://github.com/kixel-ai/rind/pull/239))
- *(x86_64)* exponentiate RSA by aws-lc's 5-bit window and bn_power5 ([#224](https://github.com/kixel-ai/rind/pull/224))
- *(p256)* multiply the x86_64 generator by aws-lc's nistz256 routines ([#234](https://github.com/kixel-ai/rind/pull/234))
- *(rsa)* run armv7 RSA on aws-lc's Montgomery multiplication and the shared code ([#227](https://github.com/kixel-ai/rind/pull/227))
- *(hash)* buffer a short SHA-1/SHA-2 update with one copy ([#247](https://github.com/kixel-ai/rind/pull/247))
- *(mlkem)* keep H(ek) in the key instead of a second encoding ([#249](https://github.com/kixel-ai/rind/pull/249))
- *(aes-gcm)* run aws-lc's aesni_gcm on x86_64 CPUs with AVX and MOVBE but no VAES ([#240](https://github.com/kixel-ai/rind/pull/240))
- *(sha1, sha256, sha512)* pick the x86_64 block function once ([#248](https://github.com/kixel-ai/rind/pull/248))

## [0.1.9](https://github.com/kixel-ai/rind/compare/rind-v0.1.8...rind-v0.1.9) - 2026-11-02

### Fixed

- *(aarch64)* emit one unwind frame per imported macOS function ([#250](https://github.com/kixel-ai/rind/pull/250))
- *(x86_64)* reduce a Montgomery result equal to the modulus to zero ([#244](https://github.com/kixel-ai/rind/pull/244))

### Other

- *(hash)* finish hashes and HMAC from a chaining state, without copies ([#230](https://github.com/kixel-ai/rind/pull/230))
- *(p256, p384, p521)* verify ECDSA in one chain of doublings ([#228](https://github.com/kixel-ai/rind/pull/228))

## [0.1.8](https://github.com/kixel-ai/rind/compare/rind-v0.1.7...rind-v0.1.8) - 2026-11-02

### Fixed

- *(rsa)* sign with keys whose q is above p ([#242](https://github.com/kixel-ai/rind/pull/242))

### Other

- *(aarch64)* aws-lc's SHA-256 routine for the SHA-256 instructions ([#231](https://github.com/kixel-ai/rind/pull/231))
- *(aarch64)* aws-lc's Montgomery multiplication for 1024- and 2048-bit moduli ([#232](https://github.com/kixel-ai/rind/pull/232))
- *(mlkem)* ML-KEM-768 encapsulation without redundant Keccak-f and compression work ([#233](https://github.com/kixel-ai/rind/pull/233))
- *(aes-gcm)* keep x86_64's per-call blocks in vector registers ([#229](https://github.com/kixel-ai/rind/pull/229))

## [0.1.7](https://github.com/kixel-ai/rind/compare/rind-v0.1.6...rind-v0.1.7) - 2026-11-02

### Fixed

- clear the nightly quality lints and verify nightly passes on main ([#212](https://github.com/kixel-ai/rind/pull/212))
- wipe only what a returned value owns ([#221](https://github.com/kixel-ai/rind/pull/221))
- *(armv7)* stop wiping RSA per-call scratch ([#216](https://github.com/kixel-ai/rind/pull/216))

### Other

- *(bench)* audit every algorithm's speed against aws-lc-rs, ring, and other sources ([#191](https://github.com/kixel-ai/rind/pull/191))
- run ctgrind in its own dev shell ([#218](https://github.com/kixel-ai/rind/pull/218))
- *(aarch64)* aws-lc's Montgomery multiplication at every RSA size ([#206](https://github.com/kixel-ai/rind/pull/206))

## [0.1.6](https://github.com/kixel-ai/rind/compare/rind-v0.1.5...rind-v0.1.6) - 2026-11-02

### Fixed

- build on the declared MSRV, raised to 1.90 ([#199](https://github.com/kixel-ai/rind/pull/199))
- *(hash)* admin/structure reports only real layering edges ([#197](https://github.com/kixel-ai/rind/pull/197))
- *(rsa)* redraw q when it is within 2^(nlen/2 - 100) of p ([#204](https://github.com/kixel-ai/rind/pull/204))
- *(fuzz)* allow the PKCS#8 v2 refusal without a public key for ECDSA and RSA ([#198](https://github.com/kixel-ai/rind/pull/198))

### Other

- drop the redundant RSA key generation tests from the gate ([#201](https://github.com/kixel-ai/rind/pull/201))
- *(x86-cpu)* run one SDE model per dispatch path set ([#205](https://github.com/kixel-ai/rind/pull/205))

## [0.1.5](https://github.com/kixel-ai/rind/compare/rind-v0.1.4...rind-v0.1.5) - 2026-11-01

### Other

- *(aarch64)* aws-lc's Montgomery multiplication for RSA at other sizes ([#179](https://github.com/kixel-ai/rind/pull/179))

## [0.1.4](https://github.com/kixel-ai/rind/compare/rind-v0.1.3...rind-v0.1.4) - 2026-11-01

### Fixed

- constant-time in debug builds ([#189](https://github.com/kixel-ai/rind/pull/189))
- *(bench)* time forced CPU paths in release builds ([#181](https://github.com/kixel-ai/rind/pull/181))

### Other

- aws-lc's one-pass ChaCha20-Poly1305 on x86_64 and aarch64 ([#190](https://github.com/kixel-ai/rind/pull/190))
- *(x86_64)* square by bn_sqrx8x_internal, zeroing its scratch first ([#187](https://github.com/kixel-ai/rind/pull/187))
- *(x86_64)* aws-lc's mulx and nohw Montgomery routines for RSA at every size ([#183](https://github.com/kixel-ai/rind/pull/183))

## [0.1.3](https://github.com/kixel-ai/rind/compare/rind-v0.1.2...rind-v0.1.3) - 2026-11-01

### Fixed

- *(rsa)* generate keys in constant time ([#182](https://github.com/kixel-ai/rind/pull/182))
- fuzz the key loaders, take compressed key pair points, refuse ECDSA and RSA PKCS#8 v2 ([#166](https://github.com/kixel-ai/rind/pull/166))

## [0.1.2](https://github.com/kixel-ai/rind/compare/rind-v0.1.1...rind-v0.1.2) - 2026-11-01

### Added

- *(x86_64)* run on CPUs without SSSE3 ([#178](https://github.com/kixel-ai/rind/pull/178))
- *(x86_64)* AES and GHASH without AVX or AES-NI ([#172](https://github.com/kixel-ai/rind/pull/172))
- *(x86_64)* run on CPUs without AVX2 ([#171](https://github.com/kixel-ai/rind/pull/171))
- *(x86_64)* run on CPUs without ADX ([#169](https://github.com/kixel-ai/rind/pull/169))

### Fixed

- refuse trailing bytes after a PKCS#8 key ([#164](https://github.com/kixel-ai/rind/pull/164))

### Other

- *(x86_64)* aws-lc's RSAZ for RSA-2048 without ADX ([#177](https://github.com/kixel-ai/rind/pull/177))
- *(x86_64)* SSE-encoded AES-GCM and GHASH on every CPU ([#176](https://github.com/kixel-ai/rind/pull/176))
- *(x86_64)* aws-lc's AES-NI CTR with AVX too ([#173](https://github.com/kixel-ai/rind/pull/173))
- *(x86_64)* aws-lc's Montgomery multiplication for RSA without ADX ([#170](https://github.com/kixel-ai/rind/pull/170))
- *(sha256)* aws-lc's AVX routine on Intel without SHA-NI ([#165](https://github.com/kixel-ai/rind/pull/165))

## [0.1.1](https://github.com/kixel-ai/rind/compare/rind-v0.1.0...rind-v0.1.1) - 2026-11-01

### Added

- *(aarch64)* run on CPUs without the crypto extension ([#157](https://github.com/kixel-ai/rind/pull/157))
- accept 33-bit RSA public exponents ([#161](https://github.com/kixel-ai/rind/pull/161))
- load PKCS#8 keys carrying attributes ([#160](https://github.com/kixel-ai/rind/pull/160))
- *(signature)* export an ECDSA key's scalar and an Ed25519 key's seed ([#158](https://github.com/kixel-ai/rind/pull/158))
- *(ring)* add rind-ring, ring 0.17's API on rind ([#151](https://github.com/kixel-ai/rind/pull/151))
- *(hkdf)* HKDF-SHA384, HKDF-SHA512, and legacy HKDF-SHA1 ([#149](https://github.com/kixel-ai/rind/pull/149))

### Other

- cheaper ECDSA and RSA key loads and ECDSA verification ([#159](https://github.com/kixel-ai/rind/pull/159))

## [0.1.0](https://github.com/kixel-ai/rind/compare/rind-v0.0.0...rind-v0.1.0) - 2026-10-31

### Added

- [**breaking**] errors by role, and RSA components take only an RSA algorithm ([#142](https://github.com/kixel-ai/rind/pull/142))
- *(signature)* [**breaking**] one PublicKey, sign and verify constants, owned encodings, RSA key checks ([#140](https://github.com/kixel-ai/rind/pull/140))
- [**breaking**] aead::Key, typed tags, legacy submodules, infallible HKDF expand ([#139](https://github.com/kixel-ai/rind/pull/139))
- ECDH and ECDSA on P-521 ([#133](https://github.com/kixel-ai/rind/pull/133))
- *(agreement,kem)* [**breaking**] PrivateKey::agree, public_key(), slice ciphertexts ([#137](https://github.com/kixel-ai/rind/pull/137))
- *(pbkdf2)* PBKDF2-HMAC over SHA-1, SHA-256, SHA-384, and SHA-512 ([#127](https://github.com/kixel-ai/rind/pull/127))
- *(signature)* legacy RSA verification and keys from components ([#130](https://github.com/kixel-ai/rind/pull/130))
- *(aead)* QUIC header-protection keys ([#132](https://github.com/kixel-ai/rind/pull/132))
- *(digest)* SHA-512/256 ([#128](https://github.com/kixel-ai/rind/pull/128))
- constant-time slice comparison ([#131](https://github.com/kixel-ai/rind/pull/131))
- SHA-384/512 from aws-lc's assembly on every backend ([#107](https://github.com/kixel-ai/rind/pull/107))
- [**breaking**] rind::rand, deviation docs, and the aws-lc-rs API surface audit ([#94](https://github.com/kixel-ai/rind/pull/94))
- *(rustls)* prefer ChaCha20-Poly1305 without AES hardware ([#92](https://github.com/kixel-ai/rind/pull/92))
- [**breaking**] signature key pairs bound to algorithm constants ([#89](https://github.com/kixel-ai/rind/pull/89))
- *(hkdf)* [**breaking**] typed HKDF output bound to an algorithm constant ([#90](https://github.com/kixel-ai/rind/pull/90))
- *(aarch64)* AES-GCM from s2n-bignum's verified kernels ([#86](https://github.com/kixel-ai/rind/pull/86))
- *(arm)* ARMv8 crypto extension for AES, GHASH, and SHA on armv7 ([#84](https://github.com/kixel-ai/rind/pull/84))
- *(hmac)* [**breaking**] reusable HMAC keys bound to an algorithm constant ([#83](https://github.com/kixel-ai/rind/pull/83))
- [**breaking**] agreement and kem modules with algorithm constants ([#79](https://github.com/kixel-ai/rind/pull/79))
- *(aead)* [**breaking**] AEAD and cipher keys bound to an algorithm constant ([#75](https://github.com/kixel-ai/rind/pull/75))
- [**breaking**] digest constants replace the Hash trait ([#77](https://github.com/kixel-ai/rind/pull/77))
- [**breaking**] fold unnameable key errors into an exported KeyRejected ([#76](https://github.com/kixel-ai/rind/pull/76))
- [**breaking**] rename truncated_ct_equal to verify_truncated and return a Result instead of panicking ([#53](https://github.com/kixel-ai/rind/pull/53))
- *(aead)* [**breaking**] AesGcm::new refuses a bad key length ([#43](https://github.com/kixel-ai/rind/pull/43))
- [**breaking**] AEADs refuse over-long messages ([#34](https://github.com/kixel-ai/rind/pull/34))
- P-384 on armv7 over fiat-crypto's arithmetic ([#23](https://github.com/kixel-ai/rind/pull/23))
- raw AES, AES-CTR, and ChaCha20 on armv7 ([#21](https://github.com/kixel-ai/rind/pull/21))
- RSA key generation on armv7 ([#22](https://github.com/kixel-ai/rind/pull/22))
- build armv7 on a libcrux backend ([#8](https://github.com/kixel-ai/rind/pull/8))
- public CPU check naming the missing feature ([#12](https://github.com/kixel-ai/rind/pull/12))
- [**breaking**] SHA-1 and HMAC-SHA1 for legacy protocols ([#7](https://github.com/kixel-ai/rind/pull/7))
- HKDF under rind::hashing::hkdf ([#13](https://github.com/kixel-ai/rind/pull/13))
- *(jsonwebtoken)* add rind-jsonwebtoken ([#9](https://github.com/kixel-ai/rind/pull/9))
- raw AES, AES-CTR, and ChaCha20 under rind::cipher ([#6](https://github.com/kixel-ai/rind/pull/6))
- [**breaking**] bootstrap rind from graviola ([#1](https://github.com/kixel-ai/rind/pull/1))

### Fixed

- *(rind)* [**breaking**] declare the crate's license with every copied source ([#91](https://github.com/kixel-ai/rind/pull/91))
- *(ed25519)* wipe the hashed seed and signing nonce, as aws-lc does ([#81](https://github.com/kixel-ai/rind/pull/81))
- inherited wipes match aws-lc ([#73](https://github.com/kixel-ai/rind/pull/73))
- *(rsa)* verify and sign with moduli of any bit length ([#68](https://github.com/kixel-ai/rind/pull/68))
- wipe only what aws-lc wipes in the remaining paths ([#60](https://github.com/kixel-ai/rind/pull/60))
- wipe only what aws-lc wipes ([#58](https://github.com/kixel-ai/rind/pull/58))
- *(mlkem)* wipe ML-KEM intermediates and SHA-3 state on drop ([#52](https://github.com/kixel-ai/rind/pull/52))
- *(hash)* wipe the SHA message schedule after each compress call ([#41](https://github.com/kixel-ai/rind/pull/41))
- wipe HMAC and HMAC-DRBG state on drop ([#42](https://github.com/kixel-ai/rind/pull/42))
- wipe HMAC's padded key block ([#30](https://github.com/kixel-ai/rind/pull/30))
- refuse P-256 and P-384 coordinates at or above the field prime ([#25](https://github.com/kixel-ai/rind/pull/25))

### Other

- README describes rind's own API, and MIGRATING.md maps every ring and aws-lc-rs item ([#145](https://github.com/kixel-ai/rind/pull/145))
- *(signature)* check every ECDSA constant against aws-lc-rs ([#129](https://github.com/kixel-ai/rind/pull/129))
- *(arm)* X25519 shared secret on BoringSSL's NEON ladder ([#120](https://github.com/kixel-ai/rind/pull/120))
- *(x86_64)* AES-GCM on BoringSSL's VAES kernels for long messages ([#124](https://github.com/kixel-ai/rind/pull/124))
- *(x86_64)* AES-GCM tails in one masked pass, hashed with one reduction ([#116](https://github.com/kixel-ai/rind/pull/116))
- *(arm)* run aws-lc's ChaCha20 and NEON Poly1305 on armv7 ([#106](https://github.com/kixel-ai/rind/pull/106))
- *(lints)* walk the in-place aarch64 AES-GCM kernels in the codegen job ([#117](https://github.com/kixel-ai/rind/pull/117))
- *(arm)* X25519 and Ed25519 from curve25519-dalek ([#113](https://github.com/kixel-ai/rind/pull/113))
- *(ec)* multiply secret P-256 and P-384 scalars by s2n-bignum ([#108](https://github.com/kixel-ai/rind/pull/108))
- *(aarch64)* run s2n-bignum's by-8 AES-256-GCM kernels on cores with SHA3 ([#114](https://github.com/kixel-ai/rind/pull/114))
- *(quest)* drop two low-payoff fastest quests, plan aarch64 alt kernels ([#112](https://github.com/kixel-ai/rind/pull/112))
- *(aarch64)* run s2n-bignum's AES-GCM kernels in place ([#110](https://github.com/kixel-ai/rind/pull/110))
- mark unverified code that measured faster than a verified alternative ([#105](https://github.com/kixel-ai/rind/pull/105))
- *(p384)* multiply the generator by an affine comb ([#102](https://github.com/kixel-ai/rind/pull/102))
- *(arm)* cache RSA's Montgomery setup and compute it in six squarings ([#101](https://github.com/kixel-ai/rind/pull/101))
- run the armv7 job locally with `just armv7` ([#96](https://github.com/kixel-ai/rind/pull/96))
- close the verified aarch64 AES-GCM setup quest ([#97](https://github.com/kixel-ai/rind/pull/97))
- attribute every algorithm's source and license ([#88](https://github.com/kixel-ai/rind/pull/88))
- stop clearing vector registers after secret operations ([#80](https://github.com/kixel-ai/rind/pull/80))
- [**breaking**] stop tracking graviola ([#87](https://github.com/kixel-ai/rind/pull/87))
- ctgrind on armv7, fixing what it finds in the arm backend ([#36](https://github.com/kixel-ai/rind/pull/36))
- *(sha1)* run the AVX2 path's rounds in plain Rust ([#71](https://github.com/kixel-ai/rind/pull/71))
- *(sha256)* AVX2 message schedule on x86_64 without SHA-NI ([#74](https://github.com/kixel-ai/rind/pull/74))
- *(sha1)* AVX2 message schedule on x86_64 without SHA-NI ([#64](https://github.com/kixel-ai/rind/pull/64))
- close the verification gaps, fixing two RSA signing bugs they found ([#62](https://github.com/kixel-ai/rind/pull/62))
- *(hkdf)* key the PRK's HMAC once at extract ([#63](https://github.com/kixel-ai/rind/pull/63))
- follow the move to kixel-ai/rind ([#50](https://github.com/kixel-ai/rind/pull/50))
- ctgrind ML-KEM, ECDSA nonces, and AES key setup ([#39](https://github.com/kixel-ai/rind/pull/39))
- one workspace rust-version ([#33](https://github.com/kixel-ai/rind/pull/33))
- ctgrind the adapter crates' secret paths ([#19](https://github.com/kixel-ai/rind/pull/19))
- start rind at 0.1.0 and enable releases ([#2](https://github.com/kixel-ai/rind/pull/2))
- update MLKEM impl strategy
- Add an ML-KEM performance note in README
- Update README to reflect the new aarch64 stitched AES-GCM.
- Update README for ML-KEM and SHA3
- Implement SHA3-256, SHA3-512, SHAKE128 and SHAKE256
- add ed25519
- Small usability improvements for the unit tests:
- 16-wide AVX512 AES-CTR
- Document and check intel adx CPU feature bit requirement
- Add a note about RSA keygen
- Correct misuse of wNAF terminology
- cut 0.2.0
- Improve SHA512 small input performance
- add badges
- update aarch64 gcm details
- Prepare 0.2.0-alpha.0
- Tone-down cautious language
- Remove misunderstanding about what s2n-bignum verifies
- add notes on CPUs
- Allow testing for optional CPU features
- Fix invalid SPDX expression
- Improve crate docs
- more
- updates
- Improve aarch64 ghash performance
- add technical details
- adjustments
- add p384
- update with chacha20
- remove cryptogams usage
- Support RSA-PSS signatures
- randomised deterministic signing
- rev
- Add logo?
- Add license tags to each new file
- aarch64 sha256 using intrinsics
- Provide RSA on aarch64
- Add readme
