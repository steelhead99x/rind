# Upstream report drafts

Drafts only. Nothing here has been posted, and nothing may be posted until the maintainer has said rind is mature enough to report upstream (the Waiting item of [the quest](/quest/m2/upstream-reports.md)) and has approved the text of each draft. Every project below is outside the orgs `AGENTS.md` lists.

Rechecked on 2026-11-19 against each upstream's current release or main, with its tracker searched first, as the quest's Plan asks. A bug is marked "not rerun" where reproducing it needs a board, a cross shell, an emulator, or a long build, so that this file never claims a result nobody saw. "Searched" below means a handful of keyword searches in the upstream's tracker, which is weaker evidence than a clean search; a maintainer reading a draft before posting should repeat them.

Delete this file before the claim lands. It is a working document for the maintainer's review.

## 1. Triage

41 entries listed (the Forks section's one fork, and every workaround entry but 1 held back, not listed): 14 draft ready, 12 not rerun, 9 existing report, 2 not a bug, 2 fixed upstream, 2 no public tracker.

| Entry | Status | Evidence | Tier |
| --- | --- | --- | --- |
| s2n-bignum (fork offer) | draft ready | #415, #420, #450 still open; PSLLDQ and PSRLDQ merged upstream on 2026-11-17 (#439) so they leave the offer; CONTRIBUTING asks for an issue before significant work | 2 |
| rust-lld cannot link ELFv1 | not rerun | needs the powerpc64 shell; Rust is 1.100.0 now, rind pins 1.98.1; master's target spec still sets ElfV1; no existing report found in two searches | 3 |
| lld links BSS-PLT objects into a crashing ppc32 binary | not rerun | needs nixpkgs' ppc32 gcc and qemu-ppc; lld's PPC.cpp at HEAD has Secure PLT code only and no BSS-PLT diagnostic that I could find; no existing report found | 3 |
| Build scripts cannot see ARM's v7 target feature | existing report | intended: `v7` is Unstable(arm_target_feature) on master, tracked by rust-lang/rust#150246 (open) | 3 |
| Rust 1.90's assembler cannot read verified-garbage's .base64 | not a bug | rind's MSRV choice, as the entry says | - |
| No AddressSanitizer for 32-bit ARM Linux | fixed upstream | armv7-unknown-linux-gnueabihf lists SanitizerSet::ADDRESS since e981edde2 (2026-04-21); the file at tag 1.98.1, rind's own pin, has it | removal |
| Valgrind hides ADX from cpuid | existing report | KDE bug 494162 (UNCONFIRMED, last change 2024-10-05); rind's flake has valgrind 3.27.1, 3.28.0 is current | - |
| Valgrind models only MXCSR's rounding mode | draft ready | reproduced with a C program under valgrind 3.27.1 (native 0x1FBF, valgrind 0x1F80); HEAD's amd64g_create_mxcsr returns 0x1F80 | (sseround << 13); no existing report found | 2 |
| Valgrind cannot run x86_64's newest extensions | existing report | KDE 383010 (AVX-512, ASSIGNED, active 2026-10-13) and 398545 (x86 SHA, UNCONFIRMED); nothing found for VAES or VPCLMULQDQ | - |
| Valgrind hides the ARM crypto extension and SHA3 | draft ready | armv7 half verified in HEAD source: AT_HWCAP2 is handled for ppc64 only and `default:` turns it into AT_IGNORE, while the AArch32 guest decodes AESE, SHA1C, SHA256H and VMULL.P64. The aarch64 half is stale: HWCAP_SHA512 is passed through, only SHA3 is missing, and EOR3 is in the unreleased 3.29 line. No existing report found | 1 |
| Valgrind cannot unwind std's frame-pointer entries on armv7 | draft ready | HEAD's gen_CfiExpr_CfiReg_ARM_GPR maps r13, r12, r15, r14 and r7 and returns -1 for anything else, r11 included; not rerun on a board; no existing report found | 2 |
| Memcheck flags OpenSSL's name map on aarch64 | not rerun | needs an aarch64 host with nixpkgs' OpenSSL 3.5.9; rind already suppresses it (kixel-ai/rind#842); the cause may be OpenSSL's or memcheck's, which a reproduction would settle | 3 |
| Valgrind on ARM does not fault guard pages | not rerun | needs an ARM host; one tracker search found nothing | 3 |
| BINSEC cannot decode much of what rind runs | draft ready | BINSEC 0.11.3 (2026-08-26) is the current release; no existing report; one consolidated coverage request covers this entry and the next two; not rerun | 2 |
| BINSEC cannot decode instructions admin/ct-binsec stubs | draft ready | same consolidated issue; not rerun | 2 |
| BINSEC cannot decode glibc's string functions | draft ready | same consolidated issue; not rerun | 2 |
| gdb dumps a guarded thread stack empty | not rerun | needs a kernel and glibc that install guard regions; one tracker search found nothing | 3 |
| BINSEC stalls on some ML-KEM ciphertexts | draft ready | evidence in kixel-ai/rind#841 (3 of 150 and 3 of 240 runs stalled; captured ciphertexts stall 12 of 12 replays, others finish 24 of 24); no existing report; not rerun here (needs about 100 runs) | 1 |
| Aeneas cannot translate several kinds of Rust | existing report | reported per limitation in its own quest, as the entry says | - |
| Aeneas emits a duplicate markerCopyInst field | existing report | AeneasVerif/aeneas#1051 (open since 2026-08-11) is this bug: NonZero, ZeroablePrimitive, two Copy supertraits named markerCopyInst. The entry's 'Reported: no' is stale | link |
| Charon panics on HACL*'s unrolled SHA-2 | draft ready | the quest's draft is sound; Charon HEAD (9b0ee438, 2026-11-18) still has MAX_STACK_DEPTH = 1024 and an ensure_sufficient_stack that panics, beside a try_ensure_sufficient_stack that returns an error; no existing report found; not rerun on HEAD | 1 |
| Lean cannot compile P-384's comb as one literal | not rerun | Lean is 4.36.0 now, rind pins 4.35.0; needs the translation build; no existing report found | 2 |
| dmtcp_command fails a checkpoint that succeeds | not rerun | DMTCP 4.2.0 (2026-06-26) is out and rind uses 4.1.1; I could not locate the command's source at the 4.2.0 tag; needs a recheck on 4.2.0 first | 2 |
| Mathlib's cache unpacks a copy into each checkout | not rerun | no existing report found; a Lake and Mathlib design matter more than a bug | 3 |
| cargo-mutants cannot see into cfg_if! | draft ready | reproduced with cargo-mutants 27.1.0 (the latest release) on a three-file crate; related but different: sourcefrog/cargo-mutants#50 | 1 |
| cargo-mutants misses compound cfg(test)s | draft ready | reproduced on 27.1.0; HEAD's attr_is_cfg_test (6c720ae8, 2026-10-19) does not descend into all(...) | 1 |
| cargo-mutants matches #[path] with .. literally | draft ready | reproduced on 27.1.0: the module is named src/a/../generic/f.rs and --in-diff reports 'No mutants to filter' with exit 0; HEAD's in_diff.rs has no normalization | 1 |
| cross's i686 Android image cannot run its binaries natively | not rerun | cross's last release is v0.2.5 (2023-02-04), so its tracker may not be watched; needs an Android image | 3 |
| Flutter's iOS simulator test run hangs when its log stream attaches late | existing report | flutter/flutter#181771 closed, fixed by #193142 (merged 2026-10-15); in beta 3.51.0-0.1.pre, not in stable 3.50.0 (2026-11-11) | - |
| Flutter's debug JIT crashes under the Android emulator's ARM translation | not rerun | needs an emulator; one tracker search found nothing | 3 |
| LeakSanitizer deadlocks under Intel SDE | no public tracker | Intel SDE has no public tracker, as the entry says | - |
| Intel SDE aborts Go's acvptool | no public tracker | as above | - |
| aws-lc cannot deny 32-bit ARM features at run time | draft ready | aws-lc main's cpu_arm_linux.c reads getauxval and /proc/cpuinfo only; no existing report (the only OPENSSL_armcap hit is unrelated) | 2 |
| aws-lc-sys targets the SDK's iOS version | not rerun | needs an iOS toolchain; could not locate the build script's handling quickly | 3 |
| curve25519-dalek cannot compile without SSE | existing report | dalek-cryptography/curve25519-dalek#601, open since 2023-11-15 with no update since | - |
| blind-rsa-signatures 0.18 does not build on rsa 0.10.0 | fixed upstream | 0.19.0 (2026-11-18) depends on rsa 0.10.0; not yet built against rind's tests | removal |
| nixpkgs' Lean cannot read Mathlib's cache | not rerun | nixpkgs' lean4 4.35.0 now lists leangz (which provides leantar) in nativeBuildInputs; whether the output ships leantar is unverified, because building it was too expensive here | 2 |
| actionlint rejects concurrency.queue | existing report | rhysd/actionlint#657 and fix #654, both open (2026-11-14) | - |
| acvptool sends ML-DSA's externalMu for the external interface | draft ready | verified in aws-lc source at v5.15.0 and main: ml_dsa.go lines 156 and 222 forward boolToBytes(group.ExternalMu) for every group; the module wrapper's own comment says only the internal interface carries the field; no existing report; not rerun end to end | 1 |
| Dependabot's Cargo lockfile updates skip its cooldown | existing report | dependabot/dependabot-core#16428 (open) covers lockfile-only updates; whether it covers the newly needed crates half was not verified | 2 |
| Ubuntu's AppArmor denies Intel SDE's sandbox | not a bug | Ubuntu's intended hardening of unprivileged user namespaces; one search in actions/runner-images found nothing | - |

Tiers: 1 is a first batch with a clean reproduction and a clear upstream-side fix; 2 is worth doing but needs a recheck, a board, or a decision on shape; 3 is a niche tool quirk to skip or batch; "removal" is rind's workaround to delete, not a report; "link" is an entry that only needs its Reported field updated.

## 2. Recommendation by tier

**Tier 1 (7 issues in 5 projects): post after approval.** Each has a reproduction I ran or a source line I read, and no existing report. The strongest reason against each, stated honestly:

| Draft | Strongest reason it might be wrong or unwelcome |
| --- | --- |
| Charon: stack depth panic | The reproduction needs rind's harness and an Aeneas nightly, not a standalone Rust file, so Charon's maintainers may ask for a smaller case; deeply nested macro-unrolled bodies may also be something they would rather handle with an opaque-body option than a limit change. I did not rerun it on Charon's HEAD. |
| Valgrind: AT_HWCAP2 on 32-bit ARM | Valgrind's tracker is slow (the ADX bug 494162 has sat UNCONFIRMED since 2024) and 32-bit ARM on an AArch64 host is a niche setup, so it may be ignored; a maintainer may also want each HWCAP2 bit tested before it is passed, as the arm64 mask is. Not rerun on an ARM host: the claim rests on the source. |
| cargo-mutants: `#[path]` with `..` | The maintainer may call an `--in-diff` miss on a `..` module an unsupported layout, and the exit code 0 may be intended for "nothing to test". The fix (normalize the path) is small and I verified the bug, but I did not write it. |
| cargo-mutants: compound `cfg(test)` | The semantics are subtle (`all(test, x)` is test-only, `any(test, x)` and `not(test)` are not), so the maintainer may want a design rather than a report. Related to the open issue sourcefrog/cargo-mutants#50, which a maintainer may want this folded into. |
| cargo-mutants: `cfg_if!` | Same open issue (#50) is nearby, and cargo-mutants may treat macro-hidden modules as out of scope, since it parses source rather than expanding macros. |
| aws-lc: acvptool `externalMu` | I confirmed the code at v5.15.0 and main, but did not run NIST's file through acvptool end to end here; if aws-lc's own run passes, the difference may be in rind's wrapper, not acvptool. aws-lc may also treat acvptool as internal tooling. |
| BINSEC: stall on some ML-KEM ciphertexts | There is no standalone reproducer in this draft; BINSEC's maintainers will likely want the binary, the core dump, the script and a stalling ciphertext, which exist only on the author's machine and must be attached first. One in a hundred inputs may also be filed as a known performance limit. I did not rerun it. |

**Tier 2 (11 entries): hold for a second batch.** Their drafts are below: Valgrind MXCSR, Valgrind EXIDX r11, one BINSEC decoder-coverage request covering three entries, aws-lc's 32-bit ARM override, and the s2n-bignum offer. The rest need a recheck first: Lean 4.36 for the P-384 comb, DMTCP 4.2.0, whether nixpkgs' `lean4` output ships `leantar`, and the Dependabot half.

**Tier 3 (10 entries): skip, or batch into one issue per upstream later.** They are tool quirks whose reproduction needs hardware, and several are about trackers that look unwatched (cross's last release is from 2023).

**Not reports at all.** Two fixed upstream, so rind's workaround should go; nine already reported, of which two need rind's own `UPSTREAM.md` fixed; two entries that are not bugs.

## 3. Reasons not to post at all

- Volume: about 40 entries, most niche. A flood of low-value issues costs the maintainer review time and rind some goodwill.
- Several entries were stale on recheck (two fixed, one already reported but listed "no", one with text that no longer matches Valgrind's aarch64 behavior). Posting without the recheck would have produced wrong issues.
- Replies land on the maintainer: an agent may not answer outside the orgs `AGENTS.md` lists without approval each time.
- rind 0.4 has not shipped, and issues linking to rind's internals may go stale.

## 4. Drafts

### 4.1 Tier 1

#### Charon

Title: Panic "stack depth limit exceeded" on deeply nested control flow from an unrolled loop

Charon panics translating libcrux-sha2's `sha256_update_nblocks` (and `sha512_update_nblocks`). libcrux-macros' `unroll_for!` unrolls their 64 or 80 rounds into one function body whose blocks nest past the fixed `MAX_STACK_DEPTH` of 1024 in `charon/src/utils.rs`, and the control-flow reconstruction panics:

```
stack depth limit exceeded (transform/control_flow/ullbc_to_llbc.rs)
```

**Version:** Aeneas nightly release `nightly-2026.11.03-ab34bd2`, which ships Charon, with Rust nightly 2026-09-17. On Charon's current `master` (`9b0ee438`, 2026-11-18) the guard is unchanged: `ensure_sufficient_stack` panics once the depth reaches `MAX_STACK_DEPTH`, while `try_ensure_sufficient_stack`, which returns `Err(StackDepthLimitExceeded)`, sits beside it in the same file.

**Reproduce:** in [kixel-ai/rind](https://github.com/kixel-ai/rind), add `--include 'libcrux_sha2::hacl::sha256_update_nblocks' --extract-opaque-bodies` to `admin/prove`'s portable pass and run `nix develop .#prove --command admin/prove lean`. Charon panics translating `sha256_update`.

**Expected:** the function translates, or Charon reports an error for that item and continues, rather than panicking. The body is straight-line code, so its depth comes from nesting, not from recursion. Using the `try_` variant in the control-flow reconstruction and reporting an error for the item, or a limit that scales with the body, would avoid the panic.

We want the translation to prove these functions in Lean with Aeneas instead of assuming HACL*'s F* theorems about them.

(Written by claude-sonnet-5-5)

#### Valgrind

Title: arm: AT_HWCAP2 is not passed to the client, so programs cannot detect the AArch32 crypto extension that the guest can run

On 32-bit ARM, `getauxval(AT_HWCAP2)` is 0 under Valgrind even on a CPU with the ARMv8 crypto extension, so libraries that gate their AES, PMULL, SHA-1 and SHA-256 code on `AT_HWCAP2` take their fallback and the extension code never runs under Memcheck.

The cause, in `coregrind/m_initimg/initimg-linux.c` at the 3.28.0 release and on master: `case AT_HWCAP2:` is compiled only for `VGP_ppc64be_linux` and `VGP_ppc64le_linux`; on every other platform the auxv loop reaches `default:`, which sets the entry to `AT_IGNORE` ("stomp out anything we don't know about"). The AArch32 guest, meanwhile, decodes `AESE`, `AESD`, `AESMC`, `AESIMC`, `SHA1C`, `SHA1P`, `SHA1M`, `SHA1SU0`, `SHA1SU1`, `SHA256H`, `SHA256H2`, `SHA256SU0`, `SHA256SU1` and `VMULL.P64` (`VEX/priv/guest_arm_toIR.c`). The arm64 branch of the same function already shows the intended shape: it passes `AT_HWCAP` masked to `ARM64_SUPPORTED_HWCAP`.

**Reproduce:** an armhf program that prints `getauxval(AT_HWCAP2)`, run natively and then under `valgrind` on an arm64 host with the crypto extension. Native shows `HWCAP2_AES | HWCAP2_PMULL | HWCAP2_SHA1 | HWCAP2_SHA2` set; Valgrind shows 0. (I read the source for this report and did not rerun it on an ARM host.)

**Suggested fix:** on ARM, pass `AT_HWCAP2` masked to the bits the guest implements: AES, PMULL, SHA1, SHA2 (and CRC32 if the guest decodes it).

Our workaround is to compare qemu traces of those code paths instead of running them under Memcheck.

(Written by claude-sonnet-5-5)

#### cargo-mutants: `#[path]` with `..`

Title: `--in-diff` matches nothing for a module included through `#[path = "../x.rs"]`, and exits 0

cargo-mutants 27.1.0 (the latest release; `src/in_diff.rs` on `main`, `6c720ae8`, has no path normalization either) records a module included by `#[path = "../generic/f.rs"]` under the name `src/a/../generic/f.rs`. `--in-diff` compares that string with the path in the diff, which has no `..`, so nothing matches and the run reports `No mutants to filter` and exits 0, as if the change needed no testing.

Reproduce, with this crate (`cfg-if = "1"` as its only dependency):

```
src/lib.rs          mod a;  pub fn real(x: u32) -> u32 { x + 3 }
src/a/mod.rs        #[path = "../generic/f.rs"]
                    mod f;
                    pub fn use_f() -> u32 { f::g(1) }
src/generic/f.rs    pub fn g(x: u32) -> u32 { x + 5 }
```

Commit it, change `x + 5` to `x + 6` in `src/generic/f.rs`, save `git diff` as `change.diff`, then:

```
$ cargo mutants --list
src/a/../generic/f.rs:1:27: replace g -> u32 with 0
...
$ cargo mutants --list --in-diff change.diff
INFO No mutants to filter        # exit status 0
```

Expected: the mutants of `src/generic/f.rs` are selected, because that is the file the diff changes. Normalizing `..` components lexically when the name is recorded, or when `diff_filter` compares, would do it.

We work around it by rewriting each diff section onto the un-normalized names before passing `--in-diff`.

(Written by claude-sonnet-5-5)

#### cargo-mutants: compound `cfg(test)`

Title: Items under `#[cfg(all(test, ...))]` are mutated, though `#[cfg(test)]` items are skipped

cargo-mutants 27.1.0 skips code under a bare `#[cfg(test)]` but mutates test-only helpers under `#[cfg(all(test, target_os = "linux"))]`. The doc comment of `attr_is_cfg_test` in `src/visit.rs` says it matches an attribute that "has `test` anywhere in it", but the `parse_nested_meta` callback only checks the top-level items and never descends into `all(...)`, so it sees `all` and returns false (checked on `main`, `6c720ae8`).

Reproduce:

```rust
#[cfg(test)]
fn plain_test_helper(x: u32) -> u32 { x + 1 }

#[cfg(all(test, target_os = "linux"))]
fn compound_test_helper(x: u32) -> u32 { x + 2 }

pub fn real(x: u32) -> u32 { x + 3 }
```

`cargo mutants --list` lists mutants of `compound_test_helper` and `real`, and none of `plain_test_helper`.

Expected: `compound_test_helper` is skipped too. An `all(...)` that contains `test` is test-only; `any(...)` and `not(...)` are not, so the check needs to descend with that in mind.

We work around it by excluding the affected files and the `tests::` modules in `.cargo/mutants.toml`.

(Written by claude-sonnet-5-5)

#### cargo-mutants: `cfg_if!`

Title: Modules declared inside `cfg_if::cfg_if!` are not found, so none of their code is mutated

cargo-mutants 27.1.0 finds no module declared inside a `cfg_if!` invocation, so it mutates none of that module's code. It looks like a macro-hidden `mod`, which cargo-mutants cannot see because it parses source rather than expanding macros; a note in the docs about it would already help.

Reproduce:

```rust
cfg_if::cfg_if! {
    if #[cfg(all())] {
        mod inside_cfg_if;      // src/inside_cfg_if.rs: pub fn from_cfg_if(x: u32) -> u32 { x + 4 }
    }
}
```

`cargo mutants --list` lists no mutant of `from_cfg_if`. A `#[cfg_attr(..., path = "...")]` on a `mod` is not followed either, which is the other form we hit.

Expected: either the module is found, or the limitation is documented. This is near the open sourcefrog/cargo-mutants#50 (cfg handling), which may be the right place instead of a new issue.

We work around it by declaring our backend modules outside `cfg_if!` and swapping portable modules with a `#[cfg]` pair and a plain `#[path]`.

(Written by claude-sonnet-5-5)

#### aws-lc: acvptool

Title: acvptool forwards ML-DSA's `externalMu` for the external interface, which the module wrapper reads as the internal interface

In `util/fipstools/acvp/acvptool/subprocess/ml_dsa.go` at v5.15.0 and on `main`, the sigGen and sigVer handlers pass `boolToBytes(group.ExternalMu)` to the wrapper for every group (lines 156 and 222), whatever the group's `signatureInterface`. NIST's ML-DSA sigGen and sigVer sets give the external-interface groups `externalMu: false`. The module wrapper's own comment in `modulewrapper.cc` says only `signatureInterface: internal` carries the `externalMu` field, so a wrapper that reads a present flag as the internal interface signs and verifies the external interface's tests without their context and domain separation, and answers them wrongly.

**Reproduce:** run an unpatched `acvptool` over NIST's `ML-DSA-sigGen-FIPS204` file against a wrapper that follows that convention: the external groups' signatures differ from the expected ones. (I confirmed the code at both revisions; I did not run NIST's file end to end for this report.)

**Suggested fix (small):** forward `externalMu` only when `group.SignatureInterface == "internal"`, in both handlers. We carry exactly that as a patch in our Nix packaging of `acvptool`.

(Written by claude-sonnet-5-5)

#### BINSEC

Title: Execution stalls inside `Term.sizeof` for some inputs, with no solver query

BINSEC 0.11.3. We check the constant time of an ML-KEM decapsulation in a Rust test binary (a core dump and a script). For about one random ciphertext in a hundred, exploration makes no further progress and sends the solver no query, until the timeout: the log shows `0 visited path covering 21223/21243 instructions`, where the other inputs finish in under ten seconds.

The input alone decides it: three captured stalling ciphertexts stalled on 12 of 12 replays, and six other ciphertexts finished on 24 of 24, so it is not the machine, the core dump, glibc's choices or load. Swapping either half of a stalling ciphertext for a finishing one's (four mixes) always finished, so it is the pair, not one coefficient. A debugger on the stalled process (OCaml frames) shows `Term.sizeof`, called from `Term.mk_binary`, `Term.binary` and `Exec.assign`, at about step 366k, inside the re-encryption.

**Expected:** the exploration finishes as it does for the other inputs. **Attached (to add before posting):** the binary, the core dump, the script, and a stalling ciphertext; the harness is `admin/ct-binsec` in [kixel-ai/rind](https://github.com/kixel-ai/rind), and the evidence is in [kixel-ai/rind#841](https://github.com/kixel-ai/rind/pull/841).

Our workaround is to decapsulate a fixed ciphertext that finishes.

(Written by claude-sonnet-5-5)

### 4.2 Tier 2

#### Valgrind: MXCSR

Title: amd64: only MXCSR's rounding mode is kept, so `stmxcsr` after `ldmxcsr` reads back `0x1F80`

On Valgrind 3.27.1, a program that runs `ldmxcsr` with `0x1FBF` and then `stmxcsr` reads back `0x1F80` under Valgrind and `0x1FBF` natively:

```c
#include <stdio.h>
#include <xmmintrin.h>
int main(void) {
    _mm_setcsr(0x1FBF);
    printf("0x%X\n", _mm_getcsr());
    return 0;
}
```

On `master`, `amd64g_create_mxcsr` returns `0x1F80 | (sseround << 13)`, so only the rounding mode survives. Tests that read back Intel's MXCSR mitigation state fail under Valgrind for that reason. This is probably a documented limitation of the guest state; if so, a line in the manual is all that is needed. I did not find an existing report.

(Written by claude-sonnet-5-5)

#### Valgrind: EXIDX and r11

Title: arm: the EXIDX reader cannot rebuild the stack pointer from r11, so frames of std built with frame pointers do not unwind

`ML_(read_exidx)` unwinds through `.ARM.exidx` entries and can express a frame-pointer-based `vsp` for `r7` (Thumb's frame pointer), but `gen_CfiExpr_CfiReg_ARM_GPR` in `coregrind/m_debuginfo/readexidx.c` maps only r13, r12, r15, r14 and r7 and returns -1 for every other register, `r11` included. Rust's prebuilt std keeps frame pointers, so its entries begin `vsp = r11`, and an unwind through them stops there. A stack that ends in `<[u8]>::starts_with` can then never match a suppression that names its caller.

I read this from the source at `master`; I have not rerun it on a board. Suggested fix: add `Creg_ARM_R11` and map it in that function.

(Written by claude-sonnet-5-5)

#### BINSEC: instruction coverage

Title: Decoder coverage for instructions that crypto code runs (AES-NI, VAES, EVEX, the Arm crypto extension, SVE, a few others)

BINSEC 0.11.3 stops with an undecodable or `uninterpreted` result at the instructions below, which constant-time checks of crypto code reach. We stub the cheap ones and deny the rest, so a decoder for any of them would remove a workaround. Which are in scope, and in what order, is your call; we can test a build against our harnesses.

| Architecture | Instructions |
| --- | --- |
| x86_64 | AES-NI, VAES, the SHA512 instructions, every EVEX encoding; `stc`, `clc`, `movmskps` and VEX `vmovmskps`, `vinsertf128` (VEX.256 0F3A 18), `vpermpd` (VEX.256.W1 0F3A 01), `vmovshdup` (VEX F3 0F 16), `stmxcsr` and `ldmxcsr`, the `syscall` in glibc's `mprotect`, and `xtest` in glibc's TSX `memcpy` variants |
| aarch64 | the crypto extension's AES, PMULL and SHA instructions, SHA3's, every SVE encoding (for example SVE2's `xar`), the `msr` that sets DIT, `mrs xN, tpidr_el0`, `tbl` with one to four table registers (8B and 16B), `cnt` (8B and 16B) |
| armv7 | NEON table lookups and the crypto extension |

We stub `stc`, `clc` and the others through `replace opcode`, which matches exact bytes; a mask form of `replace opcode` would let one stub cover every encoding of an instruction.

(Written by claude-sonnet-5-5)

#### aws-lc: 32-bit ARM feature override

Title: Allow denying CPU features at run time on 32-bit ARM, as `OPENSSL_armcap` does on aarch64

aws-lc reads `OPENSSL_armcap` to deny CPU features on aarch64 (`cpu_aarch64_*.c`), but the 32-bit ARM detection in `crypto/fipsmodule/cpucap/cpu_arm_linux.c` (on `main`) reads only `getauxval` and `/proc/cpuinfo`. To benchmark or test the NEON-only path on a CPU that has the ARMv8 crypto extension we have to rebuild aws-lc with `-DOPENSSL_STATIC_ARMCAP -DOPENSSL_STATIC_ARMCAP_NEON`. Reading the same variable on 32-bit ARM would let one build run both paths. I did not find an existing report.

(Written by claude-sonnet-5-5)

### 4.3 The fork offer

#### awslabs/s2n-bignum

s2n-bignum's CONTRIBUTING asks for an issue before significant work, so this is an offer, not a pull request. It was checked against `main` at `e95b39a1` (2026-11-17). Its three open pull requests, #415, #420 and #450, are upstream's own and stay out of the offer.

Title: Offer: x86_64 instruction models for what aws-lc and OpenSSL's crypto routines run, a ChaCha20-Poly1305 spec, and an AArch32 model

We use s2n-bignum's HOL Light models to prove assembly we ship, and we carry changes to it that we would be glad to offer, grouped the way we think you would review them. We would send each group as its own pull request if you want it, and drop any you do not.

1. **x86_64 instruction models.** What aws-lc's ChaCha20-Poly1305, AES-CTR, AES-CBC and P-256 mixed-addition routines and OpenSSL's AVX2 SHA-512 need, each with its decoder and semantics, and each cosimulated against the CPU: `VPALIGNR`, `PSLLD`, `PSRLD`, `PINSRB`, `PEXTRB`, `PEXTRQ`, `POR`, `PANDN`, `PCMPEQD`, `PUNPCKLDQ`, `PUNPCKHDQ`, `SHLX`, `SHRX`, `RORX`, `ANDN`, `VBROADCASTI128`, `PUSH r/m64` (memory form), `F3 C3` (`rep ret`), `XORPS`, `PREFETCHT0`, and `STOSB` / `REP STOSB` as a sound over-approximation (it decodes so that later code can be stepped; a proof that reaches it proves nothing). `PSLLDQ` and `PSRLDQ` are already yours (#439) and are not part of the offer.
2. **A cosimulation of those models** (`x86/proofs/rind_cosim.ml`), whose encodings would join `x86/proofs/simulator.ml`'s, as your own additions do, and the CPU features `ANDN`, `RORX`, `SHLX` and `SHRX` need in the simulator so it skips them on CPUs without BMI1 and BMI2.
3. **A ChaCha20-Poly1305 specification** (`common/chacha20poly1305.ml`): RFC 8439's ChaCha20, Poly1305 and AEAD on byte lists, with a conversion that evaluates them on literals and known-answer tests from the RFC's sections 2.4.2, 2.5.2 and 2.8.2 that run as it loads.
4. **An AArch32 model** (`aarch32/proofs/`, new): the A32 state and the semantics of the instructions armv7's proofs need, from the Arm Architecture Reference Manual's AArch32 pseudocode, with decoders for their encodings, a step relation and symbolic-execution tactics, the safety tactics specialised to the model, and a cosimulation against `qemu-arm`.

Which of these, if any, would you like, and would you prefer them in this order?

(Written by claude-sonnet-5-5)

## 5. Follow-ups for rind (not done here)

- **Remove a workaround that upstream fixed.** `fuzz.yml`'s armv7 replay row runs with `sanitizer: none`; `armv7-unknown-linux-gnueabihf` has had AddressSanitizer since Rust 1.98 (e981edde2). Try the sanitizer on that row and delete the entry.
- **Remove the blind-rsa-signatures fork.** 0.19.0 (2026-11-18) depends on `rsa` 0.10.0. Build rind's tests against it, then drop `thirdparty/blind-rsa-signatures` and its `[patch.crates-io]` entry.
- **Fix `UPSTREAM.md` where it is stale:** link AeneasVerif/aeneas#1051 on the `markerCopyInst` entry; reword the aarch64 half of "Valgrind hides the ARM crypto extension and SHA3" (HWCAP_SHA512 is passed through, SHA3 is the gap, and EOR3 is in the unreleased 3.29 line); note that Flutter's fix is in beta 3.51.0-0.1.pre and not yet in stable.
- **Recheck pins:** Rust 1.100.0, Lean 4.36.0, DMTCP 4.2.0 and Valgrind 3.28.0 are newer than what the entries and the flake record.
- **Check whether `leantar` ships in nixpkgs' `lean4` output**, since its package now lists `leangz` (which provides it) as a build input.

## 6. Method and limits

- Read: `UPSTREAM.md` from upstream `main` `96404e2f`; current releases through each project's releases API, crates.io and the Flutter release index; Valgrind's `NEWS`, `initimg-linux.c`, `readexidx.c`, `m_machine.c`, `guest_arm_toIR.c`, `guest_arm64_toIR.c`, `guest_amd64_helpers.c` at `master` (the 3.29 development line, after 3.28.0 of 2026-10-23); Charon's `utils.rs` and `ullbc_to_llbc.rs`; cargo-mutants' `visit.rs` and `in_diff.rs` at `6c720ae8`; aws-lc's `ml_dsa.go` at v5.15.0 and `main`; rust-lang/rust's target specs.
- Ran: the MXCSR program (native and under valgrind 3.27.1) and a three-file crate for the three cargo-mutants entries (27.1.0, from rind's Nix shell).
- Searched: GitHub's issue search per entry (rate-limited, so some searches were keyword-light), KDE's Bugzilla for Valgrind, and sourceware's for gdb. A zero result there is weak evidence.
- Not run: anything needing a board, qemu, an Android or iOS toolchain, Intel SDE, a long build, or a Lean build. Those rows say "not rerun".
