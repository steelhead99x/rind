# Proofs of rind's Rust

Lean proofs that rind's own Rust computes its specified result, composed with
the published proofs of the routines it imports, so that an operation's whole
computation is proven. [Charon](https://github.com/AeneasVerif/charon) and
[Aeneas](https://github.com/AeneasVerif/aeneas) translate the Rust to Lean, and
the theorems are about that translation.

`nix develop .#prove --command admin/prove` translates the Rust and checks
every proof against the translation, after the HOL Light proofs below and
`admin/prove bytes`, which checks that each imported routine those proofs
build on, from s2n-bignum, Vale, and aws-lc, is in rind's build the object
code its own proof is about. The `prove` workflow runs it nightly and on each
push to main that changes rind's source or these files. A failure gates no
merge; it alerts, and a release publishes only once these proofs passed on
the code it releases.

`lakefile.toml` turns on Lake's artifact cache, which lives in the Lean
toolchain's directory under `~/.elan` and every checkout of a user shares, so
a new worktree hard-links, or across filesystems copies, the Mathlib and
Aeneas builds and the unchanged modules another checkout already fetched or
built rather than unpacking or building its own. The cache outlives the
worktrees: uninstalling the old toolchain after a bump with `elan toolchain
uninstall` drops it, and `lake cache clean` in `proofs/` empties it at any
time, since each checkout keeps its own links and its next build puts them
back.

## TCB & Axiom Ledger

A Lean theorem here is as good as everything it trusts. Beyond Lean's kernel
and the lemmas Mathlib and Aeneas prove:

| Trusted | For | What checks it |
|---|---|---|
| Charon and Aeneas, with Aeneas's models of `core` and `Rind/Core.lean`'s | the Lean translation computes what the Rust does; drops are ignored | upstream's tests only |
| Hand models of Rust Aeneas cannot translate, below | each computes what the Rust it quotes does | `admin/prove` fails when a quote no longer matches the source; [the hand-model quest](/quest/m4/verified/aeneas-fn-pointers.md) retires them |
| Transliterated specs: FIPS 180-4, RFCs, s2n-bignum's, Vale's, and SymCrypt's | each is the standard it names | [`admin/spec-tests`](#the-spec-tests) runs each on published vectors and random inputs |
| Intrinsic models, `Rind/X86_64/Simd.lean` and `Rind/Aarch64/Neon.lean` | each computes what its instruction does | `admin/simd-vectors.rs`, `admin/neon-vectors.rs`, and `admin/avx512-vectors.rs` run it on hardware |
| Imported theorems restated as axioms, below | an upstream proof is about the Rust wrapper's arguments and result | each docstring cites the theorem at the pinned revision, [the composition rule](/quest/m4/verified/README.md#composition-rule) bounds what it says, and for VG's, `admin/vg-binding` |
| Assembly's object code | rind's build emits the instructions a proof is about, assembler and linker included | `admin/prove bytes`, `admin/prove lean`, and `admin/vg-bytes` compare the bytes |
| Instruction models: HOL Light's kernel, s2n-bignum's x86 and Arm models, VG's Lean models, rind's extensions | each instruction does what the CPU does | `admin/prove cosim` and `admin/prove vg` run each on the CPU, under Intel SDE, or under qemu |
| Lean's compiler, where the constructs below appear | compiled code agrees with the kernel's | none |
| The CPU | it implements its architecture manual | none |

Lean's compiler, trusted beyond the kernel wherever one of these appears:

| Construct | Trusts |
|---|---|
| `bv_decide`, `bv_check` | each call adds an axiom that Lean's compiled LRAT checker accepted a SAT solver's certificate |
| `native_decide`, `decide +native` | each would add an axiom that Lean's compiled code evaluated a proposition as the kernel would; `admin/ledger` fails on any |
| `@[implemented_by]`, `@[extern]` | the compiler runs another definition than the one proofs use, as for the AES S-boxes' tables, which `sboxFast_eq` and `invSboxFast_eq` prove equal |

Which axioms each top-level theorem rests on, through every definition it
uses, `Rind/<Arch>/Axioms.lean` pins, so growing it fails the build. `admin/ledger`
lists every file that declares one, and fails CI on a `sorry`, a `native_decide`,
or an axiom in a file its groups do not name. It holds no counts, which would
go stale whenever another pull request lands first. [The trust base](#trust-base)
says what each trusted item is.

<!-- admin/ledger: begin -->
Every Lean file that declares an `axiom`, by the source it restates; no file holds a `sorry`:

| Restates | Files under `proofs/Rind/` | Checked |
|---|---|---|
| s2n-bignum's HOL Light theorems of its assembly | `Aarch64/S2nBignum`, `X86_64/S2nBignum` | published proofs; `admin/prove bytes` checks rind's build emits the code they are about |
| s2n-bignum's HOL Light theorems of its ML-KEM routines, and mlkem-native's of its compression routines | `Aarch64/MlKemRoutines` | published proofs; `admin/prove bytes` checks rind's build emits the code they are about, and `admin/prove` that the tables rind passes are s2n-bignum's |
| pyca/verified-garbage's Lean theorems of its assembly | `Aarch64/VgChaCha20`, `Aarch64/VgChaCha20Poly1305`, `Aarch64/VgMlKem`, `Aarch64/VgP256`, `Aarch64/VgP384`, `Aarch64/VgPbkdf2`, `Aarch64/VgSha512`, `X86_64/VgChaCha20`, `X86_64/VgChaCha20Poly1305`, `X86_64/VgCurve25519`, `X86_64/VgMlKem`, `X86_64/VgP256`, `X86_64/VgP384`, `X86_64/VgRsa` | published proofs; `admin/vg-binding` checks each axiom cites the theorem of its routine, and `admin/vg-bytes` that rind runs that routine's bytes |
| Beneficial AI Foundation's Lean theorems of curve25519-dalek, in its X25519 spec that `admin/import-dalek` vendors | `Armv7/Dalek` | published proofs; `admin/prove dalek` checks that every definition `mul_clamped` and `mul_base_clamped` reach in armv7's configuration is the text BAIF's proofs are about |
| Vale's procedures for HACL\*'s AES-GCM | `X86_64/ValeAesGcm` | published proofs; `admin/prove bytes` checks the object code |
| aws-lc-verification's NSym proof of SHA-384/512 (aarch64) and rind's HOL Light proof of the AVX2 routine (x86_64) | `Aarch64/AwsLc`, `X86_64/AwsLc` | a published proof and rind's own; `admin/prove bytes` and `admin/prove hol-light` check the object code |
| rind's own HOL Light proofs of its assembly, and rind's Lean proofs of the SHA-256 crypto-extension routine (aarch64) and `bn_mul4x_mont` (x86_64) | `Aarch64/Sha256Hw`, `X86_64/ChaCha20Cipher`, `X86_64/CtEqual`, `X86_64/RsaMont`, `X86_64/Sha256Shaext`, `X86_64/ShaBlocks` | rind's proofs, in `proofs/hol-light/`, `Rind/Aarch64/Sha256HwAsm.lean`, and `Rind/X86_64/Mul4xProof.lean`, checked against the bytes rind's build emits |
| HOL Light theorems of AES-CTR and AES-CBC that no proof states yet | `X86_64/AesModesLow` | **assumed, not proven**: [the AES modes quest](/quest/m4/verified/aes-modes.md) owns them |

Hand models of Rust Aeneas cannot translate, each quoting the Rust it models:

- `Aarch64`: `AesGcmModel`, `FunsExternal`, `PointSelectModel`, `TypesExternal`
- `Portable`: `Compare`
- `X86_64`: `AeadDispatch`, `AesGcmModel`, `DigestAlgorithm`, `DigestDispatch`, `Dispatch`, `EcdsaDispatch`, `FunsExternal`, `GatherModel`, `GcmKey`, `HkdfExpand`, `HmacDispatch`, `P256Dispatch`, `P384Dispatch`, `PointSelectModel`, `QuicDispatch`, `RsaDispatch`, `SignatureBuffer`, `TypesExternal`
<!-- admin/ledger: end -->

## HOL Light proofs

`hol-light/<arch>/` holds rind's own [HOL Light](https://hol-light.github.io/)
proofs of the `asm!` blocks it runs, for routines whose published proofs do
not cover them, on [s2n-bignum](https://github.com/awslabs/s2n-bignum)'s
instruction models, tactics, and specs in rind's fork of it,
`thirdparty/s2n-bignum`, the revision rind's transliteration pins with rind's
changes, which [its `RIND.md`](/thirdparty/s2n-bignum/RIND.md) lists.
Each proof's object code is the block's bytes as rind's release build emits
them, which `admin/prove` extracts, so no transliteration is trusted: the
proof lists the bytes and fails unless the build's are the same. An axiom in
`Rind/<Arch>/` that restates one of these theorems names the file, whose
revision is rind's commit. `nix develop .#hol-light --command admin/prove
hol-light` checks them alone, in nixpkgs' HOL Light.

To develop one, `nix develop .#hol-light --command admin/prove session
<arch> [<file>]` starts a HOL Light session, on Linux, in which a proof
loads as `admin/prove hol-light` compiles it: s2n-bignum's `base.ml` for
`x86_64` or `aarch64` loaded, on the same load path, in the directory
holding the object code the proofs read. Given a file, such as
`proofs/hol-light/x86_64/ct_compare_16.ml`, it loads it and exits, failing if
any of it fails; otherwise it reads OCaml from stdin. Loading `base.ml`
takes minutes, so the first session on a set of inputs (HOL Light, DMTCP,
the kernel, and the fork's files) checkpoints it with DMTCP into an image of
about 400 MB in `~/.cache/rind/hol-light/`, which every later session on
those inputs, in any worktree, restores in under a second.

- `aarch64/bignum_eq.ml`: `BIGNUM_EQ_CORRECT`, s2n-bignum's proof of
  `bignum_eq` on the block in `low::aarch64::bignum_eq::bignum_eq`, which is
  s2n-bignum's routine without its `ret`.
- `x86_64/sha512_block_data_order_avx2.ml`:
  `SHA512_AVX2_SUBROUTINE_CORRECT`, rind's proof that the naked function
  `low::x86_64::sha512::sha512_block_data_order_avx2`, OpenSSL's routine for
  AVX2, computes s2n-bignum's FIPS 180-4 spec, `sha512_hash_blocks`, and
  stores it to the state, on s2n-bignum's x86 model with
  the instructions rind's fork adds (`thirdparty/s2n-bignum/RIND.md`). A
  naked function's object code is its whole section with its relocations and
  the read-only data they reach, here the round constants, which
  `admin/prove` extracts as an object file; the proof checks the constants
  against FIPS 180-4's. Its stack frame, which the routine aligns
  down to 2048 bytes, lies in the 3440 bytes below the stack pointer.
- `x86_64/sha256_block_data_order_avx2.ml`:
  `SHA256_AVX2_SUBROUTINE_CORRECT`, rind's proof that the naked function
  `low::x86_64::sha256::sha256_block_data_order_avx2`, OpenSSL's routine for
  AVX2, computes s2n-bignum's FIPS 180-4 spec, `sha256_hash_blocks`, and
  stores it to the state, as `sha512`'s above, on the same model; the proof
  checks its round constants against FIPS 180-4's. Its stack frame, which the routine aligns down to 1024
  bytes, lies in the 1648 bytes below the stack pointer.
- `x86_64/chacha20_ctr32_ssse3_4x.ml`:
  `CHACHA20_CTR32_SSSE3_4X_SUBROUTINE_CORRECT`, rind's proof that the naked
  function `low::x86_64::chacha20::chacha20_ctr32_ssse3_4x`, aws-lc's SSSE3
  ChaCha20, called in place on a nonempty buffer, as `cipher_ssse3_4x`
  calls it, leaves the buffer s2n-bignum's RFC 8439 spec,
  `chacha20_encrypt`, under the key, the 32-bit block counter, which wraps,
  and the nonce, on the same model. Its stack frame lies in the 320 bytes
  from 328 below the stack pointer, which needs the stack pointer plus 8 to be
  16-byte aligned at entry, as the ABI leaves it; its table, which `admin/prove` extracts
  with the code since the build places it in the function's own read-only
  section on Linux, must be 16-byte aligned. Its other premises, the buffer's
  disjointness from the code, table, and frame and its end at or below 2^64,
  are listed in `Rind/X86_64/ChaCha20Cipher.lean`'s module doc. It is of the
  `x86_64-unknown-linux-gnu` build's object, not musl's or Apple's:
  Apple's `aws_lc/ChaCha20_ctr32_ssse3_4x.apple.s` lacks the entry's
  `.align 32`, so its branches can land at other offsets, and its two tables
  are separate statics, not one section, so no proof covers it.
- `aarch64/bn_mul_mont.ml`: `BN_MUL_MONT_SUBROUTINE_CORRECT`, rind's
  proof that the naked function `low::aarch64::mont::bn_mul_mont`, aws-lc's
  Montgomery multiplication, writes the Montgomery product
  `x * y / 2^(64k) mod m` of its `k`-word operands, as s2n-bignum's
  `bignum_montmul` states it, given `-m^-1 mod 2^64` and
  `x * y <= 2^(64k) * m`, for every width from two words up: for `k < 2^58`,
  a 16-aligned stack pointer, and `z` and the `16k + 128` bytes below the
  stack pointer disjoint from the code, the inputs, and each other, so `z`
  may not alias `x`. It is of the Linux build's object: Apple's
  `aws_lc/bn_mul_mont.apple.s` lacks the entry's `.align 5`, so its branches
  can land at other offsets, and no proof covers it. At a multiple of four it also needs `x + 32` and `m + 32` not to wrap
  past `2^64`, since the 4x path reads the carry of adding 32 to those
  pointers. The theorem covers the dispatch, the stack frame, and the
  callee-saved registers the function restores. It joins one theorem for
  each routine the dispatch reaches, each with that routine's own frame:
  `BN_MUL_MONT_GENERIC_SUBROUTINE_CORRECT` for a width that is not a multiple
  of four, which the width-generic path runs in up to `8k + 72` bytes;
  `BN_MUL_MONT_MUL4X_SUBROUTINE_CORRECT` for a multiple of four, through
  `__bn_mul4x_mont` in `8k + 160` bytes, except a multiple of eight with
  `x = y`; and `BN_MUL_MONT_SQR8X_SUBROUTINE_CORRECT` for that case, the
  squarings `__bn_sqr8x_mont` runs in `16k + 128` bytes. No axiom in `Rind/`
  restates any of them yet. The function has no relocations.
- `x86_64/bn_mul_mont_nohw.ml`: `BN_MUL_MONT_NOHW_SUBROUTINE_CORRECT`, rind's
  proof that the naked function `low::x86_64::mont::bn_mul_mont_nohw`,
  aws-lc's word-serial Montgomery multiplication, writes the Montgomery
  product `x * y / 2^(64k) mod m` of its `k`-word operands, from two words up,
  as s2n-bignum's `bignum_montmul` states it, given `-m^-1 mod 2^64` and
  `x * y <= 2^(64k) * m`. The theorem covers the whole function: its stack
  frame of up to `8k + 1088` bytes below the stack pointer, aligned and probed
  a page at a time, and the callee-saved registers it restores. The function
  has no relocations, so its object is its section alone.
  `Rind/X86_64/RsaMont.lean` restates it as the axiom `nohw_spec`, about the
  Rust wrapper `low::x86_64::mont::nohw`, for widths below `2^32`, which the
  routine's `mov r9d, r9d` needs.
- `x86_64/sha256_compress_blocks_shaext.ml` and
  `x86_64/sha256_finish_shaext.ml`: `SHA256_COMPRESS_BLOCKS_SHAEXT_CORRECT`
  and `SHA256_FINISH_SHAEXT_CORRECT`, rind's proofs that the blocks in
  `low::x86_64::sha256::sha256_compress_blocks_shaext` and
  `sha256_finish_shaext`, its routines for the SHA extensions, compute
  s2n-bignum's FIPS 180-4 spec, `sha256_hash_blocks`. The first stores it to
  the state over its blocks, any number of them. The second leaves the
  digest's bytes in xmm2 and xmm1, over its blocks and then the padded block,
  or two, that it builds from the tail's whole 16-byte lanes in memory, the
  lane where the message ends as r10 and r11, and the length's word in r8.
  Both run one round body, which `x86_64/sha256_shaext_rounds.ml` proves
  once, `SHA256_SHAEXT_ROUNDS_CORRECT`. They read the round constants and
  the byte-swap mask through rcx from the static `low::x86_64::sha256::K`,
  whose bytes `admin/prove` extracts and the proof checks against FIPS
  180-4's. `Rind/X86_64/Sha256Shaext.lean` restates the two as axioms and
  proves that the finish's padding, plain Rust above its block, builds the
  block, or two, that FIPS 180-4 pads.
- `<arch>/ct_compare_16.ml` and `<arch>/ct_compare_bytes.ml`, on x86_64,
  aarch64, and armv7: `CT_COMPARE_16_CORRECT` and `CT_COMPARE_BYTES_CORRECT`,
  that the blocks in `low::<arch>::cpu::ct_compare_16` and `ct_compare_bytes`,
  `low::arm::cpu` on armv7, return zero exactly when their inputs are equal,
  and `CT_COMPARE_16_SAFE` and `CT_COMPARE_BYTES_SAFE`, in s2n-bignum's style,
  that their trace of loads and branches is a function of the addresses and
  length alone, each load in bounds. On x86_64 and aarch64 both functions
  are `#[inline(never)]` with fixed registers, so the proof covers their
  one copy. On armv7 they are A32 routines in a `global_asm!`, which
  `admin/prove` finds by their symbols without rind's version, and the
  theorems, on the fork's AArch32 model below, cover each from entry to
  return for a caller in A32 or T32, so every armv7 target, the Thumb-2
  Rust of `armv7-linux-androideabi` and the `thumbv7` targets included,
  runs the code they are about. `ct_compare_bytes` saves R4 and LR in the
  8 bytes below SP, which its theorems assume aligned, below 2^32, and
  apart from the code and, for `CT_COMPARE_BYTES_CORRECT`, the strings.
- `x86_64/ecp_nistz256_point_add_affine.ml` and
  `x86_64/ecp_nistz256_point_add_affinex.ml`:
  `ECP_NISTZ256_POINT_ADD_AFFINE_SUBROUTINE_CORRECT` and
  `ECP_NISTZ256_POINT_ADD_AFFINEX_SUBROUTINE_CORRECT`, rind's proofs that
  aws-lc's mixed additions in `low::x86_64::ecp_nistz256`, its mulq routine
  and its BMI2 and ADX one, called in place, add an affine point to a
  Jacobian one in Montgomery form, as s2n-bignum's `p256_montjmixadd`
  states it, and return either input for the other's infinity. Each proves
  its four field helpers from entry to return, then the body over 17 calls
  to them, with s2n-bignum's field algebra. They assume a 16-byte aligned
  stack at the call, as the System V ABI gives, since the body's MOVDQA
  stores require it, and read the field constants from the static
  `POLY`, whose `align(16)` the body's two PANDs from it require. They
  are of the Linux build's object: Apple's text aligns the helpers to 32
  bytes but not the entry, so its calls can reach them at other offsets,
  and no proof covers it.

The fork adds what these proofs need to s2n-bignum: specs from s2n-bignum
pull requests not yet merged, rind's own RFC 8439 spec of ChaCha20,
Poly1305, and ChaCha20-Poly1305, `common/chacha20poly1305.ml`, whose
known-answer tests `admin/prove hol-light` runs, the SHA extensions and
other instructions an s2n-bignum pull request adds to the x86 model, rind's
own additions to it, which `x86/proofs/rind_cosim.ml` checks against the CPU
with the pull request's, and `aarch32/`, an AArch32 model of the A32
instructions armv7's assembly runs, which `aarch32/proofs/simulator.ml`
checks against qemu-arm.
`nix develop .#hol-light --command admin/prove cosim` runs both
cosimulations, on an x86_64 CPU with AVX2.

## verified-garbage's models

[pyca/verified-garbage](https://github.com/pyca/verified-garbage) (VG)
proves its routines in Lean against its own models of x86_64 and aarch64,
and prints each routine from the same Lean code twice: as assembly text, and
as a Rust naked function of machine code from its own encoder. Those models
are VG's trusted base, and VG's CI checks its encoder only against golden
tests, so before a routine rind takes from VG counts as proven, rind checks
both against hardware. `verified-garbage/` holds the models, which
`admin/import-vg-models` copies byte for byte from VG at the commit
`admin/import-vg` pins for VG's code,
and the cosimulation over them, a Lake package of its own, since the models
import only Lean core. `nix develop .#vg --command admin/prove vg` checks,
for this CPU's target:

- that every instruction of VG's compiled naked functions, and of each `vg_*`
  routine rind vendors, is the instruction its assembly text gives, which
  `admin/vg-bytes` assembles with nixpkgs' LLVM; a branch or call need only
  reach the same instruction or function, since the assembler lays those
  out, and an encoding that differs but disassembles the same is reported;
- that each distinct instruction of VG's code ends, from random states, in
  the state VG's model gives. `Cosim/` parses each instruction's text back to
  every instruction of the model that prints as exactly that text, runs the
  model on random states, weighted toward edge values, with each memory
  operand in a window of the runner's data, and `admin/vg-cosim-runner.rs`
  runs VG's machine code for it on the CPU, or under Intel SDE or
  qemu-aarch64 for an instruction that needs a feature the CPU lacks, and
  compares every register, flag the model defines, and byte of the data.
  A conditional branch is checked for whether it is taken, and a call or
  indirect call with the `ret` that returns from it. A table load is checked
  with random table words at the address it reads.

Not cosimulated: the `jmp`/`b` and the address of a static (`lea`, or
`adrp` and `add`), which the assembler and linker resolve and the bytes
check covers, and `ret` alone, which each call's case runs. The `prove`
workflow runs it on x86_64 and aarch64, nightly with a new seed.

A gap in what the models allow across instructions is beyond what
cosimulating one instruction at a time can catch. Reviewers found one: a
freed frame's bytes kept their values in the models, so a proof could read
back a value a signal handler may have overwritten on hardware
([pyca/verified-garbage#5321](https://github.com/pyca/verified-garbage/issues/5321)).
VG fixed it in both models before the commit `admin/import-vg` pins.

`Rind/VgChaCha20.lean` proves the keystream of VG's RFC 8439 spec,
`VerifiedGarbage.Spec.ChaCha20`, is `Rind/Spec.lean`'s, and that the spec's
view of the streaming state reads only its 768 bytes.
`Rind/X86_64/VgChaCha20.lean` restates VG's theorems
about the x86_64 ChaCha20 routines rind runs, `Stream.init_verified` and
`Stream.apply_verified` for AVX2 and AVX-512 VL, as one axiom per wrapper in
`low::x86_64::chacha20`, and proves `cipher::ChaCha20` from them, with rind's
own proofs of the two-block kernel and HACL*'s loop, as "What is proven"
lists.
`Rind/Aarch64/VgChaCha20.lean` does the same for aarch64's,
`Stream.initCleared_verified` and `Stream.apply_verified` at its NEON and
SVE2 variants, about the wrappers in `low::aarch64::chacha20`. Both take what
they share about the key's and counter and nonce's words from
`Rind/VgChaCha20Glue.lean`.

`Rind/X86_64/VgCurve25519.lean` restates VG's theorems about its x86_64
AVX-512 IFMA X25519 and Ed25519 routines, one axiom per wrapper in
`low::x86_64::curve25519_ifma`, over its specs as `Rind/VgCurve25519.lean`
reads them. `Rind/X86_64/X25519.lean` and `Rind/X86_64/Ed25519Ifma.lean`
prove rind's X25519 and Ed25519 from them, as "What is proven" lists.

`verified-garbage/` also holds the `Spec` modules whose definitions the
axioms restating VG's theorems state, such as
`VerifiedGarbage.Spec.Rsa.PrivatePrecompute`, which `Rind/X86_64/VgRsa.lean`
imports, with `VerifiedGarbage.Spec.Rsa` through it, VG's FIPS 203 spec,
`VerifiedGarbage.Spec.MlKem`, which `Rind/VgOutcome.lean` imports, and `VerifiedGarbage.Spec.ChaCha20`,
which `Rind/VgChaCha20.lean` imports, with its contracts, which
`Rind/X86_64/VgChaCha20.lean`'s axioms restate, VG's RFC 7748 and
RFC 8032 specs, `VerifiedGarbage.Spec.X25519` and
`VerifiedGarbage.Spec.Ed25519` with the SHA-512 spec it states, with the
contracts `Rind/X86_64/VgCurve25519.lean`'s axioms restate, and
`VerifiedGarbage.Spec.Pbkdf2.Generic` with the hash and HMAC specs it imports,
which `Rind/VgPbkdf2.lean` proves rind's and `Rind/Aarch64/VgPbkdf2.lean`'s
axioms state. A pin that changes the ChaCha20 or PBKDF2 specs needs no review
of them: what rests on ChaCha20's is stated over `Rind/Spec.lean`, and
`Rind/VgPbkdf2.lean` proves PBKDF2's and its hashes' equal to rind's, so a
change their proofs cannot absorb fails the Lean build. A
pin that changes the others shows the change in its diff, against which that
re-pin must review the adaptation, for a change to the spec, and the axioms,
for one to the contracts. Every re-pin also moves the axioms' links to VG's theorems.
`admin/vg-bytes` checks the code, not which theorem covers it, so
`admin/vg-binding` does, from rind's side, in `admin/prove vg`: each axiom
names the routines it covers, each of which VG's text has, and the contract
VG's generated documentation gives each, which the files the axiom links
state; each link is at the pinned revision, lands on a theorem, definition, or
registration, and none of VG's files holds a `sorry` or an `axiom`; and every
routine rind vendors is one an axiom covers, through the calls in VG's text, or
one its `UNCOVERED` table lists with the quest that proves it. VG emits each
routine from an artifact whose `Verified` proof its emitter checks rests on
Lean's standard axioms, so a routine's theorem is its artifact's, and the
axiom's docstring is where rind says which. What this does not check is that
the theorem's statement is the axiom's: a reviewer reads that, as the
paragraphs above say.

`Rind/<Arch>/VgP256.lean` restates VG's contracts for the P-256 public key,
ECDH, and ECDSA verification routines rind runs, one axiom per wrapper in
`low::<arch>::p256_vg`, over `VerifiedGarbage.Spec.EcKey`, `Spec.Ecdh`, and
`Spec.Ecdsa`, whose contracts `admin/import-vg-models` vendors too.
`Rind/VgNist.lean` proves those specs are rind's for any VG curve that
`Matches` one of rind's NIST curves: VG's points add and multiply as
`nist.add` and `nist.pow`, through Mathlib's group of points
(`Rind/NistGroup.lean`), its key validation is `nist.OnCurve`, its octet
strings `beNat`'s, and its ECDSA verification `nist.ecdsaVerifies`.
`Rind/VgP256.lean` proves VG's P-256 matches rind's, and its ECDH is
`p256Pow`'s x-coordinate. `Rind/<Arch>/VgP384.lean` restates VG's contracts
for the P-384 public key and ECDSA verification routines, over
`VerifiedGarbage.Spec.EcKey.P384` and `Spec.Ecdsa.Verify.P384`, and
`Rind/VgP384.lean` proves VG's P-384 matches rind's. The P-256 and P-384
theorems below rest on them.

`Rind/VgPbkdf2.lean` proves VG's SHA-1, SHA-256, SHA-384, SHA-512, HMAC,
and PBKDF2 specs, which `VerifiedGarbage.Spec.Pbkdf2.Generic` imports, are
`Rind/HashSpec.lean`'s and `Rind/Sha2.lean`'s, PBKDF2's refusing a key longer
than `2^32 - 1` blocks as VG's does. `Rind/Aarch64/VgPbkdf2.lean` restates
VG's theorems about the aarch64 PBKDF2 routines rind runs, each variant's
`pbkdf2F`, as one axiom per hash about `low::aarch64::pbkdf2_vg::Pbkdf2::derive`,
and `Rind/Aarch64/Pbkdf2Vg.lean` proves `pbkdf2::Secret` from them, as "What
is proven" lists. `Rind/Aarch64/VgSha512.lean` restates VG's theorem about
its SHA-512 block function for the SHA-512 instructions, an internal routine
whose contract, `compressAArch64`, is in VG's proofs, as an axiom about
`low::aarch64::sha512::compress_hw`, from which it proves the wrapper
computes `Rind/Sha2.lean`'s `compress`.

`Rind/VgOutcome.lean` and `Rind/<Arch>/VgMlKem.lean` restate VG's contracts
for the ML-KEM-768 routines rind runs as one axiom per wrapper in
`low::<arch>::mlkem768_vg`. Each states only what the wrapper returns,
not VG's wipe of its scratch or what the routine may leak. The contracts
they restate, VG's `Spec/MlKem/Contract.lean` and `Spec/MlKem/EncapsH.lean`,
are not vendored, so a re-pin compares them at VG's new commit. No theorem rests
on them yet: the ✓ also needs rind's glue in `mid/mlkem.rs` proven, and its
fallback to rind's arithmetic.

`Rind/Aarch64/VgChaCha20Poly1305.lean` restates VG's theorems about the
aarch64 SVE2 and NEON ChaCha20-Poly1305 routines rind runs, `seal_framed` and
`open_framed` at each variant, as one axiom per wrapper in
`low::aarch64::chacha20poly1305`, over VG's AEAD spec,
`VerifiedGarbage.Spec.ChaCha20Poly1305` with its ChaCha20 and Poly1305
specs, which `Rind/VgChaCha20Poly1305.lean` imports and proves is
`Rind/Spec.lean`'s, so a re-pin that changes the spec fails there. Each axiom
states only what the wrapper returns, not VG's wipe of its stack scratch or
what the routine may leak. The contracts they restate, VG's
`Spec/ChaCha20Poly1305/Contract.lean`, are not vendored, so a re-pin
compares them at VG's new commit. `Rind/X86_64/VgChaCha20Poly1305.lean`
restates those about the x86_64 AVX-512 IFMA routines the same way, VG's
registrations `sealReg` and `openReg` at the `ifma` variant, which add the
clearing of the routines' stack and registers to `Shared.seal_verified` and
`Shared.open_verified`, as one axiom per wrapper in
`low::x86_64::chacha20poly1305`.

### rind's own proofs on VG's models

New proofs of the assembly rind runs are Lean theorems on VG's models, as
VG's own are, about the bytes rind's build emits. VG's aarch64 model lacks
some of what aws-lc's code uses, so `verified-garbage/RindIsa/AArch64.lean`
extends it, trusted as VG's is: its state is VG's with the frame pointer
`x29`, and its instructions are VG's, with VG's semantics, and LD1 and ST1 of
one to four registers, and aws-lc's frame of `x29` and `x30`. Each routine is
a `Code` program there, such as `RindIsa/AArch64/Sha256Hw.lean`'s, which
`RindIsa/Proven.lean` lists with the Rust path of the naked function it is
and the statics it reads. `admin/prove lean` builds `rind-asm`, which prints
each program's machine code from the model's encoder, its `adrp` and `add`
relocations, and each static's leading bytes, and fails unless rind's Linux
release build emits the same: the function's `.text`, its relocations against
the static's `.rodata`, and the static's bytes. `admin/prove vg` cosimulates
each distinct instruction and branch condition of those programs
(`Cosim/Rind.lean`, `--rind`) as it does VG's, comparing `x29` too, but for
the `adrp` and `add` the linker fills and the final `ret`, as VG's are not.

`verified-garbage/RindIsa/X86_64.lean` extends VG's x86_64 model the same
way: its state is VG's with `lo`, the lowest address the stack may reach, and
it adds the push, `lea`, `neg`, `dec`, aligned 128-bit load and store, and
`ja` aws-lc's code uses, a stack pointer move that claims the region it
passes over as writable and forgets what a release leaves below it, and the
padding (`.align` and the `jmp` over it), which runs as no instructions.
`admin/prove lean` compares each x86_64 program's bytes with the Linux build
the same way, `rind-asm x86_64` printing them, and `admin/prove vg`
cosimulates its instructions and branches (`Cosim/RindX86_64.lean`) but for
the padding, whose bytes that comparison checks.

- `Rind/X86_64/Mul4xProof.lean`: `bn_mul4x_mont_correct`, that
  `low::x86_64::mont::bn_mul4x_mont`, aws-lc's 4x Montgomery multiplication
  without BMI2 and ADX, run from a state its `Pre` holds of (a width `k`
  that is a multiple of four from eight and below `2^32`, `n0` the
  `-m⁻¹ mod 2^64` of `m`, `a` below `m`, writes to `rp` only, `rp` disjoint
  from `m`, every argument outside the `8k + 1104` bytes below the stack
  pointer it owns, and room for that frame above `lo`), writes the Montgomery
  product `a·b·2^(-64k) mod m` to `rp`, below `m`, returns 1, and changes no
  other memory outside that frame and no register SysV makes the callee
  save; that its trace is a function of its pointers, width, and stack
  pointer (`ConstantTime`); and that some state meets `Pre`. The other
  `Mul4x*` files build it: `Mul4xModel` the words a pass computes,
  `Mul4xAsm` and `Mul4xHeadAsm` the program's blocks, `Mul4xHead` the
  prologue and page walk, `Mul4xLoop` and `Mul4xOuter` the passes,
  `Mul4xSub`, `Mul4xTailAsm`, and `Mul4xFinal` the subtraction and the
  constant-time copy.
  `Rind/X86_64/RsaMont.lean` restates it as `mul4x_spec`.

- `Rind/Aarch64/Sha256HwAsm.lean`: `sha256_block_data_order_hw_correct`,
  that `low::aarch64::sha256::sha256_block_data_order_hw`, aws-lc's routine
  for the SHA-256 instructions, run from a state its `Pre` holds of (at least
  one block, a 16-byte-aligned stack pointer, reads of the blocks and `K256`
  and reads and writes of the state and the frame only, a frame that overlaps
  none of the others, and `K256` holding FIPS 180-4's constants), computes s2n-bignum's FIPS 180-4 spec,
  `sha256_hash_blocks`, of the blocks into the state, changing no memory but
  the state and the 16-byte frame below the stack pointer and no register
  AAPCS64 makes the callee save, and returning with `x29`, `x30`, and the
  stack pointer as they were; that its trace of addresses and branches is a
  function of its arguments, the stack pointer, and the table's address
  (VG's `ConstantTime`); and that some state meets its precondition. It
  replaces HOL Light's `SHA256_HW_SUBROUTINE_CORRECT`, whose conclusions it
  keeps under weaker hypotheses: the state may overlap the blocks or the
  table, and the table's address is a symbol, not an `adrp` range.

## curve25519-dalek's proofs

[Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation/curve25519-dalek-fork)
(BAIF) proves curve25519-dalek's serial backends in Lean, through Charon and
Aeneas as here, in its fork of the crate. Its theorems have no `sorry` and
rest on Lean's axioms and three of BAIF's own, which model the `alloc`,
`subtle`, and `zeroize` functions dalek calls. rind runs that backend on
armv7, and `Rind/Armv7/Dalek.lean` restates BAIF's theorems about the two
functions armv7's X25519 calls, `MontgomeryPoint::mul_clamped` and
`mul_base_clamped`, as axioms about the translation's opaque declarations of
them. `curve25519-dalek/` holds the spec modules those statements name,
`ForHumans/Specs/X25519.lean` and the modules of BAIF's it imports, which
`admin/import-dalek` copies byte for byte at the commit it pins, with the
fork's license; `lakefile.toml` requires BAIF's elliptic-curve library at the
revision that commit pins.

BAIF's theorems are about its translation of the fork's source, and rind
builds the crates.io release, so `admin/prove dalek`, which `admin/prove
lean` runs, checks that the two are the same code. It translates the release
as BAIF's `scripts/aeneas-translate.sh` translates the fork: with the Aeneas
release BAIF pins, the flake's `aeneas-dalek`, BAIF's translation patches,
Charon options, and four configurations, and the features rind's manifest
asks of dalek, which must be the ones BAIF builds with. `admin/dalek-closure`
then fails unless every definition the two functions reach in the
configuration armv7 builds, 32-bit with precomputed tables, has BAIF's text.
A patch that does not apply to the release is reported and skipped, so a
definition it would have changed fails that comparison if X25519 reaches it.
One patch writes the code of the ladder's `mul_bits_be` and `bits_le` into
their caller, so the comparison reads BAIF's copy: `admin/prove`'s
`dalek_copied` names them, and their source must be the fork's.

## What is proven

X25519 on x86_64 and aarch64, from the agreement API's `PrivateKey` to
s2n-bignum's routines, and on x86_64 CPUs with AVX-512 IFMA to
pyca/verified-garbage's, in `Rind/X86_64/X25519.lean`, which `admin/prove`
also writes for aarch64:

- `x25519_generate`: the key's scalar is the 32 drawn bytes, read
  little-endian, it holds its public key, and a failed draw is refused;
- `x25519_from_scalar`: a loaded key's scalar is the 32 given bytes, read
  little-endian, it holds its public key, and any other length is refused;
- `x25519_public_key`: the public key a key holds is the 32 little-endian
  bytes of `cpuX25519 o (scalar, 9)`;
- `x25519_agree`: a peer key that is not 32 bytes is refused, so is an
  all-zero result, and otherwise the secret is the 32 little-endian bytes of
  `cpuX25519 o (scalar, u)`, for the peer's bytes `u` read little-endian;
- `x25519_shared_secret`: the secret's bytes are those.

`cpuX25519 o` is RFC 7748's X25519, clamping and masking included, as the
code the CPU runs is proven against: HOL Light's `rfcx25519` where the IFMA
check returns no token (`o = none`, and every aarch64 CPU), and VG's
`VerifiedGarbage.Spec.X25519.x25519` of the 32 little-endian bytes, as
`Rind/VgCurve25519.lean`'s `vgX25519` reads it, where it returns one. The two
specs both transliterate RFC 7748, but HOL Light's stays opaque, so no proof
equates them. On IFMA CPUs the theorems rest on the axioms
`vg_x25519_base_spec` and `vg_x25519_exchange_spec`.

X25519 on armv7 CPUs without NEON, from the same `PrivateKey` to
curve25519-dalek's serial 32-bit backend, in the same five theorems, which
`admin/prove` writes for armv7 from `Rind/X86_64/X25519.lean` over
`Rind/Armv7/Curve25519.lean`'s dispatch. There `cpuX25519 o` is
`dalekX25519`: Beneficial AI Foundation's (BAIF's) `curve25519.X25519` of
the 32 little-endian bytes, as `Rind/Dalek.lean` reads it. The theorems take
a CPU without NEON, `DalekCpu o`, since with NEON the shared secret runs
BoringSSL's NEON ladder, which no proof covers yet; the public key runs dalek
on every CPU, but its theorems share that hypothesis with the rest. They rest
on the axioms `dalek_mul_base_clamped_spec` and `dalek_mul_clamped_spec`,
which [curve25519-dalek's proofs](#curve25519-daleks-proofs) describes.

P-256 ECDH on x86_64 and aarch64, from the same `PrivateKey` to s2n-bignum's
routines, in `Rind/X86_64/P256Agree.lean` and `Rind/X86_64/P256.lean`, which
`admin/prove` also writes for aarch64. Key generation multiplies the
generator as each target's `Rind/<Arch>/P256Base.lean` states it: aarch64 by
s2n-bignum's `p256_scalarmulbase`, and x86_64 by rind's Booth driver, which
selects each table row's point by rind's Rust select and adds it by aws-lc's
mixed addition, `ecp_nistz256_point_add_affine` or its BMI2 and ADX form,
which rind proves in HOL Light:

- `p256_generate`: the key's scalar is the first of up to 64 draws whose
  bytes, read big-endian, are in [1, n), it holds its public key, and the key
  is refused if a draw fails before one is, or none is;
- `p256_from_scalar`: a loaded key's scalar is the 32 given bytes, read
  big-endian, refused unless they are 32 bytes and in [1, n), and it holds
  its public key;
- `p256_public_key`: the public key a key holds is the X9.62 uncompressed
  encoding of the scalar times G;
- `p256_agree`: a peer key is refused unless it is a 65-byte uncompressed
  point whose coordinates are below p and on the curve, and otherwise the
  secret is the 32 big-endian bytes of the x-coordinate of the scalar times
  that point, or a fault unless that is a finite point on the curve;
- `p256_shared_secret`: the secret's bytes are those.

Every P-256 theorem, ECDSA's below included, covers pyca/verified-garbage's
P-256 too, which rind takes on x86_64 with BMI2, ADX, AVX, and AVX2 and on
every aarch64 CPU: each assumes `RunsP256`, that VG's checks return, which
read no input, and proves both what rind's own code and what VG's routine
computes, the latter from `Rind/<Arch>/VgP256.lean`'s axioms, which restate
VG's theorems, and `Rind/VgP256.lean`, which proves VG's spec of P-256 is
the one stated here. `p256_agree` takes a scalar below n, as every key
`p256_generate` and `p256_from_scalar` make has, since VG's ECDH refuses any
other.

`p256Pow` is HOL Light's `group_pow p256_group`, defined as HOL Light does
once for the NIST curves in `Rind/Spec.lean`, and `Rind/NistGroup.lean`
proves it is multiplication in Mathlib's group of points on such a curve. `Rind/P256Multiples.lean` proves G's order n: the kernel
computes (n - 1)·G by doubling and adding, checking each step's coordinates
against the group law, and finds -G, and `Rind/N256Prime.lean` proves n
prime. So a scalar in [1, n) times G is a finite point. `p256_order` gives
every finite point order n too, by `Rind/NistOrder.lean`'s count of the
curve's points, but `p256_agree` does not yet use it to rule out its fault
case for the peer's point.

P-256 ECDSA with SHA-256 and fixed-length signatures on x86_64 and aarch64,
from the signature API's `ecdsa::KeyPair` and `ecdsa::PublicKey` to s2n-bignum's
routines, in `Rind/X86_64/P256Signature.lean` over
`Rind/X86_64/P256Ecdsa.lean`, which `admin/prove` also writes for aarch64,
over each target's generator multiplication, as for ECDH, and its check of a
key pair's public key, `Rind/<Arch>/P256KeyCheck.lean`: aarch64 compares it
with the key's own encoding, and x86_64 compares an uncompressed one's point
with the generator multiplication's Jacobian result, without encoding it:

- `p256_ecdsa_generate`: the key pair's scalar is in [1, n), it holds the
  public key below, and generation is refused only if the system source's
  draws fail;
- `p256_ecdsa_from_scalar_and_public_key`: a scalar that is not 32 bytes
  is refused, so is one outside [1, n), and so is a public key that is neither
  X9.62 encoding, uncompressed or compressed, of the scalar times G, and
  otherwise the key pair's scalar is the scalar, and it holds the public key
  below;
- `p256_ecdsa_sign`: a signature signing returns is 64 bytes, the big-endian
  r and s of the ECDSA signature of the message's SHA-256 under the scalar,
  for some nonce in [1, n), neither zero, and signing is refused only if the
  nonce's random input cannot be drawn;
- `p256_ecdsa_key_pair_public_key`: the public key's bytes are the X9.62
  uncompressed encoding of the scalar times G;
- `p256_ecdsa_public_key_new`: a public key is refused unless it is a 65-byte
  uncompressed point whose coordinates are below p and on the curve, and
  otherwise its `verify` accepts exactly the signatures ECDSA verifies with
  that point: 64 bytes, r and s in [1, n), and the x-coordinate of
  e/s·G + r/s·Q, a finite point, equal to r mod n;
- `p256_ecdsa_key_pair_verify`: a key pair's public key verifies the same
  way, with its point the scalar times G.

`ecdsaP256Sign` and `ecdsaP256Verifies` in `Rind/Spec.lean` are FIPS 186-5's,
over `p256Pow` and `p256Add`. `Rind/P256Multiples.lean` proves, from
`Rind/NistGroup.lean`'s group, the laws by which the twin multiplication's
windowed sum is e/s·G + r/s·Q, and `Rind/N256Prime.lean` that n is prime, so
every nonzero scalar has an inverse. The sum also needs Q's order n. A key
pair's Q is its scalar times G, whose order follows from G's. A parsed public
key's is any point on the curve, whose order n is `p256_order`, HOL Light's
`P256_GROUP_ELEMENT_ORDER`: Mathlib has no Hasse bound to count the curve's
points, so `Rind/NistOrder.lean` counts them elementarily. Each x gives at
most two points, so the group has at most 2p + 1 < 3n; n divides its order,
as G has order n; and an order of 2n would give a point of order 2 by Cauchy,
whose x would be a root of x³ - 3x + b mod p, which the kernel checks has
none. So the order is n, a prime. The message's
SHA-256 is FIPS 180-4's (`sha256E`), through the SHA-256 proof below, so
signing and verification take its `Sha256Blocks` and messages of at most
`maxInput` bytes. Signing draws nonces until r and s are both
nonzero, with no bound, so `p256_ecdsa_sign` says what a returned signature
is, not that one returns. The nonces come from RFC 6979's HMAC-DRBG, hedged
with 16 bytes from the system source; its update takes a slice of borrowed
slices, which Aeneas cannot translate, so it is opaque, and the theorems
assume `Drbg`: it seeds and draws without panicking, and a draw never fails.
They also assume `Fills`, that the system source returns, `Held`, that the
entry guard holds, and `Cached`: a verifying key's lock-free caches of P to
15P and 17P to 31P, and a signing key's of its encoded public key, whose
atomics Aeneas cannot translate, are built from the key's own point or
scalar, and a signing key's returns whenever its build does, as x86_64's
key check stores the encoding it checked.

P-384 ECDH's agreement on x86_64 and aarch64, from the same `PrivateKey` to
s2n-bignum's routines, in `Rind/X86_64/P384.lean`, which `admin/prove` also
writes for aarch64:

- `p384_agree`: a peer key is refused unless it is a 97-byte uncompressed
  point whose coordinates are below p and on the curve, and otherwise the
  secret is the 48 big-endian bytes of the x-coordinate of the scalar times
  that point, or a fault unless that is a finite point on the curve;
- `p384_shared_secret`: the secret's bytes are those.

P-384's key generation on x86_64 and aarch64, in `Rind/X86_64/P384Keygen.lean`,
which `admin/prove` also writes for aarch64, as P-256's is on aarch64:

- `p384_generate`: the key's scalar is the first of up to 64 draws from the
  system source whose bytes, read big-endian, are in [1, n), and generation is
  refused if a draw fails first or none is;
- `p384_from_scalar`: a scalar that is not 48 bytes is refused, so is one
  outside [1, n), and otherwise the key's scalar is the scalar;
- `p384_public_key`: a key's public key is the X9.62 uncompressed encoding of
  its scalar times G.

P-384 ECDSA with SHA-384 and fixed-length signatures on x86_64 and aarch64,
from the signature API's `ecdsa::KeyPair` and `ecdsa::PublicKey` to
s2n-bignum's routines, in `Rind/X86_64/P384Signature.lean` over
`Rind/X86_64/P384Ecdsa.lean`, which `admin/prove` also writes for aarch64,
over the comb above for k·G and each target's `Rind/<Arch>/P384KeyCheck.lean`,
which reads its own translation of the public-key check: P-384 has no
uncompressed fast path, so both targets compare a given public key with the
key's own encoding. The theorems are P-256's, with 48-byte scalars, 97-byte
points, 96-byte signatures, and the message's SHA-384 (`sha384E`), through
the SHA-384 proof below, so signing and verification take its `RunsSha512`:
`p384_ecdsa_generate`, `p384_ecdsa_from_scalar_and_public_key`,
`p384_ecdsa_sign`, `p384_ecdsa_key_pair_public_key`,
`p384_ecdsa_public_key_new`, and `p384_ecdsa_key_pair_verify`.
`ecdsaP384Sign` and `ecdsaP384Verifies` in `Rind/Nist.lean` are
`Rind/Spec.lean`'s FIPS 186-5 ECDSA at P-384's p, n, and G. Verification's
twin multiplication reads a 385-digit width-5 NAF of e/s, whose multiples of G
come from the comb's first table, and of r/s over Q's odd multiples, which a
key caches, and `Rind/P384Multiples.lean` proves the laws by which its sum is
e/s·G + r/s·Q and that every finite point on the curve has order n
(`p384_order`). As for P-256, verification settles equal and opposite points
by cases before s2n-bignum's `p384_montjadd` and `p384_montjmixadd`, whose
contracts exclude them, and the theorems assume `Drbg`, `Fills`, `Held`, and
P-384's `Cached`, its keys' caches.

Where pyca/verified-garbage's checks pass, P-384 runs VG's routines: its
`d·G` for key generation and each signature's k·G, on every x86_64 and
aarch64 CPU, and its ECDSA verification, on x86_64 with BMI2 and ADX and on
aarch64 until a key's multiples are ready. `Rind/<Arch>/VgP384.lean` restates
their theorems as axioms, and the P-384 theorems assume only `RunsP384`, that
the checks return, so cover rind's code and VG's alike. VG's contracts state
SEC 1 and FIPS 186-5 over its own transcription, which `Rind/VgNist.lean`
proves rind's for any of its curves that `Matches` one of rind's NIST curves,
and `Rind/VgP384.lean` proves P-384 does, as `Rind/VgP256.lean` does P-256.
`raw_ecdsa_verify` calls rind's twin multiplication from one function,
`rind_ecdsa_verify`, so the proof is one on both targets though only aarch64
reads the multiples' cache to choose.

rind computes k·G with its own comb in Rust, aws-lc's layout: 77 Booth-recoded
5-bit windows added from 20 tables of 1 to 16 times 2^(20j)·G, with five
doublings between the four teeth. `Rind/P384Comb.lean` proves the windows'
digits sum to the scalar and that no mixed addition meets the equal points
s2n-bignum's `p384_montjmixadd` excludes, for a scalar below n, and
`Rind/X86_64/P384Table.lean` has the kernel check the translated tables
against G. The draws are modelled in `Rind/X86_64/P384Dispatch.lean`, as
P-256's are. The table lookup is rind's AVX2, SSE2, or NEON select, below,
which each target's `Rind/<Arch>/P384Select.lean` states under `Runs`.

`p384Pow` is HOL Light's `group_pow p384_group`, whose group law
`Rind/Spec.lean` defines once for the NIST curves, and `Rind/NistGroup.lean`
proves it is multiplication in Mathlib's group of points on such a curve. `Rind/P384Group.lean` proves p and n prime,
by Pratt certificates that `Rind/Pratt.lean` checks, and G's order n.

The comb's constant-time row select, `bignum_aff_point_select_p384`, on
x86_64 with P-256's and P-521's in `Rind/X86_64/PointSelect.lean`, and on
aarch64 in `Rind/Aarch64/PointSelect.lean`, over the lemmas both share in
`Rind/RowSelect.lean`:

- `bignum_aff_point_select_p256_spec`, `_p384_spec`, `_p521_spec`: the select
  returns row `index` of a table of 8-, 12-, or 18-word affine points,
  counting from 1, or zeros for an index of 0 or past the last row, on
  x86_64's AVX2 and SSE2 paths and aarch64's NEON one (P-384's alone), for a
  table of fewer than 2^32 rows;
- `bignum_aff_point_select_p384_rows16`: the same on P-384's 16-row comb
  tables, as P-384's key generation takes it.

On x86_64 they assume `RunsSelect`: `HaveAvx2::check` returns, as `Runs`
assumes of `HaveBmi2Adx::check`. aarch64's select assumes nothing.

ChaCha20 QUIC header protection on x86_64, aarch64, armv7, and the portable
backend, from `HeaderProtectionKey` to HACL*'s rounds, in
`Rind/X86_64/ChaCha20.lean`, which `admin/prove` also writes for the others:

- `chacha20_new`: a key that is not 32 bytes is refused, and otherwise the
  key holds its bytes;
- `chacha20_mask`: the mask is RFC 9001's, the first five bytes of RFC 8439's
  keystream block for the key, with the sample's first four bytes as the
  little-endian block counter and the rest as the nonce.

HACL*'s rounds are Rust, so they are translated and proven with the rest, and
no axiom stands in for HACL*'s proof of them. `chacha20_mask` assumes only
`RunsChaCha20`, that the entry guard admits it, which each target's `Runs`
implies. armv7's translation also reaches the AES-GCM API, below.

The bitsliced AES armv7 runs with neither NEON nor the crypto extension,
`low/generic/aes_nohw.rs` in 32-bit words, is proven from the key to the
block: `new_schedule_spec` in `Rind/Armv7/AesNohwKey.lean` proves that
`NohwKey::new` and `NohwKey::schedule` turn a 16-, 24-, or 32-byte key into a
schedule holding Vale's `key_to_round_keys_LE` of its words, and
`schedule_encrypt_block` that such a schedule's `encrypt_block` is Vale's
`aes_encrypt_LE` under that key. Under them, `setup_key_128_spec`,
`setup_key_192_spec`, and `setup_key_256_spec` state each key expansion
against `Rind/Aes.lean`'s round key recurrences, a step of the schedule at a
time in compact words (`rot_step`, `sub_step`, and AES-192's `step192_a` and
`step192_b`), and `encrypt_block_spec` in `Rind/Armv7/AesNohwBlock.lean`
proves that `Schedule::encrypt_block` is `cipherRounds`, Vale's `eval_cipher`
for the schedule's number of rounds, on the round keys the schedule holds, and
`encrypt_batch_spec` the same of both blocks of a batch.
`Rind/Armv7/AesNohw.lean` proves the S-box circuit, `AesNohwRound.lean`
`ShiftRows`, `MixColumns`, and `AddRoundKey`, and `AesNohwBatch.lean` the
compact form and the transpose, each at every bit position by `bv_decide`, as
`AesNohwKey.lean` proves each key schedule step at every byte,
against the FIPS 197 functions Vale's spec names: `sbox` and `mixColumns` are
irreducible definitions rather than opaque ones, so these proofs alone unfold
them, through `sbox_eq` and `mixColumns_eq`, and `Rind/AesSbox.lean` has the
kernel check the S-box table against a decision tree on its input's bits. No
theorem yet states that `ctr32` is counter mode, or anything of GHASH and the
GCM above them, so [armv7's AES-GCM](/quest/m5/verified-armv7/prove.md) has
no ✓.

Theorems that run an entry guard assume `Runs`: rind's CPU-feature checks
pass, which no input affects. `Rind/<Arch>/P256Table.lean` proves that each
target's generator table holds the multiples of G its generator
multiplication reads, on aarch64 those s2n-bignum's proof of
`p256_scalarmulbase` assumes, and `Rind/<Arch>/P256Base.lean` that its first
row holds G to 32G, which ECDSA verification's twin multiplication reads, so
no theorem assumes anything of the tables.
On x86_64, `Rind/X86_64/P256Base.lean` proves that `base_multiply`, rind's
port of aws-lc's Booth-recoded generator multiplication, computes k·G for k
below n (`base_multiply_spec`, and `jac_base_multiply_spec` before its affine
conversion): `Rind/P256Booth.lean` proves the recoded digits sum to k and that
no addition doubles, and `Rind/X86_64/P256Table.lean` that its 37-row table
holds j·2⁷ⁱ·G. Its table select is rind's Rust, which
`Rind/X86_64/PointSelect.lean` proves on both the AVX2 and SSE2 paths, under
`RunsSelect`, that `HaveAvx2::check` returns, which `Runs` includes. aws-lc's
mixed addition, both its mulq and its BMI2 and ADX routines, is proven in
HOL Light of the object code rind's Linux build emits, in
`proofs/hol-light/x86_64/ecp_nistz256_point_add_affine.ml` and
`ecp_nistz256_point_add_affinex.ml`, which `p256_point_add_affine_spec` in
`Rind/X86_64/S2nBignum.lean` restates. The proofs reuse s2n-bignum's
`p256_montjmixadd` field algebra and also cover the two infinities the
driver starts from.
`Rind/<Arch>/Axioms.lean` checks the axioms each theorem rests on.

SHA-1 and SHA-256's padding and finalization, and HMAC's keyed states over
any hash, on x86_64 and aarch64, in `Rind/X86_64/{Blockwise,Sha,Hmac}.lean`,
against FIPS 180-4 and RFC 2104 as `Rind/HashSpec.lean` transliterates them:

- `sha256_hash`, `sha1_hash`: a message's digest, one-shot, and
  `sha256_hashSpec`, `sha1_hashSpec`: every method of each `Hash` impl,
  streaming included;
- `hmac_key_new_spec`, `hmac_sign_spec`, `hmac_start_spec`,
  `hmac_update_spec`, `hmac_finish_spec`: `HmacKey` and `Hmac` over any hash
  meeting `HashSpec`, and `hmac_sha256_sign`, `hmac_sha1_sign` over SHA-256
  and SHA-1.

Below rind's padding, these theorems take `Sha1Blocks` or `Sha256Blocks` as
a hypothesis, in each target's own `Rind/<Arch>/ShaBlocks.lean`. No proof
covers a SHA-1 block function rind runs, or SHA-256's on x86_64 without the
SHA extensions or AVX2, so there each states that every such routine computes
FIPS 180-4's block function, x86_64's SHA extensions' routine for SHA-1's
padded last blocks pads as FIPS 180-4 does, and that rind's checks pass.
`Rind/X86_64/Sha256Shaext.lean` restates the HOL Light proofs above of
SHA-256's routines for the SHA extensions as the axioms
`sha256_compress_blocks_shaext_spec` and `finish_padded_spec`, and proves that
the finish's padding, `padded` and `ended`, gives FIPS 180-4's last blocks.
`Rind/X86_64/ShaBlocks.lean` restates the one above of OpenSSL's AVX2
routine as the axiom `sha256_compress_blocks_avx2_spec`.
On aarch64, `Sha256Blocks` states only that the CPU has the crypto extension
and rind's checks pass: `Rind/Aarch64/Sha256Hw.lean` restates the Lean proof
above, in `Rind/Aarch64/Sha256HwAsm.lean`, as the axiom
`sha256_block_data_order_hw_spec` about its opaque wrapper, and
`Rind/S2nSha256.lean` proves s2n-bignum's spec FIPS 180-4's block function.
`Rind/<Arch>/HashAxioms.lean` checks the axioms each theorem rests on: those
for SHA-256 on x86_64 and aarch64. An input is at most `maxInput`
(2^61 - 1) bytes, under FIPS 180-4's 2^64-bit limit. `Rind/HashSpecTest.lean`
checks the transliterations against FIPS 180-4's, RFC 4231's, RFC 5869's, and
RFC 6070's vectors.

The APIs above them, on x86_64 and aarch64, over SHA-1 and SHA-256 and, where
they take an HMAC algorithm, SHA-384 and SHA-512, against RFC 2104, RFC 5869,
and RFC 8018 as `Rind/HashSpec.lean` transliterates them:

- `digest_spec`, `digest_ctx_new_spec`, `digest_ctx_update_spec`,
  `digest_ctx_finish_spec` (`Rind/X86_64/DigestApi.lean`): `digest::digest`
  and `digest::Context` over SHA-1 and SHA-256;
- `key_new_spec`, `sign_spec`, `verify_spec`, `context_with_key_spec`,
  `context_update_spec'`, `context_sign_spec` (`Rind/X86_64/HmacApi.lean`):
  `hmac::Key`, `sign`, `verify`, and `Context`;
- `kdf.salt_extract_spec`, `kdf.prk_fill_spec`, `kdf.hkdf_fill`,
  `kdf.prk_new_fill` (`Rind/X86_64/Hkdf.lean`): HKDF's extract and expand,
  and expand from a PRK loaded from bytes;
- `kdf.derive_spec`, `kdf.verify_spec` (`Rind/X86_64/Pbkdf2.lean`): PBKDF2's
  `Secret::derive` and `Secret::verify` on rind's loop;
- `kdf.secret_new_spec`, `kdf.secret_derive_spec`, `kdf.secret_verify_spec`
  (`Rind/Aarch64/Pbkdf2Vg.lean`, aarch64 only): `Secret::new`, which keys
  pyca/verified-garbage's routine through `mid::pbkdf2_vg`, keeping HMAC's
  key, the secret or its hash past a block, or rind's loop, proven to key the
  secret on whichever it picks but not that it picks by the CPU's
  instructions, and assuming the opaque crypto-extension check returns,
  whatever it finds; and `Secret::derive` and `Secret::verify` on either,
  from `Rind/Aarch64/VgPbkdf2.lean`'s axioms. VG's branch also takes the
  iteration count to be positive, which its `NonZeroU32` holds and the
  translation forgets, and that `low::zeroise` returns. Only aarch64 translates `mid::pbkdf2_vg`; the other targets'
  second pass leaves it opaque, as no CPU of theirs runs it.

HKDF's `From<Okm>` conversions, each filling the key's length of HKDF-Expand
into a zeroed buffer and keying it, in `Rind/X86_64/Hkdf.lean` and
`Rind/X86_64/HkdfAes.lean` on both targets and `Rind/X86_64/HkdfAead.lean` on
x86_64:

- `hmac_key_from_spec`, `prk_from_spec`: the `hmac::Key` and `Prk` are keyed
  under the algorithm with the `tag_len` bytes of HKDF-Expand;
- `header_key_from_spec`: ChaCha20 header protection holds the 32 bytes of
  HKDF-Expand, through `header_new_spec` over `chacha20_new`;
- `aead_key_from_spec`: an AES-128-GCM, AES-192-GCM, or AES-256-GCM key holds AES-GCM for
  the `4 * nk` bytes of HKDF-Expand, under `RunsAesGcm`, through
  `aead_key_new_spec` over `aes_gcm_new`;
- `aead_key_from_chacha20_poly1305_spec`: a ChaCha20-Poly1305 key holds the
  32 bytes of HKDF-Expand, through `aead_key_new_chacha20_poly1305_spec` over
  `chacha20_poly1305_new`;
- `aes_header_key_from_spec`: AES-128 or AES-256 header protection holds
  FIPS 197's round keys for the `4 * nk` bytes of HKDF-Expand, under
  `RunsAesHw`, through `aes_header_new_spec` over `aes_header_new`.

`Rind/X86_64/Kdf/FunsExternal.lean`'s `new` wrappers turn a model's refusal into the panic its `expect` makes, so
each conversion panics exactly where its `expect` does.

`hmac::Key` and `Context` reach each hash through function pointers, which
`Rind/X86_64/HmacDispatch.lean` models. HKDF and PBKDF2 call that model, so
`admin/prove` translates `high::hkdf` and `high::pbkdf2` in a second pass,
into `Rind/<Arch>/Kdf/{Types,Funs}.lean`, with the first pass's items and the
HMAC model opaque below it; `Rind/X86_64/HkdfExpand.lean` models
`Prk::expand_into`, whose slice of borrowed slices Aeneas cannot translate.
The theorems over an HMAC algorithm assume `RunsHmac`: `Sha1Blocks` for SHA-1,
`Sha256Blocks` for SHA-256, and `RunsSha512` for SHA-384 and SHA-512, so `Rind/<Arch>/Axioms.lean`
checks their axioms.
`hmac::verify` and `Secret::verify` compare through `low::generic::ct_equal`,
which `Rind/X86_64/CtEqual.lean` proves returns whether its inputs are equal,
from axioms restating the HOL Light proofs of the `asm!` compares below it.

`PrivateKey` reaches each curve's `Agree` impl through function pointers
(`Algorithm`'s `generate` and `load`, and `Keyed`'s `Ops`), and `HeaderProtectionKey` each
cipher's `Mask` impl (`Algorithm`'s `new` and `Masker`'s `mask`), which Aeneas
cannot translate. `Rind/X86_64/Dispatch.lean` models the agreement dispatch
and the AES header-protection statics, and `Rind/X86_64/QuicDispatch.lean` the
rest of the header-protection dispatch, by hand, in Lean definitions beside
the Rust they model, with an agreement `Algorithm` as which static it is.
P-256's key generation draws through a `dyn
RandomSource`, which Aeneas cannot translate either, and
`Rind/X86_64/P256Dispatch.lean`, which `admin/prove` also writes for aarch64,
models it the same way, for `Rind/<Arch>/Dispatch.lean` to call. The signature API's `ecdsa::KeyPair` reaches each curve's code, and
`ecdsa::PublicKey` each ECDSA key's parser and verifier, through function
pointers, and P-256's and P-384's ECDSA key generation draws through a `dyn
RandomSource`; `Rind/X86_64/EcdsaDispatch.lean`, which `admin/prove` also
writes for aarch64, models them for P-256 with SHA-256 and P-384 with
SHA-384, each with fixed-length signatures, over `Rind/X86_64/SignatureBuffer.lean`'s model of
`Buffer::write`, whose closure returns a borrow of its argument.

SHA-384, SHA-512, and SHA-512/256, from the digest API to aws-lc's block
routine, in `Rind/X86_64/Sha512.lean`, which `admin/prove` also writes for
aarch64:

- `sha512_family_digest`: `digest`'s bytes are the hash of the message;
- `sha512_family_context`: a `Context` given the message in any chunks, then
  finished, returns its hash, for messages under 2^64 bytes.

The hash is cryptol-specs' FIPS 180-4 SHA-512, in `Rind/Sha2.lean`, with its
block compression `processBlock_Common` transliterated from FIPS 180-4 and
checked by `Rind/Sha2Test.lean` against its examples. Each theorem assumes
`RunsSha512`: on x86_64 that rind picks aws-lc's AVX routine, on an Intel CPU
with AVX but without the feature set below, or OpenSSL's AVX2 routine, on a
CPU with AVX2, BMI1, BMI2, POPCNT, and SSSE3,
whose proof is rind's HOL Light proof above,
which `Rind/X86_64/AwsLc.lean` restates as the axiom
`sha512_block_data_order_avx2_spec`; on aarch64 only that rind's checks pass,
as both routines there have proofs: aws-lc-verification's of aws-lc's
scalar routine, and pyca/verified-garbage's Lean proof of its routine for
the SHA-512 instructions, which `Rind/Aarch64/VgSha512.lean` restates as the
axiom `vg_sha512_compress_sha512_spec`. For the HOL Light proof,
`Rind/S2nSha512.lean` proves s2n-bignum's spec `Rind/Sha2.lean`'s, and for
VG's, `Rind/VgPbkdf2.lean` proves VG's spec `Rind/Sha2.lean`'s. The
digest API reaches each hash through function pointers too, which
`Rind/X86_64/DigestDispatch.lean` models, and `Rind/X86_64/DigestAlgorithm.lean`
models the `Algorithm` statics that hold them, and `Digest`, whose
`&'static Algorithm` Aeneas cannot end a borrow of `Digest` across.

SHA3-256, SHA3-384, and SHA3-512, and the SHAKE calls ML-KEM and ML-DSA make, on x86_64
and aarch64, from rind's Rust sponge to s2n-bignum's Keccak-f routines, in
`Rind/X86_64/Sha3.lean`, which `admin/prove` also writes for aarch64:

- `sha3_family_digest`: `digest`'s bytes are the hash of the message;
- `sha3_family_context`: a `Context` given the message in any chunks, then
  finished, returns its hash;
- `sha3Family_fips202`: those hashes are FIPS 202's SHA3-256, SHA3-384, and
  SHA3-512;
- `sponge_absorb_spec`, `sponge_finish_spec`, `squeezing_squeeze_spec`: a
  `Sponge` absorbs any message in any pieces, and once finished, each
  `squeeze` writes FIPS 202's sponge on it from the next whole rate block,
  skipping what the last call left of its block, as ML-KEM's J (SHAKE256)
  and its matrix sampling's tail draw;
- `shake128x4_new_spec`, `shake128x4_squeeze_spec`: `SqueezingSponge4xShake128`
  writes the first 504 bytes of SHAKE128 on each of four 34-byte inputs, and
  returns the sponges to squeeze the rest;
- `shake256_batch_spec`: `shake256_batch` writes the first 128 bytes of
  SHAKE256 on each of its 33-byte inputs, four at a time;
- `shake_new_spec`, `shake_read_spec`: a `Shake` reader on a `Sponge` that
  has absorbed a message fills each `read`'s output with the next bytes of
  SHAKE on it, as ML-DSA's H (SHAKE256) and SampleInBall;
- `shake8x_new_spec`, `shake8x_squeeze_spec`: `Shake8x` absorbs one to eight
  inputs shorter than a block, and each `squeeze` writes each lane's next
  whole blocks of SHAKE on its input, as ML-DSA's ExpandA (SHAKE128),
  ExpandS, and ExpandMask (SHAKE256), and ML-KEM-512's noise (SHAKE256).

The sponge is `Rind/Sha3.lean`'s, over bytes, which `sha3_256_eq` and its
siblings, `shake128_eq` and `shake256_eq`, prove FIPS 202's as SymCrypt's
Lean spec (`Rind/SymCrypt/Sha3.lean`, MIT) states it. Keccak-f is
s2n-bignum's `keccak 24` on lanes, the spec its routines' theorems state,
which `Rind/Keccak.lean` proves SymCrypt's KECCAK-f[1600].
`Rind/<Arch>/KeccakDispatch.lean` proves what rind's dispatch to the one-,
two-, four-, and eight-state routines computes, from those theorems. Each
theorem assumes `RunsSha3`: rind's entry guard and CPU checks pass, and on
x86_64, rind's own AVX-512 eight-way Keccak-f, which `Shake8x` and
ML-KEM-1024's sampler run, computes Keccak-f on each state. No proof covers
that kernel yet; ML-KEM-768 runs pyca/verified-garbage's code there instead.
Wherever rind's sampler runs for ML-KEM-768, it samples eight of its nine
polynomials four at a time and the ninth alone, never eight at a time.

The portable backend's Keccak-f, which its SHA-3, ML-KEM, and ML-DSA run, in
`Rind/Portable/Keccak.lean`, over a translation of `low/portable/keccak.rs`
under `--cfg rind_portable`: `keccak_f1600_spec`, `keccak4_f1600_spec`, and
`keccak_nof4_f1600_spec` state what `Rind/<Arch>/KeccakDispatch.lean`'s do,
given FIPS 202's round constants and nothing of the CPU. Each round is
`keccak_round` written out, which `round_spec` proves by unfolding.

ML-KEM's polynomial arithmetic, against FIPS 203 as SymCrypt's Lean spec
(`Rind/SymCrypt/MlKem.lean`, MIT) states it, and of rind's Rust the coding
below it and, on aarch64, ML-KEM-768's K-PKE decryption; encryption, key
generation, and the Fujisaki-Okamoto transform that decapsulation needs have
[its quest](/quest/m4/verified/mlkem-construction.md):

- `NTT_get`, `NTTInv_get` (`Rind/MlKem.lean`): Algorithms 9 and 10 compute
  the residues FIPS 203's Equations (4.12) and (4.13) define, and back;
- `forwardNtt_eq`, `inverseNtt_eq`, `mulcache_eq`, `basemul3Even_eq`,
  `basemul3Odd_eq`, and `tomont3329_eq` (`Rind/S2nMlKem.lean`): the specs
  s2n-bignum's aarch64 ML-KEM routines' theorems state are FIPS 203's `NTT`,
  its `NTTInv` times 2^16, and its `MultiplyNTTs` times 2^-16;
- `avx2ForwardNtt_eq`, `avx2InverseNtt_eq`, `avx2Mulcache_eq`, and
  `pmulaccred0K3_eq` and its siblings: the same for the x86_64 routines, which
  keep FIPS 203's coefficients in the AVX2 order.

ML-KEM's decompression, message coding, and CBD sampling, on x86_64 and
aarch64, in `Rind/X86_64/MlKemCoding.lean`, which `admin/prove` also writes
for aarch64. They are the same Rust for ML-KEM-512, 768, and 1024, and rest
on no axiom:

- `decompress_spec`: `mid::mlkem::decompress::<D, L>` writes FIPS 203's
  `Decompress_D(ByteDecode_D(bytes))`, each coefficient in `[0, q)`, for
  every `D` from 1 to 11 and `L = 32 * D` bytes, so for the 4, 5, 10, and 11
  bits a ciphertext's halves take;
- `from_message_bits_spec`: K-PKE's message, as a polynomial, is
  `Decompress_1(ByteDecode_1(m))`;
- `to_message_bits_spec`: the message K-PKE decrypts is
  `ByteEncode_1(Compress_1(f))` of a polynomial `f`, given Rust coefficients
  each in `[0, q)` and equal to `f`'s modulo `q` (`Holds 0 3328`), so its
  caller must show the coefficients canonical, not only congruent: `-1`
  stands for the same element as 3328 but does not meet it;
- `sample_cbd2_spec`, `sample_cbd3_spec`: `mid::mlkem::sample_cbd2` and
  `sample_cbd3` write FIPS 203's `SamplePolyCBD_2` and `SamplePolyCBD_3` of
  their bytes, each coefficient in `[-η, η]` (`Holds (-η) η`). Each sums the
  bits of a field of its word at once with masked adds, which `cbd2_field`
  and `cbd3_field` show carry nothing from one field into the next, by
  arithmetic rather than `bv_decide`.

On aarch64, where s2n-bignum has no routine for it, rind runs
`low::generic::mlkem`'s Rust for 12-bit unpacking, which
`Rind/Aarch64/MlKemGeneric.lean` proves, on no axiom: `mlkem_frombytes`
writes each raw 12-bit field, in `[0, 4096)`, so each coefficient is
`ByteDecode_12`'s modulo `q` but not yet reduced (`Holds 0 4095`); the
`mlkem_reduce` after it makes it canonical.
Ciphertext compression there is mlkem-native's NEON assembly, which HOL Light
proves, and `admin/prove bytes` checks rind's build of it, and of x86_64's
AVX2 compression, against the code those proofs list, and the constant table
statics it configures against the proofs' tables; which table a wrapper passes
is not part of that check. x86_64's bridge to `Compress` is still the
construction quest's.

`Rind/Aarch64/MlKemRoutines.lean` restates the HOL Light theorems about the
routines aarch64's ML-KEM runs as one axiom per wrapper in
`low::aarch64::mlkem`: s2n-bignum's NTT, inverse NTT, mulcache, base
multiplication, reduction, Montgomery conversion, 12-bit packing, and
rejection sampling, and mlkem-native's compression to 4 and 10 bits, the
only widths ML-KEM-768 takes, as `mlkem_basemul_k3` is its only base
multiplication. The zeta tables the theorems assume are not trusted: `admin/prove`
writes s2n-bignum's from its HOL Light sources into `MlKemTables`, and the
kernel checks rind's against them. The rejection sampler's 4096-byte table,
too long a literal for Lean, is the exception: its wrapper stays opaque, and
`admin/prove` checks the table's text is s2n-bignum's. The specs after the
axioms state each routine in FIPS 203's terms, and
`Rind/Aarch64/MlKemPoly.lean` lifts them to `mid::mlkem`'s vectors: the NTT,
mulcache, inverse NTT, dot product, reduction, 12-bit coding, and
coefficient-wise sums and differences.

`kpke_decrypt_fips` (`Rind/Aarch64/MlKemPke.lean`): on aarch64,
`DecapKey::kpke_decrypt` is FIPS 203's `K-PKE.Decrypt` (Algorithm 15) for
ML-KEM-768, on those axioms. Aeneas does not translate a set's `Params` impl,
so the theorem takes it as a parameter, and `Is768` states what ML-KEM-768's
is: its constants, and its types' `FixedArray` impls those of arrays.

`Rind/MlKemCoding.lean` states what they need of the spec, with no Rust:
`ByteEncode_bit`, `ByteDecode_get`, and `SamplePolyCBD_get` give each bit or
coefficient of FIPS 203's `ByteEncode`, `ByteDecode`, and `SamplePolyCBD`,
which the spec writes as loops, and `Compress_val` and `Decompress_val` give
`Compress` and `Decompress`, which it writes as rounded rationals, as
quotients of naturals. K-PKE's decryption calls them; its encryption and key
generation, the Fujisaki-Okamoto transform, SampleNTT, and x86_64's
encodings are the quest's.

Ed25519 on x86_64 and aarch64, from the signature API's `ed25519::KeyPair`
and `ed25519::PublicKey` to s2n-bignum's routines and the SHA-512 proof above, in
`Rind/X86_64/Ed25519.lean`, which `admin/prove` also writes for aarch64, and
for x86_64's verification in `Rind/X86_64/Ed25519Verify.lean`. Both targets'
verification checks a multiple of RFC 8032's equation with half-size scalars;
aarch64's is [not proven yet](/quest/m4/verified/ed25519-half-scalar.md), so
the last two theorems below are x86_64's only. On
x86_64 these assume `NoCurveIfma`, that the CPU lacks AVX-512 IFMA:

- `ed25519_generate`: the key pair's seed is the 32 drawn bytes, and a failed
  draw is refused;
- `ed25519_from_seed_and_public_key`: a seed that is not 32 bytes is refused,
  so is a public key that is not the seed's, and otherwise the key pair's
  seed is the seed;
- `ed25519_sign`: the signature's bytes are RFC 8032's PureEd25519 signature
  of the message under the seed;
- `ed25519_key_pair_public_key`: the public key's bytes are RFC 8032's public
  key of the seed;
- `ed25519_public_key_new` (x86_64): a public key is refused unless it is 32
  bytes, refused if its low 255 bits are one of libsodium's seven small-order
  y-coordinates, refused unless it encodes a point of the group, and
  otherwise its `verify` accepts exactly the signatures `ed25519Verifies`
  accepts with that point: 64 bytes, S below L, and R the encoding of SB - kA,
  for k the hash reduced mod L, rind's cofactorless check;
- `ed25519_key_pair_verify` (x86_64): a key pair's public key verifies the
  same way, with its point the base point times its secret scalar.

The spec, in `Rind/Ed25519.lean`, is RFC 8032 over HOL Light's
`edwards25519_group`, whose multiplication and power transliterate HOL Light's
`edwards_add` and `group_pow`, with s2n-bignum's `ed25519_encode` and
`ed25519_decode` of its points. `Rind/Ed25519Group.lean` proves they are the
addition and multiples of the twisted Edwards group in `Rind/Edwards.lean`,
with no axiom. Each theorem
assumes `Runs` and `RunsSha512`, and each with a message bounds it at
2^64 - 64 bytes. The two that verify also assume `RunsMsm`, the contract of
the multi-scalar multiplication `low::x86_64::adx_mux::edwards25519_msm`,
which nothing proves yet (`quest/m4/verified/ed25519-half-scalar.md`), and
`EdOrders`, the group's orders, which HOL Light proves and Lean does not yet:
every point times 8L, and the base point times L, is the identity. From them
`Rind/Ed25519Group.lean`'s `half_size_iff` proves that the half-size check
accepts exactly what `ed25519Verifies` does, and `Rind/X86_64/HalfSize.lean`
proves that `mid::half_size::split` returns `u ≡ v k (mod 8L)` with `v` odd
and below 2^128. The `ed25519` module calls no function pointer, so these
theorems are about its translation, with no hand model.

Ed25519 on x86_64 CPUs with AVX-512 IFMA, from the same API to
pyca/verified-garbage's key-pair derivation, signing, and verification, in
`Rind/X86_64/Ed25519Ifma.lean`, stated in VG's RFC 8032 spec,
`VerifiedGarbage.Spec.Ed25519`, over bytes as VG takes them, `bvs`. Each
assumes `CurveIfma (some t)`, that the IFMA check returns a token:

- `ed25519_generate_ifma`: the key pair's seed is the 32 drawn bytes, and a
  failed draw is refused;
- `ed25519_from_seed_and_public_key_ifma`: a seed that is not 32 bytes is
  refused, so is a public key that is not VG's `publicKey` of the seed, and
  otherwise the key pair's seed is the seed;
- `ed25519_sign_ifma`: the signature's bytes are VG's `sign` of the message
  under the seed;
- `ed25519_key_pair_public_key_ifma`: the public key's bytes are VG's
  `publicKey` of the seed;
- `ed25519_public_key_new_ifma`: a public key is refused unless it is 32
  bytes, refused if its low 255 bits are one of libsodium's seven small-order
  y-coordinates, refused unless it encodes a point of the group, and
  otherwise its `verify` accepts exactly the signatures VG's `verify` accepts
  with those bytes;
- `ed25519_key_pair_verify_ifma`: a key pair's public key verifies the same
  way.

Each rests on the axiom of the VG routine it calls, in
`Rind/X86_64/VgCurve25519.lean`, and proves rind's glue: that a key pair
keeps the digest and public key VG's key-pair derivation wrote, so signing's
precondition, that they are some seed's, holds, and key loading's checks,
which run rind's s2n-bignum decoding on every CPU. Each with a key pair
assumes it came from those two constructors (`VgKeyPairOf`); the
constructors and `ed25519_public_key_new_ifma` assume `Runs`, and
`ed25519_public_key_new_ifma` also that the entry guard holds, which
the theorems above take from `RunsSha512`. Unlike HOL Light's, VG's spec
takes messages of any length.

AES-128, AES-192, and AES-256 on x86_64 CPUs with AES-NI and aarch64 CPUs
with the crypto extension, from `cipher::Aes` and the header-protection API's
`HeaderProtectionKey` to rind's key expansion and block cipher on the AES
instructions, in `Rind/X86_64/AesCipher.lean`, over each target's
`Rind/<Arch>/AesKey.lean`:

- `aes_new`: a `cipher::Aes` key that is not the algorithm's length is
  refused, and otherwise the key holds FIPS 197's round keys for its bytes,
  as Vale's `key_to_round_keys_LE` lays them out;
- `aes_encrypt_block`: the block becomes Vale's `aes_encrypt_LE` of it under
  the key;
- `aes_header_new`: the same for `aead::quic::AES_128` and `AES_256`, whose
  keys reach `Aes::new` through the dispatch `Rind/X86_64/QuicDispatch.lean`
  models;
- `aes_header_mask`: the mask is RFC 9001's, the first five bytes of that
  cipher of the sample.

Each `AesKey.lean` also proves the decryption key `AesDecKey`, which AES-KW
unwraps with, against FIPS 197's equivalent inverse cipher, which
`Rind/AesInverse.lean` transliterates since Vale's spec only encrypts:

- `dec_key_new_spec`: a key of the algorithm's length holds `KeyExpansionEIC`'s
  round keys, reversed, which `invert_round_keys` computes from the cipher's;
- `hw_decrypt_block_spec`: the block becomes `EqInvCipher` of it under them.

`aesBlock`, `aesHeaderMask`, and `aesBlockDecrypt` are those specs on bytes,
which `#guard`s check against FIPS 197's and RFC 9001's vectors. The theorems
assume `RunsAesHw`, or for a key already made only its entry guard: rind's
CPU-feature checks find AES-NI, or on aarch64 the crypto extension, which no
input affects.

AES-CTR and AES-CBC on aarch64 CPUs with the crypto extension, from
`cipher::AesCtr`, `AesCbcEncryptingKey`, and `AesCbcDecryptingKey` down to
rind's NEON CTR by 8 and CBC on the AES instructions, in
`Rind/Aarch64/AesModesApi.lean` over `Rind/Aarch64/AesModesLow.lean`, against
`Rind/AesModes.lean`'s SP 800-38A modes:

- `aes_ctr_new_spec`: a key that is not the algorithm's length, or a counter
  of no bits or more than 128, is refused, and otherwise the key holds the
  round keys of its bytes and counts over that many low bits;
- `aes_ctr_apply_keystream_spec`: a buffer with more blocks than the
  counter's bits can count is refused unchanged, and otherwise becomes
  SP 800-38A's CTR mode of it from the counter block, incrementing its low
  bits;
- `aes_cbc_encrypting_key_new_spec` and `aes_cbc_decrypting_key_new_spec`:
  the same refusal, and otherwise the cipher's or the inverse cipher's round
  keys;
- `aes_cbc_encrypt_blocks_spec` and `aes_cbc_decrypt_blocks_spec`: a buffer
  that is not whole blocks is refused, and otherwise becomes SP 800-38A's CBC
  encryption or decryption of it;
- `aes_cbc_encrypt_vec_spec`: a `Vec` message always succeeds and becomes
  the CBC encryption of its PKCS#7 padding;
- `aes_cbc_decrypting_key_decrypt_spec`: whole blocks decrypt, and the message
  is returned if the PKCS#7 padding is good; otherwise decryption fails with
  the buffer zeroed, and a buffer of no or partial blocks fails unchanged.

On x86_64, `Rind/X86_64/AesModesApi.lean` proves the same over
`Rind/X86_64/AesModesLow.lean`, whose axioms `hw_ctr32_spec`,
`hw_cbc_encrypt_spec`, and `hw_cbc_decrypt_spec` restate HOL Light theorems
of aws-lc's `aes_hw_ctr32_encrypt_blocks` and `aes_hw_cbc_encrypt` that are
pending: `hol-light/x86_64/aes_hw_cbc_encrypt.ml` proves CBC encryption and
most of decryption, and CTR has no proof yet. Until they are, those theorems are not in
`Rind/X86_64/Axioms.lean` and earn no ✓, which [the AES modes
quest](/quest/m4/verified/aes-modes.md) owns.

AES key wrap on both targets, from `key_wrap::AesKek` to the block cipher and
its inverse, in `Rind/<Arch>/AesKw.lean`, against `Rind/AesKw.lean`'s SP 800-38F
transliteration, whose `#guard`s check RFC 3394's and RFC 5649's vectors:

- `kek_new_spec`: a key that is not the algorithm's length is refused, and
  otherwise the KEK holds it;
- `kek_wrap_spec` and `kek_unwrap_spec`: KW-AE and KW-AD. A wrap refuses keys
  under two semiblocks, not whole semiblocks, or an output of the wrong
  length; an unwrap refuses input under three semiblocks or not whole
  semiblocks with `DecryptFailed`, and a key buffer of the wrong length with
  `WrongLength`, both leaving the buffer as it was, and returns
  `DecryptFailed` with the buffer zeroed when KW-AD's integrity check fails;
- `kek_wrap_padded_spec` and `kek_unwrap_padded_spec`: KWP-AE and KWP-AD. A
  wrap takes any key of 1 to 2^32 - 1 bytes, aligned or not, into an output of
  the key padded to whole semiblocks plus one, and refuses anything else; an
  unwrap refuses as KW's does from two semiblocks of input, and zeroes the
  buffer when KWP-AD's integrity check fails;
- `kek_wrap_key_spec` and `kek_unwrap_key_spec`: the public `wrap_key` and
  `unwrap_key` run KW's for `Mode::Kw` and KWP's for `Mode::Kwp`, as the
  four above state, and `unwrap_key` returns the unwrapped key.

The unwraps' integrity check rests on the constant-time compares'
`Rind/<Arch>/CtEqual.lean` contracts; the rest rests on nothing.

AES-128-GCM, AES-192-GCM, and AES-256-GCM on x86_64 CPUs with AES-NI and
PCLMULQDQ, from the AEAD API's `Key` down to HACL*'s Vale AES-GCM routines on
CPUs with AVX and MOVBE but no VAES, and to rind's own by-8 AES-CTR and GHASH
on CPUs without AVX and for what Vale's routines do not take, in
`Rind/X86_64/AesGcmAead.lean`:

- `aes_gcm_new`: a key that is not the algorithm's length is refused, and
  otherwise the key holds FIPS 197's round keys for its bytes, as Vale's
  `key_to_round_keys_LE` lays them out, and the GHASH key powers Vale's
  `hkeys_reqs_pub` requires of `E_K(0)`, or by-8's table of its first eight
  powers;
- `aes_gcm_seal`: for AAD under 2^61 bytes and messages up to 2^36 - 32
  bytes, the lengths rind takes, the ciphertext in place and the tag are
  Vale's `gcm_encrypt_LE` of the key, nonce, message, and AAD;
- `aes_gcm_seal_append_tag`: the same for a seal that appends the tag to any
  buffer: the ciphertext lands in the view its `as_mut` gives, and the call
  returns what its `extend` makes of that, handed the tag; and
  `aes_gcm_seal_append_tag_vec`: a `Vec<u8>` with room for the tag becomes
  the ciphertext followed by the tag, through `Rind/Core.lean`'s models of
  std's impls, which view the whole vector and append the tag as
  `extend_from_slice` does;
- `aes_gcm_open_separate_tag` and `aes_gcm_open`: for the same lengths, the
  call succeeds exactly when Vale's `gcm_decrypt_LE` accepts the tag, leaving
  its plaintext in place, and otherwise fails, leaving zeros.

Vale's `gcm_encrypt_LE` and `gcm_decrypt_LE` bound the AAD and message under
2^32 bytes, so `Rind/Vale.lean` transliterates them without it. Vale's
routines run seals of 129 bytes and more and AAD and messages under 2^32
bytes (`aes_gcm_encrypt_vale`, `aes_gcm_decrypt_vale` in
`Rind/X86_64/AesGcm.lean`), and by-8 the rest. `Rind/X86_64/AesGcmBy8.lean`
proves by-8, as `Rind/X86_64/AesGcmModel.lean` models it by hand, is Vale's `gctr_encrypt_LE` and `ghash_LE` without their bound:
its counter is the block's 64-bit halves swapped, which `PADDD` steps as
`inc32` does, its rounds FIPS 197's, and its GHASH the Horner rule on the
padded blocks, with the eight-block loop's sum of descending powers of the
key `Rind/X86_64/GhashClmul.lean` proves equal to it.
`Rind/X86_64/AesGcmClmul.lean` proves `tagged` is `gcm_encrypt_LE` and
`gcm_decrypt_LE` for a 96-bit nonce: the counter block is
`compute_iv_BE`'s, the length block `gcm_hash`'s, and the tag GCTR on the
hash under it, which by-8's `open` compares through `ct_equal`, so the opens
rest on `Rind/X86_64/CtEqual.lean`'s contracts too. AES-192 keys run by-8 on
both tiers, since Vale's routines take only AES-128 and AES-256
(`vale_192_none`). The key
setup is rind's: its AES-NI key expansion and block cipher, which
`Rind/X86_64/AesKey.lean` proves for AES header protection too, and its
PCLMULQDQ GHASH key powers, whose Karatsuba product and reduction
`Rind/Gf128.lean` proves to be Vale's `gf128_mul_rev` of the shifted keys
(`mul_shiftKey1`). Around Vale's routines, the Rust zero-pads the partial
blocks and picks the six-block loop's share, as EverCrypt's proven Low*
wrapper does. It pads them with GHASH's `load_partial` and `store_partial`,
whose overlapping loads and stores `Rind/X86_64/PartialBlock.lean` proves are
the bytes at every length. The theorems assume `RunsAesGcm`: rind's
CPU-feature checks pick Vale's tier (`RunsValeAesGcm`) or the SSE tier
(`RunsClmulAesGcm`), and the opens that `ct_equal`'s entry guard passes.
`Rind/X86_64/AeadDispatch.lean` models the AEAD API's function pointers
(`Algorithm`'s `expand` and `Sealer`'s `Ops`), and `seal_in_place_append_tag`,
which is generic over its buffer.

On aarch64, AES-GCM is proven below the AEAD API on CPUs with the crypto
extension: for short messages with every key size, and at every length below
2^61 bytes with AES-128 and AES-256 keys; its GHASH key setup and hashing are proven at every
length. `Rind/Aarch64/GhashPmull.lean` proves
that `GhashTable::new` builds the PMULL table of H to H^8, each shifted as
Vale's `shift_key_1` does (`ghash_table_new_spec`), and that `Ghash::add` on
it is the Horner rule on the padded blocks, Vale's `ghash_LE`
(`ghash_add_spec`): its `mul!` is the x86 Karatsuba step with the key's
halves stored swapped, its `reduce!` the same reduction, and its eight-block
loop the same sum of descending powers, the target-independent lemmas shared
in `Rind/GhashSpec.lean`. `Rind/Aarch64/AesGcmModel.lean` models by hand
what Aeneas cannot translate, the NEON transmutes, `Ghash::add`'s slice
chunking, and the one-pass short path with its `Aggregate`, quoting the
Rust. `Rind/Aarch64/AesGcmShort.lean` proves that `short` is Vale's
`gctr_encrypt_LE` from the block after the counter block, and its tag GCTR
from the counter block on `gcm_hash` of the AAD and the ciphertext
(`short_spec`): its counter blocks are `inc32` of the counter block, its
rounds FIPS 197's, `load` and `store` move a partial block's bytes, `KEEP`
masks the keystream past a short ciphertext chunk before it is hashed, and
`Aggregate` is the Horner rule, each group of up to eight blocks multiplied by
descending powers of H and reduced once. `Rind/Aarch64/AesGcm.lean` proves
that the counter block of a 96-bit nonce and of any other IV under 2^61 bytes is
`compute_iv_BE`'s (`counter_block_eq`, `initial_counter_spec`), and that
`tagged_from`, when the AAD's and the message's blocks, each rounded up,
number at most the 15 sealing or 31 opening that `short` takes, is GCTR and
the tag on `gcm_hash` from the counter block it is given
(`tagged_from_short_spec`), so `tagged` with a 96-bit nonce is
`gcm_encrypt_LE` and `gcm_decrypt_LE` (`tagged_seal_short_spec`,
`tagged_open_short_spec`). The lemmas both targets' AES-GCM proofs use are in
`Rind/GcmSpec.lean`. Longer messages run `cipher`, which hands the whole
blocks to one of s2n-bignum's eight stitched AES-GCM kernels, for AES-128 or
AES-256, sealing or opening, on cores with or without SHA3, whose theorems
`Rind/Aarch64/S2nBignum.lean` restates over `Rind/S2nGcm.lean`'s
transliteration of their HOL Light specs. `Rind/S2nGcm.lean` proves those
specs are Vale's: FIPS 197's rounds as s2n-bignum writes them are
`eval_cipher` (`aes128Cipher_eq`, `aes256Cipher_eq`), each counter block's
keystream is `gctr_encrypt_block`'s (`aesCtrBlock_eq`), the bit-reflected
GHASH is `ghash_LE` (`toPoly_nistGhash`), and the POLYVAL table the kernels
read is the PMULL table's (`toPoly_hPower`). `Rind/Aarch64/AesGcmLong.lean`
proves that `stitched` is GCTR and GHASH over the blocks (`stitched_spec`),
that `partial` is `short`'s last chunk (`partial_spec`), so `cipher` is GCTR
from the block after the counter block and GHASH over the AAD and the
ciphertext (`cipher_spec`), and `tagged_from` and `tagged` at every length
below 2^61 bytes are GCTR and the tag on `gcm_hash` (`tagged_from_spec`) and `gcm_encrypt_LE` and
`gcm_decrypt_LE` (`tagged_seal_spec`, `tagged_open_spec`). With a table for
the cores with SHA3, each takes `KernelBuffersLow`, which names the `_alt`
kernels' requirement that the blocks' address plus their length is below
2^63, as a hypothesis: untagged user-space addresses meet it, and a pointer
tag that sets bit 63 breaks it. AES-192 past the
short path, which runs aws-lc's stitched kernels, eight-way on cores with SHA3
and four-way otherwise, and the AEAD API above `tagged` remain to prove.

`aead::gcm::Key`, which takes an IV of any length and tags of any
`TagLength`, is proven on the same tiers, in `Rind/X86_64/GcmKey.lean`, a
hand model over `AeadDispatch` that quotes `rind/src/aead/gcm.rs`. Its `new`
for AES-128, AES-192, or AES-256 holds the `aead::Key` for the algorithm,
which refuses a key of another length (`gcm_key_new`). For an IV of 1 to
2^61 - 1 bytes and the same AAD and message lengths, its
`seal_in_place_separate_tag` leaves AES-GCM's ciphertext and returns the
first `tag_len` bytes of its tag (`gcm_key_seal`), and
`seal_in_place_append_tag` returns what its `extend` makes of that, handed
the tag (`gcm_key_seal_append_tag`), and `open_in_place` and
`open_in_place_separate_tag` succeed exactly when the tag is those bytes,
leaving the plaintext, and otherwise fail (`gcm_key_open`,
`gcm_key_open_separate_tag`). Only an authentication failure clears the
ciphertext to zeros; a refusal, of an input shorter than the tag or a
separate tag that is not the key's length, leaves the buffer unchanged. SP 800-38D's MSB_t truncation is the first bytes of Vale's tag, which
`gcmDecryptTrunc` compares. A seal under a 12-byte IV runs `aead::Key`'s path
and truncates its tag, and an open runs that path only under a 12-byte IV
with a 16-byte tag; the model's other arms run `AesGcm::encrypt_any` and `decrypt_any`, which
`Rind/X86_64/AesGcmAny.lean` proves: `initial_counter` is `compute_iv_BE`: the
96-bit counter block for a 12-byte IV, and otherwise the GHASH branch,
through by-8's table and the IV's length block, and the
tag's prefix is compared through `ct_equal`. They refuse an empty IV, one of
2^61 bytes or more, and AAD and messages past GCM's bounds with
`WrongLength`, leaving the buffer as it was (`check_gcm_iv_spec`,
`check_gcm_lengths_eq`), but those refusals are stated only for
`encrypt_any` and `decrypt_any`: the 96-bit path's theorems, and the
`gcm::Key` theorems above both, still take the AAD and message bounds as
hypotheses.
The AVX-512 tier's messages below 2 KB, which run rind's by-16 AES-CTR and
GHASH from 256 bytes and by-8 below that, are proven in
`Rind/X86_64/AesGcmAvx512.lean`, over `Rind/X86_64/AesGcmModel.lean`'s hand
model of `_cipher_avx512`, `Counter512`, `GhashTableAvx512::add`, `_mul16`,
and `_mul_tail`:

- `cipher_avx512_spec`: `_cipher_avx512` is Vale's `gctr_encrypt_LE` of the
  message from the counter after J0, and folds the padded AAD and ciphertext
  into the hash by the Horner rule, as by-8 does. Each lane of its 512-bit
  counters, round keys, and blocks runs by-8's 128-bit steps, and its last
  chunk of up to 255 bytes runs masked 64-byte loads and stores and
  `_mul_tail`'s sum of descending key powers;
- `avx512_add_spec` (`Rind/X86_64/GhashAvx512.lean`):
  `GhashTableAvx512::add` is the same Horner rule, 16 blocks a step;
- `cipher_avx512_tier`: `cipher` on the tier, below 2 KB, is the same, by-16
  from 256 bytes and by-8 below (`by8_spec_of`, by-8 over any table whose
  `Ghash::add` is the Horner rule, `GhashOf`);
- `tagged_from_avx512_spec`: `tagged_from` on the tier, below 2 KB, is
  `tagged_from_spec`'s ciphertext and tag.

They take the tier's key powers as hypotheses: `Avx512Powers`, that
`VaesKernel::powers` gives the key's first 16 powers, and `TableFor` of the
PCLMULQDQ table `from_powers` builds from them. BoringSSL's
`gcm_init_vpclmulqdq_avx512` sets both up, and
[the VAES quest](/quest/m4/verified/aes-gcm-x86-vaes.md) proves it, the
kernels the tier runs from 2 KB, and the tier's seals and opens. Toward it,
`Rind/S2nGcmAe.lean` proves s2n-bignum's SP 800-38D, `common/gcm.ml`, Vale's:
GCTR from any counter block is `gctr_encrypt_LE`'s blocks (`gctr_eq`), and
`gcm_ae` and `gcm_ad` with a 96-bit IV and whole blocks are `gcm_encrypt_LE`
and `gcm_decrypt_LE` (`gcmAe_eq`, `gcmAd_eq`) for any cipher that is Vale's
AES under the key, as FIPS 197's AES-128 and AES-256 are under s2n-bignum's
key schedules, which are `key_to_round_keys_LE` (`aes128KeyExpansion_eq`,
`aes256KeyExpansion_eq`).

ChaCha20-Poly1305 and XChaCha20-Poly1305, from the AEAD API's `Key` and
`RandomizedNonceKey` down to the call of the target's one pass,
`low::<arch>::chacha20poly1305`'s `seal` and `open`, in
`Rind/X86_64/ChaCha20Poly1305Api.lean`, which `admin/prove` copies to
aarch64:

- `chacha20_poly1305_new`: a key that is not 32 bytes is refused, and
  otherwise the key holds its bytes;
- `chacha20_poly1305_seal`, `chacha20_poly1305_seal_append_tag`, and
  `chacha20_poly1305_seal_append_tag_vec`: a message past 2^38 - 64 bytes, as
  many as the 32-bit block counter covers from block 1, is refused and left as
  it is, and otherwise the ciphertext and the tag are RFC 8439 section 2.8's;
- `chacha20_poly1305_open_separate_tag` and `chacha20_poly1305_open`: past
  2^38 - 64 bytes the same refusal, and otherwise the call succeeds exactly
  when RFC 8439's tag is the one given, leaving the plaintext in place, and
  otherwise fails, leaving zeros;
- `randomized_nonce_key_new`, `randomized_nonce_key_seal_append_tag_vec`,
  and `randomized_nonce_key_open`: the same for draft-irtf-cfrg-xchacha-03's
  XChaCha20-Poly1305, under the nonce the system's random source fills, whose
  failure the seal returns as `RngFailed`.

HChaCha20, which derives XChaCha20's subkey, runs HACL*'s rounds, which
`hchacha20_spec` proves. 32-bit portable HChaCha20 is the rolled loop in
`low/generic/chacha20.rs`, which this proof does not cover; the output loop
stays inside the unrolled `hchacha20` so Aeneas still extracts
`hchacha20_loop`. The theorems assume `Seals` or `Opens` of the message's
length: that the one pass seals or opens a message that long as RFC 8439
does. Each target's `ChaCha20Poly1305.lean` proves those where a proof covers
the one pass.

On x86_64, `Rind/X86_64/ChaCha20Poly1305.lean`'s `seals` and `opens` prove
them at every length, assuming `RunsChaCha20Poly1305`: rind's CPU-feature
checks find what VG's IFMA routines need, or find SSE4.1 but not that and
`OnePass` holds, that aws-lc's one-pass routines compute RFC 8439's AEAD,
which no proof covers yet;
[the ChaCha20-Poly1305 quest](/quest/m4/verified/chacha20-poly1305-x86/aead.md)
owns their HOL Light proofs, against the s2n-bignum fork's `common/chacha20poly1305.ml`,
which `Rind/S2nChaCha20Poly1305.lean` proves is `Rind/Spec.lean`'s RFC 8439
for a 32-byte key and a 12-byte nonce. On CPUs with IFMA they rest instead on
the axioms `vg_chacha20_poly1305_seal_ifma_spec` and
`vg_chacha20_poly1305_open_ifma_spec` in `Rind/X86_64/VgChaCha20Poly1305.lean`,
which restate VG's theorems and from which `seal_ifma_spec` and
`open_ifma_spec` prove the one pass computes RFC 8439's AEAD at every
length, so the theorems earn the ✓ there. VG's open leaves zeros where the
tag is wrong and aws-lc's the plaintext; the `mid` glue zeroes it either way.
CPUs that fail the check and lack SSE4.1 run the separate ChaCha20 and
Poly1305 passes, which no theorem here covers. `AeadDispatch` models
`RandomizedNonceKey`, which reaches the system's random source, and
`Rind/ChaCha20Poly1305Test.lean` checks `Rind/Spec.lean`'s transliterations
against RFC 8439's and draft-irtf-cfrg-xchacha-03's test vectors.

ChaCha20-Poly1305's one pass on aarch64, from
`low::aarch64::chacha20poly1305`'s `seal` and `open` down to
pyca/verified-garbage's SVE2 routines, on CPUs with SVE2, and its NEON
routines, on CPUs without it at the lengths `seal_runs_vg` and
`open_runs_vg` name (`SealsNeon`: 577 to 768 bytes and from 897;
`OpensNeon`: 129 to 256, 449 to 895, and from 961), in
`Rind/Aarch64/VgChaCha20Poly1305.lean`:

- `chacha20_poly1305_seal_sve2_spec` and `chacha20_poly1305_seal_neon_spec`:
  the data becomes RFC 8439 section 2.8's ciphertext, and the tag is its tag
  over the AAD and it;
- `chacha20_poly1305_open_sve2_spec` and `chacha20_poly1305_open_neon_spec`:
  the result is whether RFC 8439's tag over the AAD and the ciphertext is the
  one given, leaving the plaintext in place if it is and zeros if not.

They rest on the axioms `vg_chacha20_poly1305_seal_sve2_spec`,
`vg_chacha20_poly1305_open_sve2_spec`, `vg_chacha20_poly1305_seal_neon_spec`,
and `vg_chacha20_poly1305_open_neon_spec`, which restate VG's theorems, and
assume the CPU-feature check finds SVE2, or finds none, as the routine needs.
No length bound is needed: VG's spec and `Rind/Spec.lean`'s both wrap the
32-bit block counter, which the AEAD API stops short of.
`Rind/Aarch64/ChaCha20Poly1305.lean` carries them to the AEAD API:

- `seals_sve2` and `opens_sve2`: `Seals` and `Opens` at every length where
  the SVE2 check finds SVE2;
- `seals_neon` and `opens_neon`: `Seals` at `SealsNeon`'s lengths and
  `Opens` at `OpensNeon`'s where it finds none.

Each assumes `RunsChaCha20Poly1305`: the entry guard admits the call and the
SVE2 check returns. CPUs without SVE2 run aws-lc's `chacha20_poly1305_armv8`
at the other lengths, which no proof covers yet, so `seals` and `opens`,
which cover every length, assume its contract, `AwsLc`, there;
[the aarch64 aws-lc ChaCha20-Poly1305 quest](/quest/m4/verified/chacha20-poly1305-aarch64/aead.md)
owns that proof.

ChaCha20 on x86_64, at every length, from `cipher::ChaCha20` down to
pyca/verified-garbage's AVX2 and AVX-512 VL routines, rind's two-block AVX2
kernel, aws-lc's SSSE3 routine, and HACL*'s rounds, in
`Rind/X86_64/ChaCha20Cipher.lean`:

- `chacha20_apply_keystream`, on any CPU (where `new` picks no VG routine and
  finds SSSE3 it assumes `LinuxBuild`, rind's `x86_64-unknown-linux-gnu` build; an x86_64 Mac's
  SSSE3 routine is Apple's copy, which no proof covers): a buffer that needs more blocks
  than remain before the 32-bit block counter wraps is refused with
  `WrongLength` and left as it is, and otherwise it becomes RFC 8439's
  encryption of it under the key, the block counter, and the nonce.

It rests on the axioms `vg_chacha20_init_spec`,
`vg_chacha20_apply_avx2_spec`, and `vg_chacha20_apply_avx512vl_spec` in
`Rind/X86_64/VgChaCha20.lean`, which restate VG's theorems, and
`chacha20_ctr32_ssse3_4x_spec`, which restates rind's HOL Light proof of
aws-lc's SSSE3 routine, `CHACHA20_CTR32_SSSE3_4X_SUBROUTINE_CORRECT` in
`hol-light/x86_64/chacha20_ctr32_ssse3_4x.ml`, and composes them
as `cipher` does: VG's routines from 256 bytes over the whole buffer, or,
when what follows its last whole 512-byte group is 65 to 255 bytes, over the
groups, and the kernel over that remainder from the block counter past them;
the kernel alone from 65 bytes; and HACL*'s rounds, in rind's loop,
below. `Rind/X86_64/ChaCha20Avx2.lean` proves the kernel, `kernel`, over
`Rind/X86_64/Simd.lean`'s models of the AVX2 intrinsics it calls, which
`admin/prove` tests against the CPU: each double round is RFC 8439's inner
block on both blocks' states at once, and the stored and XORed keystream is
the two blocks'. Where `new` picked no VG routine but found SSSE3 (a CPU
without AVX2, or with AVX2 but not the BMI2 VG needs), `cipher` runs aws-lc's
`ChaCha20_ctr32_ssse3_4x` from 129 bytes, in place, whose HOL Light proof
steps its setup, the four blocks' rounds, each 256-byte group's XOR, and the
tail of fewer than 256 bytes, by induction over the groups.
`chacha20_apply_keystream` assumes `RunsCipher`: the entry guard admits the
call, constructing the VG state succeeds (the model leaves `VgState::uninit`
opaque), the CPU-feature checks return, whatever they find, and, where `new`
picks no VG routine and finds SSSE3, so that `cipher` can run the SSSE3 routine,
rind's build assembled the `x86_64-unknown-linux-gnu` object the HOL Light proof covers
(`LinuxBuild`, which no axiom states). A CPU where either VG feature check returns a token needs no such
premise.

ChaCha20 on aarch64, from `cipher::ChaCha20` down to pyca/verified-garbage's
NEON and SVE2 routines, in `Rind/Aarch64/VgChaCha20.lean`:

- `chacha20_apply_keystream_vg`, on the requests VG's routines run, from 128
  bytes where the SVE2 check finds SVE2, and otherwise from 192 to 256 bytes
  and from 448 (`RunsVgAt`), and `chacha20_apply_keystream`, at every
  length: a buffer that needs more blocks than remain before the 32-bit block
  counter wraps is refused with `WrongLength` and left as it is, and
  otherwise it becomes RFC 8439's encryption of it under the key, the block
  counter, and the nonce.

They rest on the axioms `vg_chacha20_init_spec`,
`vg_chacha20_apply_neon_spec`, and `vg_chacha20_apply_sve2_spec`, which
restate VG's theorems, and compose them as `cipher` does: VG runs the whole
request, so no tail resumes on rind's code. Both assume the entry guard
admits the call, constructing the VG state succeeds, and the SVE2 check
returns. rind's NEON code runs every other request, which no proof covers
yet, so `chacha20_apply_keystream` also assumes its contract, `Neon`;
[the aarch64 NEON ChaCha20 quest](/quest/m4/verified/chacha20-poly1305-aarch64/cipher.md)
owns that proof.

RSASSA-PKCS1-v1_5 and RSASSA-PSS verification with SHA-256 on x86_64, from
the signature API's `rsa::PublicKey` to the Montgomery products, in
`Rind/X86_64/RsaDispatch.lean`, against RFC 8017 as `Rind/Rsa.lean`
transliterates it:

- `rsa_signature_new_spec`, `rsa_signature_from_spki_spec`: a key
  `PublicKey::new` or `PublicKey::from_spki` returns has a modulus N of 1017
  to 8192 bits and an exponent E;
- `rsa_signature_from_components_spec`: the same for a key
  `PublicKey::from_components` returns, with N and E its components read
  big-endian;
- `rsa_pkcs1_sha256_verify_spec`, `rsa_pss_sha256_verify_spec`: such a key's
  `verify` with `verify::PKCS1_SHA256` or `verify::PSS_SHA256` refuses the
  key if N is under 2048 bits, and otherwise accepts exactly the signatures
  RSASSA-PKCS1-V1_5-VERIFY accepts under (N, E) with SHA-256's
  `DigestInfo`, or RSASSA-PSS-VERIFY with MGF1-SHA-256 and a 32-byte salt;
- `rsa2048_mont_products`: on a CPU with BMI2 and ADX, a 2048-bit modulus's
  Montgomery products, s2n-bignum's Karatsuba routines and Montgomery
  reduction, return their results.

Below the API, `Rind/X86_64/RsaKey.lean` proves key loading
(`from_components_spec`): components with no leading zero byte, an odd
modulus of 1017 to 8192 bits, and an odd exponent from 3 to below 2^33 load,
and a loaded key holds them, with an odd modulus of 1017 to 8192 bits, an
odd exponent of at least 3, R^2 mod N, and `mont_neg_inverse`'s
-N^-1 mod 2^64. R^2 mod N is `pub_montifier`'s, or, for a modulus of a
multiple of four words whose top bit is set on a CPU with BMI2 and ADX,
pyca/verified-garbage's `vg_rsa_public_precompute_adx`'s, through the axiom
`Rind/X86_64/VgRsa.lean` restates from that project's Lean proof.
`Rind/X86_64/RsaPublic.lean` proves the public operation's square-and-multiply,
`Rind/X86_64/RsaIfma.lean` the public operation (`public_op_spec`), which
runs pyca/verified-garbage's AVX-512 IFMA routine for the exponent 65537 and
2048-, 3072-, and 4096-bit moduli on a CPU with it, through the axiom
`Rind/X86_64/VgRsa.lean` restates from that project's Lean proof,
`Rind/X86_64/RsaBytes.lean` the conversions between
bytes and words, and `Rind/X86_64/{RsaVerify,RsaPss}.lean`
EMSA-PKCS1-v1_5's encoding check and EMSA-PSS-VERIFY. DER is opaque, as the ✓
leaves it out, so the `new` and `from_spki` theorems hold for every key
those return without saying which encodings they accept. The loaders assume
that the entry guard holds and `Runs`, and each `verify`
theorem `Runs`, `Sha256Blocks`, messages of at most `maxInput` bytes, and
`MontProducts k`, that `low::x86_64::mont`'s products
return their results at the modulus's width of k words, and
`IfmaCheckReturns`, that the CPU check for AVX-512 IFMA returns.
`Rind/X86_64/RsaMont.lean`'s `mont_products` proves it at 16 and 32 words
with BMI2 and ADX, from s2n-bignum's theorems; on any CPU at a width that is
under eight words or not a multiple of four, from `nohw_spec`, which restates
rind's HOL Light proof of `bn_mul_mont_nohw` below, of the Linux build's
object, so not of the macOS one ([its quest](/quest/m4/verified/apple-bytes.md));
and from `AwsLcMont`, that
aws-lc's unproven `bn_mulx4x_mont` and `bn_sqr8x_mont` return theirs, at every
other width and CPU. Its products through `bn_mul4x_mont`, without BMI2 and
ADX, follow from `mul4x_spec`, which restates `Mul4xProof.lean`'s theorem
above, but `mont_products` still takes `AwsLcMont` at those widths, since it
does not name the CPU.
`PublicKey::verify` reaches each algorithm's verification through a function
pointer, and every loader encodes the key through `Buffer::write`, which
`Rind/X86_64/RsaDispatch.lean` models for these two algorithms. On aarch64 the products are aws-lc's, so these proofs are not
copied there yet.

RSA's private operation on x86_64, in `Rind/X86_64/RsaPrivate.lean`:
`private_op_spec` proves that `RsaPrivateKey::private_op` refuses with
`WrongLength` a c not below N, and otherwise returns RSASP1 of c in its CRT
form, `rsasp1Crt` in `Rind/Rsa.lean`, which raised to E modulo N is c, or
refuses with `Fault` where it is not. It holds for a key meeting `PrivKeyInv`,
the values `RsaPrivateKey::new` computes, which no proof yet shows it does,
with primes of 16 or 32 words, on a CPU with BMI2 and ADX, where
pyca/verified-garbage's IFMA CRT does not run (`ifma.w = 0`) and neither does
aws-lc's dual RSAZ (`NoRsazPair`), given `MontProducts` at the primes' and the
modulus's widths. `private_op_rsa2048_spec` discharges the products, by
s2n-bignum's Karatsuba routines at 16 and 32 words, and the dual RSAZ for
RSA-2048; RSA-4096's 64-word modulus still needs `AwsLcMont` for its fault
check's products. `Rind/X86_64/RsaExp.lean` proves
`mont_exp`'s fixed-window exponentiation on that path, and
`Rind/X86_64/RsaGather.lean` its table gather on both paths `HaveAvx2::check`
picks, over `Rind/X86_64/GatherModel.lean`'s hand model of the AVX2 one.

`admin/prove` fails if a hand model's quote no longer matches the source, if
the source names `Ops`, builds a `Masker`, or writes its `mask` outside the
dispatch models' quotes, if it builds a digest `Algorithm` outside
`DigestAlgorithm.lean`'s, or if `signature/ecdsa.rs` mentions `Key::` or
`EcdsaKey::`, clones a `Key`, builds a `VerifyOps`, `EcdsaOps`, or
`EcdsaPair`, or reads an `ops` outside `EcdsaDispatch.lean`'s. RSA's two
statics are built wholly by quoted code.

## The portable backend

`admin/prove` translates the portable backend too, under `--cfg
rind_portable`, the cfg CI's portable jobs build with, on x86_64, into
`Rind/Portable/`: the hash, HMAC, KDF, and header-protection paths, down to
the SHA-2 block functions, and the Keccak-f above, alone. None of that Rust picks by pointer width or CPU, and Aeneas's `usize` is either
width, so the theorems hold on every target the backend builds for, but
for two bodies the extraction leaves out: ESP-IDF Xtensa's SHA-256,
`low/portable/sha256_iram.rs`, and 32-bit microcontrollers' SHA-512,
`low::generic::sha512_rolled`, which
[the rolled-SHA-2 quest](../quest/m4/verified/rolled-sha2-esp.md) covers. The
x86_64 proofs of SHA-256's padding, the SHA-512 family, HMAC's keyed states,
the digest, HMAC, HKDF, and PBKDF2 APIs, and ChaCha20 header protection are
written for it with the target renamed, as for aarch64, over what differs:

- `Rind/Portable/Sha256Compress.lean` and `Rind/Portable/Sha512Compress.lean`:
  SHA-256's and SHA-512's block functions, `low::generic::sha256` and
  `low::generic::sha512`, aws-lc's C in Rust, compute FIPS 180-4's
  compression of each whole block in turn. Each round and schedule step is a
  function the unrolled passes call with the working variables renamed, so
  one lemma covers every round, and `Window` says which pass's word each slot
  of the sixteen-word schedule window holds.
- `Rind/Portable/Sha512Entry.lean`: `RunsSha512`, which assumes only the
  entry checks, as no dispatch picks a routine, and states SHA-512's block
  function's theorem in the form the SHA-512 proof takes it.
- `Rind/Portable/ShaBlocks.lean`: `Sha256Blocks` and `Sha1Blocks`, the entry
  checks, and for SHA-1 the contract of its block function,
  `low::generic::sha1`, which no proof covers here.
- `Rind/Portable/Compare.lean` and `Rind/Portable/CtEqual.lean`: the
  constant-time compares behind `hmac::verify` and `pbkdf2::Secret::verify`,
  Rust here, read through raw pointers and `black_box`, so modelled by hand
  and proven, where x86_64 and aarch64 take HOL Light's theorems as axioms.

`Rind/Portable/HashAxioms.lean` and `Rind/Portable/Axioms.lean` check the
axioms each theorem rests on: none beyond Lean's own.

Every other operation the portable backend runs has no proof yet, and
these quests prove its code, whose proofs then run on this translation:

- SHA-3 and ML-KEM: [the sponge's proof over its Keccak-f](/quest/m4/verified/sha3-portable.md),
  which `Rind/Portable/Keccak.lean` proves,
  [the construction](/quest/m4/verified/mlkem-construction.md), and
  [the portable arithmetic](/quest/m4/verified/mlkem-portable.md);
- ChaCha20-Poly1305:
  [Graviola's Poly1305 and the separate-pass glue](/quest/m5/verified/chacha20-poly1305-portable.md);
- AES and AES-GCM: rind's `aes_nohw.c` and `gcm_nohw.c` ports, in
  [armv7's Rust proofs](/quest/m5/verified-armv7/prove.md) and
  [x86_64 without AES-NI](/quest/m5/verified/x86-no-aesni.md), which share one
  source file across word widths;
- X25519: [its own quest](/quest/m5/verified/x25519-portable.md), over armv7's
  proof and its dalek axioms;
- Ed25519: curve25519-dalek's serial backend under rind's glue, in
  [armv7's Curve25519](/quest/m5/verified-armv7/curve25519.md);
- P-256, P-384, and P-521: [armv7's NIST curves](/quest/m5/verified-armv7/nist-curves.md),
  whose point arithmetic `low/generic/limb64.rs` builds again over
  fiat-crypto's 64-bit field and scalar arithmetic;
- RSA: [verification](/quest/m4/verified/rsa-verify-portable.md), whose glue
  `Rind/X86_64/RsaDispatch.lean` proves over the Montgomery products as
  hypotheses, and [signing](/quest/m4/verified/rsa-sign.md), both over
  `low/generic/mont.rs`'s products, on 64-bit limbs here;
- SHA-1: `low::generic::sha1`, the block function `Sha1Blocks` stands for
  here, in [SHA-1's quest](/quest/m5/verified/sha1.md);
- MD5: [its own quest](/quest/m5/verified/md5.md).

[The re-audit](/quest/m4/verified/re-audit.md) plans whatever still lacks a
proof after those.

## Layout

- `hol-light/<arch>/`: rind's HOL Light proofs, one file per routine, on
  rind's fork of s2n-bignum in `thirdparty/s2n-bignum`.
- `verified-garbage/VerifiedGarbage/`: VG's ISA models and the `Spec`
  modules its theorems state, copied;
  `verified-garbage/RindIsa/`, rind's extension of them and its programs,
  with `rind-asm`; and `verified-garbage/Cosim/`, the cosimulation of both,
  which [verified-garbage's models](#verified-garbages-models) describes.
- `curve25519-dalek/`: BAIF's curve25519-dalek specs, copied, which
  [curve25519-dalek's proofs](#curve25519-daleks-proofs) describes.
- `Rind/<Arch>/{Types,Funs}.lean`: Aeneas's translation, which `admin/prove`
  writes and git ignores.
- `Rind/<Arch>/{Types,Funs}External.lean` and `Rind/Core.lean`: what the
  translation leaves opaque, and models of the few standard-library items
  Aeneas's library lacks.
- `Rind/<Arch>/S2nBignum.lean`, `Rind/<Arch>/AwsLc.lean`, and
  `Rind/X86_64/ValeAesGcm.lean`: s2n-bignum's, aws-lc-verification's, and
  Vale's theorems, restated as axioms about the routines' Rust wrappers.
- `Rind/X86_64/Simd.lean`: models of the x86_64 intrinsics rind's AES,
  AES-GCM setup, partial blocks, by-8 and by-16 kernels, point select, and
  two-block ChaCha20 kernel call;
  `Rind/X86_64/AesGcmModel.lean`: a hand model, over those intrinsics, of its
  PCLMULQDQ GHASH, by-8 AES-GCM, and AVX-512 by-16 AES-GCM, whose raw
  pointers, `transmute` constants, `as_chunks`, and zipped iterators Aeneas
  cannot translate; `Rind/X86_64/Avx512Vectors.lean`, the vectors
  `admin/avx512-vectors.rs` tests the AVX-512, VAES, and VPCLMULQDQ models
  with; `Rind/X86_64/Lanes512.lean`, those intrinsics lane by lane;
  `Rind/X86_64/PointSelectModel.lean`, of its AVX2 and SSE2 point selects,
  whose raw-pointer loads and `as_chunks` Aeneas cannot translate, and
  `Rind/X86_64/PointSelect.lean`, their proofs; `Rind/X86_64/GatherModel.lean`,
  of RSA's AVX2 table gather, whose raw-pointer loads, `chunks_mut`, and
  const generic picked by each block's length Aeneas cannot translate;
  `Rind/Aarch64/Neon.lean`, of the aarch64 intrinsics rind's AES and point
  select call, `Rind/Aarch64/NeonVectors.lean`, the vectors
  `admin/neon-vectors.rs` tests them with, `Rind/Aarch64/PointSelectModel.lean`,
  a hand model of its NEON point select, and `Rind/Aarch64/PointSelect.lean`,
  its proof; `Rind/Lanes.lean`, both targets' vector lanes and bytes, and
  `Rind/RowSelect.lean`, what both targets' select proofs share.
- `Rind/Spec.lean` and `Rind/Bytes.lean`: the elliptic-curve, ChaCha20,
  Poly1305, and ChaCha20-Poly1305 specs and byte-conversion lemmas, and
  `Rind/ChaCha20Poly1305Test.lean`, the AEAD specs' known-answer tests; `Rind/Sha2.lean` and
  `Rind/Sha2Lemmas.lean`: SHA-512's, and `Rind/Sha2Test.lean`, its
  known-answer tests; `Rind/S2nSha512.lean`, s2n-bignum's SHA-512 spec,
  transliterated, and its proof that it is `Rind/Sha2.lean`'s;
  `Rind/Ed25519.lean`: Ed25519's;
  `Rind/HashSpec.lean`: SHA-1's, SHA-256's, HMAC's, HKDF's, and PBKDF2's, and
  `Rind/HashSpecTest.lean`, their known-answer tests; `Rind/Vale.lean`,
  `Rind/ValeBytes.lean`, and `Rind/Gf128.lean`: Vale's AES and GF(2^128) specs
  and their lemmas, and `Rind/AesInverse.lean`, FIPS 197's equivalent inverse
  cipher.
- `Rind/SpecTest/`: the spec tests' executable twins, each proven equal to
  the spec it runs, `Upstream.lean`'s stand-ins for the opaque constants,
  and `Server.lean`, the executable `admin/spec-tests` drives, which
  [the spec tests](#the-spec-tests) describes.
- `Rind/X86_64/{Dispatch,QuicDispatch,DigestDispatch,DigestAlgorithm,AeadDispatch,HmacDispatch,GcmKey}.lean`:
  the hand models of the agreement, header-protection, digest, AEAD, and HMAC
  APIs' dispatch, `Rind/X86_64/SignatureBuffer.lean`, of the signature
  modules' `Buffer::write`, and of `aead::gcm::Key` over the AEAD model; `Rind/X86_64/HkdfExpand.lean` and
  `Rind/X86_64/Kdf/{TypesExternal,FunsExternal}.lean`, of what the HKDF and
  PBKDF2 pass leaves opaque, and `Rind/Aarch64/Kdf/VgExternal.lean`, of what
  aarch64's alone does.
- `Rind/Armv7/Curve25519.lean`: armv7's X25519 dispatch, over
  `Rind/Armv7/Dalek.lean`, the axioms restating BAIF's theorems, and
  `Rind/Dalek.lean`, BAIF's X25519 and byte encodings as those proofs read
  them.
- `Rind/X86_64/{X25519,Sha512,ChaCha20,Ed25519}.lean`: the X25519, SHA-512,
  ChaCha20, and Ed25519 proofs, with `Rind/X86_64/X25519Bytes.lean`, X25519's
  byte and limb conversions, `Rind/X86_64/Ed25519Ifma.lean`, Ed25519's on
  pyca/verified-garbage's IFMA routines, `Rind/X86_64/VgCurve25519.lean`, the
  axioms restating those routines' theorems, and `Rind/VgCurve25519.lean`,
  VG's X25519 and byte encodings as those proofs read them, `Rind/X86_64/{Blockwise,Sha,Hmac}.lean`,
  SHA-1's, SHA-256's, and HMAC's, and
  `Rind/X86_64/{DigestApi,HmacApi,Hkdf,Pbkdf2}.lean`, the digest, HMAC, HKDF,
  and PBKDF2 APIs'; `Rind/X86_64/HkdfAead.lean`, HKDF's conversion to AES-GCM
  and ChaCha20-Poly1305 keys, and `Rind/X86_64/HkdfAes.lean`, to AES
  header-protection keys; `Rind/Aes.lean`, FIPS 197's AES on bytes and its
  key schedule word by word; `Rind/<Arch>/AesKey.lean`, each target's key
  expansion and block cipher on the AES instructions;
  `Rind/X86_64/AesCipher.lean`, `cipher::Aes` and AES header protection;
  `Rind/AesModes.lean`, `Rind/AesModesBytes.lean`, and `Rind/AesKw.lean`,
  SP 800-38A's CTR and CBC and SP 800-38F's key wrap on bytes, and
  `Rind/<Arch>/{AesModesLow,AesModesApi,AesKw}.lean`, their proofs;
  `hol-light/x86_64/aes_hw_spec.ml`, AES on the AES-NI instructions and CTR32's
  counter blocks, for the x86_64 routines' HOL Light proofs; and
  `Rind/GhashSpec.lean` and
  `Rind/X86_64/{Ghash,PartialBlock,AesGcmGlue,AesGcm,GhashClmul,AesGcmBy8,AesGcmClmul,AesGcmAead,AesGcmAny,GhashAvx512,AesGcmAvx512}.lean`:
  the AES-GCM proof, on x86_64 alone; `Rind/Aarch64/{AesGcmModel,GhashPmull,AesGcmShort,AesGcm,AesGcmLong}.lean`,
  aarch64's hand model and its PMULL GHASH and AES-GCM proofs;
  `Rind/S2nGcm.lean`, s2n-bignum's AES and GHASH specs, transliterated, and
  their proofs that they are Vale's; `Rind/S2nGcmAe.lean`, its GCM-AE,
  GCM-AD, and AES key schedules, likewise; `Rind/X86_64/GcmKey.lean`, the hand model
  of `aead::gcm::Key` and its proofs; `Rind/X86_64/AeadVec.lean`, the AEAD
  API's `Vec` buffers; `Rind/X86_64/ChaCha20Poly1305Api.lean`, the
  ChaCha20-Poly1305 and XChaCha20-Poly1305 proof down to the one pass, both
  shared with aarch64; `Rind/X86_64/ChaCha20Poly1305.lean`, the x86_64 one
  pass above aws-lc's and pyca/verified-garbage's routines, and
  `Rind/Aarch64/ChaCha20Poly1305.lean`, aarch64's; and
  `Rind/X86_64/VgChaCha20Poly1305.lean`, the x86_64 one pass over VG's IFMA
  routines;
  `Rind/VgChaCha20Poly1305.lean`, the proof that pyca/verified-garbage's
  ChaCha20-Poly1305 spec is `Rind/Spec.lean`'s, and
  `Rind/Aarch64/VgChaCha20Poly1305.lean`, the aarch64 one pass over its SVE2
  and NEON routines; `Rind/VgChaCha20.lean`, the proof that pyca/verified-garbage's
  ChaCha20 spec is `Rind/Spec.lean`'s, `Rind/VgChaCha20Glue.lean`, what both
  targets' `cipher::ChaCha20` proofs share, and
  `Rind/{X86_64,Aarch64}/VgChaCha20.lean`, each target's glue over VG's
  routines.
- `Rind/Rsa.lean` and `Rind/RsaLemmas.lean`: RFC 8017's verification,
  transliterated, and its lemmas; `Rind/X86_64/{RsaBytes,RsaMont,RsaPublic,RsaKey,RsaVerify,RsaPss}.lean`:
  the RSA verification proof, on x86_64 alone,
  `Rind/X86_64/RsaDispatch.lean`, the hand model of the signature API's RSA
  public keys and its theorems, and `Rind/X86_64/{RsaGather,RsaExp,RsaPrivate}.lean`:
  the private operation's proof.
- `Rind/SymCrypt/{Defs,Sha3}.lean`: SymCrypt's Lean FIPS 202 spec, vendored;
  `Rind/Keccak.lean`: s2n-bignum's Keccak spec, transliterated, and its proof
  that it is SymCrypt's; `Rind/Sha3.lean`: the sponge over bytes, and its
  proof that it is SymCrypt's; `Rind/KeccakStates.lean`: Keccak-f states as
  lanes, shared by `Rind/<Arch>/KeccakDispatch.lean`: rind's Keccak-f dispatch
  on each target, and `Rind/Portable/Keccak.lean`: the portable backend's
  Keccak-f; `Rind/X86_64/Sha3.lean`: the SHA-3 and
  SHAKE proofs.
- `Rind/SymCrypt/{NatBit,Round,Xof,MlKem,MlKemPolynomials,MlKemNtt}.lean`:
  SymCrypt's Lean FIPS 203 spec and its NTT lemmas, vendored;
  `Rind/MlKem.lean`: FIPS 203's NTT and inverse NTT in closed form;
  `Rind/S2nMlKem.lean`: s2n-bignum's ML-KEM specs, transliterated, and their
  proofs that they are FIPS 203's; `Rind/MlKemCoding.lean`: FIPS 203's byte
  coding, compression, and CBD sampling bit by bit and coefficient by
  coefficient; `Rind/X86_64/MlKemCoding.lean`, on both targets: that rind's
  decompression, message coding, and CBD sampling are FIPS 203's;
  `Rind/Aarch64/MlKemGeneric.lean`: that aarch64's Rust 12-bit
  unpacking is; `Rind/MlKemPacking.lean`: packed words as FIPS 203's
  `ByteEncode`; `Rind/Aarch64/MlKemRoutines.lean`: the axioms for aarch64's
  ML-KEM routines and their specs in FIPS 203's terms;
  `Rind/Aarch64/MlKemPoly.lean`: `mid::mlkem`'s vector operations over them;
  `Rind/Aarch64/MlKemPke.lean`: ML-KEM-768's K-PKE decryption.
- `Rind/<Arch>/ShaBlocks.lean`: SHA-1 and SHA-256's block functions on each
  target, SHA-1's padded last blocks, and SHA-256's padded last blocks and
  finish; `Rind/Aarch64/Sha256Hw.lean`, the axiom for aarch64's routine with
  the SHA-256 instructions, and `Rind/Aarch64/Sha256HwAsm.lean`, its Lean
  proof; `Rind/X86_64/Sha256Shaext.lean`, the axioms for
  x86_64's routines for the SHA extensions and the proof of the finish's
  padding; and `Rind/S2nSha256.lean`, s2n-bignum's SHA-256
  spec, transliterated, and its proof that it is `Rind/HashSpec.lean`'s;
  `Rind/S2nChaCha20Poly1305.lean`, rind's HOL Light ChaCha20-Poly1305 spec,
  transliterated, and its proof that it is `Rind/Spec.lean`'s.
- `admin/prove` copies the other `Rind/X86_64/` models and proofs to
  `Rind/Aarch64/` with the target renamed, and the hash, KDF, and
  header-protection ones to `Rind/Portable/`.
- `Rind/Portable/{TypesExternal,FunsExternal,Compare,Sha256Compress,Sha512Compress,Sha512Entry,ShaBlocks,CtEqual}.lean`:
  the portable backend's opaque items, its compares' hand model, and its own
  proofs, which [the portable backend](#the-portable-backend) describes.
- `Rind/NistGroup.lean`: that the NIST curves' `nist.add` is the addition of
  Mathlib's group of points on the curve; `Rind/NistOrder.lean`: that every
  finite point has order n, by counting the curve's points;
  `Rind/P256Group.lean`: that `p256` is prime, by a Pratt certificate;
  `Rind/N256Prime.lean`: that `n256` is prime; `Rind/P256Multiples.lean`: the
  group laws and multiples ECDSA's twin multiplication relies on;
  `Rind/P384Multiples.lean`: the same for P-384.
- `Rind/Edwards.lean`: the twisted Edwards group law, from the Beneficial AI
  Foundation's curve25519-dalek simulation under the MIT license;
  `Rind/Ed25519Group.lean`: that `d` is a non-square, so `edMul` and `edPow`
  are that group's addition and multiples, that `L` is prime, by a Pratt
  certificate, and `half_size_iff`, the half-size check's argument;
  `Rind/X86_64/HalfSize.lean`: `mid::half_size::split`.
- `Rind/X86_64/Naf.lean`, on both targets: that `mid::util::public_naf`
  writes a scalar's width-5 or width-6 non-adjacent form, for any number of
  words, which P-256's and P-384's ECDSA verification reads.
- `Rind/X86_64/P256Dispatch.lean`, `Rind/X86_64/P256Agree.lean`, and
  `Rind/X86_64/P256.lean`: the hand model of P-256's key generation, and the
  P-256 agreement and key generation proofs, on both targets.
- `Rind/VgNist.lean`: that pyca/verified-garbage's NIST curve specs are
  rind's for any curve that matches; `Rind/VgP256.lean` and
  `Rind/VgP384.lean`: that VG's P-256 and P-384 match, and
  `Rind/<Arch>/VgP256.lean` and `Rind/<Arch>/VgP384.lean`, one per target,
  the axioms restating VG's theorems about its P-256 and P-384 routines.
- `Rind/P256Booth.lean`: the arithmetic of x86_64's Booth-recoded generator
  multiplication.
- `Rind/<Arch>/P256Table.lean` and `Rind/<Arch>/P256Base.lean`, one per
  target: its generator table's proof, and what the shared proofs take of its
  generator multiplication and table, `base_multiply_spec` and `first_row`,
  with x86_64's `jac_base_multiply_spec` for its key check.
- `Rind/X86_64/EcdsaDispatch.lean`, `Rind/X86_64/P256Ecdsa.lean`, and
  `Rind/X86_64/P256Signature.lean`, on both targets, over
  `Rind/<Arch>/P256KeyCheck.lean`, one per target: the hand model of ECDSA's
  dispatch and key generation, the proof of `high::ecdsa` and `mid::p256`'s
  ECDSA at P-256, the signature API's theorems, and each target's check of a
  key pair's public key.
- `Rind/X86_64/P384Ecdsa.lean` and `Rind/X86_64/P384Signature.lean`, on both
  targets, over `Rind/<Arch>/P384KeyCheck.lean`, one per target: the same for
  P-384 with SHA-384.

## Trust base

Beyond Lean's kernel:

- Charon and Aeneas's translation, and Aeneas's models of `core`, with
  `Rind/Core.lean`'s.
- That each hand model computes what the Rust it quotes does. They add no
  axiom.
- For the theorems that rest on `bv_decide`, the bitsliced AES's among them,
  Lean's compiler and its LRAT checker: each call adds an axiom that the
  compiled checker accepted a SAT solver's certificate.
- That `Rind/HashSpec.lean` transliterates FIPS 180-4, RFC 2104, RFC 5869,
  and RFC 8018.
- The restatement of each s2n-bignum, mlkem-native, and aws-lc-verification
  theorem, and of each of rind's own HOL Light theorems, as an axiom, under the composition rule in the
  [verification epic](/quest/m4/verified/README.md#composition-rule), and on aarch64 the
  caveats aws-lc-verification lists for its NSym proof. It lets a
  group-membership fact a proof must decide be its defining equation, so
  `group_carrier p256_group` is the curve equation that HOL Light's
  [`P256_GROUP`](https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/nistp256.ml#L82)
  proves it is, and `group_carrier edwards25519_group` the one
  [`EDWARDS25519_GROUP`](https://github.com/jrh13/hol-light/blob/217dd32e798d98926d3ab81ed3dfcdf435831e1f/EC/edwards25519.ml#L92)
  does. A function a proof must compute, such as `group_pow p256_group`, is
  its HOL Light definition, transliterated, rather than opaque, so `nist.add`,
  `nist.pow`, and `nist.inv` in `Rind/Spec.lean` are trusted to be
  `weierstrass_add`, `group_pow`, and `ring_inv` on each NIST curve's group,
  and `edMul` and `edPow` in `Rind/Ed25519.lean` `edwards_add` and
  `group_pow` on `edwards25519_group`.
- That `Rind/SymCrypt/Sha3.lean` is FIPS 202, as SymCrypt's authors state,
  and that `Rind/Keccak.lean` transliterates s2n-bignum's `keccak_spec.ml`,
  in which the Keccak-f axioms state their results.
- That `Rind/SymCrypt/MlKem.lean` is FIPS 203, as SymCrypt's authors state,
  and that `Rind/S2nMlKem.lean` transliterates the s2n-bignum ML-KEM specs it
  names.
- That `Rind/MlKemPacking.lean`'s `numOfWords` and `wordsOfNum`
  transliterate s2n-bignum's `num_of_wordlist` and `wordlist_of_num`, and its
  `compressD` mlkem-native's `compress_d`, in which the ML-KEM routines'
  axioms state their results.
- That `admin/prove`'s text comparison of aarch64's rejection-sampling table
  with s2n-bignum's reads both correctly.
- That `Rind/S2nGcm.lean` and `Rind/S2nGcmAe.lean` transliterate the
  s2n-bignum AES, GHASH, GCM, and key-schedule specs they name.
- That `Rind/Sha2.lean` restates cryptol-specs' SHA-512, its
  `processBlock_Common` as FIPS 180-4's, `Rind/S2nSha256.lean` and
  `Rind/S2nSha512.lean` transliterate s2n-bignum's SHA-256 and SHA-512 specs,
  and `Rind/S2nChaCha20Poly1305.lean` rind's HOL Light ChaCha20-Poly1305 spec.
- That `Rind/Rsa.lean` transliterates RFC 8017's RSASSA-PKCS1-v1_5 and
  RSASSA-PSS verification.
- That `Rind/Spec.lean`'s ChaCha20, Poly1305, and ChaCha20-Poly1305
  transliterate RFC 8439 and RFC 9001, its HChaCha20 and XChaCha20-Poly1305
  draft-irtf-cfrg-xchacha-03, its ECDSA FIPS 186-5, and
  `Rind/Ed25519.lean` RFC 8032 and s2n-bignum's encoding and decoding of
  edwards25519 points, whose `ed25519_decode` picks by Hilbert's choice as
  Lean's `Classical.epsilon` does.
- That `Rind/Vale.lean` transliterates Vale's AES and GF(2^128) specs and
  `hkeys_reqs_pub`, with the round functions Vale's AES spec assumes read as
  FIPS 197's, the S-box and `MixColumns` irreducible; that
  `Rind/AesInverse.lean` transliterates FIPS 197's equivalent inverse cipher,
  its inverse S-box and `InvMixColumns` opaque; and that `Rind/Aes.lean`'s header
  mask is RFC 9001's, `Rind/AesModes.lean`'s CTR and CBC SP 800-38A's with
  RFC 5652's PKCS#7 padding, and `Rind/AesKw.lean`'s KW and KWP SP 800-38F's.
- That `Rind/X86_64/Simd.lean`'s and `Rind/Aarch64/Neon.lean`'s intrinsics
  compute what their instructions do beyond the inputs they are tested on.
  `admin/simd-vectors.rs` runs each x86_64 instruction on the checking
  machine's CPU, on every immediate it reads, zero and all-ones lanes, and
  random inputs from a fixed seed, and Lean checks each model gives the
  same. `admin/neon-vectors.rs` does the same for the aarch64 ones; its
  output is committed as `Rind/Aarch64/NeonVectors.lean`, which Lean checks
  on any host, and the `prove` workflow reruns it on an aarch64 CPU and fails
  if the output changed. `admin/avx512-vectors.rs` does the same for the
  AVX-512, VAES, and VPCLMULQDQ ones, committed as
  `Rind/X86_64/Avx512Vectors.lean`; `admin/prove` reruns it only on a CPU
  with those features, and fails if the output changed. The AES models run the S-box and
  `MixColumns` as FIPS 197 computes them, bodies Lean evaluates while proofs
  keep the two opaque. All are tested on hardware, none under an emulator;
  `admin/prove` fails on a `core.core_arch` model it does not test.
- For the Lean proofs of rind's assembly, VG's models, which
  `admin/prove vg` checks against the CPU, and rind's extension of them in
  `verified-garbage/RindIsa/`, its semantics and its encoder, which `admin/prove
  vg` checks the same way and `admin/prove lean` against the bytes rind's
  build emits, and the restatement of each such theorem as an axiom about the
  Rust wrapper, under the composition rule.
- That rind's inline assembly is s2n-bignum's, aws-lc's, and Vale's object
  code, as for `benchmarks/verified.toml`'s other entries, except where a
  proof in `hol-light/` or a Lean proof above covers the bytes rind's build
  emits. For those, HOL
  Light's kernel and s2n-bignum's instruction models, as for s2n-bignum's
  own theorems, with the fork's additions to the x86 model, from
  awslabs/s2n-bignum#450 and rind's own, which
  `admin/prove cosim` checks against the CPU as s2n-bignum checks its own.
- For armv7's X25519, BAIF's Lean proofs of curve25519-dalek and their three
  axioms, the restatement of each theorem as an axiom, and the translation
  `admin/prove dalek` compares, which shows the release rind builds is the
  code BAIF's proofs are about.
- The translation ignores drops, which here wipe keys and keyed state and
  restore CPU state, and computes nothing an output
  depends on.

### The spec tests

`admin/spec-tests` tests the transliterations above against what they
transliterate. `admin/prove spec-tests` builds the specs into an executable,
`Rind/SpecTest/Server.lean`'s `spec-server`, and the driver runs each on its
algorithm's published vectors in `thirdparty/vectors/` (CAVP's, Wycheproof's,
CCTV's, aws-lc's, and the RFCs' own) and on random inputs from a fixed seed
compared with rind's output, and fails on any disagreement. The seed
reproduces every random input but those rind draws itself, having no seeded
API for them (RSA and ML-KEM keys, ML-KEM encapsulations, ECDSA nonces,
RSA-PSS salts, and XChaCha20-Poly1305 nonces), which the module
documentation of `admin/spec-tests/src/main.rs` lists. By default
`admin/prove spec-tests` runs a sample: a vector file
of more than 400 cases runs every k-th, the specs too slow for that fewer (PBKDF2's 4096-iteration vectors, SymCrypt's
ML-KEM, and s2n-bignum's SHA-512 forms, as `admin/spec-tests/src/cases.rs`
says of each), and a budget of 8 random cases a test from seed 1. The
`prove` workflow's nightly `spec-tests` job samples nothing: it runs every
vector the filters in `cases.rs` admit, and a budget of 64 random cases a
test from the run's own seed, each of the driver's groups of sections on a
runner of its own (`SPEC_TESTS_GROUP`). Most filters keep a spec to the domain its
theorems pass it; one is a runtime limit, PBKDF2's vectors past 100,000
iterations (RFC 6070's 2^24), which would take hours. A case may send more than one request, ML-KEM's sampled run spends a
quarter of the budget, and the specs `NO_RANDOM` in
`admin/spec-tests/src/main.rs` lists run on no random inputs; the driver's
table prints what each ran.

A spec Lean cannot run fast enough, or at all, runs through an executable
twin in `Rind/SpecTest/`, proven equal to it on the inputs the proofs pass
it:

- `nist.inv`, `nist.add`, and `nist.pow`, which `Classical.choose` and a
  recursion once per unit of the scalar define, through `invC`, `addC`, and
  the double-and-add `powC` on points of the curve, and ECDSA's signing and
  verification over them (`Nist.lean`);
- `edDecode`, a choice, through `decodeC`, RFC 8032's square root, which
  `decodeC_spec` proves picks the point a valid encoding names and refuses
  every encoding that names none (`Ed25519.lean`);
- `rsavp1`, which raises before it reduces, by square-and-multiply mod `n`,
  and RSASSA-PKCS1-v1_5's and RSASSA-PSS's verifications, propositions with
  existential witnesses, decided, PSS's computing MGF1's mask once
  (`Rsa.lean`);
- Vale's `gf128MulLE`, a product of Mathlib polynomials, through
  `Rind/Gf128.lean`'s bitwise multiplication, and GHASH and AES-GCM over it
  (`Gcm.lean`);
- Vale's and FIPS 197's S-boxes, opaque to proofs, which run as tables that
  `sboxFast_eq` and `invSboxFast_eq` prove are the bodies they evaluate.

`rfcx25519` is opaque: under the composition rule it stands for HOL Light's
definition, and nothing is assumed of it, so no twin can be proven equal to
it. `edPow` transliterates HOL Light's `group_pow`, which adds its point once
per unit of its exponent, too slowly to run. The tests run the specs around
them, X25519's
encoding of the scalar and the result, and Ed25519's hashing, clamping, and
encodings, with `Rind/SpecTest/Upstream.lean`'s transliterations of the
upstream definitions in their place, which checks those specs, not the
constants.

Run through a spec proven equal to them rather than themselves:
`Rind/S2nSha256.lean`'s and `Rind/S2nSha512.lean`'s SHA-2 run on short
messages only, as HOL Light's message schedules, transliterated, recurse
without sharing, while FIPS 180-4's, which they are proven equal to, run on
every vector; `Rind/S2nMlKem.lean`'s specs, which its bridges prove are FIPS
203's NTT, NTT⁻¹, and products, with no executable whole; `Rind/S2nGcm.lean`'s
AES and GHASH and `Rind/S2nGcmAe.lean`'s GCM and key schedules, which their
bridges prove are Vale's; and VG's specs,
which `Rind/Vg*.lean` prove are `Rind/Spec.lean`'s. Not run: `hkeysReqsPub`
and the P-256 and P-384 representation predicates, preconditions on a
routine's state rather than functions of inputs that vectors exercise.
