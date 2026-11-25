# Apple aarch64 (iPad) optimisation leads

For [steelhead99x/rind#260](https://github.com/steelhead99x/rind/issues/260) to
[#263](https://github.com/steelhead99x/rind/issues/263).
Read at `856e12f3e` (the DIT bench matrix branch, not `main`); every `file:line` below is at that commit.
Code reading only: nothing was built or measured, and nothing here claims a speedup.
Every lead is a hypothesis to measure on the iPad Pro M4 and the iPad mini A17 Pro.

## 0. Before touching kernels: macOS M4 and iPadOS M4 disagree

- `benchmarks/report.json`, host `kixtop` (Apple M4, macOS 26.6.2, commit `9e7f6a5a`):
  `sha512/16KB` rind 8.85 us vs fastest 8.59 us (1.03x); `mlkem768-keygen` rind 6.11 us, tied fastest.
- The M1 Pro proxy comments on #260 to #263 also show no 16 KB SHA gap and no ML-KEM/ML-DSA keygen gap.
- Dispatch does not differ between macOS and iOS: `HaveSha3::check()` (`rind/src/low/aarch64/cpu.rs:142`)
  reads `is_aarch64_feature_detected!("sha3")` (`cpu.rs:250`); `check_keccak()` (`cpu.rs:151`) keys on
  `target_vendor = "apple"`, which includes iOS.
- Measurement-side items to rule out first (not code changes):
  - A Quick run is one round; `rind-devbench/src/lib.rs:374` alternates file order only between rounds,
    so rind's rows sit at a fixed point of a one-round run (thermal state, P vs E core placement).
  - The run thread is a plain `std::thread` (`rind-devbench/src/lib.rs:493`) with no QoS class; the
    catalog runs at `QOS_CLASS_USER_INITIATED` (`rind-devbench/ios/main.m:126`).
  - Hypothesis: a high QoS run thread plus rounds > 1 changes the rind/competitor ratio.
- Log `HaveSha3::check().is_some()` and `check_keccak().is_some()` once in the iPad build.

## 1. SHA-512 (#260)

What runs today on Apple:
- `sha512_compress_blocks` (`rind/src/low/aarch64/sha512.rs:15`) checks `HaveSha3::check()` (`:22`)
  and calls `compress_hw` (`:36`), i.e. aws-lc's `sha512_block_data_order_hw` (`:82`), body in
  `rind/src/low/aarch64/aws_lc/sha512_block_data_order_hw.apple.s`.
- It does use FEAT_SHA512: per block 40 `sha512h`, 40 `sha512h2`, 32 `sha512su0`, 32 `sha512su1`
  (as `.long` words). One call per run of whole blocks (`rind/src/mid/sha2.rs:256`, `:288`).

Leads:
1. Alignment. The Apple `.s` has no `.align` at entry (the Linux one has `.align 6`, line 7); the loop
   has `.align 4` (`.apple.s:29`). Try `.p2align 6` on the loop and measure. Same instruction stream as
   the proof covers; `admin/prove-bytes` layout checks would need rerunning.
2. Schedule. The body reloads `K512` with an `ld1` per round pair and copies state with `orr` per block
   (`.apple.s:31` onwards). RustCrypto `sha2` 0.11 issues the same instructions via intrinsics, scheduled
   by LLVM. Compare per-block cost of rind's body vs a disassembled LLVM body on the iPad.
3. Scalar vs hardware. `RIND_CPU_DISABLE_sha3` selects `_nohw`. If `_nohw` is not slower than `_hw` on the
   iPad, the hardware path is not taken or is stalling, which points at (1) and (2), not the Rust glue.
4. 64 B rows. Per-call work outside the kernel: nested `Entry::new_secret()` (`sha2.rs:293`,
   `rind/src/high/digest.rs:137`), `Blockwise` buffering, and the `adrp`/`ld1`/`rev64` prologue.
   Measure with DIT denied to isolate them.

## 2. SHA-3 / SHAKE / Keccak (#261)

What runs today on Apple:
- One state: `sha3_keccak_f1600` (`rind/src/low/aarch64/sha3_keccak_f1600_mux.rs:5`) calls s2n-bignum's
  `sha3_keccak_f1600_alt` (`sha3_keccak_f1600_alt.rs:51`): `eor3`/`rax1`/`xar`/`bcax` on lane 0 of
  128-bit vectors, i.e. one-way, half of each vector idle.
- Batches: `sha3_keccak_nof4_f1600` (`sha3_keccak_nof4_f1600.rs:14`): N=2 is one `sha3_keccak2_f1600`
  (`sha3_keccak2_f1600.rs:57`, two-way NEON+SHA3), N=3 is keccak2 plus `_alt` (`nof4:23-26`), N=4 is two
  keccak2 calls (`nof4:28-29`). `sha3_keccak4_f1600` (`sha3_keccak4_f1600_mux.rs:7`) is just N=4.
- No four-way or hybrid kernel in this checkout: commit `91d7dc0c0` (hybrid scalar+NEON four-way, from
  mlkem-native) lives on other branches, is not an ancestor of `856e12f3e`, and excludes Apple.

Leads:
1. Rolled loop. `_alt` does one round per iteration with `sub`/`cbnz` and an `ld1r` of the round constant
   (`_alt.rs:91`, `:132`, `:159-160`); keccak2 likewise (`keccak2.rs:170`). XKCP, which RustCrypto
   `keccak` 0.2 `backends/aarch64_sha3.rs` adapts, compiles to LLVM-scheduled code. Try a 2- or 4-round
   unrolled body. Trade-off: the s2n-bignum proof covers the rolled code.
2. Double callee-save. `_alt` and keccak2 save and restore `d8-d15` themselves (`_alt.rs:65-69`,
   `:180-184`; `keccak2.rs:70-73`) and also list `v8`..`v15` as clobbers (`_alt.rs:188-220`,
   `keccak2.rs:290` area), so the Rust wrapper likely saves them again. Confirm in disassembly; dropping
   one save removes 16 memory ops per permutation, most visible at 64 B (one permutation).
3. Multi-block absorb. `Sponge::absorb` (`rind/src/mid/sha3.rs:332`) runs, per 136-byte block, Rust
   `add_bytes` (`sha3.rs:377`) then the `#[inline(never)]` kernel (`sha3.rs:350`), which reloads 25 lanes,
   spills, permutes and stores. Try an absorb-N-blocks kernel keeping the state in registers (as OpenSSL's
   armv8 `SHA3_absorb` does); same for `SqueezingSponge::squeeze` (`sha3.rs:151`).
4. 64 B copies. `Sha3Context::finish` (`sha3.rs:33`) copies the 200-byte state in `padded_state`
   (`sha3.rs:362`) and again into `SqueezingSponge::new`. The M1 Pro proxy's remaining gap is at 64 B.
5. Two-way layout. keccak2 transposes both states in (`keccak2.rs:81-123`, 25 `trn`) and out
   (`keccak2.rs:204-247`, 25 `trn`) every permutation. Multi-block squeezes (ML-KEM 3 blocks, ML-DSA
   ExpandA 5) pay that per block. Try a two-way "permute and squeeze K blocks" kernel that keeps the pair
   interleaved. mlkem-native's `keccak_f1600_x2_v84a` uses `ld2`/`st2`; rind avoids them for the
   s2n-bignum model (`keccak2.rs:61-66`).

## 3. ML-KEM (#262)

What runs today on Apple:
- ML-KEM-768 encaps: verified-garbage `vg_mlkem768_encaps_x2_sha3_keccak_sha3`, selected by
  `Encaps::check` = `HaveSha3::check()` and `cfg!(target_vendor = "apple")`
  (`rind/src/low/aarch64/mlkem768_vg.rs:34-35`, `:59`, `:84`). VG's own Keccak, not `_alt`.
- Keygen and decaps for every size, and encaps for 512/1024: rind's path (aarch64 `KeyPair` is the generic
  stub, `mlkem768_vg.rs:17`). NTT, basemul, `mlkem_rej_uniform_vartime` are s2n-bignum NEON
  (`rind/src/low/aarch64/mlkem.rs:7`, `:30`).
- `sample_ntt` (`rind/src/mid/mlkem/sample_ntt.rs:13`): k=3 skips eight-way (`:40-43`), does 4+4 via
  `sample_poly_ntt_4x` (`:54-58`, `:74`) and the ninth polynomial alone (`:60-63`, three one-way `_alt`
  permutations). Each four-way batch squeezes 3 blocks (`rind/src/mid/sha3.rs:172`, `:187`): two keccak2
  calls per block. k=2 is one batch, k=4 four (`_sample_poly_ntt_8x`, `sample_ntt.rs:66`).
- CBD: `sample_poly_cbd2` (`rind/src/mid/mlkem.rs:1247`) hashes four at a time for k=3 (`:1275`):
  768 keygen 6 polys (4+2), 768 encrypt 7 (4+3, last batch keccak2 plus `_alt`). `sample_poly_cbd3`
  (512) batches 4.
- One-way permutations left in 768 keygen: G (`mlkem.rs:477`), the ninth matrix poly (3), H(ek) in
  `EncapKey::new` (`mlkem.rs:729`, SHA3-256 over 1184 bytes, about 9). Decaps adds J = SHAKE256(z || c)
  (`mlkem.rs:451`, about 9) and G.

Leads:
1. Fill the lanes. In 768 keygen the ninth SHAKE128 state and the two leftover CBD SHAKE256 states are
   independent, and Keccak-f ignores rate, so they can share one batch (mixed-rate batching). Same for the
   3-lane CBD batch in encrypt. Measure as fewer one-way calls per operation.
2. Hybrid four-way on Apple. Bring in `91d7dc0c0`'s kernel (mlkem-native
   `keccak_f1600_x4_v8a_v84a_scalar_hybrid`) and time it against keccak2+keccak2 for N=4, and a scalar
   state beside one keccak2 for N=3. The current split rests on the `cpu.rs:146-150` comment and
   ALGORITHMS.md's Neoverse N2 numbers, not an iPad measurement.
3. Keygen extras vs aws-lc. It samples A untransposed (`mlkem.rs:487`), transposes and stores it
   (`:519`, `transpose` at `:998`), boxes a `Decoded` (`:736`), and the bench's drop wipes it (`:571-573`,
   `free_decoded` `:707`). Try building `Decoded` lazily on first use (as ML-DSA's `ReuseCache`), or
   sampling transposed directly (`Coeffs::sample(rho, true)`, `:962`) with a column-walking `mul_add`
   (`:978`).
4. Decaps re-decodes `s_hat` each call (`mlkem.rs:557`); caching it in `DecapKey` is a small lead (aws-lc
   also decodes per call).
5. VG encaps uses a 32 KiB `Scratch` the routine wipes every call (`mlkem768_vg.rs:19-26`). Fixed by VG's
   proof; just context for reading 768 encaps rows.
6. `encaps_mitigated`'s fallback (`mlkem.rs:811-812`) clones `bytes` and the whole `Decoded` and re-hashes
   ek only to get H(ek). Probability below 2^-261, so needless work rather than a speed lead.

## 4. ML-DSA (#263)

What runs today on Apple:
- NEON (s2n-bignum/mldsa-native): NTT, INTT, pointwise, `pointwise_acc_l4/l5/l7`, caddq, chknorm,
  decompose, use_hint, polyz_unpack, rejection samplers (`rind/src/low/aarch64/mldsa.rs:14-80`).
- Portable: `mldsa_reduce` (`mldsa.rs:11`, `rind/src/low/generic/mldsa_poly.rs:163`); `mldsa_nttunpack`
  is a no-op (`mldsa_poly.rs:139`).
- SHAKE via `Shake128x4`/`Shake256x4` (four at a time, i.e. keccak2 pairs) or one-way `Shake256`.
- Keygen (`rind/src/mid/mldsa.rs:610`), ML-DSA-65: seed SHAKE256 one-way (`:617`); `expand_s` (`:1137`)
  11 polys as 4+4+3, 2 blocks each; `expand_a` (`:1105`) 30 polys as 7 fours plus a pair, 5 blocks
  up front (`:1106`); tr = H(pk) over 1952 bytes one-way (`:646-647`, about 15 permutations); then NTTs
  of s2 and t0 (`:648-649`) used only by the cached signing expansion.
- Load-verify (bench: `PublicKey::new` then verify): `from_bytes` (`:307`) hashes tr one-way (`:313`,
  `tr` at `:482`); the first verify takes the unkept path (`ReuseCache`, `:938-939`), allocating and
  zero-filling K*L = 30 polys (`:947`) before `expand_a` (`:948`).
- Sign (`:771`, already ahead on the iPads): A, s1, s2, t0 cached in the key (`from_seed`, `:368`), not
  recomputed. `expand_mask` (`:1183`) runs per attempt: 4+1 for L=5 (fifth poly one-way), 4+3 for L=7.

Leads:
1. Keccak first. ExpandA is about 75 keccak2 calls per ML-DSA-65 keygen or load, so #261 leads 1, 2 and 5
   apply directly; the 5-block up-front squeeze (`mldsa.rs:1106`, same depth as mldsa-native) pays
   keccak2's transposes 5 times per pair.
2. Hybrid four-way on Apple, as ML-KEM lead 2: ML-DSA batches are four lanes apart from tails.
3. Keygen extras vs aws-lc: `Polys::new(secret_expansion_len)` (`:368`, `:579-580`) allocates and
   zero-fills 47 polys (`:280`), keygen runs 2K extra NTTs (`:648-649`), and the bench's drop wipes it all
   (`Polys::free` `:594-596`, `KeyPair` drop `:472-476`). Try building the signing expansion lazily on
   first sign (A and NTT'd s1 are needed for t anyway, so keep or recompute those by measurement).
4. Load-verify allocation: `alloc::vec![Poly::ZERO; k * l]` (`:947`) zero-fills 30 KiB that `expand_a`
   overwrites. For a struct element type `vec!` likely clones rather than `calloc`s; confirm in
   disassembly, then try a stack buffer or uninitialised storage.
5. Fill tr's lanes. tr's one-way absorb of 1952 bytes could ride in ExpandA's last batch, which uses 2 of
   4 lanes (30 = 7*4 + 2), removing about 15 one-way permutations per keygen and per load. Complex;
   measure the one-way share first.
6. ExpandMask tail (L=5): speculatively expand the next attempt's first polys in the same batch (nonces
   are `kappa + n`, deterministic). Sign is already ahead, so low priority.
7. `mldsa_reduce` portable (`mldsa_poly.rs:163-168`), called per row in compute_t, sign and verify. Check
   whether LLVM vectorises it for `aarch64-apple-ios` (base `apple-a7` tuning); if not, a NEON version is
   small.
8. Small copies: `mldsa_poly_use_hint_32/88` copy a 1 KiB poly per call (`mldsa.rs:61`, `:67`);
   `mldsa_rej_uniform_vartime` (`mldsa.rs:84`) uses NEON only at offset 0 with length a multiple of 24,
   so every extra ExpandA block takes the portable sampler.

## 5. Suggested measurement order

1. Rule out section 0 (QoS, rounds, routine-taken log).
2. Micro-time one `sha3_keccak_f1600_alt`, one `sha3_keccak2_f1600`, and `sha512_block_data_order_hw`
   per block, vs `_nohw`/scalar, on both iPads and on a macOS M4 with the same build.
3. Count one-way vs two-way Keccak calls per ML-KEM/ML-DSA operation (instrumented build) to size
   leads 3.1, 4.5 and 4.6 before writing code.
4. Then one at a time: double-save removal, unrolled `_alt`/keccak2, hybrid four-way on Apple, lazy key
   expansion (3.3, 4.3).

## 6. Correctness and constant-time notes (separate from performance)

- `rej_eta` (`rind/src/low/aarch64/mldsa.rs:95-110`) marks the whole SHAKE256 buffer public (`:103`)
  before the NEON eta sampler, on secret input (s1, s2). The comment argues the rejection pattern is
  public, but declassifying the whole buffer also stops CT tooling checking how accepted values are
  handled. The portable fallback (offset != 0) does not declassify, so the two paths are annotated
  differently. Worth a reviewer confirming the intended scope.
- `sign_internal` declassifies `c_tilde` on every attempt, rejected ones included (`mldsa.rs:829`), and
  each `rejected()` result (`:892`). Worth confirming this follows mldsa-native's argument for rejected
  attempts' challenges.
- `expand_a` clamps padding-lane indices with `.min(P::K * P::L - 1)` (`mldsa.rs:1110`) but only uses
  `polys.len()` lanes, so the clamp is harmless; noted because it reads like a bug.
- The keccak kernels' double `d8-d15` save (section 2 lead 2) is not a correctness problem.
- `sha3_keccak_nof4_f1600`'s N=3 split (`nof4:23-26`, pair 0 then state 2) looks correct.
