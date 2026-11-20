module

public import VerifiedGarbage.Impl.MlKem.X86_64.Sample4

/-!
# ML-KEM on x86-64: three entries of the matrix and three blocks of `H(ek)` at once

`sampleH` is a fragment that encapsulation inlines (not a function), with
the interface of `vg_mlkem_sample_ntt4_avx2` (`Sample4.lean`): `seeds` in
`rdi`, `a` in `rsi` and `scratch` in `rdx`. It runs `SampleNTT` on the first
three seeds to the first three polynomials from `a`, as
`vg_mlkem_sample_ntt4_avx2` does, while the fourth state of the four
Keccak states, which that function uses for a fourth seed, absorbs three
blocks of the input of `H = SHA3-256` (rate 136): the state of that sponge
is at `scratch + 6720` (`oHS`, 200 bytes, as `[u64; 25]`), and the three
blocks at `scratch + 6920` (`oHB`, 408 bytes), past what the sampling uses.

The code is `vg_mlkem_sample_ntt4_avx2`'s with three changes:

1. After the padded seeds are written to the four states, the fourth state
   is overwritten with the sponge's state (`hload`).
2. Each of the three squeezes first XORs the next block (17 lanes, from
   `r8`, which the permutation keeps) into the fourth state (`hxor`), so
   that its permutation is the sponge's absorption of that block.
3. After the three squeezes, the fourth state is stored back as the
   sponge's (`hsave`), and only the first three seeds are sampled
   (`run1 0` to `run1 2`, then `tail3`): if one of them has fewer than 256
   coefficients, the two more squeezes permute all four states again (the
   fourth is no longer needed), and each of the three runs 112 more
   iterations.

The fourth state's output is copied to the fourth buffer, which nothing
reads. The XOR and the copies have fixed addresses, so the sponge's state
and blocks do not affect timing; the sampling's branches and addresses
depend on the first three seeds only.
-/

@[expose] public section

namespace VG.Impl.MlKem.X86_64.Sample4

open VG.X86_64
open VG.Impl.Sha3.X86_64.X4 (rcTable)

/-- The state of the sponge of `H` (200 bytes) and its next three blocks
(408 bytes), in the scratch space. -/
def oHS : Nat := 6720
def oHB : Nat := 6920

/-- The sponge's state to the fourth state (lane `i` at byte `32 i + 24`). -/
def hload : List Instr :=
  (List.range 25).flatMap fun i => [.mov .rax (.mem (at_ .rbx (oHS + 8 * i))), .store (at_ .rbx (32 * i + 24)) .rax]

/-- The block at `r8` XORed into the fourth state, and `r8` to the next. -/
def hxor : List Instr :=
  ((List.range 17).flatMap fun i => [.mov .rax (.mem (at_ .r8 (8 * i))),
    .alu .xor .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (32 * i + 24)) .rax]) ++
  [.alu .add .r8 (.imm 136)]

/-- A block XORed into the fourth state, then a squeeze. -/
def squeezeH (fast : Bool := false) : Prog isa := .seq (.block hxor) (squeeze fast)

/-- The three squeezes, each absorbing a block from `scratch + oHB`. -/
def squeezesH (fast : Bool := false) : Prog isa :=
  .seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oHB))])
    (blocks oBuf 168 3 (squeezeH fast))

/-- The fourth state back to the sponge's. -/
def hsave : List Instr :=
  (List.range 25).flatMap fun i => [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .rbx (oHS + 8 * i)) .rax]

/-- `r14` is 1 if each of the first three seeds has 256 coefficients, and 0 otherwise. -/
def cntFlags3 : List Instr := .mov32 .r14 (.imm 1) :: (List.range 3).flatMap fun k =>
  [.mov .rax (.mem (at_ .rbx (oCnt + 8 * k))), .shift .shr .rax 8, .alu32 .and .r14 (.reg .rax)]

/-- Two more blocks of each state, and 112 more iterations on each of the first three seeds. -/
def more3 (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block [.mov32 .r14 (.imm 1)]) (.seq (squeezes 0 2 fast) (.seq (.block tabAddr)
    (.seq (run2 0 w16 fast) (.seq (run2 1 w16 fast) (.seq (run2 2 w16 fast) (.block cntFlags3))))))

/-- If one of the first three seeds has fewer than 256 coefficients, `more3`; then the return value. -/
def tail3 (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block (cntFlags3 ++ ([.alu32 .cmp .r14 (.imm 0)] : List Instr)))
    (.seq (.ite .e (more3 fast w16) (.block [])) (.block (([.vop .vzeroupper] : List Instr) ++ epi)))

/-- Three entries of the matrix and three blocks of `H`'s sponge, with
32-bit coefficients or, if `w16`, 16-bit ones. -/
def sampleH (fast : Bool := false) (w16 : Bool := false) : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4)) (.seq (.block hload) (.seq (squeezesH fast)
    (.seq (.block hsave) (.seq (.block tabAddr) (.seq (run1 0 w16 fast) (.seq (run1 1 w16 fast) (.seq (run1 2 w16 fast) (tail3 fast w16))))))))

/-- The three squeezes, the first `m ≤ 3` each absorbing a block from
`scratch + oHB`, with the fourth state saved as the sponge's after the
`m`-th (before the first, for `m = 0`). -/
def squeezesHM (fast : Bool) (m : Nat) : Prog isa :=
  .seq (if m = 0 then .block [] else squeezesH' fast m)
    (.seq (.block hsave) (if m = 3 then .block [] else squeezes m (3 - m) fast))
where
  /-- The first `m` squeezes, each absorbing a block. -/
  squeezesH' (fast : Bool) (m : Nat) : Prog isa :=
    .seq (.block [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oHB))])
      (blocks oBuf 168 m (squeezeH fast))

/-- `sampleH` absorbing only the first `m ≤ 3` of the three blocks: three
entries of the matrix, with 16-bit coefficients, and `m` blocks of `H`'s
sponge. -/
def sampleHM (fast : Bool) (m : Nat) : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4)) (.seq (.block hload) (.seq (squeezesHM fast m)
    (.seq (.block tabAddr) (.seq (run1 0 true fast) (.seq (run1 1 true fast) (.seq (run1 2 true fast) (tail3 fast true)))))))

/-! ## Two outputs of `PRF₂` in the fourth state

`sampleP` runs `SampleNTT` on the first three seeds as `sampleHM fast 0`
does, while the fourth state computes `PRF₂(σ, 0)` and `PRF₂(σ, 1)`
(SHAKE256 of `σ ‖ N`, 128 bytes): before each of the first two squeezes it
is overwritten with the padded block of `σ ‖ N` (`σ` at `scratch + oPS`,
`r9` holding lane 4: `N` and SHAKE's suffix), and after it the first 128
bytes of its output go to `scratch + oPO + 128 N` (`r8`, which the
permutation keeps, as it keeps `r9`). The input of `PRF₂` is one block of
SHAKE256 (rate 136) and its output fewer bytes than the rate, so each is
one permutation. The stores have fixed addresses, so `σ` does not affect
timing. -/

/-- `σ` (32 bytes) and the two outputs of `PRF₂` (256 bytes), in the
scratch space, past what the sampling and the sponge of `H` use. -/
def oPS : Nat := 6920
def oPO : Nat := 7424

/-- Lane `j` of the fourth state: of the padded block of `σ ‖ N`, with lane
4 (`N` and SHAKE's suffix) in `r9`. -/
def plane (j : Nat) : List Instr :=
  if j < 4 then [.mov .rax (.mem (at_ .rbx (oPS + 8 * j))), .store (at_ .rbx (32 * j + 24)) .rax]
  else if j = 4 then [.store (at_ .rbx (32 * 4 + 24)) .r9]
  else if j = 16 then [.movImm64 .rax 0x8000000000000000#64, .store (at_ .rbx (32 * 16 + 24)) .rax]
  else [.mov32 .rax (.imm 0), .store (at_ .rbx (32 * j + 24)) .rax]

/-- The fourth state: the padded block of `σ ‖ N`. -/
def pload : List Instr := (List.range 25).flatMap plane

/-- The first 128 bytes of the fourth state to `r8`, `r8` to the next
output and `r9` to the next `N`. -/
def pext : List Instr :=
  ((List.range 16).flatMap fun i => [.mov .rax (.mem (at_ .rbx (32 * i + 24))), .store (at_ .r8 (8 * i)) .rax]) ++
    [.alu .add .r8 (.imm 128), .alu .add .r9 (.imm 1)]

/-- A squeeze with an output of `PRF₂` in the fourth state. -/
def squeezeP (fast : Bool := false) : Prog isa := .seq (.block pload) (.seq (squeeze fast) (.block pext))

/-- Three entries of the matrix, with 16-bit coefficients, and `PRF₂(σ, N₀)`,
…, `PRF₂(σ, N₀ + m - 1)`, for `m ≤ 3`: one in each of the first `m`
squeezes, to `scratch + oPO + 128 i` (the loops of the squeezes run at
least once, so a count of none is no loop). -/
def samplePN (fast : Bool) (N₀ m : Nat) : Prog isa :=
  .seq (.block (pro ++ rcTable .rbx (oRc / 32) ++ absorb4 ++
      [.mov .r8 (.reg .rbx), .alu .add .r8 (.imm (BitVec.ofNat 32 oPO)), .mov32 .r9 (.imm (BitVec.ofNat 32 (0x1f00 + N₀)))]))
    (.seq (if m = 0 then .block [] else blocks oBuf 168 m (squeezeP fast))
      (.seq (if m = 3 then .block [] else squeezes m (3 - m) fast)
      (.seq (.block tabAddr) (.seq (run1 0 true fast) (.seq (run1 1 true fast) (.seq (run1 2 true fast) (tail3 fast true)))))))

/-- The first output `N₀` and the count `m` of each `samplePN fast N₀ m` its
callers inline: key generation's `PRF₂(σ, 0)` and `PRF₂(σ, 1)`, and
encapsulation's seven (`EncapsHP16.lean`). -/
def pnUses : List (Nat × Nat) := [(0, 2), (1, 3), (4, 3), (0, 1)]

end VG.Impl.MlKem.X86_64.Sample4
