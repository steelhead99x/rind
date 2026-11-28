import Rind.Aarch64.ChaCha20Poly1305Poly
import RindIsa.AArch64.ChaCha20Poly1305

open VG VG.AArch64 rind.aarch64.asm rind.spec.poly1305 Rind.AArch64.ChaCha20Poly1305
open VG.Spec.Poly1305 (bytesAt)

set_option linter.unusedSimpArgs false

/-!
# The AAD hash in rind's copy of aws-lc's aarch64 ChaCha20-Poly1305

Seal and open inline aws-lc's `poly_hash_ad_internal` on each of their two
paths: `adBlocks` hashes the AAD's whole blocks, `x4` bytes from `x3`, after
the `cmp x4, #16` before it, and `adTail` the partial block left,
zero-padded. `ad_ok` runs them on rind's model: from the flags of that
`cmp`, fewer than `2^63` bytes of AAD, readable if any, an accumulator in
`(x8, x9, x10)` below `5 · 2^128` that is, modulo `p`, `a`, with `r` in
`(x16, x17)`, each word below `2^60` as clamping leaves them, and 1 in
`x15` (`Ctx.Ok`, `BInv`), they leave the accumulator below `5 · 2^128` and, modulo `p`,
RFC 8439's from `a` over the AAD zero-padded to whole blocks (`padBlocks`,
`Rind.Poly1305Limbs`); they change no memory and no register but `x3`,
`x4`, `x8` to `x14`, and `v20`; and their traces, `blocksTrace` and
`tailTrace`, are functions of the AAD's address and length alone.
-/

namespace rind.aarch64.chacha20poly1305asm

/-! ## The programs -/

/-- `ldp x11, x12, [x3], #16`: the next 16 bytes to hash. -/
def polyLoad : Ins := .ldpPost .x11 .x12 .x3 16

/-- Count a block off `x4`, and compare the bytes left with 16. -/
def subCmp : List Ins := [.vg (.subImm .x .x4 .x4 16), .cmpImm .x4 16]

/-- The 16 bytes at `x3`, hashed. -/
def polyBlock : List Ins := [polyLoad] ++ polyAdd ++ polyMul

/-- One whole block of the AAD. -/
def adBlock : List Ins := polyBlock ++ subCmp

/-- The AAD's whole blocks, if any. -/
def adBlocks : Prog I := .ite (.flags .lt) (.block []) (.loop (.block adBlock) (.flags .ge))

/-- Clear `v20` and index the partial block's last byte. -/
def tailInit : List Ins := [vop (.logic .eor .v20 .v20 .v20), .vg (.subImm .x .x4 .x4 1)]

/-- Shift `v20` a byte up and the byte at `x3 + x4` in below it. -/
def tailByte : List Ins :=
  [vop (.ext .v20 .v20 .v20 15), .ldrbReg .x11 .x3 .x4, vop (.ins .b16 .v20 0 .x11), .subsImm .x4 .x4 1]

/-- `v20`'s two halves to `(x11, x12)`. -/
def umovs : List Ins := [.vg (.umov .x .x11 .v20 0), .vg (.umov .x .x12 .v20 1)]

/-- Hash the partial block in `v20`. -/
def tailHash : List Ins := umovs ++ polyAdd ++ polyMul

/-- The AAD's partial block, if any. -/
def adTail : Prog I :=
  .ite (.vg (.zero .x .x4)) (.block [])
    (seqs [.block tailInit, .loop (.block tailByte) (.flags .ge), .block tailHash])

/-! ## Flags -/

/-- The flags `cmp a, #imm` and `subs` leave, for `a` and `imm` below `2^63`,
as comparisons of numbers. -/
structure SubFlags (g : VG.AArch64.State) (a : BitVec 64) (imm : Nat) : Prop where
  nf : g.nf = decide (a.toNat < imm)
  vf : g.vf = false
  zf : g.zf = decide (a.toNat = imm)
  c : g.c = decide (imm ≤ a.toNat)

theorem subFlags_nf (a : BitVec 64) (imm : Nat) (hi : imm < 2 ^ 63) (ha : a.toNat < 2 ^ 63) :
    (a + ~~~BitVec.ofNat 64 imm + BitVec.ofNat 64 (true.toNat)).msb = decide (a.toNat < imm) := by
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true]
  have : imm % 2 ^ 64 = imm := Nat.mod_eq_of_lt (by omega)
  rw [this]
  by_cases h : a.toNat < imm <;> simp [h] <;> omega

theorem subFlags_vf (a : BitVec 64) (imm : Nat) (hi : imm < 2 ^ 63) (ha : a.toNat < 2 ^ 63) :
    decide ((a + ~~~BitVec.ofNat 64 imm + BitVec.ofNat 64 (true.toNat)).toInt ≠
      a.toInt + (~~~BitVec.ofNat 64 imm).toInt + ((true.toNat : Nat) : Int)) = false := by
  rw [decide_eq_false_iff_not, not_not]
  simp only [BitVec.toInt_eq_toNat_cond, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat,
    Bool.toNat_true]
  have : imm % 2 ^ 64 = imm := Nat.mod_eq_of_lt (by omega)
  rw [this]
  split_ifs <;> omega

theorem subFlags_zf (a : BitVec 64) (imm : Nat) (hi : imm < 2 ^ 63) :
    decide (a + ~~~BitVec.ofNat 64 imm + BitVec.ofNat 64 (true.toNat) = 0) = decide (a.toNat = imm) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true,
    show (0 : BitVec 64).toNat = 0 from rfl]
  have : imm % 2 ^ 64 = imm := Nat.mod_eq_of_lt (by omega)
  rw [this]
  have := a.isLt
  constructor <;> intro h <;> omega

theorem subFlags_c (a : BitVec 64) (imm : Nat) (hi : imm < 2 ^ 63) :
    carry a (~~~BitVec.ofNat 64 imm) true = decide (imm ≤ a.toNat) := by
  simp only [carry, BitVec.toNat_not, BitVec.toNat_ofNat, Bool.toNat_true]
  have : imm % 2 ^ 64 = imm := Nat.mod_eq_of_lt (by omega)
  rw [this]
  have := a.isLt
  by_cases h : imm ≤ a.toNat <;> simp [h] <;> omega

theorem subFlags_flagsAdd (g : VG.AArch64.State) (a : BitVec 64) (imm : Nat) (hi : imm < 2 ^ 63)
    (ha : a.toNat < 2 ^ 63) : SubFlags (g.flagsAdd a (~~~BitVec.ofNat 64 imm) true) a imm :=
  ⟨subFlags_nf a imm hi ha, subFlags_vf a imm hi ha, subFlags_zf a imm hi, subFlags_c a imm hi⟩

theorem subFlags_addWithCarry (g : VG.AArch64.State) (d : Reg) (a : BitVec 64) (imm : Nat)
    (hi : imm < 2 ^ 63) (ha : a.toNat < 2 ^ 63) :
    SubFlags (g.addWithCarry .x d a (~~~BitVec.ofNat 64 imm) true) a imm :=
  ⟨subFlags_nf a imm hi ha, subFlags_vf a imm hi ha, subFlags_zf a imm hi, subFlags_c a imm hi⟩

theorem SubFlags.lt {g a imm} (h : SubFlags g a imm) : CondCode.holds g .lt = decide (a.toNat < imm) := by
  simp [CondCode.holds, h.nf, h.vf]

theorem SubFlags.ge {g a imm} (h : SubFlags g a imm) : CondCode.holds g .ge = decide (imm ≤ a.toNat) := by
  simp only [CondCode.holds, h.nf, h.vf]
  by_cases e : a.toNat < imm <;> simp [e]; omega

/-! ## Bytes and vectors as numbers -/

theorem byte_eq (m : Mem) (a : Addr) : (((m.read a 1).setWidth 32).setWidth 64).setWidth 8 = m a := by
  apply BitVec.eq_of_toNat_eq
  have := (m a).isLt
  simp only [Mem.read, BitVec.toNat_setWidth, BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_shiftLeft, Nat.zero_or]
  omega

theorem rotate_eq (v : BitVec 128) (h : v.toNat < 2 ^ 120) :
    ((v ++ v) >>> 120).extractLsb' 0 128 = v <<< 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_ushiftRight, BitVec.toNat_append,
    ← Nat.shiftLeft_add_eq_or_of_lt v.isLt, BitVec.toNat_shiftLeft]
  simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.shiftRight_zero, Nat.pow_zero,
    Nat.div_one]
  have e : (v.toNat * 2 ^ 128 + v.toNat) / 2 ^ 120 = v.toNat * 2 ^ 8 := by
    rw [show v.toNat * 2 ^ 128 = v.toNat * 2 ^ 8 * 2 ^ 120 by ring, Nat.add_comm,
      Nat.add_mul_div_right _ _ (by norm_num), Nat.div_eq_of_lt h, Nat.zero_add]
  rw [e]

theorem setLane_eq (v : BitVec 128) (b : BitVec 8) :
    setLane (v <<< 8) 8 0 b = (v <<< 8) ||| b.setWidth 128 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [setLane, Nat.mul_zero, BitVec.shiftLeft_zero, BitVec.getLsbD_or, BitVec.getLsbD_and,
    BitVec.getLsbD_not, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes, hi,
    decide_true, Bool.true_and]
  by_cases h8 : i < 8 <;> simp [h8]

theorem compose_toNat (v : BitVec 128) (b : BitVec 8) (h : v.toNat < 2 ^ 120) :
    (setLane (((v ++ v) >>> 120).extractLsb' 0 128) 8 0 b).toNat = v.toNat * 256 + b.toNat := by
  rw [rotate_eq v h, setLane_eq]
  have hz : (v <<< 8) &&& b.setWidth 128 = 0#128 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth, BitVec.getLsbD_zero]
    by_cases h8 : i < 8
    · simp [h8]
    · simp [h8, BitVec.getLsbD_of_ge b i (by omega)]
  rw [← BitVec.add_eq_or_of_and_eq_zero _ _ hz, BitVec.toNat_add, BitVec.toNat_shiftLeft,
    BitVec.toNat_setWidth, Nat.shiftLeft_eq]
  have := b.isLt
  rw [Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
  omega

theorem halves_toNat (v : BitVec 128) :
    (v.extractLsb' 0 64).toNat + 2 ^ 64 * (v.extractLsb' 64 64).toNat = v.toNat := by
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  simp only [Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  have := v.isLt
  omega

/-! ## The blocks on rind's model -/

theorem adcV_not (a : BitVec 64) (imm : Nat) :
    adcV a (~~~BitVec.ofNat 64 imm) true = a - BitVec.ofNat 64 imm := by
  apply BitVec.eq_of_toNat_eq
  simp only [adcV, BitVec.toNat_add, BitVec.toNat_not, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Bool.toNat_true]
  have := a.isLt
  omega

/-- `ldp x11, x12, [x3], #16` loads the 16 bytes at `x3` and steps past them. -/
theorem polyLoad_ok (s : S) (h0 : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x3) 8)
    (h1 : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x3 + 8#64) 8) :
    ∃ s', execBlock I [polyLoad] s = some (s', [.addr (s.vg.gpr .x3), .addr (s.vg.gpr .x3 + 8#64)]) ∧
      s'.vg.gpr .x11 = (s.vg.mem.read (s.vg.gpr .x3) 8).setWidth 64 ∧
      s'.vg.gpr .x12 = (s.vg.mem.read (s.vg.gpr .x3 + 8#64) 8).setWidth 64 ∧
      s'.vg.gpr .x3 = s.vg.gpr .x3 + 16#64 ∧ s'.vg.mem = s.vg.mem ∧ Frame s s' [] [.x3, .x11, .x12] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    a64_run [polyLoad]
    rfl
  · rfl
  · a64_out

/-- `subCmp` counts a block off `x4` and compares what is left with 16. -/
theorem subCmp_ok (s : S) (h : (s.vg.gpr .x4 - 16#64).toNat < 2 ^ 63) :
    ∃ s', execBlock I subCmp s = some (s', []) ∧ s'.vg.gpr .x4 = s.vg.gpr .x4 - 16#64 ∧
      SubFlags s'.vg (s.vg.gpr .x4 - 16#64) 16 ∧ s'.vg.mem = s.vg.mem ∧ Frame s s' [] [.x4] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    a64_run [subCmp]
    rfl
  · rfl
  · refine ⟨?_, subFlags_flagsAdd _ _ _ (by norm_num) h, ?_⟩
    all_goals a64_out

/-- `tailInit` clears `v20` and takes one off `x4`. -/
theorem tailInit_ok (s : S) :
    ∃ s', execBlock I tailInit s = some (s', []) ∧ s'.vg.v .v20 = 0 ∧ s'.vg.gpr .x4 = s.vg.gpr .x4 - 1#64 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.v20] [.x4] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    a64_run [tailInit, vop]
    rfl
  · rfl
  · a64_out
    exact BitVec.xor_self

set_option maxRecDepth 20000 in
/-- `tailByte` shifts the byte at `x3 + x4` in below `v20`, and takes one off `x4`. -/
theorem tailByte_ok (s : S) (h : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x3 + s.vg.gpr .x4) 1)
    (h4 : (s.vg.gpr .x4).toNat < 2 ^ 63) :
    ∃ s', execBlock I tailByte s = some (s', [.addr (s.vg.gpr .x3 + s.vg.gpr .x4)]) ∧
      s'.vg.v .v20 = setLane (((s.vg.v .v20 ++ s.vg.v .v20) >>> 120).extractLsb' 0 128) 8 0
        (s.vg.mem (s.vg.gpr .x3 + s.vg.gpr .x4)) ∧
      s'.vg.gpr .x4 = s.vg.gpr .x4 - 1#64 ∧ SubFlags s'.vg (s.vg.gpr .x4) 1 ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [.v20] [.x4, .x11] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    a64_run [tailByte, vop, byte_eq]
    rfl
  · rfl
  · refine ⟨?_, ?_, subFlags_addWithCarry _ .x4 (s.vg.gpr .x4) 1 (by norm_num) h4, ?_⟩
    · a64_out
    · simp only [gpr_addWithCarry, ↓reduceIte]
      exact adcV_not _ _
    · a64_out

/-- `umovs` moves `v20`'s halves to `(x11, x12)`. -/
theorem umovs_ok (s : S) :
    ∃ s', execBlock I umovs s = some (s', []) ∧ s'.vg.gpr .x11 = (s.vg.v .v20).extractLsb' 0 64 ∧
      s'.vg.gpr .x12 = (s.vg.v .v20).extractLsb' 64 64 ∧ s'.vg.mem = s.vg.mem ∧
      Frame s s' [] [.x11, .x12] := by
  apply ex_of_eq
  · rw [execBlock_acc]
    a64_run [umovs]
    rfl
  · rfl
  · a64_out

/-! ## Numbers -/

theorem word_toNat (M : Mem) (a : Addr) : ((M.read a 8).setWidth 64).toNat = leNum (bytesAt M a 8) := by
  rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (M.read a 8).isLt, read_toNat]

/-- A 16-byte block of the AAD as the two words `polyLoad` loads. -/
theorem block_val (M : Mem) (ad : Addr) (len j : Nat) (h : 16 * (j + 1) ≤ len) :
    ((M.read (ad + BitVec.ofNat 64 (16 * j)) 8).setWidth 64).toNat +
        2 ^ 64 * ((M.read (ad + BitVec.ofNat 64 (16 * j) + 8#64) 8).setWidth 64).toNat =
      leNum (((bytesAt M ad len).drop (16 * j)).take 16) := by
  rw [bytesAt_drop _ _ (by omega), bytesAt_take _ _ (by omega),
    show (16 : Nat) = 8 + 8 from rfl, bytesAt_add, leNum_append, bytesAt_length, word_toNat, word_toNat]
  norm_num

theorem ofNat_eq_zero (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0) = decide (n = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toNat_inj]
  simp only [BitVec.toNat_ofNat, show (0 : BitVec 64).toNat = 0 from rfl]
  rw [Nat.mod_eq_of_lt h]

theorem one_eq : (1#64 : BitVec 64) = BitVec.ofNat 64 1 := rfl
theorem one_eq' : (1 : BitVec 64) = BitVec.ofNat 64 1 := rfl

/-! ## What the hash is given -/

/-- The hash's inputs: the AAD, `len` bytes at `ad` in memory `M`; `r`'s
two words; and the accumulator's value before. -/
structure Ctx where
  M : Mem
  ad : Addr
  len : Nat
  r0 : BitVec 64
  r1 : BitVec 64
  a : Nat

/-- The AAD. -/
abbrev Ctx.x (c : Ctx) : List (BitVec 8) := bytesAt c.M c.ad c.len

/-- `r`. -/
abbrev Ctx.r (c : Ctx) : Nat := c.r0.toNat + 2 ^ 64 * c.r1.toNat

/-- The general registers the hash changes. -/
abbrev clobbers : List Reg := [.x3, .x4, .x8, .x9, .x10, .x11, .x12, .x13, .x14]

/-- `s0` holds `c`: its memory, 1 in `x15`, `r` in `(x16, x17)` with each
word below `2^60`, and the AAD readable if there is any. -/
structure Ctx.Ok (c : Ctx) (s0 : S) : Prop where
  mem : s0.vg.mem = c.M
  x15 : s0.vg.gpr .x15 = 1#64
  x16 : s0.vg.gpr .x16 = c.r0
  x17 : s0.vg.gpr .x17 = c.r1
  hr0 : c.r0.toNat < 2 ^ 60
  hr1 : c.r1.toNat < 2 ^ 60
  len : c.len < 2 ^ 63
  a : c.a < p
  ad : c.len ≠ 0 → InRegions (s0.vg.rd ++ s0.vg.wr) c.ad c.len

/-- An AAD region of `s0` is one of `s`'s, as `s` keeps `s0`'s regions. -/
theorem Ctx.Ok.region {c : Ctx} {s0 s : S} (ok : c.Ok s0) (hrd : s.vg.rd = s0.vg.rd)
    (hwr : s.vg.wr = s0.vg.wr) (k m : Nat) (hk : k + m ≤ c.len) (hm : 0 < m) :
    InRegions (s.vg.rd ++ s.vg.wr) (c.ad + BitVec.ofNat 64 k) m := by
  rw [hrd, hwr]
  exact InRegions.sub (ok.ad (by omega)) k m hk

/-- A register outside a frame's, through three frames. -/
theorem Frame.gpr3 {s₁ s₂ s₃ s₄ : S} {vs₁ gs₁ vs₂ gs₂ vs₃ gs₃} (f₁ : Frame s₁ s₂ vs₁ gs₁)
    (f₂ : Frame s₂ s₃ vs₂ gs₂) (f₃ : Frame s₃ s₄ vs₃ gs₃) (r : Reg) (h₁ : r ∉ gs₁) (h₂ : r ∉ gs₂)
    (h₃ : r ∉ gs₃) : s₄.vg.gpr r = s₁.vg.gpr r :=
  (f₃.gpr r h₃).trans ((f₂.gpr r h₂).trans (f₁.gpr r h₁))

/-! ## The whole blocks -/

/-- After `j` blocks: `x3` and `x4` at the next, the flags of `x4` against
16, and the accumulator over the first `j`. -/
structure BInv (c : Ctx) (s0 : S) (j : Nat) (s : S) : Prop where
  x3 : s.vg.gpr .x3 = c.ad + BitVec.ofNat 64 (16 * j)
  x4 : s.vg.gpr .x4 = BitVec.ofNat 64 (c.len - 16 * j)
  le : 16 * j ≤ c.len
  flags : SubFlags s.vg (s.vg.gpr .x4) 16
  mem : s.vg.mem = c.M
  frame : Frame s0 s [] clobbers
  lt : limbs (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) < 5 * 2 ^ 128
  acc : limbs (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) % p = padBlocks c.r c.a (c.x.take (16 * j))

/-- Block `j`'s trace: its two words. -/
def blockTrace (ad : Addr) (j : Nat) : List Leak :=
  [.addr (ad + BitVec.ofNat 64 (16 * j)), .addr (ad + BitVec.ofNat 64 (16 * j) + 8#64)]

/-- `r` and 1, through a frame that keeps them. -/
theorem Ctx.Ok.keys {c : Ctx} {s0 s : S} (ok : c.Ok s0) {vs gs} (f : Frame s0 s vs gs)
    (h15 : Reg.x15 ∉ gs) (h16 : Reg.x16 ∉ gs) (h17 : Reg.x17 ∉ gs) :
    s.vg.gpr .x15 = 1#64 ∧ s.vg.gpr .x16 = c.r0 ∧ s.vg.gpr .x17 = c.r1 :=
  ⟨(f.gpr _ h15).trans ok.x15, (f.gpr _ h16).trans ok.x16, (f.gpr _ h17).trans ok.x17⟩

/-- `polyAdd` then `polyMul`, from an accumulator below `5 · 2^128`: the
next accumulator, below `5 · 2^128` again. -/
theorem hash_ok (c : Ctx) (s0 s : S) (ok : c.Ok s0) {vs gs} (f : Frame s0 s vs gs)
    (h15 : Reg.x15 ∉ gs) (h16 : Reg.x16 ∉ gs) (h17 : Reg.x17 ∉ gs) (a m : Nat)
    (hlt : limbs (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) < 5 * 2 ^ 128)
    (ha : limbs (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) % p = a % p)
    (hm : (s.vg.gpr .x11).toNat + 2 ^ 64 * (s.vg.gpr .x12).toNat = m) :
    ∃ s', execBlock I (polyAdd ++ polyMul) s = some (s', []) ∧
      limbs (s'.vg.gpr .x8) (s'.vg.gpr .x9) (s'.vg.gpr .x10) < 5 * 2 ^ 128 ∧
      limbs (s'.vg.gpr .x8) (s'.vg.gpr .x9) (s'.vg.gpr .x10) % p = (a + m + 2 ^ 128) * c.r % p ∧
      s'.vg.mem = s.vg.mem ∧ Frame s s' [] [.x8, .x9, .x10, .x11, .x12, .x13, .x14] := by
  obtain ⟨k15, k16, k17⟩ := ok.keys f h15 h16 h17
  obtain ⟨s₁, x₁, b8, b9, b10, m₁, f₁⟩ := polyAdd_ok s
  obtain ⟨s₂, x₂, c8, c9, c10, m₂, f₂⟩ := polyMul_ok s₁
  have e16 : s₁.vg.gpr .x16 = c.r0 := (f₁.gpr _ (by decide)).trans k16
  have e17 : s₁.vg.gpr .x17 = c.r1 := (f₁.gpr _ (by decide)).trans k17
  rw [k15] at b8 b9 b10
  rw [e16, e17, b8, b9, b10] at c8 c9 c10
  obtain ⟨lt', acc'⟩ := acc_step _ _ _ _ _ c.r0 c.r1 a m ok.hr0 ok.hr1 hlt ha hm
  rw [← c8, ← c9, ← c10] at lt' acc'
  exact ⟨s₂, by simpa using execBlock_append_of x₁ x₂, lt', acc', by rw [m₂, m₁],
    f₁.mono (by simp) (by decide) |>.trans (f₂.mono (by simp) (by decide))⟩

/-- One iteration of the block loop: block `j`, then whether another whole block is left. -/
theorem block_step (c : Ctx) (s0 : S) (ok : c.Ok s0) (j : Nat) (s : S) (inv : BInv c s0 j s)
    (hj : 16 * (j + 1) ≤ c.len) :
    ∃ s', Exec I (.block adBlock) s (blockTrace c.ad j) s' ∧
      I.eval (.flags .ge) s' = some (decide (16 * (j + 1 + 1) ≤ c.len)) ∧ BInv c s0 (j + 1) s' := by
  obtain ⟨hx3, hx4, hle, -, hmem, fr, hlt, hacc⟩ := inv
  have hl := ok.len
  obtain ⟨s₁, x₁, a11, a12, a3, m₁, f₁⟩ := polyLoad_ok s
    (by rw [hx3]; exact ok.region fr.rd fr.wr (16 * j) 8 (by omega) (by omega))
    (by rw [hx3, add_ofNat]; exact ok.region fr.rd fr.wr (16 * j + 8) 8 (by omega) (by omega))
  rw [hx3, hmem] at a11 a12
  have f₁' : Frame s0 s₁ [] clobbers := fr.trans (f₁.mono (by simp) (by decide))
  have hm := block_val c.M c.ad c.len j hj
  rw [← a11, ← a12] at hm
  have g8 : s₁.vg.gpr .x8 = s.vg.gpr .x8 := f₁.gpr _ (by decide)
  have g9 : s₁.vg.gpr .x9 = s.vg.gpr .x9 := f₁.gpr _ (by decide)
  have g10 : s₁.vg.gpr .x10 = s.vg.gpr .x10 := f₁.gpr _ (by decide)
  have hpad : padBlocks c.r c.a (c.x.take (16 * j)) < p :=
    padBlocks_lt _ _ _ _ le_rfl ok.a
  obtain ⟨s₂, x₂, lt₂, acc₂, m₂, f₂⟩ := hash_ok c s0 s₁ ok f₁' (by decide) (by decide) (by decide)
    (padBlocks c.r c.a (c.x.take (16 * j))) _ (by rw [g8, g9, g10]; exact hlt)
    (by rw [g8, g9, g10, hacc, Nat.mod_eq_of_lt hpad]) hm
  have x4₂ : s₂.vg.gpr .x4 = BitVec.ofNat 64 (c.len - 16 * j) := by
    rw [f₂.gpr _ (by decide), f₁.gpr _ (by decide), hx4]
  have hsub : BitVec.ofNat 64 (c.len - 16 * j) - 16#64 = BitVec.ofNat 64 (c.len - 16 * (j + 1)) := by
    rw [ofNat_sub _ _ (by omega) (by omega)]; congr 1
  obtain ⟨s₃, x₃, d4, dfl, m₃, f₃⟩ := subCmp_ok s₂ (by
    rw [x4₂, hsub, BitVec.toNat_ofNat]; omega)
  rw [x4₂, hsub] at d4 dfl
  refine ⟨s₃, Exec.block ?_, ?_, ?_⟩
  · have := execBlock_append_of (execBlock_append_of x₁ x₂) x₃
    simpa [adBlock, polyBlock, blockTrace, hx3, List.append_assoc] using this
  · show some (CondCode.holds s₃.vg .ge) = _
    rw [dfl.ge, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases h : 16 * (j + 1 + 1) ≤ c.len <;> simp [h] <;> omega
  · have g : ∀ r ∈ [Reg.x8, .x9, .x10], s₃.vg.gpr r = s₂.vg.gpr r := by
      intro r hr; exact f₃.gpr r (by simp at hr; rcases hr with rfl | rfl | rfl <;> decide)
    refine ⟨?_, d4, by omega, by rw [d4]; exact dfl, by rw [m₃, m₂, m₁, hmem], ?_, ?_, ?_⟩
    · rw [f₃.gpr _ (by decide), f₂.gpr _ (by decide), a3, hx3, add_ofNat]; congr 2
    · exact f₁'.trans ((f₂.mono (by simp) (by decide)).trans (f₃.mono (by simp) (by decide)))
    · rw [g _ (by simp), g _ (by simp), g _ (by simp)]; exact lt₂
    · rw [g _ (by simp), g _ (by simp), g _ (by simp), acc₂,
        padBlocks_take_succ _ _ _ _ (by rw [bytesAt_length]; omega)]

/-- The block loop's trace: none for fewer than 16 bytes, else each block's. -/
def blocksTrace (ad : Addr) (len : Nat) : List Leak :=
  if len < 16 then [.branch true] else .branch false :: loopTrace (blockTrace ad) 1 0 (len / 16 - 1)

/-- The block loop, skipped for fewer than 16 bytes, hashes every whole block. -/
theorem blocks_ok (c : Ctx) (s0 s : S) (ok : c.Ok s0) (inv : BInv c s0 0 s) :
    ∃ s', Exec I adBlocks s (blocksTrace c.ad c.len) s' ∧ BInv c s0 (c.len / 16) s' := by
  have hl := ok.len
  have hlt : I.eval (.flags .lt) s = some (decide (c.len < 16)) := by
    show some (CondCode.holds s.vg .lt) = _
    rw [inv.flags.lt, inv.x4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rfl
  by_cases h : c.len < 16
  · refine ⟨s, ?_, by rw [Nat.div_eq_of_lt h]; exact inv⟩
    simp only [blocksTrace, h, ↓reduceIte]
    exact Exec.iteT (by rw [hlt]; simp [h]) (Exec.block rfl)
  · obtain ⟨s', x, inv'⟩ := loop_ok (BInv c s0) (fun j => 16 * (j + 1) ≤ c.len)
      (fun j => decide (16 * (j + 1 + 1) ≤ c.len)) (blockTrace c.ad) 1 (block_step c s0 ok)
      (c.len / 16 - 1) 0 s inv (fun i hi => by omega) (fun i hi => by simp only [decide_eq_true_eq]; omega)
      (by simp only [decide_eq_false_iff_not]; omega)
    refine ⟨s', ?_, by rwa [show 0 + 1 * (c.len / 16 - 1 + 1) = c.len / 16 by omega] at inv'⟩
    simp only [blocksTrace, h, ↓reduceIte]
    exact Exec.iteF (by rw [hlt]; simp [h]) x

/-! ## The partial block -/

/-- After `k` of the last `rem` bytes, from the last down, since `sb`: `x3`
at the partial block, `x4` at the next byte, and `v20` the `k` bytes as a
number. -/
structure TInv (c : Ctx) (sb : S) (rem k : Nat) (s : S) : Prop where
  x3 : s.vg.gpr .x3 = c.ad + BitVec.ofNat 64 (c.len - rem)
  x4 : k < rem → s.vg.gpr .x4 = BitVec.ofNat 64 (rem - 1 - k)
  le : k ≤ rem
  mem : s.vg.mem = c.M
  frame : Frame sb s [.v20] [.x4, .x11]
  val : (s.vg.v .v20).toNat = leNum (bytesAt c.M (c.ad + BitVec.ofNat 64 (c.len - k)) k)

/-- Byte `k` from the end's trace. -/
def byteTrace (ad : Addr) (len k : Nat) : List Leak := [.addr (ad + BitVec.ofNat 64 (len - (k + 1)))]

/-- One iteration of the byte loop: byte `k` from the end, then whether another is left. -/
theorem byte_step (c : Ctx) (s0 sb : S) (ok : c.Ok s0) (hrd : sb.vg.rd = s0.vg.rd)
    (hwr : sb.vg.wr = s0.vg.wr) (rem : Nat) (hrem : rem ≤ 15) (hrl : rem ≤ c.len) (k : Nat) (s : S)
    (inv : TInv c sb rem k s) (hk : k < rem) :
    ∃ s', Exec I (.block tailByte) s (byteTrace c.ad c.len k) s' ∧
      I.eval (.flags .ge) s' = some (decide (k + 1 < rem)) ∧ TInv c sb rem (k + 1) s' := by
  obtain ⟨hx3, hx4, hle, hmem, fr, hval⟩ := inv
  have hl := ok.len
  have hx4' := hx4 hk
  have ea : s.vg.gpr .x3 + s.vg.gpr .x4 = c.ad + BitVec.ofNat 64 (c.len - (k + 1)) := by
    rw [hx3, hx4', add_ofNat]; congr 2; omega
  obtain ⟨s₁, x₁, a20, a4, afl, m₁, f₁⟩ := tailByte_ok s
    (by rw [ea]; exact ok.region (fr.rd.trans hrd) (fr.wr.trans hwr) _ 1 (by omega) (by omega))
    (by rw [hx4', BitVec.toNat_ofNat]; omega)
  rw [ea] at x₁ a20
  refine ⟨s₁, Exec.block x₁, ?_, ?_⟩
  · show some (CondCode.holds s₁.vg .ge) = _
    rw [afl.ge, hx4', BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    by_cases h : k + 1 < rem <;> simp [h] <;> omega
  · refine ⟨by rw [f₁.gpr _ (by decide), hx3], fun h => ?_, by omega, by rw [m₁, hmem], fr.trans f₁, ?_⟩
    · rw [a4, hx4', one_eq, ofNat_sub _ _ (by omega) (by omega)]; congr 1
    · have hb : (s.vg.v .v20).toNat < 2 ^ 120 := by
        rw [hval]
        have := leNum_lt (bytesAt c.M (c.ad + BitVec.ofNat 64 (c.len - k)) k)
        rw [bytesAt_length] at this
        calc _ < 256 ^ k := this
          _ ≤ 256 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ < 2 ^ 120 := by norm_num
      rw [a20, compose_toNat _ _ hb, hval, bytesAt_succ, leNum_cons, one_eq', add_ofNat,
        show c.len - (k + 1) + 1 = c.len - k by omega, hmem]
      ring

/-- The partial block's trace: none for a whole number of blocks, else each byte's. -/
def tailTrace (ad : Addr) (len : Nat) : List Leak :=
  if len % 16 = 0 then [.branch true] else .branch false :: loopTrace (byteTrace ad len) 1 0 (len % 16 - 1)

/-- What the hash leaves: the accumulator over the AAD. -/
structure Done (c : Ctx) (s0 s : S) : Prop where
  lt : limbs (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) < 5 * 2 ^ 128
  acc : limbs (s.vg.gpr .x8) (s.vg.gpr .x9) (s.vg.gpr .x10) % p = padBlocks c.r c.a c.x
  mem : s.vg.mem = c.M
  frame : Frame s0 s [.v20] clobbers

/-- The partial block, if any, completes the hash. -/
theorem tail_ok (c : Ctx) (s0 s : S) (ok : c.Ok s0) (inv : BInv c s0 (c.len / 16) s) :
    ∃ s', Exec I adTail s (tailTrace c.ad c.len) s' ∧ Done c s0 s' := by
  obtain ⟨hx3, hx4, hle, -, hmem, fr, hlt, hacc⟩ := inv
  have hl := ok.len
  have hx : c.x.length = c.len := bytesAt_length _ _ _
  have hq : 16 * (c.len / 16) + c.len % 16 = c.len := Nat.div_add_mod _ _
  have hx4' : s.vg.gpr .x4 = BitVec.ofNat 64 (c.len % 16) := by rw [hx4]; congr 1; omega
  have hz : I.eval (.vg (.zero .x .x4)) s = some (decide (c.len % 16 = 0)) := by
    show some (s.vg.read .x .x4 == 0) = _
    rw [read_x, hx4', ofNat_eq_zero _ (by omega)]
  by_cases h : c.len % 16 = 0
  · refine ⟨s, ?_, hlt, ?_, hmem, fr.mono (by simp) (by simp)⟩
    · simp only [tailTrace, h, ↓reduceIte]
      exact Exec.iteT (by rw [hz]; simp [h]) (Exec.block rfl)
    · rw [hacc, padBlocks_whole c.r c.a c.x (by rw [hx]; exact h), hx]
  · -- `tailInit`, the bytes, then `tailHash`
    obtain ⟨s₁, x₁, a20, a4, m₁, f₁⟩ := tailInit_ok s
    have inv₀ : TInv c s₁ (c.len % 16) 0 s₁ := by
      refine ⟨?_, fun _ => ?_, by omega, by rw [m₁, hmem], Frame.refl _ _ _, ?_⟩
      · rw [f₁.gpr _ (by decide), hx3]; congr 2; omega
      · rw [a4, hx4', one_eq, ofNat_sub _ _ (by omega) (by omega), Nat.sub_zero]
      · rw [a20]; simp [bytesAt, leNum]
    have frd : s₁.vg.rd = s0.vg.rd := f₁.rd.trans fr.rd
    have fwr : s₁.vg.wr = s0.vg.wr := f₁.wr.trans fr.wr
    obtain ⟨s₂, x₂, inv₂⟩ := loop_ok (TInv c s₁ (c.len % 16)) (fun k => k < c.len % 16)
      (fun k => decide (k + 1 < c.len % 16)) (byteTrace c.ad c.len) 1
      (byte_step c s0 s₁ ok frd fwr (c.len % 16) (by omega) (by omega))
      (c.len % 16 - 1) 0 s₁ inv₀ (fun i hi => by omega)
      (fun i hi => by simp only [decide_eq_true_eq]; omega) (by simp only [decide_eq_false_iff_not]; omega)
    rw [show 0 + 1 * (c.len % 16 - 1 + 1) = c.len % 16 by omega] at inv₂
    obtain ⟨-, -, -, hmem₂, fr₂, hval⟩ := inv₂
    obtain ⟨s₃, x₃, b11, b12, m₃, f₃⟩ := umovs_ok s₂
    have hm : (s₃.vg.gpr .x11).toNat + 2 ^ 64 * (s₃.vg.gpr .x12).toNat =
        leNum (bytesAt c.M (c.ad + BitVec.ofNat 64 (16 * (c.len / 16))) (c.len % 16)) := by
      rw [b11, b12, halves_toNat, hval, show c.len - c.len % 16 = 16 * (c.len / 16) by omega]
    have fb : Frame s0 s₁ [.v20] clobbers := (fr.mono (by simp) (by simp)).trans (f₁.mono (by simp) (by decide))
    have f₃' : Frame s0 s₃ [.v20] clobbers :=
      (fb.trans (fr₂.mono (by simp) (by decide))).trans (f₃.mono (by simp) (by decide))
    have g : ∀ r ∈ [Reg.x8, .x9, .x10], s₃.vg.gpr r = s.vg.gpr r := by
      intro r hr
      have hr' : r ∉ [Reg.x4, .x11] ∧ r ∉ [Reg.x11, .x12] ∧ r ∉ [Reg.x4] := by
        simp at hr; rcases hr with rfl | rfl | rfl <;> decide
      rw [f₃.gpr r hr'.2.1, fr₂.gpr r hr'.1, f₁.gpr r hr'.2.2]
    have hpad : padBlocks c.r c.a (c.x.take (16 * (c.len / 16))) < p :=
      padBlocks_lt _ _ _ _ le_rfl ok.a
    obtain ⟨s₄, x₄, lt₄, acc₄, m₄, f₄⟩ := hash_ok c s0 s₃ ok f₃' (by decide) (by decide) (by decide)
      (padBlocks c.r c.a (c.x.take (16 * (c.len / 16)))) _
      (by rw [g _ (by simp), g _ (by simp), g _ (by simp)]; exact hlt)
      (by rw [g _ (by simp), g _ (by simp), g _ (by simp), hacc, Nat.mod_eq_of_lt hpad]) hm
    refine ⟨s₄, ?_, lt₄, ?_, by rw [m₄, m₃, hmem₂], f₃'.trans (f₄.mono (by simp) (by decide))⟩
    · have x := Exec.iteF (M := I) (th := .block []) (by rw [hz]; simp [h])
        (Exec.seq (Exec.block x₁) (Exec.seq x₂ (Exec.block (execBlock_append_of x₃ x₄))))
      simp only [List.nil_append, List.append_nil] at x
      simp only [tailTrace, h, ↓reduceIte]
      exact x
    · rw [acc₄, padBlocks_partial c.r c.a c.x (by rw [hx]; exact h), hx, bytesAt_drop _ _ (by omega),
        show c.len - 16 * (c.len / 16) = c.len % 16 by omega]

/-- The whole hash: the blocks, then the partial one. -/
theorem ad_ok (c : Ctx) (s0 s : S) (ok : c.Ok s0) (inv : BInv c s0 0 s) :
    ∃ s₁ s', Exec I adBlocks s (blocksTrace c.ad c.len) s₁ ∧ Exec I adTail s₁ (tailTrace c.ad c.len) s' ∧
      Done c s0 s' := by
  obtain ⟨s₁, x₁, inv₁⟩ := blocks_ok c s0 s ok inv
  obtain ⟨s', x', done⟩ := tail_ok c s0 s₁ ok inv₁
  exact ⟨s₁, s', x₁, x', done⟩

end rind.aarch64.chacha20poly1305asm

/-- info: 'rind.aarch64.chacha20poly1305asm.ad_ok' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.aarch64.chacha20poly1305asm.ad_ok
