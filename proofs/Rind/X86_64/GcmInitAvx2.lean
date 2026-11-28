import Rind.X86_64.Asm
import Rind.GhashSpec
import RindIsa.X86_64.GcmInitAvx2
import VerifiedGarbage.TCB.X86_64.Target

open VG VG.X86_64 rind.x86_64.asm rind.vale Polynomial

set_option linter.unusedSimpArgs false

/-!
# BoringSSL's `gcm_init_vpclmulqdq_avx2`, proven

`gcm_init_vpclmulqdq_avx2_correct`: the routine
`RindIsa/X86_64/GcmInitAvx2.lean` gives as `prog`, which `admin/prove lean`
checks is the machine code and relocations of rind's naked function
`low::x86_64::aes_gcm_vaes::gcm_init_vpclmulqdq_avx2` as rind's Linux release
build emits it, with the two statics it reads, run in rind's extension of
VG's x86_64 model from a state `Pre` holds of, terminates in one that `Post`
relates it to: for the key `H` in the two words at `rsi`, high first, the
table's first eight blocks are H^8 down to H^1, each shifted as Vale's
`shift_key_1` does (the form `Rind/X86_64/GhashClmul.lean`'s `TableFor`
states), and its next 64 bytes each block's halves XORed in BoringSSL's
order; no other memory changes, the table's last 64 bytes included, and the general registers and those the
System V ABI makes the callee save are as they were. Its trace is a function
of its two pointers alone (`ConstantTime`, with `Pub`), and some state meets
`Pre`.

The proof runs the routine's blocks symbolically, shows each `_ghash_mul`
lane is `mulModel` (`lane_mul`, `square_eq`), so the lanes hold `pw`'s
powers, which `pw_spec` shows are `gPower`'s shifted, and reads the table
back from the six 256-bit stores (`readW_sub`, `readW_far`). Every theorem
rests only on Lean's three axioms.
-/

local notation "P" => Polynomial (ZMod 2)

namespace rind.x86_64.gcm_init_avx2

/-! ## The lane arithmetic -/

theorem vgClmul_aux (a b : BitVec 64) (k : Nat) :
    (List.range k).foldl (fun acc j => if a.getLsbD j then acc ^^^ (b.setWidth 128 <<< j) else acc) 0 =
      rind.simd.clmulAux b a k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, rind.simd.clmulAux]
    split <;> simp_all

/-- VG's carry-less multiply is rind's. -/
theorem vgClmul (a b : BitVec 64) : VG.X86_64.clmul a b = rind.simd.clmul a b := by
  have e : VG.X86_64.clmul a b = rind.simd.clmul b a := by
    unfold VG.X86_64.clmul rind.simd.clmul
    exact vgClmul_aux a b 64
  apply toPoly_inj
  rw [e, toPoly_clmul, toPoly_clmul, mul_comm]

theorem pclmul_00 (a b : BitVec 128) : pclmul a b 0x00 = rind.simd.clmul (lo a) (lo b) := by
  rw [pclmul, vgClmul]; rfl
theorem pclmul_01 (a b : BitVec 128) : pclmul a b 0x01 = rind.simd.clmul (hi a) (lo b) := by
  rw [pclmul, vgClmul]; rfl
theorem pclmul_10 (a b : BitVec 128) : pclmul a b 0x10 = rind.simd.clmul (lo a) (hi b) := by
  rw [pclmul, vgClmul]; rfl
theorem pclmul_11 (a b : BitVec 128) : pclmul a b 0x11 = rind.simd.clmul (hi a) (hi b) := by
  rw [pclmul, vgClmul]; rfl

set_option maxHeartbeats 1000000 in
theorem shuf_4e (x : BitVec 128) : shufDwords x 0x4e = swap x := by
  rw [show shufDwords x 0x4e = ofDwords (dword x 2) (dword x 3) (dword x 0) (dword x 1) from rfl]
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  simp only [ofDwords, dword, swap, lo, hi, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb']
  interval_cases i <;> simp

theorem add_self_shl (q : BitVec 64) : q + q = q <<< 1 := by
  rw [← BitVec.mul_two, BitVec.shiftLeft_eq_mul_twoPow]; rfl

/-- `gfpoly_and_internal_carrybit`, as `vpand` reads it. -/
def carryV : BitVec 128 := 0xc200000000000001#64 ++ 1#64

/-- `gfpoly`, as `vbroadcasti128` reads it. -/
def gfv : BitVec 128 := c64 ++ 1#64

theorem hi_gfv : hi gfv = c64 := hi_append _ _

set_option maxHeartbeats 4000000 in
/-- `vpshufd`, `vpsrad`, `vpaddq`, `vpand`, and `vpxor` multiply the key by `x`. -/
theorem head_eq (h : BitVec 128) :
    XBinOp.eval .paddq h h ^^^ (XShiftOp.eval .psrad (shufDwords h 0xd3) 31 &&& carryV) = skBV h := by
  rw [show shufDwords h 0xd3 = ofDwords (dword h 3) (dword h 0) (dword h 1) (dword h 3) from rfl]
  simp only [XBinOp.eval, XShiftOp.eval, add_self_shl, skBV, carryV]
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  by_cases hb : h.getLsbD 127 <;>
  simp only [hb, ofDwords, dword, qword, BitVec.getLsbD_append, BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last, ite_true] <;>
  interval_cases i <;> simp_all

theorem lo_swap (x : BitVec 128) : lo (swap x) = hi x := lo_append _ _

theorem mid_eq (a b : BitVec 128) :
    rind.simd.clmul (lo (swap a ^^^ a)) (lo (swap b ^^^ b)) ^^^ rind.simd.clmul (lo a) (lo b) ^^^
        rind.simd.clmul (hi a) (hi b) =
      rind.simd.clmul (hi a) (lo b) ^^^ rind.simd.clmul (lo a) (hi b) := by
  apply toPoly_inj
  simp only [toPoly_xor, toPoly_clmul, lo_xor, lo_swap]
  linear_combination (toPoly (lo a) * toPoly (lo b) + toPoly (hi a) * toPoly (hi b)) * two_eq_zero_P

/-- `_ghash_mul` of one lane is `mulModel`: the low, middle, and high schoolbook products, the low folded into the
middle and the middle into the high, by `gfpoly`'s high word. -/
theorem lane_mul (a b : BitVec 128) :
    rind.simd.clmul (hi a) (hi b) ^^^
        swap (rind.simd.clmul (hi a) (lo b) ^^^ rind.simd.clmul (lo a) (hi b) ^^^
          swap (rind.simd.clmul (lo a) (lo b)) ^^^ rind.simd.clmul c64 (lo (rind.simd.clmul (lo a) (lo b)))) ^^^
        rind.simd.clmul c64 (lo (rind.simd.clmul (hi a) (lo b) ^^^ rind.simd.clmul (lo a) (hi b) ^^^
          swap (rind.simd.clmul (lo a) (lo b)) ^^^ rind.simd.clmul c64 (lo (rind.simd.clmul (lo a) (lo b))))) =
      mulModel a b := by
  simp only [mulModel]
  rw [mid_eq]

theorem cross_zero (h : BitVec 128) : rind.simd.clmul (hi h) (lo h) ^^^ rind.simd.clmul (lo h) (hi h) = 0#128 := by
  apply toPoly_inj
  rw [toPoly_xor, toPoly_clmul, toPoly_clmul, toPoly_zero']
  linear_combination (toPoly (lo h) * toPoly (hi h)) * two_eq_zero_P

/-- The square in `xmm`, whose middle product is zero. -/
theorem square_eq (h : BitVec 128) :
    rind.simd.clmul (hi h) (hi h) ^^^
        swap (rind.simd.clmul c64 (lo (rind.simd.clmul (lo h) (lo h))) ^^^ swap (rind.simd.clmul (lo h) (lo h))) ^^^
        rind.simd.clmul c64 (lo (rind.simd.clmul c64 (lo (rind.simd.clmul (lo h) (lo h))) ^^^
          swap (rind.simd.clmul (lo h) (lo h)))) =
      mulModel h h := by
  rw [← lane_mul, cross_zero, BitVec.zero_xor,
    BitVec.xor_comm (swap (rind.simd.clmul (lo h) (lo h)))]

/-- The routine's powers of the key `h`: H^1, `h` times `x`; H^2, its square; and from H^3 each the one two below
times H^2. -/
def pw (h : BitVec 128) : Nat → BitVec 128
  | 0 => 0
  | 1 => skBV h
  | 2 => mulModel (skBV h) (skBV h)
  | n + 3 => mulModel (pw h (n + 1)) (mulModel (skBV h) (skBV h))

theorem pw_spec (h : BitVec 128) : ∀ n, 1 ≤ n →
    toPoly (pw h n) = shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly h) n)
  | 0, hn => absurd hn (by omega)
  | 1, _ => by rw [pw, toPoly_skBV, gPower_one]
  | 2, _ => by
    rw [pw, mul_shiftKey1 _ _ (small_toPoly h) (small_toPoly h) _ _ (toPoly_skBV h) (toPoly_skBV h)]
    have e := gPower_add (toPoly h) 1 le_rfl 1 le_rfl
    rw [gPower_one] at e
    rw [e]
  | n + 3, _ => by
    have s := small_gPower (toPoly h) (small_toPoly h)
    show toPoly (mulModel (pw h (n + 1)) (pw h 2)) = _
    rw [mul_shiftKey1 _ _ (s (n + 1)) (s 2) _ _ (pw_spec h (n + 1) (by omega)) (pw_spec h 2 (by omega)),
      gPower_add _ _ (by omega) _ (by omega)]

theorem pw_two (h : BitVec 128) : pw h 2 = mulModel (pw h 1) (pw h 1) := by simp only [pw]
theorem pw_succ (h : BitVec 128) (n : Nat) : pw h (n + 3) = mulModel (pw h (n + 1)) (pw h 2) := by simp only [pw]

/-! ## Running the blocks -/

abbrev G := VG.X86_64.State

section
variable (g : G)

theorem lane_setV_ne (len : VLen) {r r' : XReg} (x y : BitVec 128) (i : Nat) (h : r' ≠ r) :
    (g.setV len r x y).lane r' i = g.lane r' i := by
  simp only [State.setV, State.lane, h, ite_false]

@[simp] theorem lane_setV_0 (len : VLen) (r : XReg) (x y : BitVec 128) : (g.setV len r x y).lane r 0 = x := by
  simp [State.setV, State.lane]
@[simp] theorem lane_setV_256 (r : XReg) (x y : BitVec 128) : (g.setV .l256 r x y).lane r 1 = y := by
  simp [State.setV, State.lane]
@[simp] theorem lane_setV_128 (r : XReg) (x y : BitVec 128) : (g.setV .l128 r x y).lane r 1 = 0 := by
  simp [State.setV, State.lane]

theorem xmm_lane (r : XReg) : g.xmm r = g.lane r 0 := rfl
theorem ymm_lane (r : XReg) : g.ymm r = g.lane r 1 ++ g.lane r 0 := rfl

@[simp] theorem setV_gpr (len : VLen) (r : XReg) (x y : BitVec 128) : (g.setV len r x y).gpr = g.gpr := by cases g; rfl
@[simp] theorem setV_mem (len : VLen) (r : XReg) (x y : BitVec 128) : (g.setV len r x y).mem = g.mem := by cases g; rfl
@[simp] theorem setV_rd (len : VLen) (r : XReg) (x y : BitVec 128) : (g.setV len r x y).rd = g.rd := by cases g; rfl
@[simp] theorem setV_wr (len : VLen) (r : XReg) (x y : BitVec 128) : (g.setV len r x y).wr = g.wr := by cases g; rfl
@[simp] theorem setV_mxcsr (len : VLen) (r : XReg) (x y : BitVec 128) : (g.setV len r x y).mxcsr = g.mxcsr := by cases g; rfl

@[simp] theorem vexec_gpr (o : VOp) : (o.exec g).gpr = g.gpr := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem vexec_mem (o : VOp) : (o.exec g).mem = g.mem := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem vexec_rd (o : VOp) : (o.exec g).rd = g.rd := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem vexec_wr (o : VOp) : (o.exec g).wr = g.wr := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem vexec_mxcsr (o : VOp) : (o.exec g).mxcsr = g.mxcsr := by
  cases o <;> simp only [VOp.exec] <;> (try split) <;> rfl
@[simp] theorem vexec_ea (o : VOp) (m : MemOp) : (o.exec g).ea m = g.ea m := by
  simp only [State.ea, vexec_gpr]
@[simp] theorem setV_ea (len : VLen) (r : XReg) (x y : BitVec 128) (m : MemOp) : (g.setV len r x y).ea m = g.ea m := by cases g; rfl

theorem gpr_setMem' (M : Mem) : (setMem g M).gpr = g.gpr := by cases g; rfl
theorem rd_setMem' (M : Mem) : (setMem g M).rd = g.rd := by cases g; rfl
theorem wr_setMem' (M : Mem) : (setMem g M).wr = g.wr := by cases g; rfl
theorem mem_setMem' (M : Mem) : (setMem g M).mem = M := by cases g; rfl
theorem mxcsr_setMem' (M : Mem) : (setMem g M).mxcsr = g.mxcsr := by cases g; rfl
theorem ea_setMem (M : Mem) (m : MemOp) : (setMem g M).ea m = g.ea m := by cases g; rfl
theorem lane_setMem (M : Mem) (r : XReg) (i : Nat) : (setMem g M).lane r i = g.lane r i := by cases g; rfl
theorem ymm_setMem (M : Mem) (r : XReg) : (setMem g M).ymm r = g.ymm r := by cases g; rfl

theorem store256_of {a : Addr} {v : BitVec 256} (h : InRegions g.wr a 32) :
    g.store256 a v = some (setMem g (g.mem.writeW a v)) := by
  simp [State.store256, h, setMem]

theorem store256_setMem (M : Mem) {a : Addr} {v : BitVec 256} (h : InRegions g.wr a 32) :
    (setMem g M).store256 a v = some (setMem g (M.writeW a v)) := by
  simp [State.store256, h, setMem]
end

/-- A block of vector instructions keeps all but the vector registers. -/
macro "keeps" : tactic => `(tactic| exact ⟨rfl, by simp only [vexec_gpr, setV_gpr, gpr_setMem'],
  by simp only [vexec_rd, setV_rd, rd_setMem'], by simp only [vexec_wr, setV_wr, wr_setMem'],
  by simp only [vexec_mxcsr, setV_mxcsr, mxcsr_setMem']⟩)

theorem eval_pxor (a b : BitVec 128) : XBinOp.eval .pxor a b = a ^^^ b := rfl
theorem eval_pand (a b : BitVec 128) : XBinOp.eval .pand a b = a &&& b := rfl
theorem eval_punpcklqdq (a b : BitVec 128) : XBinOp.eval .punpcklqdq a b = lo b ++ lo a := rfl
theorem eval_punpckhqdq (a b : BitVec 128) : XBinOp.eval .punpckhqdq a b = hi b ++ hi a := rfl
theorem bit_one : (1 : BitVec 8).getLsbD 0 = true := rfl

theorem static_carry : Rind.X86_64.static128 Rind.X86_64.GcmInitAvx2.carry = some carryV := rfl
theorem static_gfpoly : Rind.X86_64.static128 Rind.X86_64.GcmInitAvx2.gfpoly = some gfv := rfl

/-- What every block keeps: all but the vector registers and memory. -/
structure Keeps (s s' : S) : Prop where
  lo : s'.lo = s.lo
  gpr : s'.vg.gpr = s.vg.gpr
  rd : s'.vg.rd = s.vg.rd
  wr : s'.vg.wr = s.vg.wr
  mxcsr : s'.vg.mxcsr = s.vg.mxcsr

theorem Keeps.trans {s₁ s₂ s₃ : S} (a : Keeps s₁ s₂) (b : Keeps s₂ s₃) : Keeps s₁ s₃ :=
  ⟨b.lo.trans a.lo, b.gpr.trans a.gpr, b.rd.trans a.rd, b.wr.trans a.wr, b.mxcsr.trans a.mxcsr⟩

theorem execBlock_app {A B : List Ins} {s s₁ s₂ : S} {t₁ t₂ : List Leak} (h₁ : execBlock I A s = some (s₁, t₁))
    (h₂ : execBlock I B s₁ = some (s₂, t₂)) : execBlock I (A ++ B) s = some (s₂, t₁ ++ t₂) := by
  rw [execBlock_append, h₁]; simp [h₂]

/-- Runs a block one instruction at a time. -/
syntax "run_block" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| run_block) => `(tactic| simp only [execBlock_acc, execAcc_cons, execAcc_nil, Rind.X86_64.exec,
    Rind.X86_64.addrs, VG.X86_64.exec, VG.X86_64.addrs, Rind.X86_64.GcmInitAvx2.vop, Option.map_some, List.map_nil,
    List.map_cons, List.append_nil, List.nil_append, List.cons_append])
  | `(tactic| run_block [$xs,*]) => `(tactic| simp only [$xs,*, execBlock_acc, execAcc_cons, execAcc_nil,
    Rind.X86_64.exec, Rind.X86_64.addrs, VG.X86_64.exec, VG.X86_64.addrs, Rind.X86_64.GcmInitAvx2.vop,
    Option.map_some, List.map_nil, List.map_cons, List.append_nil, List.nil_append, List.cons_append])

/-- Proves two registers differ. -/
macro "reg_ne" : tactic => `(tactic| first | assumption | exact Ne.symm (by assumption) | decide)

/-- Reads a lane of the registers a block leaves. -/
syntax "lanes" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| lanes) => `(tactic| simp (disch := reg_ne) only [VOp.exec, VBinOp.sse, eval_pxor,
    eval_pand, eval_punpcklqdq, eval_punpckhqdq, pclmul_00, pclmul_01, pclmul_10, pclmul_11, shuf_4e, hi_gfv,
    bit_one, ite_true, xmm_lane, lane_setMem, lane_setV_0, lane_setV_256, lane_setV_128, lane_setV_ne])
  | `(tactic| lanes [$xs,*]) => `(tactic| simp (disch := reg_ne) only [$xs,*, VOp.exec, VBinOp.sse, eval_pxor,
    eval_pand, eval_punpcklqdq, eval_punpckhqdq, pclmul_00, pclmul_01, pclmul_10, pclmul_11, shuf_4e, hi_gfv,
    bit_one, ite_true, xmm_lane, lane_setMem, lane_setV_0, lane_setV_256, lane_setV_128, lane_setV_ne])

/-- The key: the two words at `rsi`, high first. -/
def key (s : S) : BitVec 128 := swap (s.vg.mem.readW (s.vg.gpr .rsi) 128)

/-- `vpshufd` from `[rsi]` loads the key into `xmm3`. -/
theorem load_run (s : S) (h : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .rsi) 16) :
    ∃ s', execBlock I [.vpshufdLoad .xmm3 { base := .rsi } 0x4e] s = some (s', [.addr (s.vg.gpr .rsi)]) ∧
      Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧ s'.vg.lane .xmm3 0 = key s := by
  have hl : s.vg.load128 (s.vg.gpr .rsi) = some (s.vg.mem.readW (s.vg.gpr .rsi) 128) := by
    simp [State.load128, h]
  have he : s.vg.ea { base := .rsi } = s.vg.gpr .rsi := by simp [State.ea]
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · run_block [hl, he]
    rfl
  · refine ⟨by keeps, by simp only [setV_mem], ?_⟩
    lanes
    rfl

/-- The sign masks and the doubled words of `shift_key_1`. -/
theorem shift_run (s : S) :
    ∃ s', execBlock I [Rind.X86_64.GcmInitAvx2.vop (.vpshufd .l128 .xmm0 .xmm3 0xd3),
        Rind.X86_64.GcmInitAvx2.vop (.vshift .psrad .l128 .xmm0 .xmm0 31),
        Rind.X86_64.GcmInitAvx2.vop (.vbin .vpaddq .l128 .xmm3 .xmm3 .xmm3)] s = some (s', []) ∧
      Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧
      s'.vg.lane .xmm0 0 = XShiftOp.eval .psrad (shufDwords (s.vg.lane .xmm3 0) 0xd3) 31 ∧
      s'.vg.lane .xmm3 0 = XBinOp.eval .paddq (s.vg.lane .xmm3 0) (s.vg.lane .xmm3 0) ∧
      ∀ r, r ≠ .xmm0 → r ≠ .xmm3 → ∀ i, s'.vg.lane r i = s.vg.lane r i := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · run_block
    rfl
  · refine ⟨by keeps, by simp only [vexec_mem], ?_, ?_, ?_⟩
    · lanes
    · lanes
    · intro r h0 h3 i
      lanes [h0, h3]

/-- The carries added, and `gfpoly` broadcast to `ymm6`. -/
theorem mask_run (s : S) :
    ∃ s', execBlock I [.rip (.vbin .vpand .l128 .xmm0 .xmm0) Rind.X86_64.GcmInitAvx2.carryName
          Rind.X86_64.GcmInitAvx2.carry,
        Rind.X86_64.GcmInitAvx2.vop (.vbin .vpxor .l128 .xmm3 .xmm3 .xmm0),
        .rip (.vbroadcasti128 .xmm6) Rind.X86_64.GcmInitAvx2.gfpolyName Rind.X86_64.GcmInitAvx2.gfpoly] s =
        some (s', [.addr 0, .addr 0]) ∧
      Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧
      s'.vg.lane .xmm3 0 = s.vg.lane .xmm3 0 ^^^ (s.vg.lane .xmm0 0 &&& carryV) ∧
      s'.vg.lane .xmm6 0 = gfv ∧ s'.vg.lane .xmm6 1 = gfv := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · run_block [static_carry, static_gfpoly]
    rfl
  · refine ⟨by keeps, by simp only [vexec_mem, setV_mem], ?_, ?_, ?_⟩
    · lanes
    · lanes
    · lanes

/-- All but the load of `head` multiply `xmm3` by `x`. -/
theorem key_run (s : S) :
    ∃ s', execBlock I (Rind.X86_64.GcmInitAvx2.head.drop 1) s = some (s', [.addr 0, .addr 0]) ∧
      Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧ s'.vg.lane .xmm3 0 = skBV (s.vg.lane .xmm3 0) ∧
      s'.vg.lane .xmm6 0 = gfv ∧ s'.vg.lane .xmm6 1 = gfv := by
  obtain ⟨s₁, x₁, k₁, m₁, a₁, b₁, -⟩ := shift_run s
  obtain ⟨s₂, x₂, k₂, m₂, a₂, g₀, g₁⟩ := mask_run s₁
  refine ⟨s₂, execBlock_app x₁ x₂, k₁.trans k₂, m₂.trans m₁, ?_, g₀, g₁⟩
  rw [a₂, a₁, b₁]
  exact head_eq _

/-- `head` leaves H^1 in `xmm3` and `gfpoly` in both lanes of `ymm6`. -/
theorem head_run (s : S) (h : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .rsi) 16) :
    ∃ s', execBlock I Rind.X86_64.GcmInitAvx2.head s = some (s', [.addr (s.vg.gpr .rsi), .addr 0, .addr 0]) ∧
      Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧ s'.vg.lane .xmm3 0 = pw (key s) 1 ∧ s'.vg.lane .xmm6 0 = gfv ∧
      s'.vg.lane .xmm6 1 = gfv := by
  obtain ⟨s₁, x₁, k₁, m₁, a₁⟩ := load_run s h
  obtain ⟨s₂, x₂, k₂, m₂, a₂, g₀, g₁⟩ := key_run s₁
  refine ⟨s₂, execBlock_app x₁ x₂, k₁.trans k₂, m₂.trans m₁, ?_, g₀, g₁⟩
  rw [a₂, a₁]
  rfl

/-- `square` leaves H^1's square in `xmm5`. -/
theorem square_run (s : S) (g0 : s.vg.lane .xmm6 0 = gfv) :
    ∃ s', execBlock I Rind.X86_64.GcmInitAvx2.square s = some (s', []) ∧ Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧
      s'.vg.lane .xmm5 0 = mulModel (s.vg.lane .xmm3 0) (s.vg.lane .xmm3 0) ∧
      ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm5 → ∀ i, s'.vg.lane r i = s.vg.lane r i := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · simp only [Rind.X86_64.GcmInitAvx2.square]
    run_block
    rfl
  · refine ⟨by keeps, by simp only [vexec_mem, setV_mem], ?_, ?_⟩
    · lanes [g0]
      exact square_eq _
    · intro r h0 h1 h5 i
      lanes [h0, h1, h5]

/-- The two `vinserti128`s pair H^2 with H^1 in `ymm3` and with itself in `ymm5`. -/
theorem ins_run (s : S) :
    ∃ s', execBlock I [Rind.X86_64.GcmInitAvx2.vop (.vinserti128 .xmm3 .xmm5 .xmm3 1),
        Rind.X86_64.GcmInitAvx2.vop (.vinserti128 .xmm5 .xmm5 .xmm5 1)] s = some (s', []) ∧
      Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧
      s'.vg.lane .xmm3 0 = s.vg.lane .xmm5 0 ∧ s'.vg.lane .xmm3 1 = s.vg.lane .xmm3 0 ∧
      s'.vg.lane .xmm5 0 = s.vg.lane .xmm5 0 ∧ s'.vg.lane .xmm5 1 = s.vg.lane .xmm5 0 ∧
      ∀ r, r ≠ .xmm3 → r ≠ .xmm5 → ∀ i, s'.vg.lane r i = s.vg.lane r i := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · run_block
    rfl
  · refine ⟨by keeps, by simp only [vexec_mem, setV_mem], ?_, ?_, ?_, ?_, ?_⟩
    · lanes
    · lanes
    · lanes
    · lanes
    · intro r h3 h5 i
      lanes [h3, h5]

/-- `mul a b d` leaves each lane of `d` the `mulModel` product of those of `a` and `b`. -/
theorem mul_run (s : S) {a b d : XReg}
    (ha0 : a ≠ .xmm0) (ha1 : a ≠ .xmm1) (ha2 : a ≠ .xmm2) (hb0 : b ≠ .xmm0) (hb1 : b ≠ .xmm1)
    (hb2 : b ≠ .xmm2) (hd0 : d ≠ .xmm0) (hd1 : d ≠ .xmm1) (hd6 : d ≠ .xmm6)
    (g0 : s.vg.lane .xmm6 0 = gfv) (g1 : s.vg.lane .xmm6 1 = gfv) :
    ∃ s', execBlock I (Rind.X86_64.GcmInitAvx2.mul a b d) s = some (s', []) ∧ Keeps s s' ∧ s'.vg.mem = s.vg.mem ∧
      s'.vg.lane d 0 = mulModel (s.vg.lane a 0) (s.vg.lane b 0) ∧
      s'.vg.lane d 1 = mulModel (s.vg.lane a 1) (s.vg.lane b 1) ∧
      ∀ r, r ≠ d → r ≠ .xmm0 → r ≠ .xmm1 → r ≠ .xmm2 → ∀ i, s'.vg.lane r i = s.vg.lane r i := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · simp only [Rind.X86_64.GcmInitAvx2.mul]
    run_block
    rfl
  · refine ⟨by keeps, by simp only [vexec_mem, setV_mem], ?_, ?_, ?_⟩
    · lanes [g0, ha0, ha1, ha2, hb0, hb1, hb2, hd0, hd1, hd6]
      exact lane_mul _ _
    · lanes [g1, ha0, ha1, ha2, hb0, hb1, hb2, hd0, hd1, hd6]
      exact lane_mul _ _
    · intro r hd h0 h1 h2 i
      lanes [hd, h0, h1, h2]

/-- A Karatsuba word pair: `x`'s halves XORed, then `y`'s. -/
def kv (x y : BitVec 128) : BitVec 128 := (lo y ++ lo x) ^^^ (hi y ++ hi x)

theorem lo_kv (x y : BitVec 128) : lo (kv x y) = lo x ^^^ hi x := by rw [kv, lo_xor, lo_append, lo_append]
theorem hi_kv (x y : BitVec 128) : hi (kv x y) = lo y ^^^ hi y := by rw [kv, hi_xor, hi_append, hi_append]

/-- `karatsuba d` stores the halves of `ymm4`'s and `ymm3`'s blocks XORed to `[rdi + d]`. -/
theorem kara_run (s : S) (d : Int) (h : InRegions s.vg.wr (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d)) 32) :
    ∃ s', execBlock I (Rind.X86_64.GcmInitAvx2.karatsuba d) s =
        some (s', [.addr (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d))]) ∧ Keeps s s' ∧
      s'.vg.mem = s.vg.mem.writeW (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d))
        (kv (s.vg.lane .xmm4 1) (s.vg.lane .xmm3 1) ++ kv (s.vg.lane .xmm4 0) (s.vg.lane .xmm3 0)) ∧
      ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → ∀ i, s'.vg.lane r i = s.vg.lane r i := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · simp only [Rind.X86_64.GcmInitAvx2.karatsuba]
    run_block [store256_of, vexec_wr, vexec_ea, h]
    rfl
  · refine ⟨by keeps, ?_, ?_⟩
    · simp only [mem_setMem', vexec_mem, vexec_ea, ymm_lane]
      congr 1
    · intro r h0 h1 i
      lanes [h0, h1]

/-- Two 256-bit stores. -/
theorem stores_run (s : S) (d₁ d₂ : Int) (r₁ r₂ : XReg)
    (h₁ : InRegions s.vg.wr (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d₁)) 32)
    (h₂ : InRegions s.vg.wr (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d₂)) 32) :
    ∃ s', execBlock I [.vg (.vmovdquStore .l256 (Rind.X86_64.GcmInitAvx2.at_ d₁) r₁),
        .vg (.vmovdquStore .l256 (Rind.X86_64.GcmInitAvx2.at_ d₂) r₂)] s =
        some (s', [.addr (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d₁)), .addr (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d₂))]) ∧
      Keeps s s' ∧
      s'.vg.mem = (s.vg.mem.writeW (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d₁)) (s.vg.ymm r₁)).writeW
          (s.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d₂)) (s.vg.ymm r₂) ∧
      ∀ r i, s'.vg.lane r i = s.vg.lane r i := by
  refine ⟨?_, ?_, ?_⟩
  pick_goal 2
  · run_block [store256_of _ h₁, store256_setMem _ _ h₂, ea_setMem, ymm_setMem, mem_setMem']
    rfl
  · refine ⟨by keeps, by simp only [mem_setMem', ea_setMem, ymm_setMem], fun r i => by simp only [lane_setMem]⟩

/-- `vzeroupper` changes only the vector registers. -/
theorem vzu_run (s : S) :
    ∃ s', execBlock I [Rind.X86_64.GcmInitAvx2.vop .vzeroupper] s = some (s', []) ∧ Keeps s s' ∧
      s'.vg.mem = s.vg.mem := by
  refine ⟨?_, ?_, ?_, ?_⟩
  pick_goal 2
  · run_block
    rfl
  · keeps
  · simp only [vexec_mem]


/-! ## The table -/

theorem getLsbD_read (m : Mem) : ∀ (n : Nat) (a : Addr) (i : Nat), i < 8 * n →
    (m.read a n).getLsbD i = (m (a + BitVec.ofNat 64 (i / 8))).getLsbD (i % 8)
  | 0, _, _, h => absurd h (by omega)
  | n + 1, a, i, h => by
    rw [Mem.read, BitVec.getLsbD_append]
    by_cases hi : i < 8
    · rw [ite_eq_left hi, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]; simp
    · rw [ite_eq_right hi, getLsbD_read m n (a + 1) (i - 8) (by omega)]
      have e : a + 1 + BitVec.ofNat 64 ((i - 8) / 8) = a + BitVec.ofNat 64 (i / 8) := by
        rw [BitVec.add_assoc]; congr 1
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e, show (i - 8) % 8 = i % 8 by omega]

/-- A read inside a 256-bit write, both from `x`, reads the written bits. -/
theorem readW_sub (m : Mem) (x : Addr) (c d : Nat) (v : BitVec 256) (w' : Nat) (hw' : w' % 8 = 0)
    (hd : d ≤ c) (h : 8 * (c - d) + w' ≤ 256) (hc : c ≤ 512) :
    (m.writeW (x + BitVec.ofNat 64 d) v).readW (x + BitVec.ofNat 64 c) w' = v.extractLsb' (8 * (c - d)) w' := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Mem.readW, Mem.writeW, BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb', hi, decide_true,
    Bool.true_and]
  rw [getLsbD_read _ _ _ _ (by omega)]
  simp only [Mem.write]
  have e : (x + BitVec.ofNat 64 c + BitVec.ofNat 64 (i / 8) - (x + BitVec.ofNat 64 d)).toNat = c - d + i / 8 := by
    have : i / 8 < 32 := by omega
    bv_omega
  rw [e, ite_eq_left (by omega)]
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_setWidth]
  rw [show 8 * (c - d + i / 8) + i % 8 = 8 * (c - d) + i by omega]
  simp only [show i % 8 < 8 by omega, show 8 * (c - d) + i < 8 * (256 / 8) by omega, decide_true, Bool.true_and]

/-- A read apart from a write, both from `x`, reads what was there. -/
theorem readW_far (m : Mem) (x : Addr) (c d : Nat) {w : Nat} (v : BitVec w) (w' : Nat)
    (h : c + w' / 8 ≤ d ∨ d + w / 8 ≤ c) (hc : c ≤ 512) (hd : d ≤ 512) (hw : 8 ≤ w ∧ w ≤ 512)
    (hw' : 8 ≤ w' ∧ w' ≤ 512) :
    (m.writeW (x + BitVec.ofNat 64 d) v).readW (x + BitVec.ofNat 64 c) w' = m.readW (x + BitVec.ofNat 64 c) w' :=
  readW_writeW_disj _ _ _ _ _ (by constructor <;> rcases h with h | h <;> bv_omega)

theorem writeW_other (m : Mem) (a : Addr) {w : Nat} (v : BitVec w) (y : Addr) (h : w / 8 ≤ (y - a).toNat) :
    m.writeW a v y = m y :=
  write_other _ _ _ _ _ h

set_option maxHeartbeats 1000000 in
theorem ext_lo128 (x y : BitVec 128) : (x ++ y).extractLsb' 0 128 = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases i <;> simp
set_option maxHeartbeats 1000000 in
theorem ext_hi128 (x y : BitVec 128) : (x ++ y).extractLsb' 128 128 = x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases i <;> simp
set_option maxHeartbeats 1000000 in
theorem ext_q0 (x y : BitVec 128) : (x ++ y).extractLsb' 0 64 = lo y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  simp only [lo, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases i <;> simp
set_option maxHeartbeats 1000000 in
theorem ext_q1 (x y : BitVec 128) : (x ++ y).extractLsb' 64 64 = hi y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  simp only [hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases i <;> simp
set_option maxHeartbeats 1000000 in
theorem ext_q2 (x y : BitVec 128) : (x ++ y).extractLsb' 128 64 = lo x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  simp only [lo, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases i <;> simp
set_option maxHeartbeats 1000000 in
theorem ext_q3 (x y : BitVec 128) : (x ++ y).extractLsb' 192 64 = hi x := by
  apply BitVec.eq_of_getLsbD_eq; intro i hlt
  simp only [hi, BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  interval_cases i <;> simp

theorem inR_at (g : G) (d : Int) (n : Nat) (hw : (⟨g.gpr .rdi, 256⟩ : Region) ∈ g.wr) (h : d = n)
    (hn : n + 32 ≤ 256) : InRegions g.wr (g.ea (Rind.X86_64.GcmInitAvx2.at_ d)) 32 := by
  subst h
  refine ⟨_, hw, ?_⟩
  show ((g.gpr .rdi + BitVec.ofInt 64 (n : Int)) - g.gpr .rdi).toNat + 32 ≤ 256
  rw [add_sub_left, BitVec.ofInt_natCast, BitVec.toNat_ofNat]
  simp only [Nat.reducePow]
  omega

theorem ea_K {s s' : S} (k : Keeps s s') (d : Int) :
    s'.vg.ea (Rind.X86_64.GcmInitAvx2.at_ d) = s.vg.gpr .rdi + BitVec.ofInt 64 d := by
  show s'.vg.gpr .rdi + BitVec.ofInt 64 d = _
  rw [k.gpr]

/-! ## The routine -/

/-- The theorem's hypotheses, `Htable = rdi` and `H = rsi`: the routine may read the key's 16 bytes and write the
table's 256, and the return address lies outside the table. -/
structure Pre (s : S) : Prop where
  rd : ⟨s.vg.gpr .rsi, 16⟩ ∈ s.vg.rd
  wr : ⟨s.vg.gpr .rdi, 256⟩ ∈ s.vg.wr
  ret : ∀ c < 8, 256 ≤ (s.vg.gpr .rsp + BitVec.ofNat 64 c - s.vg.gpr .rdi).toNat

/-- The block whose halves XORed the table's word `j` past its 128 bytes of powers holds: BoringSSL's order for
its 256-bit Karatsuba multiplies. -/
def karaBlock : Nat → Nat
  | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3 | 4 => 4 | 5 => 6 | 6 => 5 | _ => 7

/-- What the routine ensures: the table's block `i` is H^(8-i), each shifted, for the key `H` at `rsi`; its next
64 bytes are each block's halves XORed, in `karaBlock`'s order; memory from the table's byte 192 on is unchanged;
and so are the general registers, what the System V ABI makes the callee keep, and the regions. -/
structure Post (s s' : S) : Prop where
  pow : ∀ i < 8, toPoly (s'.vg.mem.readW (s.vg.gpr .rdi + BitVec.ofNat 64 (16 * i)) 128) =
    shiftKey1 128 gf128ModulusLowTerms (gPower (toPoly (key s)) (8 - i))
  kara : ∀ j < 8, s'.vg.mem.readW (s.vg.gpr .rdi + BitVec.ofNat 64 (128 + 8 * j)) 64 =
    lo (s'.vg.mem.readW (s.vg.gpr .rdi + BitVec.ofNat 64 (16 * karaBlock j)) 128) ^^^
      hi (s'.vg.mem.readW (s.vg.gpr .rdi + BitVec.ofNat 64 (16 * karaBlock j)) 128)
  mem : ∀ y, 192 ≤ (y - s.vg.gpr .rdi).toNat → s'.vg.mem y = s.vg.mem y
  gpr : s'.vg.gpr = s.vg.gpr
  abi : abiPreserved s.vg s'.vg
  rd : s'.vg.rd = s.vg.rd
  wr : s'.vg.wr = s.vg.wr

/-- What is public: the arguments. The key is not. -/
def Pub (s₁ s₂ : S) : Prop := s₁.vg.gpr .rdi = s₂.vg.gpr .rdi ∧ s₁.vg.gpr .rsi = s₂.vg.gpr .rsi

/-- The routine's trace: the key's address, the two statics' offsets, and the table's six stores. -/
def trace (s : S) : List Leak :=
  let t (d : Nat) : Leak := .addr (s.vg.gpr .rdi + BitVec.ofNat 64 d)
  [.addr (s.vg.gpr .rsi), .addr 0, .addr 0, t 96, t 64, t 160, t 32, t 0, t 128]

theorem pw_3 (h : BitVec 128) : pw h 3 = mulModel (pw h 1) (pw h 2) := pw_succ h 0
theorem pw_4 (h : BitVec 128) : pw h 4 = mulModel (pw h 2) (pw h 2) := pw_succ h 1
theorem pw_5 (h : BitVec 128) : pw h 5 = mulModel (pw h 3) (pw h 2) := pw_succ h 2
theorem pw_6 (h : BitVec 128) : pw h 6 = mulModel (pw h 4) (pw h 2) := pw_succ h 3
theorem pw_7 (h : BitVec 128) : pw h 7 = mulModel (pw h 5) (pw h 2) := pw_succ h 4
theorem pw_8 (h : BitVec 128) : pw h 8 = mulModel (pw h 6) (pw h 2) := pw_succ h 5

set_option maxHeartbeats 4000000 in
theorem correct (s : S) (h : Pre s) : ∃ s', Exec I Rind.X86_64.GcmInitAvx2.prog s (trace s) s' ∧ Post s s' := by
  obtain ⟨hrd, hwr, hret⟩ := h
  have hrsi : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .rsi) 16 :=
    ⟨_, List.mem_append_left _ hrd, by simp [Region.Contains]⟩
  have hw : ∀ s' : S, Keeps s s' → (⟨s'.vg.gpr .rdi, 256⟩ : Region) ∈ s'.vg.wr := fun s' k => by
    rw [k.gpr, k.wr]; exact hwr
  -- H^1 in `xmm3`, and `gfpoly` in `ymm6`.
  obtain ⟨s₁, x₁, k₁, m₁, a₁, g₁₀, g₁₁⟩ := head_run s hrsi
  -- H^2 in `xmm5`.
  obtain ⟨s₂, x₂, k₂, m₂, a₂, o₂⟩ := square_run s₁ g₁₀
  have e₂30 : s₂.vg.lane .xmm3 0 = pw (key s) 1 := (o₂ .xmm3 (by decide) (by decide) (by decide) 0).trans a₁
  have e₂50 : s₂.vg.lane .xmm5 0 = pw (key s) 2 := by rw [a₂, a₁]; exact (pw_two _).symm
  have e₂60 := (o₂ .xmm6 (by decide) (by decide) (by decide) 0).trans g₁₀
  have e₂61 := (o₂ .xmm6 (by decide) (by decide) (by decide) 1).trans g₁₁
  -- `[H^2, H^1]` in `ymm3` and `[H^2, H^2]` in `ymm5`.
  obtain ⟨s₃, x₃, k₃, m₃, a₃0, a₃1, b₃0, b₃1, o₃⟩ := ins_run s₂
  have e₃30 : s₃.vg.lane .xmm3 0 = pw (key s) 2 := a₃0.trans e₂50
  have e₃31 : s₃.vg.lane .xmm3 1 = pw (key s) 1 := a₃1.trans e₂30
  have e₃50 : s₃.vg.lane .xmm5 0 = pw (key s) 2 := b₃0.trans e₂50
  have e₃51 : s₃.vg.lane .xmm5 1 = pw (key s) 2 := b₃1.trans e₂50
  have e₃60 := (o₃ .xmm6 (by decide) (by decide) 0).trans e₂60
  have e₃61 := (o₃ .xmm6 (by decide) (by decide) 1).trans e₂61
  -- `[H^4, H^3]` in `ymm4`.
  obtain ⟨s₄, x₄, k₄, m₄, d₄0, d₄1, o₄⟩ := mul_run s₃ (a := .xmm3) (b := .xmm5) (d := .xmm4) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    e₃60 e₃61
  have e₄40 : s₄.vg.lane .xmm4 0 = pw (key s) 4 := by rw [d₄0, e₃30, e₃50]; exact (pw_4 _).symm
  have e₄41 : s₄.vg.lane .xmm4 1 = pw (key s) 3 := by rw [d₄1, e₃31, e₃51]; exact (pw_3 _).symm
  have e₄30 := (o₄ .xmm3 (by decide) (by decide) (by decide) (by decide) 0).trans e₃30
  have e₄31 := (o₄ .xmm3 (by decide) (by decide) (by decide) (by decide) 1).trans e₃31
  have e₄50 := (o₄ .xmm5 (by decide) (by decide) (by decide) (by decide) 0).trans e₃50
  have e₄51 := (o₄ .xmm5 (by decide) (by decide) (by decide) (by decide) 1).trans e₃51
  have e₄60 := (o₄ .xmm6 (by decide) (by decide) (by decide) (by decide) 0).trans e₃60
  have e₄61 := (o₄ .xmm6 (by decide) (by decide) (by decide) (by decide) 1).trans e₃61
  have K₄ := k₁.trans (k₂.trans (k₃.trans k₄))
  -- Their stores and Karatsuba words.
  obtain ⟨s₅, x₅, k₅, m₅, o₅⟩ := stores_run s₄ 96 64 .xmm3 .xmm4 (inR_at _ 96 96 (hw _ K₄) rfl (by norm_num))
    (inR_at _ 64 64 (hw _ K₄) rfl (by norm_num))
  have K₅ := K₄.trans k₅
  obtain ⟨s₆, x₆, k₆, m₆, o₆⟩ := kara_run s₅ 160 (inR_at _ 160 160 (hw _ K₅) rfl (by norm_num))
  have K₆ := K₅.trans k₆
  have e₆ : ∀ r, r ≠ .xmm0 → r ≠ .xmm1 → ∀ i, s₆.vg.lane r i = s₄.vg.lane r i := fun r h0 h1 i =>
    (o₆ r h0 h1 i).trans (o₅ r i)
  -- `[H^6, H^5]` in `ymm3`.
  obtain ⟨s₇, x₇, k₇, m₇, d₇0, d₇1, o₇⟩ := mul_run s₆ (a := .xmm4) (b := .xmm5) (d := .xmm3) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((e₆ .xmm6 (by decide) (by decide) 0).trans e₄60) ((e₆ .xmm6 (by decide) (by decide) 1).trans e₄61)
  have e₇30 : s₇.vg.lane .xmm3 0 = pw (key s) 6 := by
    rw [d₇0, e₆ .xmm4 (by decide) (by decide), e₆ .xmm5 (by decide) (by decide), e₄40, e₄50]
    exact (pw_6 _).symm
  have e₇31 : s₇.vg.lane .xmm3 1 = pw (key s) 5 := by
    rw [d₇1, e₆ .xmm4 (by decide) (by decide), e₆ .xmm5 (by decide) (by decide), e₄41, e₄51]
    exact (pw_5 _).symm
  have e₇5 : ∀ i, s₇.vg.lane .xmm5 i = s₄.vg.lane .xmm5 i := fun i =>
    (o₇ .xmm5 (by decide) (by decide) (by decide) (by decide) i).trans (e₆ .xmm5 (by decide) (by decide) i)
  have e₇6 : ∀ i, s₇.vg.lane .xmm6 i = s₄.vg.lane .xmm6 i := fun i =>
    (o₇ .xmm6 (by decide) (by decide) (by decide) (by decide) i).trans (e₆ .xmm6 (by decide) (by decide) i)
  -- `[H^8, H^7]` in `ymm4`.
  obtain ⟨s₈, x₈, k₈, m₈, d₈0, d₈1, o₈⟩ := mul_run s₇ (a := .xmm3) (b := .xmm5) (d := .xmm4) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    ((e₇6 0).trans e₄60) ((e₇6 1).trans e₄61)
  have e₈40 : s₈.vg.lane .xmm4 0 = pw (key s) 8 := by
    rw [d₈0, e₇30, e₇5, e₄50]; exact (pw_8 _).symm
  have e₈41 : s₈.vg.lane .xmm4 1 = pw (key s) 7 := by
    rw [d₈1, e₇31, e₇5, e₄51]; exact (pw_7 _).symm
  have e₈30 := (o₈ .xmm3 (by decide) (by decide) (by decide) (by decide) 0).trans e₇30
  have e₈31 := (o₈ .xmm3 (by decide) (by decide) (by decide) (by decide) 1).trans e₇31
  have K₈ := K₆.trans (k₇.trans k₈)
  -- Their stores and Karatsuba words.
  obtain ⟨s₉, x₉, k₉, m₉, o₉⟩ := stores_run s₈ 32 0 .xmm3 .xmm4 (inR_at _ 32 32 (hw _ K₈) rfl (by norm_num))
    (inR_at _ 0 0 (hw _ K₈) rfl (by norm_num))
  have K₉ := K₈.trans k₉
  obtain ⟨s₁₀, x₁₀, k₁₀, m₁₀, -⟩ := kara_run s₉ 128 (inR_at _ 128 128 (hw _ K₉) rfl (by norm_num))
  obtain ⟨s₁₁, x₁₁, k₁₁, m₁₁⟩ := vzu_run s₁₀
  have K := K₉.trans (k₁₀.trans k₁₁)
  -- The table.
  have hM : s₁₁.vg.mem =
      (((((s.vg.mem.writeW (s.vg.gpr .rdi + BitVec.ofNat 64 96) (pw (key s) 1 ++ pw (key s) 2)).writeW
        (s.vg.gpr .rdi + BitVec.ofNat 64 64) (pw (key s) 3 ++ pw (key s) 4)).writeW
        (s.vg.gpr .rdi + BitVec.ofNat 64 160) (kv (pw (key s) 3) (pw (key s) 1) ++ kv (pw (key s) 4) (pw (key s) 2))).writeW
        (s.vg.gpr .rdi + BitVec.ofNat 64 32) (pw (key s) 5 ++ pw (key s) 6)).writeW
        (s.vg.gpr .rdi + BitVec.ofNat 64 0) (pw (key s) 7 ++ pw (key s) 8)).writeW
        (s.vg.gpr .rdi + BitVec.ofNat 64 128) (kv (pw (key s) 7) (pw (key s) 5) ++ kv (pw (key s) 8) (pw (key s) 6)) := by
    rw [m₁₁, m₁₀, m₉, m₈, m₇, m₆, m₅, m₄, m₃, m₂, m₁, ea_K K₉, ea_K K₈, ea_K K₈, ea_K K₅, ea_K K₄, ea_K K₄]
    simp only [ymm_lane, o₉, o₅, e₈30, e₈31, e₈40, e₈41, e₄30, e₄31, e₄40, e₄41, BitVec.ofInt_ofNat]
  have hmem : ∀ y, 192 ≤ (y - s.vg.gpr .rdi).toNat → s₁₁.vg.mem y = s.vg.mem y := by
    intro y hy
    rw [hM]
    repeat rw [writeW_other _ _ _ _ (by bv_omega)]
  have hx := execBlock_app (execBlock_app x₁ x₂) (execBlock_app (execBlock_app (execBlock_app (execBlock_app
    (execBlock_app (execBlock_app (execBlock_app (execBlock_app x₃ x₄) x₅) x₆) x₇) x₈) x₉) x₁₀) x₁₁)
  refine ⟨s₁₁, Exec.block (hx.trans ?_), ?_, ?_, hmem, K.gpr, ⟨fun r _ => by rw [K.gpr], ?_, by rw [K.mxcsr]⟩,
    K.rd, K.wr⟩
  · simp only [ea_K K₄, ea_K K₅, ea_K K₈, ea_K K₉, BitVec.ofInt_ofNat, List.append_nil, List.nil_append,
      List.cons_append, trace]
  · intro i hi
    rw [hM]
    interval_cases i <;>
      simp (disch := omega) only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, readW_far, readW_sub, ext_lo128,
        ext_hi128] <;>
      exact pw_spec _ _ (by norm_num)
  · intro j hj
    rw [hM]
    interval_cases j <;>
      simp (disch := omega) only [karaBlock, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, readW_far, readW_sub,
        ext_lo128, ext_hi128, ext_q0, ext_q1, ext_q2, ext_q3, lo_kv, hi_kv]
  · simp only [Mem.readW]
    congr 1
    apply read_congr
    intro c hc
    exact hmem _ (le_trans (by norm_num) (hret c (by omega)))

theorem constant_time : ConstantTime I Pre Pub Rind.X86_64.GcmInitAvx2.prog := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨e0, e1⟩ x₁ x₂
  obtain ⟨_, y₁, -⟩ := correct s₁ h₁
  obtain ⟨_, y₂, -⟩ := correct s₂ h₂
  rw [(exec_det x₁ y₁).1, (exec_det x₂ y₂).1]
  simp only [trace, e0, e1]

/-! ## The precondition holds of some state -/

/-- A state the precondition holds of: the table at `0x10000`, the key at `0x20000`, and the stack pointer at
`0x30000`. -/
def witness : S where
  vg := { gpr := fun r => if r = .rdi then 0x10000#64 else if r = .rsi then 0x20000#64
            else if r = .rsp then 0x30000#64 else 0,
          cf := none, zf := none, sf := none, of := none,
          mem := fun _ => 0,
          rd := [⟨0x20000#64, 16⟩],
          wr := [⟨0x10000#64, 256⟩] }
  lo := 0

theorem pre_witness : Pre witness := ⟨by decide, by decide, by decide⟩

/-- The routine writes the key's powers H^8 down to H^1 and their Karatsuba words to the table, changing nothing
else the System V ABI or its caller relies on; its trace depends only on its arguments; and some state meets its
precondition. -/
theorem gcm_init_vpclmulqdq_avx2_correct :
    (∀ s, Pre s → ∃ t s', Exec I Rind.X86_64.GcmInitAvx2.prog s t s' ∧ Post s s') ∧
      ConstantTime I Pre Pub Rind.X86_64.GcmInitAvx2.prog ∧ ∃ s, Pre s :=
  ⟨fun s h => let ⟨s', e, p⟩ := correct s h; ⟨_, s', e, p⟩, constant_time, _, pre_witness⟩

end rind.x86_64.gcm_init_avx2

/-- info: 'rind.x86_64.gcm_init_avx2.gcm_init_vpclmulqdq_avx2_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.x86_64.gcm_init_avx2.gcm_init_vpclmulqdq_avx2_correct
