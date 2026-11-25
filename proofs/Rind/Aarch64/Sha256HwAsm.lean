import RindIsa.AArch64.Sha256Hw
import VerifiedGarbage.TCB.AArch64.Target
import Rind.S2nSha256
import Rind.VgPbkdf2
import Mathlib.Tactic.IntervalCases

open VG VG.AArch64 Rind.AArch64 Rind.AArch64.Sha256Hw rind.spec

/-!
# aws-lc's SHA-256 block function for the SHA-2 instructions, proven

`sha256_block_data_order_hw_correct`: the routine
`RindIsa/AArch64/Sha256Hw.lean` gives as `prog`, which `admin/prove lean`
checks is the machine code of rind's naked function
`low::aarch64::sha256::sha256_block_data_order_hw` as rind's Linux release
build emits it, run in rind's extension of VG's AArch64 model
(`RindIsa/AArch64.lean`) from a state `Pre` holds of, terminates in one that
`Post` relates it to: the state's eight words become s2n-bignum's
`sha256_hash_blocks` of the blocks, as `SHA256_HW_SUBROUTINE_CORRECT`, the
HOL Light theorem this replaces, had it; nothing changes but the state, the
16 bytes below the stack pointer, and registers AAPCS64 lets a callee
change; and the return address `x30`, the stack pointer, and `x29` are as
they were, so the `ret` the function ends with returns to the caller. Its
trace of addresses and branches is a function of the arguments, the stack
pointer, and the table's address alone (`ConstantTime`, with `Pub`), and some
state meets `Pre`.

The proof runs the sixteen groups of four rounds symbolically
(`group_ok`), shows each computes four of FIPS 180-4's rounds and schedule
words as s2n-bignum's spec states them (`rounds_eq`, `schedule_eq`), and
inducts over the groups and then the blocks. Every theorem rests only on
Lean's three axioms: `bv_decide` here proves its goals in its
preprocessing, never reaching the SAT solver whose certificate check runs
native code.
-/


namespace rind.aarch64.sha256hw

/-! ## Lanes -/

@[simp] theorem vword_ofVWords_0 (a b c d : BitVec 32) : vword (ofVWords a b c d) 0 = a := by
  simp only [vword, ofVWords]; bv_decide
@[simp] theorem vword_ofVWords_1 (a b c d : BitVec 32) : vword (ofVWords a b c d) 1 = b := by
  simp only [vword, ofVWords]; bv_decide
@[simp] theorem vword_ofVWords_2 (a b c d : BitVec 32) : vword (ofVWords a b c d) 2 = c := by
  simp only [vword, ofVWords]; bv_decide
@[simp] theorem vword_ofVWords_3 (a b c d : BitVec 32) : vword (ofVWords a b c d) 3 = d := by
  simp only [vword, ofVWords]; bv_decide

/-! ## The SHA-256 instructions as rounds and schedule -/

/-- The first four words of a hash state, as `v0` holds them. -/
def abcd (l : List (BitVec 32)) : BitVec 128 := ofVWords l[0]! l[1]! l[2]! l[3]!
/-- The last four. -/
def efgh (l : List (BitVec 32)) : BitVec 128 := ofVWords l[4]! l[5]! l[6]! l[7]!
/-- Words `4i` to `4i + 3` of `f`. -/
def quad (f : Nat → BitVec 32) (i : Nat) : BitVec 128 :=
  ofVWords (f (4 * i)) (f (4 * i + 1)) (f (4 * i + 2)) (f (4 * i + 3))

theorem step_eq (l : List (BitVec 32)) (k w : BitVec 32) :
    sha256Step (k + w) (abcd l, efgh l) = (abcd (s2n.round l k w), efgh (s2n.round l k w)) := by
  simp only [sha256Step, abcd, efgh, s2n.round, vword_ofVWords_0, vword_ofVWords_1,
    vword_ofVWords_2, vword_ofVWords_3, List.getElem!_cons_zero, List.getElem!_cons_succ]
  simp only [shaChoose, shaMajority, shaHashSigma0, shaHashSigma1, s2n.choose, s2n.maj,
    s2n.hashSigma0, s2n.hashSigma1, BitVec.xor_assoc, Prod.mk.injEq]
  constructor <;> congr 1 <;> ac_rfl

theorem map2_add (x y : BitVec 128) :
    VArr.s4.map2 (fun _ a b => a + b) x y =
      ofVWords (vword x 0 + vword y 0) (vword x 1 + vword y 1) (vword x 2 + vword y 2)
        (vword x 3 + vword y 3) := rfl

/-- SHA256H and SHA256H2 run four rounds. -/
theorem hash_eq (l : List (BitVec 32)) (k0 k1 k2 k3 w0 w1 w2 w3 : BitVec 32) (b : Bool) :
    sha256Hash (abcd l) (efgh l) (ofVWords (k0 + w0) (k1 + w1) (k2 + w2) (k3 + w3)) b =
      let l4 := s2n.round (s2n.round (s2n.round (s2n.round l k0 w0) k1 w1) k2 w2) k3 w3
      if b then abcd l4 else efgh l4 := by
  simp only [sha256Hash, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3, step_eq]

/-- Rounds `4i` to `4i + 3` of block `M` from `H`. -/
theorem rounds_eq (M H : List (BitVec 32)) (i : Nat) (b : Bool) :
    sha256Hash (abcd (s2n.compressRounds M H (4 * i))) (efgh (s2n.compressRounds M H (4 * i)))
      (VArr.s4.map2 (fun _ a b => a + b) (quad (fun t => table[t]!) i) (quad (s2n.msgSchedule M) i)) b =
      if b then abcd (s2n.compressRounds M H (4 * (i + 1)))
      else efgh (s2n.compressRounds M H (4 * (i + 1))) := by
  rw [map2_add]
  simp only [quad, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3]
  rw [hash_eq]
  simp only [show 4 * (i + 1) = 4 * i + 3 + 1 by omega, s2n.compressRounds,
    show table = s2n.constants from rfl]

theorem W_add16 (M : List (BitVec 32)) (t : Nat) :
    s2n.msgSchedule M (t + 16) = sha256.smallSigma1 (s2n.msgSchedule M (t + 14)) +
      (sha256.smallSigma0 (s2n.msgSchedule M (t + 1)) + s2n.msgSchedule M t) +
      s2n.msgSchedule M (t + 9) := by
  rw [s2n.msgSchedule_add16]; ac_rfl

/-- SHA256SU0 and SHA256SU1 schedule four words. -/
theorem schedule_eq (M : List (BitVec 32)) (i : Nat) :
    sha256Su1 (sha256Su0 (quad (s2n.msgSchedule M) i) (quad (s2n.msgSchedule M) (i + 1)))
      (quad (s2n.msgSchedule M) (i + 2)) (quad (s2n.msgSchedule M) (i + 3)) =
      quad (s2n.msgSchedule M) (i + 4) := by
  simp only [sha256Su1, sha256Su0, quad, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2,
    vword_ofVWords_3]
  have w0 := W_add16 M (4 * i)
  have w1 := W_add16 M (4 * i + 1)
  have w2 := W_add16 M (4 * i + 2)
  have w3 := W_add16 M (4 * i + 3)
  simp only [sha256.smallSigma0, sha256.smallSigma1] at w0 w1 w2 w3
  simp only [show 4 * (i + 4) = 4 * i + 16 by omega, w0, w1, w2, w3]
  simp only [show 4 * i + 14 = 4 * (i + 3) + 2 by omega, show 4 * i + 1 + 14 = 4 * (i + 3) + 3 by omega,
    show 4 * i + 9 = 4 * (i + 2) + 1 by omega, show 4 * i + 1 + 9 = 4 * (i + 2) + 2 by omega,
    show 4 * i + 2 + 9 = 4 * (i + 2) + 3 by omega, show 4 * i + 3 + 9 = 4 * (i + 3) by omega,
    show 4 * i + 1 + 1 = 4 * i + 2 by omega, show 4 * i + 2 + 1 = 4 * i + 3 by omega,
    show 4 * i + 3 + 1 = 4 * (i + 1) by omega]

/-! ## Blocks of instructions -/

theorem execBlock_append (a b : List Rind.AArch64.Instr) (s : Rind.AArch64.State) :
    execBlock Rind.AArch64.isa (a ++ b) s = (execBlock Rind.AArch64.isa a s).bind fun p =>
      (execBlock Rind.AArch64.isa b p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction a generalizing s with
  | nil => simp [execBlock]
  | cons i a ih =>
    simp only [List.cons_append, execBlock]
    cases Rind.AArch64.exec i s with
    | none => rfl
    | some s₁ =>
      simp only [ih]
      cases execBlock Rind.AArch64.isa a s₁ <;> simp [Function.comp_def]

/-- Exec is deterministic. -/
theorem exec_det {M : ISA} {c : Prog M} {s t₁ s₁ t₂ s₂} (h₁ : Exec M c s t₁ s₁) (h₂ : Exec M c s t₂ s₂) :
    t₁ = t₂ ∧ s₁ = s₂ := by
  induction h₁ generalizing t₂ s₂ with
  | block h => cases h₂ with | block h' => rw [h] at h'; cases h'; exact ⟨rfl, rfl⟩
  | seq _ _ ih₁ ih₂ =>
    cases h₂ with
    | seq a b => obtain ⟨rfl, rfl⟩ := ih₁ a; obtain ⟨rfl, rfl⟩ := ih₂ b; exact ⟨rfl, rfl⟩
  | iteT hc _ ih =>
    cases h₂ with
    | iteT _ b => obtain ⟨rfl, rfl⟩ := ih b; exact ⟨rfl, rfl⟩
    | iteF hc' _ => rw [hc] at hc'; cases hc'
  | iteF hc _ ih =>
    cases h₂ with
    | iteT hc' _ => rw [hc] at hc'; cases hc'
    | iteF _ b => obtain ⟨rfl, rfl⟩ := ih b; exact ⟨rfl, rfl⟩
  | loopExit _ hc ih =>
    cases h₂ with
    | loopExit b _ => obtain ⟨rfl, rfl⟩ := ih b; exact ⟨rfl, rfl⟩
    | loopNext b hc' _ => obtain ⟨rfl, rfl⟩ := ih b; rw [hc] at hc'; cases hc'
  | loopNext _ hc _ ih ih' =>
    cases h₂ with
    | loopExit b hc' => obtain ⟨rfl, rfl⟩ := ih b; rw [hc] at hc'; cases hc'
    | loopNext b _ c => obtain ⟨rfl, rfl⟩ := ih b; obtain ⟨rfl, rfl⟩ := ih' c; exact ⟨rfl, rfl⟩
  | call hc _ hr ih =>
    cases h₂ with
    | call hc' b hr' =>
      rw [hc] at hc'; cases hc'; obtain ⟨rfl, rfl⟩ := ih b; rw [hr] at hr'; cases hr'; exact ⟨rfl, rfl⟩
  | frame hp _ hq ih =>
    cases h₂ with
    | frame hp' b hq' =>
      rw [hp] at hp'; cases hp'; obtain ⟨rfl, rfl⟩ := ih b; rw [hq] at hq'; cases hq'; exact ⟨rfl, rfl⟩
  | icall hi hc _ hr ih =>
    cases h₂ with
    | icall _ hc' b hr' =>
      rw [hc] at hc'; cases hc'; obtain ⟨rfl, rfl⟩ := ih b; rw [hr] at hr'; cases hr'; exact ⟨rfl, rfl⟩
    | icallNext hi' hne _ => rw [hi] at hi'; cases hi'; exact absurd rfl hne
  | icallNext hi hne _ ih =>
    cases h₂ with
    | icall hi' _ _ _ => rw [hi] at hi'; cases hi'; exact absurd rfl hne
    | icallNext _ _ b => exact ih b

/-! Memory -/

theorem read_congr (m m' : Mem) (a : Addr) (n : Nat)
    (h : ∀ k < n, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) : m'.read a n = m.read a n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Mem.read]
    have h0 := h 0 (by omega)
    simp only [BitVec.add_zero] at h0
    rw [h0, ih (a + 1) fun k hk => by
      have e : a + 1 + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (k + 1) := by
        apply BitVec.eq_of_toNat_eq; simp; omega
      rw [e]; exact h (k + 1) (by omega)]

theorem write_other (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (x : Addr)
    (h : n ≤ (x - a).toNat) : m.write a n v x = m x := by
  simp only [Mem.write]; rw [ite_eq_right_iff.mpr (by omega)]

theorem read4 (m : Mem) (a : Addr) : m.read a 4 = m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [Mem.read, BitVec.getLsbD_append, BitVec.add_assoc, BitVec.reduceAdd]
  split_ifs <;> first | rfl | omega

/-- Vectors are equal if their bytes are; `bv_decide` proves each byte's
equation in its preprocessing, without the SAT solver and its native code. -/
theorem ext_vbyte {x y : BitVec 128} (h : ∀ e < 16, vbyte x e = vbyte y e) : x = y := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun z => z.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [vbyte, BitVec.getLsbD_extractLsb'] at this
  rwa [show 8 * (i / 8) + i % 8 = i by omega, decide_eq_true (show i % 8 < 8 by omega), Bool.true_and,
    Bool.true_and] at this

theorem read16 (m : Mem) (a : Addr) :
    m.read a 16 = ofVWords (m.read a 4) (m.read (a + 4) 4) (m.read (a + 8) 4) (m.read (a + 12) 4) := by
  apply ext_vbyte; intro e he
  interval_cases e <;>
  · simp only [Mem.read, BitVec.add_assoc, BitVec.reduceAdd, ofVWords, vbyte]
    bv_decide

/-- The big-endian word at `a`. -/
def be (m : Mem) (a : Addr) : BitVec 32 := be32 (m a) (m (a + 1)) (m (a + 2)) (m (a + 3))

theorem rev32_read (m : Mem) (a : Addr) :
    VRevOp.eval .rev32b (m.read a 16) = ofVWords (be m a) (be m (a + 4)) (be m (a + 8)) (be m (a + 12)) := by
  apply ext_vbyte; intro e he
  interval_cases e <;>
  · simp only [VRevOp.eval, ofVBytes, vbyte, be, rind.spec.vg.be32_eq, Mem.read, BitVec.add_assoc,
      BitVec.reduceAdd, ofVWords, Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd]
    bv_decide

@[simp] theorem add_sub_left (a c : BitVec 64) : a + c - a = c := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

@[simp] theorem add_sub_add (a c d : BitVec 64) : a + c - (a + d) = c - d := by bv_omega
@[simp] theorem sub_add_self (a d : BitVec 64) : a - (a + d) = 0 - d := by bv_omega

theorem read_write8 (m : Mem) (a : Addr) (v : BitVec 64) : (m.write a 8 v).read a 8 = v := by
  simp only [Mem.read, Mem.write, BitVec.add_assoc, BitVec.reduceAdd, add_sub_left,
    BitVec.sub_self, BitVec.toNat_ofNat]
  simp only [BitVec.toNat_ofNat, Nat.reduceMul, BitVec.ofNat_eq_ofNat]
  bv_decide

/-! ## A group of four rounds -/

/-- What no instruction of a block changes, of VG's part of the state. -/
def others (g : VG.AArch64.State) :=
  (g.sp, g.c, g.nf, g.zf, g.vf, g.dit, g.mem, g.rd, g.wr, g.unknowns, g.syms)

/-- `s'` is `s` but for the vector registers `vs` and general ones `gs`. -/
structure Frame (s s' : Rind.AArch64.State) (vs : List VReg) (gs : List Reg) : Prop where
  v : ∀ r, r ∉ vs → s'.vg.v r = s.vg.v r
  gpr : ∀ r, r ∉ gs → s'.vg.gpr r = s.vg.gpr r
  others : others s'.vg = others s.vg
  x29 : s'.x29 = s.x29

@[simp] theorem setV_v (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) (r' : VReg) :
    (g.setV r x).v r' = if r' = r then x else g.v r' := rfl
@[simp] theorem setV_gpr (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) (r' : Reg) :
    (g.setV r x).gpr r' = g.gpr r' := rfl
@[simp] theorem setV_others (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) :
    others (g.setV r x) = others g := rfl
@[simp] theorem setV_mem (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) :
    (g.setV r x).mem = g.mem := rfl
@[simp] theorem setV_rd (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) :
    (g.setV r x).rd = g.rd := rfl
@[simp] theorem setV_wr (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) :
    (g.setV r x).wr = g.wr := rfl
@[simp] theorem write_v (g : VG.AArch64.State) (sz : Size) (r : Reg) (x : BitVec sz.bits) (r' : VReg) :
    (g.write sz r x).v r' = g.v r' := rfl
@[simp] theorem write_gpr (g : VG.AArch64.State) (r : Reg) (x : BitVec 64) (r' : Reg) :
    (g.write .x r x).gpr r' = if r' = r then x else g.gpr r' := by
  simp [VG.AArch64.State.write]
@[simp] theorem write_others (g : VG.AArch64.State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
    others (g.write sz r x) = others g := rfl
@[simp] theorem write_mem (g : VG.AArch64.State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
    (g.write sz r x).mem = g.mem := rfl
@[simp] theorem write_rd (g : VG.AArch64.State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
    (g.write sz r x).rd = g.rd := rfl
@[simp] theorem write_wr (g : VG.AArch64.State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
    (g.write sz r x).wr = g.wr := rfl

@[simp] theorem setV_read (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) (sz : Size) (r' : Reg) :
    (g.setV r x).read sz r' = g.read sz r' := rfl
@[simp] theorem read_x (g : VG.AArch64.State) (r : Reg) : g.read .x r = g.gpr r := by
  simp [VG.AArch64.State.read]

@[simp] theorem setV_syms (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) :
    (g.setV r x).syms = g.syms := rfl
@[simp] theorem setV_sp (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) : (g.setV r x).sp = g.sp := rfl
@[simp] theorem write_syms (g : VG.AArch64.State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
    (g.write sz r x).syms = g.syms := rfl
@[simp] theorem write_sp (g : VG.AArch64.State) (sz : Size) (r : Reg) (x : BitVec sz.bits) :
    (g.write sz r x).sp = g.sp := rfl

theorem ex_of_eq {α : Type} {o : Option (α × List Leak)} {x : α} {t t' : List Leak} {P : α → Prop}
    (h : o = some (x, t)) (ht : t = t') (hp : P x) : ∃ s', o = some (s', t') ∧ P s' :=
  ⟨x, ht ▸ h, hp⟩

theorem group_ok (i : Nat) (hi : i < 16) (s : Rind.AArch64.State)
    (hk : i < 15 → InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x3) 16) :
    ∃ s', execBlock Rind.AArch64.isa (group i) s = some (s', if i < 15 then [.addr (s.vg.gpr .x3)] else []) ∧
      s'.vg.v .v0 = sha256Hash (s.vg.v .v0) (s.vg.v .v1)
        (VArr.s4.map2 (fun _ a b => a + b) (s.vg.v (kreg i)) (s.vg.v (msg i))) true ∧
      s'.vg.v .v1 = sha256Hash (s.vg.v .v0) (s.vg.v .v1)
        (VArr.s4.map2 (fun _ a b => a + b) (s.vg.v (kreg i)) (s.vg.v (msg i))) false ∧
      (i < 15 → s'.vg.v (kreg (i + 1)) = s.vg.mem.read (s.vg.gpr .x3) 16) ∧
      (i < 12 → s'.vg.v (msg i) = sha256Su1 (sha256Su0 (s.vg.v (msg i)) (s.vg.v (msg (i + 1))))
        (s.vg.v (msg (i + 2))) (s.vg.v (msg (i + 3)))) ∧
      s'.vg.gpr .x3 = (if i < 14 then s.vg.gpr .x3 + 16
        else if i = 14 then s.vg.gpr .x3 - 240 else s.vg.gpr .x3) ∧
      Frame s s' [.v0, .v1, .v2, kreg i, kreg (i + 1), msg i] [.x3] := by
  obtain ⟨g, x29⟩ := s
  interval_cases i <;>
  · simp only [group, kreg, msg, vop, Nat.reduceAdd, Nat.reduceMod, Nat.lt_irrefl,
      ↓reduceIte, List.getD_cons_zero, List.getD_cons_succ, List.cons_append, List.nil_append,
      Nat.reduceEqDiff, Nat.reduceLT] at hk ⊢
    apply ex_of_eq
    · simp (config := { decide := true }) only [execBlock, Rind.AArch64.exec, VG.AArch64.exec, ldVecs,
        advance, State.load, hk, VOp.eval, Rind.AArch64.isa, Option.map_some, Option.bind_some,
        ↓reduceIte, Rind.AArch64.addrs, VG.AArch64.addrs, setV_v, write_v]
      rfl
    · simp [List.range_succ]
    repeat' apply And.intro
    all_goals try (simp (config := { decide := true }) only [setV_v, setV_gpr, read_x, write_v,
      write_gpr, ↓reduceIte, Nat.reduceMul, BitVec.ofNat_eq_ofNat, true_implies, IsEmpty.forall_iff])
    all_goals try (exact ⟨fun r hr => by simp at hr; simp [hr], fun r hr => by simp at hr; simp [hr],
      by simp only [setV_others, write_others], rfl⟩)

/-! ## The sixteen groups -/

theorem Frame.refl (s : Rind.AArch64.State) (vs gs) : Frame s s vs gs :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

theorem Frame.trans {s₁ s₂ s₃ : Rind.AArch64.State} {vs gs} (h₁ : Frame s₁ s₂ vs gs)
    (h₂ : Frame s₂ s₃ vs gs) : Frame s₁ s₃ vs gs :=
  ⟨fun r hr => (h₂.v r hr).trans (h₁.v r hr), fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr),
    h₂.others.trans h₁.others, h₂.x29.trans h₁.x29⟩

theorem Frame.mono {s s' : Rind.AArch64.State} {vs gs vs' gs'} (h : Frame s s' vs gs)
    (hv : ∀ r ∈ vs, r ∈ vs') (hg : ∀ r ∈ gs, r ∈ gs') : Frame s s' vs' gs' :=
  ⟨fun r hr => h.v r fun m => hr (hv r m), fun r hr => h.gpr r fun m => hr (hg r m), h.others, h.x29⟩

theorem Frame.mem {s s' : Rind.AArch64.State} {vs gs} (h : Frame s s' vs gs) : s'.vg.mem = s.vg.mem :=
  congrArg (fun o => o.2.2.2.2.2.2.1) h.others
theorem Frame.rd {s s' : Rind.AArch64.State} {vs gs} (h : Frame s s' vs gs) : s'.vg.rd = s.vg.rd :=
  congrArg (fun o => o.2.2.2.2.2.2.2.1) h.others
theorem Frame.wr {s s' : Rind.AArch64.State} {vs gs} (h : Frame s s' vs gs) : s'.vg.wr = s.vg.wr :=
  congrArg (fun o => o.2.2.2.2.2.2.2.2.1) h.others
theorem Frame.sp {s s' : Rind.AArch64.State} {vs gs} (h : Frame s s' vs gs) : s'.vg.sp = s.vg.sp :=
  congrArg (fun o => o.1) h.others

theorem msg_cases (i : Nat) : msg i = .v4 ∧ i % 4 = 0 ∨ msg i = .v5 ∧ i % 4 = 1 ∨
    msg i = .v6 ∧ i % 4 = 2 ∨ msg i = .v7 ∧ i % 4 = 3 := by
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;> simp [msg, h]

theorem kreg_cases (i : Nat) : kreg i = .v16 ∨ kreg i = .v17 := by
  unfold kreg; split <;> simp

theorem msg_add4 (i : Nat) : msg (i + 4) = msg i := by simp [msg, Nat.add_mod_right]

theorem msg_other {i j : Nat} (h : j % 4 ≠ i % 4) :
    msg j ∉ [VReg.v0, .v1, .v2, kreg i, kreg (i + 1), msg i] := by
  rcases msg_cases i with ⟨hi, hi'⟩ | ⟨hi, hi'⟩ | ⟨hi, hi'⟩ | ⟨hi, hi'⟩ <;>
  rcases msg_cases j with ⟨hj, hj'⟩ | ⟨hj, hj'⟩ | ⟨hj, hj'⟩ | ⟨hj, hj'⟩ <;>
  rcases kreg_cases i with hk | hk <;> rcases kreg_cases (i + 1) with hk' | hk' <;>
  simp only [hi, hj, hk, hk'] <;> first | omega | decide

/-- The groups' registers. -/
def groupV : List VReg := [.v0, .v1, .v2, .v4, .v5, .v6, .v7, .v16, .v17]

theorem group_frame (i : Nat) : ∀ r ∈ [VReg.v0, .v1, .v2, kreg i, kreg (i + 1), msg i], r ∈ groupV := by
  rcases msg_cases i with ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ | ⟨hi, -⟩ <;>
  rcases kreg_cases i with hk | hk <;> rcases kreg_cases (i + 1) with hk' | hk' <;>
  simp only [hi, hk, hk'] <;> decide

/-- Rewrite an address. -/
macro "addr" : tactic => `(tactic| first | bv_omega | (apply BitVec.eq_of_toNat_eq; simp; omega))

/-- The table's words are at `k`. -/
def TableAt (m : Mem) (k : Addr) : Prop := ∀ j < 64, m.read (k + BitVec.ofNat 64 (4 * j)) 4 = table[j]!

theorem table_quad {m : Mem} {k : Addr} (h : TableAt m k) {i : Nat} (hi : i < 16) :
    m.read (k + BitVec.ofNat 64 (16 * i)) 16 = quad (fun t => table[t]!) i := by
  rw [read16, quad, ← h (4 * i) (by omega), ← h (4 * i + 1) (by omega), ← h (4 * i + 2) (by omega),
    ← h (4 * i + 3) (by omega)]
  congr 2 <;> addr

/-- What holds after `i` groups of block `M` from state `H`, with the table
at `k`: the state is round `4 i`'s; the next group's constants are loaded,
the schedule's next four groups of words are in `msg`, and `x3` addresses
the constants to load next, the last group's from the table's start. -/
structure GInv (M H : List (BitVec 32)) (k : Addr) (i : Nat) (s : Rind.AArch64.State) : Prop where
  v0 : s.vg.v .v0 = abcd (s2n.compressRounds M H (4 * i))
  v1 : s.vg.v .v1 = efgh (s2n.compressRounds M H (4 * i))
  kr : i < 16 → s.vg.v (kreg i) = quad (fun t => table[t]!) i
  w : ∀ j, i ≤ j → j < i + 4 → j < 16 → s.vg.v (msg j) = quad (s2n.msgSchedule M) j
  x3 : s.vg.gpr .x3 = if i < 15 then k + BitVec.ofNat 64 (16 * (i + 1)) else k

/-- The groups' trace. -/
def groupsTrace (k : Addr) (n : Nat) : List Leak :=
  (List.range n).flatMap fun i => if i < 15 then [.addr (k + BitVec.ofNat 64 (16 * (i + 1)))] else []

theorem groups_ok (M H : List (BitVec 32)) (k : Addr) (s : Rind.AArch64.State)
    (h0 : GInv M H k 0 s) (hm : TableAt s.vg.mem k)
    (hr : ∀ i < 16, InRegions (s.vg.rd ++ s.vg.wr) (k + BitVec.ofNat 64 (16 * i)) 16) :
    ∀ n ≤ 16, ∃ s', execBlock Rind.AArch64.isa ((List.range n).flatMap group) s = some (s', groupsTrace k n) ∧
      GInv M H k n s' ∧ Frame s s' groupV [.x3] := by
  intro n hn
  induction n with
  | zero => exact ⟨s, rfl, h0, Frame.refl _ _ _⟩
  | succ n ih =>
    obtain ⟨s₁, e₁, g, f₁⟩ := ih (by omega)
    have hx3 : n < 15 → s₁.vg.gpr .x3 = k + BitVec.ofNat 64 (16 * (n + 1)) := fun h => by
      rw [g.x3, ite_eq_left h]
    obtain ⟨s₂, e₂, h0', h1', hk', hw', hx3', f₂⟩ := group_ok n (by omega) s₁ fun h => by
      rw [f₁.rd, f₁.wr, hx3 h]; exact hr (n + 1) (by omega)
    refine ⟨s₂, ?_, ?_, f₁.trans (f₂.mono (group_frame n) (by decide))⟩
    · rw [List.range_succ, List.flatMap_append, execBlock_append, e₁]
      simp only [Option.bind_some, List.flatMap_singleton, e₂, Option.map_some]
      congr 2
      simp only [groupsTrace, List.range_succ, List.flatMap_append, List.flatMap_singleton]
      split <;> simp_all
    · have hkn := g.kr (by omega)
      have hwn := g.w n le_rfl (by omega) (by omega)
      refine ⟨?_, ?_, fun h => ?_, fun j hj hj' hj'' => ?_, ?_⟩
      · rw [h0', hkn, hwn, g.v0, g.v1, rounds_eq, ite_eq_left rfl]
      · rw [h1', hkn, hwn, g.v0, g.v1, rounds_eq]; rfl
      · rw [hk' (by omega), hx3 (by omega), f₁.mem]; exact table_quad hm h
      · by_cases e : j = n + 4
        · subst e
          rw [msg_add4, hw' (by omega), g.w n le_rfl (by omega) (by omega),
            g.w (n + 1) (by omega) (by omega) (by omega),
            g.w (n + 2) (by omega) (by omega) (by omega), g.w (n + 3) (by omega) (by omega) (by omega),
            schedule_eq]
        · rw [f₂.v _ (msg_other (by omega)), g.w j (by omega) (by omega) hj'']
      · rw [hx3']
        by_cases a : n < 14
        · rw [ite_eq_left a, hx3 (by omega), ite_eq_left (by omega)]; addr
        · by_cases b : n = 14
          · subst b
            rw [ite_eq_right (by omega), ite_eq_left rfl, hx3 (by omega), ite_eq_right (by omega)]
            bv_omega
          · rw [ite_eq_right a, ite_eq_right b, g.x3, ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## A block -/

/-- The head's trace: the block's four loads, then the first group's constants'. -/
def headTrace (p k : Addr) : List Leak := [.addr p, .addr (p + 16), .addr (p + 32), .addr (p + 48), .addr k]

theorem head_ok (s : Rind.AArch64.State)
    (hp : ∀ j < 4, InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x1 + BitVec.ofNat 64 (16 * j)) 16)
    (hk : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x3) 16) :
    ∃ s', execBlock Rind.AArch64.isa head s = some (s', headTrace (s.vg.gpr .x1) (s.vg.gpr .x3)) ∧
      s'.vg.v .v4 = VRevOp.eval .rev32b (s.vg.mem.read (s.vg.gpr .x1) 16) ∧
      s'.vg.v .v5 = VRevOp.eval .rev32b (s.vg.mem.read (s.vg.gpr .x1 + 16) 16) ∧
      s'.vg.v .v6 = VRevOp.eval .rev32b (s.vg.mem.read (s.vg.gpr .x1 + 32) 16) ∧
      s'.vg.v .v7 = VRevOp.eval .rev32b (s.vg.mem.read (s.vg.gpr .x1 + 48) 16) ∧
      s'.vg.v .v16 = s.vg.mem.read (s.vg.gpr .x3) 16 ∧
      s'.vg.v .v18 = s.vg.v .v0 ∧ s'.vg.v .v19 = s.vg.v .v1 ∧
      s'.vg.gpr .x1 = s.vg.gpr .x1 + 64 ∧ s'.vg.gpr .x2 = s.vg.gpr .x2 - 1 ∧
      s'.vg.gpr .x3 = s.vg.gpr .x3 + 16 ∧
      Frame s s' [.v4, .v5, .v6, .v7, .v16, .v18, .v19] [.x1, .x2, .x3] := by
  obtain ⟨g, x29⟩ := s
  have h0 := hp 0 (by omega); have h1 := hp 1 (by omega); have h2 := hp 2 (by omega)
  have h3 := hp 3 (by omega)
  simp only [Nat.reduceMul, BitVec.add_zero] at h0 h1 h2 h3
  simp only [head, vop]
  apply ex_of_eq
  · simp (config := { decide := true }) only [execBlock, Rind.AArch64.exec, VG.AArch64.exec, ldVecs,
      advance, State.load, h0, h1, h2, h3, hk, VOp.eval, Rind.AArch64.isa, Option.map_some, Option.bind_some,
      ↓reduceIte, Rind.AArch64.addrs, VG.AArch64.addrs, setV_v, setV_gpr, setV_mem, setV_rd, setV_wr,
      write_v, write_gpr, write_mem, write_rd, write_wr, BitVec.add_assoc, BitVec.reduceAdd, VReg.succ,
      read_x, BitVec.ofNat_eq_ofNat]
    rfl
  · simp [headTrace, List.range_succ]
  repeat' apply And.intro
  all_goals try (simp (config := { decide := true }) only [setV_v, setV_gpr, write_v, write_gpr,
    ↓reduceIte, Nat.reduceMul, BitVec.ofNat_eq_ofNat])
  all_goals try (exact ⟨fun r hr => by simp at hr; simp [hr], fun r hr => by simp at hr; simp [hr],
    by simp only [setV_others, write_others], rfl⟩)

theorem tail_ok (s : Rind.AArch64.State) :
    ∃ s', execBlock Rind.AArch64.isa tail s = some (s', []) ∧
      s'.vg.v .v0 = VArr.s4.map2 (fun _ a b => a + b) (s.vg.v .v0) (s.vg.v .v18) ∧
      s'.vg.v .v1 = VArr.s4.map2 (fun _ a b => a + b) (s.vg.v .v1) (s.vg.v .v19) ∧
      Frame s s' [.v0, .v1] [] := by
  obtain ⟨g, x29⟩ := s
  apply ex_of_eq
  · simp only [tail, vop, execBlock, Rind.AArch64.exec, VG.AArch64.exec, VOp.eval, Rind.AArch64.isa,
      Option.map_some, Rind.AArch64.addrs, VG.AArch64.addrs]
    rfl
  · rfl
  refine ⟨by simp, by simp, fun r hr => by simp at hr; simp [hr], fun r _ => by simp, by simp, rfl⟩

/-- Block `p`'s sixteen big-endian words. -/
def msgOf (m : Mem) (p : Addr) : List (BitVec 32) :=
  (List.range 16).map fun j => be m (p + BitVec.ofNat 64 (4 * j))

theorem msgOf_get (m : Mem) (p : Addr) {t : Nat} (ht : t < 16) :
    (msgOf m p)[t]! = be m (p + BitVec.ofNat 64 (4 * t)) := by
  simp [msgOf, ht]

theorem quad_msg (m : Mem) (p : Addr) {j : Nat} (hj : j < 4) :
    quad (s2n.msgSchedule (msgOf m p)) j =
      VRevOp.eval .rev32b (m.read (p + BitVec.ofNat 64 (16 * j)) 16) := by
  rw [rev32_read, quad, s2n.msgSchedule_lt _ (by omega), s2n.msgSchedule_lt _ (by omega),
    s2n.msgSchedule_lt _ (by omega), s2n.msgSchedule_lt _ (by omega), msgOf_get _ _ (by omega),
    msgOf_get _ _ (by omega), msgOf_get _ _ (by omega), msgOf_get _ _ (by omega)]
  congr 2 <;> addr

/-- The registers a block changes. -/
def bodyV : List VReg := [.v0, .v1, .v2, .v4, .v5, .v6, .v7, .v16, .v17, .v18, .v19]

/-- A block's trace. -/
def bodyTrace (p k : Addr) : List Leak := headTrace p k ++ groupsTrace k 16 ++ []

theorem body_ok (s : Rind.AArch64.State) (H : List (BitVec 32))
    (hv0 : s.vg.v .v0 = abcd H) (hv1 : s.vg.v .v1 = efgh H) (hm : TableAt s.vg.mem (s.vg.gpr .x3))
    (hp : ∀ j < 4, InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x1 + BitVec.ofNat 64 (16 * j)) 16)
    (hr : ∀ i < 16, InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x3 + BitVec.ofNat 64 (16 * i)) 16) :
    ∃ s', execBlock Rind.AArch64.isa body s = some (s', bodyTrace (s.vg.gpr .x1) (s.vg.gpr .x3)) ∧
      s'.vg.v .v0 = abcd (s2n.block (msgOf s.vg.mem (s.vg.gpr .x1)) H) ∧
      s'.vg.v .v1 = efgh (s2n.block (msgOf s.vg.mem (s.vg.gpr .x1)) H) ∧
      s'.vg.gpr .x1 = s.vg.gpr .x1 + 64 ∧ s'.vg.gpr .x2 = s.vg.gpr .x2 - 1 ∧
      s'.vg.gpr .x3 = s.vg.gpr .x3 ∧ Frame s s' bodyV [.x1, .x2, .x3] := by
  have hk0 := hr 0 (by omega)
  simp only [Nat.mul_zero, BitVec.add_zero] at hk0
  obtain ⟨s₁, e₁, h4, h5, h6, h7, h16, h18, h19, hx1, hx2, hx3, f₁⟩ := head_ok s hp hk0
  have hm₁ : s₁.vg.mem = s.vg.mem := f₁.mem
  have g0 : GInv (msgOf s.vg.mem (s.vg.gpr .x1)) H (s.vg.gpr .x3) 0 s₁ := by
    refine ⟨?_, ?_, fun _ => ?_, fun j _ hj _ => ?_, ?_⟩
    · rw [f₁.v _ (by decide), hv0]; rfl
    · rw [f₁.v _ (by decide), hv1]; rfl
    · have := table_quad hm (i := 0) (by omega)
      simp only [Nat.mul_zero, BitVec.add_zero] at this
      rw [show kreg 0 = .v16 from rfl, h16, this]
    · rw [quad_msg _ _ (by omega)]
      interval_cases j
      · simpa [msg] using h4
      · simpa [msg] using h5
      · simpa [msg] using h6
      · simpa [msg] using h7
    · rw [hx3]; simp
  obtain ⟨s₂, e₂, g, f₂⟩ := groups_ok _ H _ s₁ g0 (by rw [hm₁]; exact hm)
    (by rw [f₁.rd, f₁.wr]; exact hr) 16 le_rfl
  obtain ⟨s₃, e₃, h0', h1', f₃⟩ := tail_ok s₂
  refine ⟨s₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [body, execBlock_append, execBlock_append, e₁]
    simp only [Option.bind_some, e₂, Option.map_some, e₃]
    rfl
  · rw [h0', g.v0, f₂.v _ (by decide), h18, hv0, map2_add]
    simp [abcd, s2n.block]
  · rw [h1', g.v1, f₂.v _ (by decide), h19, hv1, map2_add]
    simp [efgh, s2n.block]
  · rw [f₃.gpr _ (by decide), f₂.gpr _ (by decide), hx1]
  · rw [f₃.gpr _ (by decide), f₂.gpr _ (by decide), hx2]
  · rw [f₃.gpr _ (by decide), g.x3]; rfl
  · exact (f₁.mono (by decide) (by decide)).trans ((f₂.mono (by decide) (by decide)).trans
      (f₃.mono (by decide) (by decide)))

/-! ## The loop -/

/-- Block `i` of the data at `p`. -/
def msgs (m : Mem) (p : Addr) (i : Nat) : List (BitVec 32) := msgOf m (p + BitVec.ofNat 64 (64 * i))

/-- The loop's trace from block `p`, with `c` more blocks after it. -/
def loopTrace (p k : Addr) : Nat → List Leak
  | 0 => bodyTrace p k ++ [.branch false]
  | c + 1 => bodyTrace p k ++ .branch true :: loopTrace (p + 64) k c

/-- The loop. -/
abbrev loop : Prog Rind.AArch64.isa := .loop (.block body) (.nonzero .x .x2)

theorem eval_x2 (s : Rind.AArch64.State) :
    Rind.AArch64.isa.eval (.nonzero .x .x2) s = some (s.vg.gpr .x2 != 0) := by
  simp [VG.AArch64.eval]

theorem loop_ok (s₀ : Rind.AArch64.State) (H : List (BitVec 32)) (n : Nat) (hn : n < 2 ^ 64)
    (hm : TableAt s₀.vg.mem (s₀.vg.gpr .x3))
    (hp : ∀ b < n, ∀ j < 4, InRegions (s₀.vg.rd ++ s₀.vg.wr)
      (s₀.vg.gpr .x1 + BitVec.ofNat 64 (64 * b) + BitVec.ofNat 64 (16 * j)) 16)
    (hr : ∀ i < 16, InRegions (s₀.vg.rd ++ s₀.vg.wr) (s₀.vg.gpr .x3 + BitVec.ofNat 64 (16 * i)) 16) :
    ∀ c b (s : Rind.AArch64.State), b + c + 1 = n → Frame s₀ s bodyV [.x1, .x2, .x3] →
      s.vg.v .v0 = abcd (s2n.hashBlocks (msgs s₀.vg.mem (s₀.vg.gpr .x1)) H b) →
      s.vg.v .v1 = efgh (s2n.hashBlocks (msgs s₀.vg.mem (s₀.vg.gpr .x1)) H b) →
      s.vg.gpr .x1 = s₀.vg.gpr .x1 + BitVec.ofNat 64 (64 * b) → s.vg.gpr .x2 = BitVec.ofNat 64 (c + 1) →
      s.vg.gpr .x3 = s₀.vg.gpr .x3 →
      ∃ s', Exec Rind.AArch64.isa loop s (loopTrace (s.vg.gpr .x1) (s₀.vg.gpr .x3) c) s' ∧
        s'.vg.v .v0 = abcd (s2n.hashBlocks (msgs s₀.vg.mem (s₀.vg.gpr .x1)) H n) ∧
        s'.vg.v .v1 = efgh (s2n.hashBlocks (msgs s₀.vg.mem (s₀.vg.gpr .x1)) H n) ∧
        s'.vg.gpr .x1 = s₀.vg.gpr .x1 + BitVec.ofNat 64 (64 * n) ∧ s'.vg.gpr .x2 = 0 ∧
        s'.vg.gpr .x3 = s₀.vg.gpr .x3 ∧ Frame s₀ s' bodyV [.x1, .x2, .x3] := by
  intro c
  induction c with
  | zero => ?_
  | succ c ih => ?_
  all_goals
    intro b s hb f hv0 hv1 hx1 hx2 hx3
    obtain ⟨s₁, e, h0, h1, hx1', hx2', hx3', f₁⟩ := body_ok s _ hv0 hv1 (by rw [f.mem, hx3]; exact hm)
      (by rw [f.rd, f.wr, hx1]; exact hp b (by omega)) (by rw [f.rd, f.wr, hx3]; exact hr)
    rw [f.mem, hx1] at h0 h1
  · refine ⟨s₁, ?_, ?_, ?_, ?_, ?_, ?_, f.trans f₁⟩
    · rw [hx3] at e
      exact .loopExit (.block e) (by rw [eval_x2, hx2', hx2]; rfl)
    · rw [h0, ← hb]; rfl
    · rw [h1, ← hb]; rfl
    · rw [hx1', hx1, ← hb]; addr
    · rw [hx2', hx2]; rfl
    · rw [hx3', hx3]
  · obtain ⟨s', e', h0', h1', hx1'', hx2'', hx3'', f'⟩ := ih (b + 1) s₁ (by omega) (f.trans f₁)
      (by rw [h0]; rfl) (by rw [h1]; rfl) (by rw [hx1', hx1]; addr)
      (by rw [hx2', hx2]; addr) (by rw [hx3', hx3])
    refine ⟨s', ?_, h0', h1', hx1'', hx2'', hx3'', f'⟩
    rw [hx3] at e
    rw [hx1'] at e'
    exact .loopNext (.block e) (by
      rw [eval_x2, hx2', hx2]
      simp only [bne_iff_ne, ne_eq, Option.some.injEq]
      intro h
      have := congrArg BitVec.toNat h
      simp at this
      omega) e'

/-! ## The prologue and epilogue -/

theorem prologue_ok (s : Rind.AArch64.State) (hsp : s.vg.sp.toNat % 16 = 0)
    (hf0 : InRegions s.vg.wr (s.vg.sp - 16) 8) (hf1 : InRegions s.vg.wr (s.vg.sp - 16 + 8) 8)
    (hs0 : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x0) 16)
    (hs1 : InRegions (s.vg.rd ++ s.vg.wr) (s.vg.gpr .x0 + 16) 16) :
    ∃ s', execBlock Rind.AArch64.isa prologue s = some (s',
        [.addr (s.vg.sp - 16), .addr (s.vg.sp - 8), .addr (s.vg.gpr .x0), .addr (s.vg.gpr .x0 + 16)]) ∧
      s'.vg.mem = (s.vg.mem.write (s.vg.sp - 16) 8 s.x29).write (s.vg.sp - 16 + 8) 8 (s.vg.gpr .x30) ∧
      s'.vg.sp = s.vg.sp - 16 ∧
      s'.vg.v .v0 = s'.vg.mem.read (s.vg.gpr .x0) 16 ∧ s'.vg.v .v1 = s'.vg.mem.read (s.vg.gpr .x0 + 16) 16 ∧
      s'.vg.gpr .x3 = s.vg.syms kName ∧
      (∀ r, r ≠ .x3 → s'.vg.gpr r = s.vg.gpr r) ∧ (∀ r, r ∉ [.v0, .v1] → s'.vg.v r = s.vg.v r) ∧
      s'.vg.rd = s.vg.rd ∧ s'.vg.wr = s.vg.wr := by
  obtain ⟨g, x29⟩ := s
  simp only at *
  apply ex_of_eq
  · simp (config := { decide := true }) only [prologue, execBlock, Rind.AArch64.exec, VG.AArch64.exec, ldVecs,
      advance, State.load, State.store, hsp, hf0, hf1, Rind.AArch64.isa, Option.map_some, Option.bind_some,
      ↓reduceIte, Rind.AArch64.addrs, VG.AArch64.addrs, setV_mem, setV_rd, setV_wr, VReg.succ]
    simp (config := { decide := true }) only [hs0, hs1, ↓reduceIte, Option.bind_some, Option.map_some]
    rfl
  · simp [List.range_succ]
  refine ⟨by simp, by simp, by simp, by simp, by simp, fun r hr => by simp [hr], fun r hr => ?_, by simp,
    by simp⟩
  simp at hr; simp [hr]

theorem epilogue_ok (s : Rind.AArch64.State) (hsp : s.vg.sp.toNat % 16 = 0)
    (hs0 : InRegions s.vg.wr (s.vg.gpr .x0) 16) (hs1 : InRegions s.vg.wr (s.vg.gpr .x0 + 16) 16)
    (hf : InRegions (s.vg.rd ++ s.vg.wr) s.vg.sp 8) :
    ∃ s', execBlock Rind.AArch64.isa epilogue s = some (s',
        [.addr (s.vg.gpr .x0), .addr (s.vg.gpr .x0 + 16), .addr s.vg.sp]) ∧
      s'.vg.mem = (s.vg.mem.write (s.vg.gpr .x0) 16 (s.vg.v .v0)).write (s.vg.gpr .x0 + 16) 16 (s.vg.v .v1) ∧
      s'.vg.sp = s.vg.sp + 16 ∧ s'.x29 = s'.vg.mem.read s.vg.sp 8 ∧
      s'.vg.gpr = s.vg.gpr ∧ s'.vg.v = s.vg.v := by
  obtain ⟨g, x29⟩ := s
  simp only at *
  apply ex_of_eq
  · simp (config := { decide := true }) only [epilogue, execBlock, Rind.AArch64.exec, stVecs,
      advance, State.load, State.store, hsp, hs0, hs1, Rind.AArch64.isa, Option.map_some, Option.bind_some,
      ↓reduceIte, Rind.AArch64.addrs, VReg.succ]
    simp (config := { decide := true }) only [hf, ↓reduceIte, Option.map_some]
    rfl
  · simp [List.range_succ]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Memory outside the stores -/

theorem contains_byte {r : Region} {a : Addr} {n k : Nat} (h : r.Contains a n) (hk : k < n) :
    r.Contains (a + BitVec.ofNat 64 k) 1 := by
  simp only [Region.Contains] at *
  have : (a + BitVec.ofNat 64 k - r.base).toNat ≤ (a - r.base).toNat + k := by
    rw [show a + BitVec.ofNat 64 k - r.base = a - r.base + BitVec.ofNat 64 k by bv_omega, BitVec.toNat_add]
    simp only [BitVec.toNat_ofNat]
    have := Nat.mod_le ((a - r.base).toNat + k % 2 ^ 64) (2 ^ 64)
    have := Nat.mod_le k (2 ^ 64)
    omega
  omega

theorem contains_of {base a : Addr} {len n off : Nat} (h : (a - base).toNat ≤ off) (h' : off + n ≤ len) :
    Region.Contains ⟨base, len⟩ a n := by
  simp only [Region.Contains]; omega

/-- A read of `n` bytes in `r`, which `m'` and `m` agree on. -/
theorem read_in {m m' : Mem} {r : Region} {a : Addr} {n : Nat} (hr : r.Contains a n)
    (h : ∀ x, r.Contains x 1 → m' x = m x) : m'.read a n = m.read a n :=
  read_congr m m' a n fun _ hk => h _ (contains_byte hr hk)

theorem outside {base a : Addr} {len : Nat} (h : ¬ Region.Contains ⟨base, len⟩ a 1) :
    len ≤ (a - base).toNat := by
  simp only [Region.Contains] at h; omega

/-- The frame's two stores change only the frame. -/
theorem frame_other (m : Mem) (sp x y a : Addr) (h : ¬ Region.Contains ⟨sp - 16, 16⟩ a 1) :
    (m.write (sp - 16) 8 x).write (sp - 16 + 8) 8 y a = m a := by
  have := outside h
  rw [write_other _ _ _ _ _ (by bv_omega), write_other _ _ _ _ _ (by omega)]

/-- The state's two stores change only the state. -/
theorem state_other (m : Mem) (p a : Addr) (v w : BitVec 128) (h : ¬ Region.Contains ⟨p, 32⟩ a 1) :
    (m.write p 16 v).write (p + 16) 16 w a = m a := by
  have := outside h
  rw [write_other _ _ _ _ _ (by bv_omega), write_other _ _ _ _ _ (by omega)]

theorem hashBlocks_congr {m m' : Nat → List (BitVec 32)} (H : List (BitVec 32)) {n : Nat}
    (h : ∀ i < n, m' i = m i) : s2n.hashBlocks m' H n = s2n.hashBlocks m H n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [s2n.hashBlocks, h n (by omega), ih fun i hi => h i (by omega)]

/-! ## The routine -/

/-- The eight words of the state at `a`, each read little-endian, as the
caller's `uint32_t[8]` holds them. -/
def words8 (m : Mem) (a : Addr) : List (BitVec 32) :=
  (List.range 8).map fun j => m.read (a + BitVec.ofNat 64 (4 * j)) 4

theorem read16_words8 (m : Mem) (a : Addr) :
    m.read a 16 = abcd (words8 m a) ∧ m.read (a + 16) 16 = efgh (words8 m a) := by
  rw [read16, read16]
  simp only [abcd, efgh, words8]
  constructor
  · simp
  · simp; congr 2 <;> addr

theorem words8_write (m : Mem) (a : Addr) (v w : BitVec 128) :
    words8 ((m.write a 16 v).write (a + 16) 16 w) a =
      [vword v 0, vword v 1, vword v 2, vword v 3, vword w 0, vword w 1, vword w 2, vword w 3] := by
  simp only [words8, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
    List.map_nil, List.cons_append, Nat.reduceMul, List.cons.injEq, and_true]
  simp only [Mem.read, Mem.write, BitVec.add_assoc, BitVec.reduceAdd, add_sub_left, add_sub_add, sub_add_self,
    BitVec.sub_self, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.reduceSub, BitVec.reduceToNat,
    Nat.reduceLT,
    ↓reduceIte, Nat.reduceMul, vword]
  bv_decide

/-- The state, `state` (`x0`). -/
def stateR (s : Rind.AArch64.State) : Region := ⟨s.vg.gpr .x0, 32⟩
/-- The blocks, `data` (`x1`), `blocks` (`x2`) of them. -/
def dataR (s : Rind.AArch64.State) : Region := ⟨s.vg.gpr .x1, 64 * (s.vg.gpr .x2).toNat⟩
/-- The table's words the routine reads. -/
def tableR (s : Rind.AArch64.State) : Region := ⟨s.vg.syms kName, 256⟩
/-- The 16 bytes below the stack pointer the routine saves `x29` and `x30` to. -/
def frameR (s : Rind.AArch64.State) : Region := ⟨s.vg.sp - 16, 16⟩

/-- The theorem's hypotheses: at least one block; the stack pointer 16-byte
aligned; the routine may read the blocks and the table, and read and write
the state and the frame; the frame overlaps none of the others; and the table holds
FIPS 180-4's constants. They are weaker than `SHA256_HW_SUBROUTINE_CORRECT`'s:
the state may overlap the blocks or the table, since the routine writes it
only after its last read, and the table is at a symbol's address, so no
`adrp` range or code region is assumed. -/
structure Pre (s : Rind.AArch64.State) : Prop where
  n : s.vg.gpr .x2 ≠ 0
  sp : s.vg.sp.toNat % 16 = 0
  rd : s.vg.rd = [dataR s, tableR s]
  wr : s.vg.wr = [stateR s, frameR s]
  disjoint : ∀ r ∈ [stateR s, dataR s, tableR s], r.Disjoint (frameR s)
  table : TableAt s.vg.mem (s.vg.syms kName)

/-- What the routine ensures: the state's words become `hashBlocks` of the
blocks, read big-endian, from them; memory but the state and the frame is
unchanged; and the registers AAPCS64 makes the callee save, the stack pointer
and the return address in `x30` among them, are as they were, with `x29`. -/
structure Post (s s' : Rind.AArch64.State) : Prop where
  state : words8 s'.vg.mem (s.vg.gpr .x0) =
    s2n.hashBlocks (msgs s.vg.mem (s.vg.gpr .x1)) (words8 s.vg.mem (s.vg.gpr .x0)) (s.vg.gpr .x2).toNat
  mem : ∀ a, ¬ (stateR s).Contains a 1 → ¬ (frameR s).Contains a 1 → s'.vg.mem a = s.vg.mem a
  abi : VG.AArch64.abiPreserved s.vg s'.vg
  x29 : s'.x29 = s.x29

/-- What is public: the arguments, the stack pointer, and the table's
address. The state and blocks are not. -/
def Pub (s₁ s₂ : Rind.AArch64.State) : Prop :=
  s₁.vg.gpr .x0 = s₂.vg.gpr .x0 ∧ s₁.vg.gpr .x1 = s₂.vg.gpr .x1 ∧ s₁.vg.gpr .x2 = s₂.vg.gpr .x2 ∧
    s₁.vg.sp = s₂.vg.sp ∧ s₁.vg.syms kName = s₂.vg.syms kName

/-- The routine's trace, a function of what is public. -/
def trace (s : Rind.AArch64.State) : List Leak :=
  [.addr (s.vg.sp - 16), .addr (s.vg.sp - 8), .addr (s.vg.gpr .x0), .addr (s.vg.gpr .x0 + 16)] ++
    (loopTrace (s.vg.gpr .x1) (s.vg.syms kName) ((s.vg.gpr .x2).toNat - 1) ++
      [.addr (s.vg.gpr .x0), .addr (s.vg.gpr .x0 + 16), .addr (s.vg.sp - 16)])

theorem mem_wr {s : Rind.AArch64.State} {r : Region} {a : Addr} {n : Nat} (h : r ∈ s.vg.wr)
    (h' : r.Contains a n) : InRegions s.vg.wr a n := ⟨r, h, h'⟩

theorem mem_rdwr {s : Rind.AArch64.State} {r : Region} {a : Addr} {n : Nat} (h : r ∈ s.vg.rd ++ s.vg.wr)
    (h' : r.Contains a n) : InRegions (s.vg.rd ++ s.vg.wr) a n := ⟨r, h, h'⟩

theorem add_ofNat (a : Addr) (x y : Nat) :
    a + BitVec.ofNat 64 x + BitVec.ofNat 64 y = a + BitVec.ofNat 64 (x + y) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem off_le (a : Addr) (x : Nat) : (a + BitVec.ofNat 64 x - a).toNat ≤ x := by
  rw [add_sub_left, BitVec.toNat_ofNat]; exact Nat.mod_le _ _

theorem be_congr {m m' : Mem} {a : Addr}
    (h : ∀ k < 4, m' (a + BitVec.ofNat 64 k) = m (a + BitVec.ofNat 64 k)) : be m' a = be m a := by
  have h0 : m' a = m a := by simpa using h 0 (by omega)
  have h1 : m' (a + 1) = m (a + 1) := h 1 (by omega)
  have h2 : m' (a + 2) = m (a + 2) := h 2 (by omega)
  have h3 : m' (a + 3) = m (a + 3) := h 3 (by omega)
  simp only [be, h0, h1, h2, h3]

theorem list8 : ∀ l : List (BitVec 32), l.length = 8 →
    [l[0]!, l[1]!, l[2]!, l[3]!, l[4]!, l[5]!, l[6]!, l[7]!] = l
  | [_, _, _, _, _, _, _, _], _ => rfl

theorem correct (s : Rind.AArch64.State) (h : Pre s) :
    ∃ s', Exec Rind.AArch64.isa prog s (trace s) s' ∧ Post s s' := by
  have hfr : frameR s ∈ s.vg.wr := by simp [h.wr]
  have hst : stateR s ∈ s.vg.wr := by simp [h.wr]
  obtain ⟨s₁, e₁, hm₁, hsp₁, hv0₁, hv1₁, hx3₁, hg₁, hv₁, hrd₁, hwr₁⟩ := prologue_ok s h.sp
    (mem_wr hfr (contains_of (off := 0) (by simp []) (by omega)))
    (mem_wr hfr (contains_of (off := 8) (by simp []) (by omega)))
    (mem_rdwr (List.mem_append_right _ hst) (contains_of (off := 0) (by simp []) (by omega)))
    (mem_rdwr (List.mem_append_right _ hst) (contains_of (off := 16) (by simp []) (by omega)))
  -- The memory the loop reads is the caller's.
  have hout : ∀ r ∈ [stateR s, dataR s, tableR s], ∀ x, r.Contains x 1 → s₁.vg.mem x = s.vg.mem x :=
    fun r hr x hx => by rw [hm₁]; exact frame_other _ _ _ _ _ (h.disjoint r hr x hx)
  have hx0₁ : s₁.vg.gpr .x0 = s.vg.gpr .x0 := hg₁ _ (by decide)
  have hx1₁ : s₁.vg.gpr .x1 = s.vg.gpr .x1 := hg₁ _ (by decide)
  have hx2₁ : s₁.vg.gpr .x2 = s.vg.gpr .x2 := hg₁ _ (by decide)
  have hn : (s.vg.gpr .x2).toNat ≠ 0 := fun e => h.n (BitVec.eq_of_toNat_eq (by simpa using e))
  have hst0 : (stateR s).Contains (s.vg.gpr .x0) 16 := contains_of (off := 0) (by simp []) (by omega)
  have hst1 : (stateR s).Contains (s.vg.gpr .x0 + 16) 16 :=
    contains_of (off := 16) (by simp []) (by omega)
  have hH := read16_words8 s.vg.mem (s.vg.gpr .x0)
  have hdata : ∀ i < (s.vg.gpr .x2).toNat, msgs s₁.vg.mem (s.vg.gpr .x1) i =
      msgs s.vg.mem (s.vg.gpr .x1) i := fun i hi => by
    simp only [msgs, msgOf, List.map_inj_left, List.mem_range]
    intro j hj
    refine be_congr fun k hk => hout (dataR s) (by simp) _ ?_
    rw [add_ofNat, add_ofNat]
    exact contains_of (off_le _ _) (by omega)
  obtain ⟨s₂, e₂, hv0₂, hv1₂, -, -, -, f₂⟩ := loop_ok s₁ (words8 s.vg.mem (s.vg.gpr .x0)) (s.vg.gpr .x2).toNat
    (BitVec.isLt _)
    (by
      intro j hj
      rw [hx3₁, read_in (r := tableR s) (contains_of (off_le _ _) (by omega)) (hout _ (by simp))]
      exact h.table j hj)
    (by
      intro b hb j hj
      rw [hrd₁, hwr₁, hx1₁, add_ofNat]
      exact mem_rdwr (s := s) (r := dataR s) (by simp [h.rd]) (contains_of (off_le _ _) (by omega)))
    (by
      intro i hi
      rw [hrd₁, hwr₁, hx3₁]
      exact mem_rdwr (s := s) (r := tableR s) (by simp [h.rd]) (contains_of (off_le _ _) (by omega)))
    ((s.vg.gpr .x2).toNat - 1) 0 s₁ (by omega) (Frame.refl _ _ _)
    (by rw [hv0₁, read_in hst0 (hout _ (by simp)), hH.1]; rfl)
    (by rw [hv1₁, read_in hst1 (hout _ (by simp)), hH.2]; rfl)
    (by simp) (by rw [hx2₁]; addr) rfl
  rw [hashBlocks_congr _ (by rw [hx1₁]; exact hdata)] at hv0₂ hv1₂
  have hx0₂ : s₂.vg.gpr .x0 = s.vg.gpr .x0 := (f₂.gpr _ (by decide)).trans hx0₁
  have hsp₂ : s₂.vg.sp = s.vg.sp - 16 := f₂.sp.trans hsp₁
  obtain ⟨s₃, e₃, hm₃, hsp₃, hx29₃, hg₃, hv₃⟩ := epilogue_ok s₂
    (by rw [hsp₂]; have := h.sp; bv_omega)
    (by rw [f₂.wr, hwr₁, hx0₂]; exact mem_wr hst hst0)
    (by rw [f₂.wr, hwr₁, hx0₂]; exact mem_wr hst hst1)
    (by rw [f₂.rd, f₂.wr, hrd₁, hwr₁, hsp₂]
        exact mem_rdwr (List.mem_append_right _ hfr) (contains_of (off := 0) (by simp []) (by omega)))
  refine ⟨s₃, ?_, ⟨?_, fun a ha hf => ?_, ⟨fun r hr => ?_, ?_, fun r hr => ?_⟩, ?_⟩⟩
  · have := Exec.seq (Exec.block e₁) (Exec.seq e₂ (Exec.block e₃))
    rwa [hx0₂, hsp₂, hx1₁, hx3₁] at this
  · rw [hm₃, hx0₂, f₂.mem, words8_write, hv0₂, hv1₂]
    simp only [abcd, efgh, vword_ofVWords_0, vword_ofVWords_1, vword_ofVWords_2, vword_ofVWords_3]
    exact list8 _ (s2n.length_hashBlocks _ _ (by simp [words8]) _)
  · rw [hm₃, hx0₂, state_other _ _ _ _ _ ha, f₂.mem, hm₁, frame_other _ _ _ _ _ hf]
  · rw [hg₃, f₂.gpr _ (by revert r hr; decide), hg₁ _ (by revert r hr; decide)]
  · rw [hsp₃, hsp₂, BitVec.sub_add_cancel]
  · rw [hv₃, f₂.v _ (by revert r hr; decide), hv₁ _ (by revert r hr; decide)]
  · rw [hx29₃, hsp₂, hm₃, hx0₂, f₂.mem]
    rw [read_in (r := frameR s) (m := s₁.vg.mem) (contains_of (off := 0) (by simp []) (by omega))
      fun x hx => state_other _ _ _ _ _ fun hs => h.disjoint (stateR s) (by simp) x hs hx]
    rw [hm₁, read_congr _ _ _ _ fun k hk => write_other _ _ _ _ _ (by bv_omega), read_write8]

theorem constant_time : ConstantTime Rind.AArch64.isa Pre Pub prog := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ ⟨e0, e1, e2, esp, ek⟩ x₁ x₂
  obtain ⟨_, y₁, -⟩ := correct s₁ h₁
  obtain ⟨_, y₂, -⟩ := correct s₂ h₂
  rw [(exec_det x₁ y₁).1, (exec_det x₂ y₂).1]
  simp only [trace, e0, e1, e2, esp, ek]

/-! ## The precondition holds of some state -/

/-- Memory holding the table at `k`, and zeros elsewhere. -/
def tableMem (k : Addr) : Mem := fun a =>
  if (a - k).toNat < 256 then (table[(a - k).toNat / 4]!).extractLsb' (8 * ((a - k).toNat % 4)) 8 else 0

theorem tableMem_at (k : Addr) {j c : Nat} (hj : j < 64) (hc : c < 4) :
    tableMem k (k + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c) = (table[j]!).extractLsb' (8 * c) 8 := by
  have : (k + BitVec.ofNat 64 (4 * j) + BitVec.ofNat 64 c - k).toNat = 4 * j + c := by
    rw [add_ofNat, add_sub_left, BitVec.toNat_ofNat]; omega
  simp only [tableMem, this, show 4 * j + c < 256 by omega, ite_true]
  congr <;> omega

theorem tableAt_tableMem (k : Addr) : TableAt (tableMem k) k := by
  intro j hj
  rw [read4]
  have h0 : tableMem k (k + BitVec.ofNat 64 (4 * j)) = (table[j]!).extractLsb' 0 8 := by
    simpa using tableMem_at k hj (c := 0) (by omega)
  have h1 : tableMem k (k + BitVec.ofNat 64 (4 * j) + 1) = (table[j]!).extractLsb' 8 8 :=
    tableMem_at k hj (c := 1) (by omega)
  have h2 : tableMem k (k + BitVec.ofNat 64 (4 * j) + 2) = (table[j]!).extractLsb' 16 8 :=
    tableMem_at k hj (c := 2) (by omega)
  have h3 : tableMem k (k + BitVec.ofNat 64 (4 * j) + 3) = (table[j]!).extractLsb' 24 8 :=
    tableMem_at k hj (c := 3) (by omega)
  rw [h0, h1, h2, h3]
  generalize table[j]! = w
  bv_decide

/-- A state the precondition holds of: one block at 512, the state at 0, the
table at 1024, and the stack pointer at 4096. -/
def witness : Rind.AArch64.State where
  vg := { gpr := fun r => if r = .x1 then 512 else if r = .x2 then 1 else 0, sp := 4096,
          mem := tableMem 1024, rd := [⟨512, 64⟩, ⟨1024, 256⟩], wr := [⟨0, 32⟩, ⟨4080, 16⟩],
          syms := fun _ => 1024 }
  x29 := 0

theorem pre_witness : Pre witness := by
  refine ⟨by decide, by decide, rfl, rfl, ?_, tableAt_tableMem _⟩
  intro r hr a h₁ h₂
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;>
    simp only [stateR, dataR, tableR, frameR, witness, Region.Contains] at h₁ h₂ <;>
    simp at h₁ h₂ <;> bv_omega

/-- The routine computes s2n-bignum's `sha256_hash_blocks` of the blocks,
keeping what AAPCS64 and its contract require; its trace depends only on its
arguments, the stack pointer, and the table's address; and some state meets
its precondition. -/
theorem sha256_block_data_order_hw_correct :
    (∀ s, Pre s → ∃ t s', Exec Rind.AArch64.isa prog s t s' ∧ Post s s') ∧
      ConstantTime Rind.AArch64.isa Pre Pub prog ∧ ∃ s, Pre s :=
  ⟨fun s h => let ⟨s', e, p⟩ := correct s h; ⟨_, s', e, p⟩, constant_time, _, pre_witness⟩

end rind.aarch64.sha256hw

/-- info: 'rind.aarch64.sha256hw.sha256_block_data_order_hw_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rind.aarch64.sha256hw.sha256_block_data_order_hw_correct
