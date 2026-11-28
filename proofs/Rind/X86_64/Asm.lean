import RindIsa.X86_64
import Mathlib.Tactic
import Std.Tactic.BVDecide

open VG VG.X86_64

/-!
# Running rind's x86_64 programs symbolically

What the proofs of aws-lc's routines on rind's extension of VG's x86_64
model (`RindIsa/X86_64.lean`) share: `simp` runs a block one instruction at
a time (`execAcc_cons`), keeping each state a term of folded updates
(`setReg`, `arithFlags`, `setMem`, `execMul`) whose projections it reads
through the lemmas below, and the products, carries, and addresses in forms
`omega` and `bv_omega` take.
-/

namespace rind.x86_64.asm

open Lean Elab Tactic in
/-- Runs `t` without error recovery, so that a discharger's failure stays a
failure rather than an error logged against an admitted goal, as the last
alternative of a `first` otherwise is. -/
elab "no_recover " t:tactic : tactic => withoutRecover (evalTactic t)

abbrev S := Rind.X86_64.State
abbrev I := Rind.X86_64.isa
abbrev Ins := Rind.X86_64.Instr

/-! ## Blocks, one instruction at a time -/

/-- The rest of a block, `is`, run from `o`, its trace appended to `acc`.
`execAcc_congr` keeps `simp` from running the rest of the block before the
instruction in front of it has run. -/
def execAcc (o : Option S) (acc : List Leak) (is : List Ins) : Option (S × List Leak) :=
  o.bind fun s => (execBlock I is s).map fun p => (p.1, acc ++ p.2)

@[congr] theorem execAcc_congr {o o' : Option S} {acc acc' : List Leak} (h : o = o') (h' : acc = acc')
    (is : List Ins) : execAcc o acc is = execAcc o' acc' is := h ▸ h' ▸ rfl

theorem execBlock_acc {is : List Ins} {s : S} : execBlock I is s = execAcc (some s) [] is := by
  simp only [execAcc, Option.bind_some, List.nil_append]
  cases execBlock I is s <;> rfl

theorem execAcc_cons {i : Ins} {is : List Ins} {s : S} {acc : List Leak} :
    execAcc (some s) acc (i :: is) =
      execAcc (Rind.X86_64.exec i s) (acc ++ (Rind.X86_64.addrs i s).map .addr) is := by
  simp only [execAcc, Option.bind_some]
  show ((execBlock I (i :: is) s).map _) = _
  simp only [execBlock]
  cases Rind.X86_64.exec i s with
  | none => rfl
  | some s₁ =>
    simp only [Option.bind_some, Option.map_map]
    cases execBlock I is s₁ <;> simp [I, List.append_assoc]

theorem execAcc_nil {s : S} {acc : List Leak} : execAcc (some s) acc [] = some (s, acc) := by
  simp [execAcc, execBlock]

theorem execBlock_append (a b : List Ins) (s : S) :
    execBlock I (a ++ b) s = (execBlock I a s).bind fun p =>
      (execBlock I b p.1).map fun q => (q.1, p.2 ++ q.2) := by
  induction a generalizing s with
  | nil => simp [execBlock]
  | cons i a ih =>
    simp only [List.cons_append, execBlock]
    cases Rind.X86_64.exec i s with
    | none => rfl
    | some s₁ =>
      simp only [ih]
      cases execBlock I a s₁ <;> simp [Function.comp_def]

/-- `Exec` is deterministic. -/
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

theorem ex_of_eq {α : Type} {o : Option (α × List Leak)} {x : α} {t t' : List Leak} {P : α → Prop}
    (h : o = some (x, t)) (ht : t = t') (hp : P x) : ∃ s', o = some (s', t') ∧ P s' :=
  ⟨x, ht ▸ h, hp⟩

/-! ## Folded state updates -/

/-- The state with memory `m`. -/
def setMem (s : VG.X86_64.State) (m : Mem) : VG.X86_64.State := { s with mem := m }

/-- The products `mul` leaves: the high and low words of `a·b`. -/
def mulHi (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat / 2 ^ 64)
def mulLo (a b : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (a.toNat * b.toNat)
/-- The carry out of `a + b`. -/
def carry (a b : BitVec 64) : Bool := decide (2 ^ 64 ≤ a.toNat + b.toNat)

theorem decide_carry (a b : BitVec 64) : decide (2 ^ 64 ≤ a.toNat + b.toNat) = carry a b := rfl

theorem decide_carry' (a b : BitVec 64) : decide (18446744073709551616 ≤ a.toNat + b.toNat) = carry a b := rfl

/-- What VG's state keeps that no instruction here but `ldmxcsr` changes. -/
def others (g : VG.X86_64.State) :=
  (g.ymmHi, g.zmmHi, g.ymmH, g.zmmHiH, g.mxcsr, g.rd, g.unknowns, g.syms)

section
variable (s : VG.X86_64.State)
@[simp] theorem gpr_setReg (d : Reg) (v : BitVec 64) (r : Reg) :
    (s.setReg d v).gpr r = if r = d then v else s.gpr r := rfl
@[simp] theorem mem_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).mem = s.mem := rfl
@[simp] theorem rd_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).rd = s.rd := rfl
@[simp] theorem wr_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).wr = s.wr := rfl
@[simp] theorem cf_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).cf = s.cf := rfl
@[simp] theorem zf_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).zf = s.zf := rfl
@[simp] theorem xmm_setReg (d : Reg) (v : BitVec 64) : (s.setReg d v).xmm = s.xmm := rfl
@[simp] theorem others_setReg (d : Reg) (v : BitVec 64) : others (s.setReg d v) = others s := rfl
@[simp] theorem gpr_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).gpr = s.gpr := rfl
@[simp] theorem mem_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).mem = s.mem := rfl
@[simp] theorem rd_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).rd = s.rd := rfl
@[simp] theorem wr_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).wr = s.wr := rfl
@[simp] theorem cf_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).cf = a := rfl
@[simp] theorem zf_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).zf = c := rfl
@[simp] theorem xmm_setFlags (a b c d : Option Bool) : (s.setFlags a b c d).xmm = s.xmm := rfl
@[simp] theorem others_setFlags (a b c d : Option Bool) : others (s.setFlags a b c d) = others s := rfl
@[simp] theorem gpr_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).gpr = s.gpr := rfl
@[simp] theorem mem_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).mem = s.mem := rfl
@[simp] theorem rd_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).rd = s.rd := rfl
@[simp] theorem wr_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).wr = s.wr := rfl
@[simp] theorem cf_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).cf = some c := rfl
@[simp] theorem zf_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) :
    (arithFlags s x c o).zf = some (x == 0) := rfl
@[simp] theorem xmm_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) : (arithFlags s x c o).xmm = s.xmm := rfl
@[simp] theorem others_arithFlags {w : Nat} (x : BitVec w) (c o : Bool) :
    others (arithFlags s x c o) = others s := rfl
@[simp] theorem gpr_setMem (m : Mem) : (setMem s m).gpr = s.gpr := rfl
@[simp] theorem mem_setMem (m : Mem) : (setMem s m).mem = m := rfl
@[simp] theorem rd_setMem (m : Mem) : (setMem s m).rd = s.rd := rfl
@[simp] theorem wr_setMem (m : Mem) : (setMem s m).wr = s.wr := rfl
@[simp] theorem cf_setMem (m : Mem) : (setMem s m).cf = s.cf := rfl
@[simp] theorem zf_setMem (m : Mem) : (setMem s m).zf = s.zf := rfl
@[simp] theorem xmm_setMem (m : Mem) : (setMem s m).xmm = s.xmm := rfl
@[simp] theorem others_setMem (m : Mem) : others (setMem s m) = others s := rfl

@[simp] theorem gpr_execImul (d r r' : Reg) : (execImul d r s).gpr r' =
    if r' = d then s.gpr d * s.gpr r else s.gpr r' := by
  simp only [execImul, VG.X86_64.State.setReg, VG.X86_64.State.setFlags]
  split_ifs
  · rw [BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt]
  · rfl
@[simp] theorem mem_execImul (d r : Reg) : (execImul d r s).mem = s.mem := rfl
@[simp] theorem rd_execImul (d r : Reg) : (execImul d r s).rd = s.rd := rfl
@[simp] theorem wr_execImul (d r : Reg) : (execImul d r s).wr = s.wr := rfl
@[simp] theorem xmm_execImul (d r : Reg) : (execImul d r s).xmm = s.xmm := rfl
@[simp] theorem others_execImul (d r : Reg) : others (execImul d r s) = others s := rfl

variable (r : Reg)
@[simp] theorem gpr_execMul (r' : Reg) : (execMul r s).gpr r' =
    if r' = .rdx then mulHi (s.gpr .rax) (s.gpr r) else if r' = .rax then mulLo (s.gpr .rax) (s.gpr r)
    else s.gpr r' := by
  simp only [execMul, mulHi, mulLo, VG.X86_64.State.setReg]; split_ifs <;> simp_all
@[simp] theorem mem_execMul : (execMul r s).mem = s.mem := rfl
@[simp] theorem rd_execMul : (execMul r s).rd = s.rd := rfl
@[simp] theorem wr_execMul : (execMul r s).wr = s.wr := rfl
@[simp] theorem xmm_execMul : (execMul r s).xmm = s.xmm := rfl
@[simp] theorem others_execMul : others (execMul r s) = others s := rfl
@[simp] theorem cf_execMul : (execMul r s).cf = some (mulHi (s.gpr .rax) (s.gpr r) != 0) := rfl

theorem load64_of {a : Addr} (h : InRegions (s.rd ++ s.wr) a 8) : s.load64 a = some (s.mem.readW a 64) := by
  simp [State.load64, h]
theorem store64_of {a : Addr} {v : BitVec 64} (h : InRegions s.wr a 8) :
    s.store64 a v = some (setMem s (s.mem.writeW a v)) := by
  simp [State.store64, h, setMem]
end

@[simp] theorem signExtend_zero : (0#32).signExtend 64 = 0 := by decide

theorem signExtend_zero' : (0 : BitVec 32).signExtend 64 = 0 := by decide

theorem ofNat_zero : BitVec.ofNat 64 0 = 0 := rfl

theorem add_zero' (x : BitVec 64) : x + 0 = x := BitVec.add_zero x

theorem zero_add' (x : BitVec 64) : 0 + x = x := BitVec.zero_add x

/-! ## Memory -/

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

@[simp] theorem add_sub_left (a c : BitVec 64) : a + c - a = c := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

theorem write_other (m : Mem) (a : Addr) (n : Nat) (v : BitVec (8 * n)) (x : Addr)
    (h : n ≤ (x - a).toNat) : m.write a n v x = m x := by
  simp only [Mem.write]; rw [ite_eq_right_iff.mpr (by omega)]

/-- The quadwords at `a` and `b` do not overlap. -/
def Apart (a b : Addr) : Prop := 8 ≤ (b - a).toNat ∧ 8 ≤ (a - b).toNat

theorem readW_writeW_sep (m : Mem) (a b : Addr) (v : BitVec 64) (h : Apart a b) :
    (m.writeW a v).readW b 64 = m.readW b 64 := by
  simp only [Mem.readW, Mem.writeW, Nat.reduceDiv, Nat.reduceMul]
  congr 1
  apply read_congr
  intro k hk
  apply write_other
  obtain ⟨h1, h2⟩ := h
  have : (b + BitVec.ofNat 64 k - a).toNat = (b - a).toNat + k := by
    have : (BitVec.ofNat 64 k).toNat = k := by simp; omega
    bv_omega
  omega

theorem readW_writeW_self (m : Mem) (a : Addr) (v : BitVec 64) : (m.writeW a v).readW a 64 = v := by
  simp only [Mem.readW, Mem.writeW, Mem.read, Mem.write, BitVec.add_assoc, BitVec.reduceAdd, add_sub_left,
    BitVec.sub_self, BitVec.toNat_ofNat, Nat.reduceDiv, Nat.reduceMul]
  simp only [BitVec.toNat_ofNat, BitVec.ofNat_eq_ofNat]
  bv_decide

theorem readW_writeW_eq (m : Mem) (a b : Addr) (v : BitVec 64) (h : a = b) :
    (m.writeW a v).readW b 64 = v := h ▸ readW_writeW_self m a v

theorem readW_writeW_disj (m : Mem) (a b : Addr) {w : Nat} (v : BitVec w) (w' : Nat)
    (h : w / 8 ≤ (b - a).toNat ∧ w' / 8 ≤ (a - b).toNat) : (m.writeW a v).readW b w' = m.readW b w' := by
  simp only [Mem.readW, Mem.writeW]
  congr 1
  apply read_congr
  intro k hk
  apply write_other
  obtain ⟨h1, h2⟩ := h
  have : (b + BitVec.ofNat 64 k - a).toNat = (b - a).toNat + k := by
    have : (BitVec.ofNat 64 k).toNat = k := by simp; omega
    bv_omega
  omega

/-- An access `n` bytes long at `a`, which lies in the region `r` of `rs`. -/
theorem inR {rs : List Region} {r : Region} {a : Addr} {n : Nat} (hr : r ∈ rs)
    (h : (a - r.base).toNat + n ≤ r.len) : InRegions rs a n := ⟨r, hr, h⟩

/-! ## Addresses

`simp` brings an indexed operand's address `b + x·8 + d`, for an index
`x = j + c` and constants `c` and `d`, to `b + (j + c')·8`, the form the
word `j + c'` of an array at `b` is read at. -/

theorem ofInt_lit (d : Int) : BitVec.ofInt 64 d = BitVec.ofNat 64 (d % 2 ^ 64).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofInt, BitVec.toNat_ofNat]
  omega

theorem ea_pos (b x : BitVec 64) (L : Nat) (h : L % 8 = 0 ∧ L < 2 ^ 63) :
    b + x * 8#64 + BitVec.ofNat 64 L = b + (x + BitVec.ofNat 64 (L / 8)) * 8#64 := by
  rw [BitVec.add_mul, ← BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ea_neg (b x : BitVec 64) (L : Nat) (h : L % 8 = 0 ∧ 2 ^ 63 ≤ L ∧ L < 2 ^ 64) :
    b + x * 8#64 + BitVec.ofNat 64 L = b + (x - BitVec.ofNat 64 ((2 ^ 64 - L) / 8)) * 8#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat, BitVec.toNat_sub]
  omega

/-- A displacement alone: the word `L / 8`. -/
theorem disp_pos (b : BitVec 64) (L : Nat) (h : L % 8 = 0 ∧ 0 < L ∧ L < 2 ^ 63) :
    b + BitVec.ofNat 64 L = b + BitVec.ofNat 64 (L / 8) * 8#64 := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat]
  omega

theorem ea_comb (b x y : BitVec 64) : b + x * 8#64 + y * 8#64 = b + (x + y) * 8#64 := by
  rw [BitVec.add_mul, BitVec.add_assoc]

theorem ofNat_add_pos (n L : Nat) (_h : L < 2 ^ 63) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 L = BitVec.ofNat 64 (n + L) := BitVec.ofNat_add_ofNat ..

theorem ofNat_add_neg (n L : Nat) (h : 2 ^ 63 ≤ L ∧ L < 2 ^ 64 ∧ 2 ^ 64 - L ≤ n) :
    BitVec.ofNat 64 n + BitVec.ofNat 64 L = BitVec.ofNat 64 (n - (2 ^ 64 - L)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem ofNat_sub_ofNat (n a c : Nat) (h : c ≤ a) :
    BitVec.ofNat 64 (n + a) - BitVec.ofNat 64 c = BitVec.ofNat 64 (n + (a - c)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-! ## Products and carries -/

theorem mul_toNat (a b : BitVec 64) :
    (mulHi a b).toNat * 2 ^ 64 + (mulLo a b).toNat = a.toNat * b.toNat := by
  have ha := a.isLt; have hb := b.isLt
  have : a.toNat * b.toNat < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
  simp only [mulHi, mulLo, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : a.toNat * b.toNat / 2 ^ 64 < 2 ^ 64)]
  omega

theorem mul_le (a b : BitVec 64) : a.toNat * b.toNat + 2 * 2 ^ 64 ≤ 2 ^ 64 * 2 ^ 64 + 1 := by
  have ha : a.toNat ≤ 2 ^ 64 - 1 := by have := a.isLt; omega
  have hb : b.toNat ≤ 2 ^ 64 - 1 := by have := b.isLt; omega
  have := Nat.mul_le_mul ha hb
  have e : (2 ^ 64 - 1) * (2 ^ 64 - 1) + 2 * 2 ^ 64 = 2 ^ 64 * 2 ^ 64 + 1 := by norm_num
  omega

theorem ofBool_toNat (c : Bool) : ((BitVec.ofBool c).setWidth 64).toNat = c.toNat := by
  cases c <;> rfl

/-- An add into `x` whose carry goes into `h`, the word above, which does not
overflow. -/
theorem addc_toNat (h x y : BitVec 64) (hb : h.toNat * 2 ^ 64 + x.toNat + y.toNat < 2 ^ 64 * 2 ^ 64) :
    (h + (BitVec.ofBool (carry x y)).setWidth 64).toNat * 2 ^ 64 + (x + y).toNat =
      h.toNat * 2 ^ 64 + x.toNat + y.toNat := by
  have hx := x.isLt; have hy := y.isLt
  simp only [BitVec.toNat_add, ofBool_toNat, carry]
  by_cases hc : 2 ^ 64 ≤ x.toNat + y.toNat
  · simp only [hc, decide_true, Bool.toNat_true]
    rw [Nat.mod_eq_of_lt (by omega : h.toNat + 1 < 2 ^ 64)]
    omega
  · simp only [hc, decide_false, Bool.toNat_false]
    omega

/-- `a·b + c` as `mul`, then `add` of `c` to the low word and `adc` of 0 to
the high one leave it: `(lo, hi)`. -/
def mac (a b c : BitVec 64) : BitVec 64 × BitVec 64 :=
  (c + mulLo a b, mulHi a b + (BitVec.ofBool (carry c (mulLo a b))).setWidth 64)

/-- `(lo, hi)` with `d` added, by `add` to `lo` and `adc` of 0 to `hi`. -/
def acc (p : BitVec 64 × BitVec 64) (d : BitVec 64) : BitVec 64 × BitVec 64 :=
  (p.1 + d, p.2 + (BitVec.ofBool (carry p.1 d)).setWidth 64)

theorem mac_toNat (a b c : BitVec 64) :
    (mac a b c).2.toNat * 2 ^ 64 + (mac a b c).1.toNat = a.toNat * b.toNat + c.toNat := by
  have h1 := mul_toNat a b; have h2 := mul_le a b; have h3 := c.isLt
  show (mulHi a b + (BitVec.ofBool (carry c (mulLo a b))).setWidth 64).toNat * 2 ^ 64 + (c + mulLo a b).toNat = _
  rw [addc_toNat _ _ _ (by linarith)]
  linarith

theorem acc_toNat (p : BitVec 64 × BitVec 64) (d : BitVec 64)
    (h : p.2.toNat * 2 ^ 64 + p.1.toNat + d.toNat < 2 ^ 64 * 2 ^ 64) :
    (acc p d).2.toNat * 2 ^ 64 + (acc p d).1.toNat = p.2.toNat * 2 ^ 64 + p.1.toNat + d.toNat :=
  addc_toNat _ _ _ h

/-! ## Frames and loops -/

/-- What a block leaves unchanged: the general registers but `gs`, and the rest of the state but memory and
the flags. -/
structure Frame (s s' : S) (gs : List Reg) : Prop where
  gpr : ∀ r, r ∉ gs → s'.vg.gpr r = s.vg.gpr r
  others : others s'.vg = others s.vg
  wr : s'.vg.wr = s.vg.wr
  xmm : s'.vg.xmm = s.vg.xmm
  lo : s'.lo = s.lo

theorem Frame.refl (s : S) (gs : List Reg) : Frame s s gs := ⟨fun _ _ => rfl, rfl, rfl, rfl, rfl⟩

theorem Frame.trans {s₁ s₂ s₃ : S} {gs : List Reg} (h₁ : Frame s₁ s₂ gs) (h₂ : Frame s₂ s₃ gs) :
    Frame s₁ s₃ gs :=
  ⟨fun r hr => (h₂.gpr r hr).trans (h₁.gpr r hr), h₂.others.trans h₁.others, h₂.wr.trans h₁.wr,
    h₂.xmm.trans h₁.xmm, h₂.lo.trans h₁.lo⟩

theorem Frame.mono {s s' : S} {gs gs' : List Reg} (h : Frame s s' gs) (hg : ∀ r ∈ gs, r ∈ gs') :
    Frame s s' gs' :=
  ⟨fun r hr => h.gpr r fun h' => hr (hg r h'), h.others, h.wr, h.xmm, h.lo⟩

theorem Frame.rd {s s' : S} {gs : List Reg} (h : Frame s s' gs) : s'.vg.rd = s.vg.rd :=
  congrArg (fun x => x.2.2.2.2.2.1) h.others

/-- A loop's trace from index `j`, `m + 1` iterations long, each `d` on from the last. -/
def loopTrace (T : Nat → List Leak) (d j : Nat) : Nat → List Leak
  | 0 => T j ++ [.branch false]
  | m + 1 => T j ++ .branch true :: loopTrace T d (j + d) m

/-- A loop that runs `m + 1` times: each iteration, from index `j` in range, keeps `Inv`, and continues
while `go j`. -/
theorem loop_ok {body : Prog I} {c : Rind.X86_64.Cond} (Inv : Nat → S → Prop) (R : Nat → Prop) (go : Nat → Bool)
    (T : Nat → List Leak) (d : Nat)
    (hstep : ∀ j s, Inv j s → R j → ∃ s', Exec I body s (T j) s' ∧ I.eval c s' = some (go j) ∧ Inv (j + d) s') :
    ∀ m j s, Inv j s → (∀ i ≤ m, R (j + d * i)) → (∀ i < m, go (j + d * i) = true) → go (j + d * m) = false →
      ∃ s', Exec I (.loop body c) s (loopTrace T d j m) s' ∧ Inv (j + d * (m + 1)) s' := by
  intro m
  induction m with
  | zero =>
    intro j s hI hR _ hg
    obtain ⟨s', hx, hc, hI'⟩ := hstep j s hI (by simpa using hR 0 (by omega))
    refine ⟨s', Exec.loopExit hx ?_, by simpa using hI'⟩
    rw [hc]; simpa using hg
  | succ m ih =>
    intro j s hI hR hgo hg
    obtain ⟨s₁, hx, hc, hI₁⟩ := hstep j s hI (by simpa using hR 0 (by omega))
    obtain ⟨s', hx', hI'⟩ := ih (j + d) s₁ hI₁
      (fun i hi => by have := hR (i + 1) (by omega); rwa [show j + d * (i + 1) = j + d + d * i by ring] at this)
      (fun i hi => by have := hgo (i + 1) (by omega); rwa [show j + d * (i + 1) = j + d + d * i by ring] at this)
      (by rwa [show j + d * (m + 1) = j + d + d * m by ring] at hg)
    refine ⟨s', Exec.loopNext hx (by rw [hc]; simpa using hgo 0 (by omega)) hx', ?_⟩
    rwa [show j + d * (m + 1 + 1) = j + d + d * (m + 1) by ring]

end rind.x86_64.asm
