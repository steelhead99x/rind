import RindIsa.AArch64

open VG VG.AArch64 Rind.AArch64

/-!
# A constant-time check for programs in rind's AArch64 model

`check` follows a program of rind's extension of VG's AArch64 model
(`RindIsa/AArch64.lean`) through which general-purpose registers, and
whether the flags, hold the same values in any two runs that start out
agreeing on a set of them, on the stack pointer, and on some statics'
addresses (`Agree`). It fails at a memory access whose address, or a branch
whose condition, it cannot show is the same in both runs, at a loop whose
invariant it does not find within its fuel, and at any instruction it does
not know. It treats every vector register and every byte of memory as
different in the two runs, so a value loaded from memory is too.

`constantTime_of_check`: where `check` succeeds, the program is
constant-time (`ConstantTime`) for `Agree` of the registers it started with:
it compares two runs that both finish without a fault.
Running `check` on a program of thousands of instructions is a computation
the kernel checks (`decide +kernel`), so the proof of each program is one
line, and rests on no axiom beyond Lean's.
-/

namespace rind.aarch64.taint

/-- The register of index `i`, inverting `Reg.index`. -/
def regOf : Nat → Reg
  | 0 => .x0 | 1 => .x1 | 2 => .x2 | 3 => .x3 | 4 => .x4 | 5 => .x5 | 6 => .x6 | 7 => .x7
  | 8 => .x8 | 9 => .x9 | 10 => .x10 | 11 => .x11 | 12 => .x12 | 13 => .x13 | 14 => .x14
  | 15 => .x15 | 16 => .x16 | 17 => .x17 | 19 => .x19 | 20 => .x20 | 21 => .x21 | 22 => .x22
  | 23 => .x23 | 24 => .x24 | 25 => .x25 | 26 => .x26 | 27 => .x27 | 28 => .x28 | _ => .x30

theorem regOf_index (r : Reg) : regOf r.index = r := by cases r <;> rfl

theorem index_inj {r r' : Reg} (h : r.index = r'.index) : r = r' := by
  rw [← regOf_index r, h, regOf_index]

/-- What two runs are known to agree on: the general-purpose registers whose
bits `regs` sets, by `Reg.index`, and NZCV if `flags`. -/
structure Taint where
  regs : Nat
  flags : Bool
  deriving DecidableEq, Repr

namespace Taint

/-- Whether the runs agree on `r`. -/
def pub (a : Taint) (r : Reg) : Bool := a.regs.testBit r.index

/-- `a`, agreeing on `r` if `b` and not otherwise. -/
def set (a : Taint) (r : Reg) (b : Bool) : Taint :=
  if a.pub r = b then a else { a with regs := a.regs ^^^ 2 ^ r.index }

/-- What both `a` and `b` agree on. -/
def meet (a b : Taint) : Taint := ⟨a.regs &&& b.regs, a.flags && b.flags⟩

/-- Whether `b` agrees on all `a` does. -/
def le (a b : Taint) : Bool := (a.regs &&& b.regs == a.regs) && (!a.flags || b.flags)

theorem pub_set (a : Taint) (r r' : Reg) (b : Bool) :
    (a.set r b).pub r' = if r' = r then b else a.pub r' := by
  unfold set
  split
  · split <;> simp_all
  · simp only [pub, Nat.testBit_xor, Nat.testBit_two_pow]
    split
    · subst r'; cases b <;> simp_all [pub]
    · have : r.index ≠ r'.index := fun h => by simp_all [index_inj h]
      simp [this]

@[simp] theorem flags_set (a : Taint) (r : Reg) (b : Bool) : (a.set r b).flags = a.flags := by
  unfold set; split <;> rfl

theorem pub_meet (a b : Taint) (r : Reg) : (a.meet b).pub r = (a.pub r && b.pub r) := by
  simp [meet, pub, Nat.testBit_and]

theorem pub_le {a b : Taint} (h : a.le b = true) {r : Reg} (hr : a.pub r = true) : b.pub r = true := by
  simp only [le, Bool.and_eq_true, beq_iff_eq] at h
  have := congrArg (·.testBit r.index) h.1
  simp only [Nat.testBit_and] at this
  simp only [pub] at hr ⊢
  simp_all

theorem flags_le {a b : Taint} (h : a.le b = true) (hf : a.flags = true) : b.flags = true := by
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.2 with h | h <;> simp_all

theorem meet_le_left (a b : Taint) : (a.meet b).le a = true := by
  simp only [le, meet, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨Nat.eq_of_testBit_eq fun i => ?_, ?_⟩
  · simp only [Nat.testBit_and]; cases a.regs.testBit i <;> simp
  · cases a.flags <;> simp

theorem meet_le_right (a b : Taint) : (a.meet b).le b = true := by
  simp only [le, meet, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨Nat.eq_of_testBit_eq fun i => ?_, ?_⟩
  · simp only [Nat.testBit_and]; cases a.regs.testBit i <;> cases b.regs.testBit i <;> simp
  · cases a.flags <;> cases b.flags <;> simp

theorem le_trans {a b c : Taint} (h₁ : a.le b = true) (h₂ : b.le c = true) : a.le c = true := by
  simp only [le, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h₁ h₂ ⊢
  refine ⟨Nat.eq_of_testBit_eq fun i => ?_, ?_⟩
  · have e₁ := congrArg (·.testBit i) h₁.1
    have e₂ := congrArg (·.testBit i) h₂.1
    simp only [Nat.testBit_and] at e₁ e₂ ⊢
    cases ha : a.regs.testBit i <;> cases hb : b.regs.testBit i <;> simp_all
  · rcases h₁.2 with h | h <;> rcases h₂.2 with h' | h' <;> simp_all

end Taint

/-- Two VG states agree on what `a` names, the stack pointer, and the
addresses of the statics `names`. -/
def AgreeV (names : List String) (a : Taint) (g₁ g₂ : VG.AArch64.State) : Prop :=
  (∀ r, a.pub r = true → g₁.gpr r = g₂.gpr r) ∧
  (a.flags = true → g₁.nf = g₂.nf ∧ g₁.zf = g₂.zf ∧ g₁.c = g₂.c ∧ g₁.vf = g₂.vf) ∧
  g₁.sp = g₂.sp ∧ ∀ n ∈ names, g₁.syms n = g₂.syms n

/-- Two states of rind's model agree on what `a` names, the stack pointer,
and the addresses of the statics `names`. -/
def Agree (names : List String) (a : Taint) (s₁ s₂ : Rind.AArch64.State) : Prop :=
  AgreeV names a s₁.vg s₂.vg

/-- `g'` keeps `g`'s general-purpose registers, flags, stack pointer, and
statics: it differs at most in vector registers and memory. -/
structure Same (g g' : VG.AArch64.State) : Prop where
  gpr : g'.gpr = g.gpr
  nf : g'.nf = g.nf
  zf : g'.zf = g.zf
  c : g'.c = g.c
  vf : g'.vf = g.vf
  sp : g'.sp = g.sp
  syms : g'.syms = g.syms

theorem Same.refl (g : VG.AArch64.State) : Same g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans {g g' g'' : VG.AArch64.State} (h : Same g g') (h' : Same g' g'') : Same g g'' :=
  ⟨h'.gpr.trans h.gpr, h'.nf.trans h.nf, h'.zf.trans h.zf, h'.c.trans h.c, h'.vf.trans h.vf,
    h'.sp.trans h.sp, h'.syms.trans h.syms⟩

theorem same_setV (g : VG.AArch64.State) (r : VReg) (x : BitVec 128) : Same g (g.setV r x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_store {g g' : VG.AArch64.State} {a : Addr} {n : Nat} {v : BitVec (8 * n)}
    (h : g.store a n v = some g') : Same g g' := by
  simp only [State.store] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_ldVecs {g g' : VG.AArch64.State} {a : Addr} {t : VReg} {k : Nat}
    (h : ldVecs g a t k = some g') : Same g g' := by
  induction k generalizing g a t with
  | zero => simp only [ldVecs, Option.some.injEq] at h; subst h; exact .refl _
  | succ k ih =>
    simp only [ldVecs, Option.bind_eq_some_iff] at h
    obtain ⟨x, -, h⟩ := h
    exact (same_setV g t x).trans (ih h)

theorem same_stVecs {g g' : VG.AArch64.State} {a : Addr} {t : VReg} {k : Nat}
    (h : stVecs g a t k = some g') : Same g g' := by
  induction k generalizing g a t with
  | zero => simp only [stVecs, Option.some.injEq] at h; subst h; exact .refl _
  | succ k ih =>
    simp only [stVecs, Option.bind_eq_some_iff] at h
    obtain ⟨g₁, h₁, h⟩ := h
    exact (same_store h₁).trans (ih h)

theorem same_ldReps {g g' : VG.AArch64.State} {a : Addr} {t : VReg} {k : Nat}
    (h : ldReps g a t k = some g') : Same g g' := by
  induction k generalizing g a t with
  | zero => simp only [ldReps, Option.some.injEq] at h; subst h; exact .refl _
  | succ k ih =>
    simp only [ldReps, Option.bind_eq_some_iff] at h
    obtain ⟨x, -, h⟩ := h
    exact (same_setV g t _).trans (ih h)

theorem same_stD {g g' : VG.AArch64.State} {a : Addr} {t1 t2 : VReg}
    (h : stD g a t1 t2 = some g') : Same g g' := by
  simp only [stD, Option.bind_eq_some_iff] at h
  obtain ⟨g₁, h₁, h⟩ := h
  exact (same_store h₁).trans (same_store h)

theorem same_ldD {g g' : VG.AArch64.State} {a : Addr} {t1 t2 : VReg}
    (h : ldD g a t1 t2 = some g') : Same g g' := by
  simp only [ldD] at h
  split at h
  · simp at h
  · simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨x, -, y, -, rfl⟩ := h
    exact (same_setV _ _ _).trans (same_setV _ _ _)

namespace AgreeV

variable {names : List String} {a : Taint} {g₁ g₂ : VG.AArch64.State}

theorem same (h : AgreeV names a g₁ g₂) {g₁' g₂' : VG.AArch64.State} (h₁ : Same g₁ g₁')
    (h₂ : Same g₂ g₂') : AgreeV names a g₁' g₂' := by
  obtain ⟨hg, hf, hsp, hsy⟩ := h
  refine ⟨fun r hr => ?_, fun hfl => ?_, ?_, fun n hn => ?_⟩
  · rw [h₁.gpr, h₂.gpr]; exact hg r hr
  · rw [h₁.nf, h₂.nf, h₁.zf, h₂.zf, h₁.c, h₂.c, h₁.vf, h₂.vf]; exact hf hfl
  · rw [h₁.sp, h₂.sp]; exact hsp
  · rw [h₁.syms, h₂.syms]; exact hsy n hn

theorem mono {b : Taint} (h : AgreeV names b g₁ g₂) (hab : a.le b = true) : AgreeV names a g₁ g₂ :=
  ⟨fun r hr => h.1 r (Taint.pub_le hab hr), fun hf => h.2.1 (Taint.flags_le hab hf), h.2.2⟩

theorem gpr (h : AgreeV names a g₁ g₂) {r : Reg} (hr : a.pub r = true) : g₁.gpr r = g₂.gpr r :=
  h.1 r hr

theorem read (h : AgreeV names a g₁ g₂) {r : Reg} (hr : a.pub r = true) (sz : Size) :
    g₁.read sz r = g₂.read sz r := by
  simp only [State.read, h.gpr hr]

theorem c (h : AgreeV names a g₁ g₂) (hf : a.flags = true) : g₁.c = g₂.c := (h.2.1 hf).2.2.1

theorem holds (h : AgreeV names a g₁ g₂) (hf : a.flags = true) (cc : CondCode) :
    cc.holds g₁ = cc.holds g₂ := by
  obtain ⟨hn, hz, hc, hv⟩ := h.2.1 hf
  cases cc <;> simp [CondCode.holds, hn, hz, hc, hv]

theorem write (h : AgreeV names a g₁ g₂) (d : Reg) {b : Bool} {v₁ v₂ : BitVec 64}
    (hv : b = true → v₁ = v₂) : AgreeV names (a.set d b) (g₁.write .x d v₁) (g₂.write .x d v₂) := by
  obtain ⟨hg, hf, hsp, hsy⟩ := h
  refine ⟨fun r hr => ?_, fun hfl => hf (by simpa using hfl), hsp, hsy⟩
  rw [Taint.pub_set] at hr
  simp only [State.write]
  split
  · simp_all
  · simp_all

theorem write32 (h : AgreeV names a g₁ g₂) (d : Reg) {v₁ v₂ : BitVec 32} :
    AgreeV names (a.set d false) (g₁.write .w d v₁) (g₂.write .w d v₂) := by
  obtain ⟨hg, hf, hsp, hsy⟩ := h
  refine ⟨fun r hr => ?_, fun hfl => hf (by simpa using hfl), hsp, hsy⟩
  rw [Taint.pub_set] at hr
  simp only [State.write]
  split <;> simp_all

theorem addWithCarry (h : AgreeV names a g₁ g₂) (d : Reg) {p : Bool} {x₁ y₁ x₂ y₂ : BitVec 64}
    {c₁ c₂ : Bool} (hp : p = true → x₁ = x₂ ∧ y₁ = y₂ ∧ c₁ = c₂) :
    AgreeV names { a.set d p with flags := p } (g₁.addWithCarry .x d x₁ y₁ c₁)
      (g₂.addWithCarry .x d x₂ y₂ c₂) := by
  have hw := h.write d (b := p) (v₁ := x₁ + y₁ + BitVec.ofNat 64 c₁.toNat)
    (v₂ := x₂ + y₂ + BitVec.ofNat 64 c₂.toNat) fun hp' => by
      obtain ⟨rfl, rfl, rfl⟩ := hp hp'; rfl
  refine ⟨hw.1, fun hfl => ?_, hw.2.2⟩
  obtain ⟨rfl, rfl, rfl⟩ := hp hfl
  simp [State.addWithCarry, State.write]

theorem flagsAdd (h : AgreeV names a g₁ g₂) {p : Bool} {x₁ y₁ x₂ y₂ : BitVec 64}
    (hp : p = true → x₁ = x₂ ∧ y₁ = y₂) :
    AgreeV names { a with flags := p } (g₁.flagsAdd x₁ y₁ true) (g₂.flagsAdd x₂ y₂ true) := by
  obtain ⟨hg, hf, hsp, hsy⟩ := h
  refine ⟨hg, fun hfl => ?_, hsp, hsy⟩
  obtain ⟨rfl, rfl⟩ := hp hfl
  simp [State.flagsAdd]

end AgreeV

/-! ## The check -/

/-- What an instruction leaves the runs agreeing on, from `a`; `none` if
its addresses may differ, or for an instruction `step` does not know. A
value from memory or a vector register is taken to differ. -/
def step (names : List String) : Rind.AArch64.Instr → Taint → Option Taint
  | .vg (.vop _), a | .vg (.align _), a => some a
  | .vg (.add .x d n m), a | .vg (.sub .x d n m), a | .vg (.mul .x d n m), a
  | .vg (.umulh d n m), a => some (a.set d (a.pub n && a.pub m))
  | .vg (.extr .x d n m _), a => some (a.set d (a.pub n && a.pub m))
  | .vg (.adds .x d n m), a | .vg (.subs .x d n m), a =>
    some { a.set d (a.pub n && a.pub m) with flags := a.pub n && a.pub m }
  | .vg (.adcs .x d n m), a | .vg (.sbcs .x d n m), a =>
    some { a.set d (a.pub n && a.pub m && a.flags) with flags := a.pub n && a.pub m && a.flags }
  | .vg (.adc .x d n m), a | .vg (.csel .x d n m), a =>
    some (a.set d (a.pub n && a.pub m && a.flags))
  | .vg (.cselc .x d n m _), a => some (a.set d (a.pub n && a.pub m && a.flags))
  | .vg (.subImm .x d n _), a | .vg (.lsr .x d n _), a => some (a.set d (a.pub n))
  | .vg (.movz .x d _ _), a => some (a.set d true)
  | .vg (.adrSym d name), a => some (a.set d (names.contains name))
  | .vg (.umov .x d _ _), a => some (a.set d false)
  | .vg (.stp _ _ n _), a => if a.pub n then some a else none
  | .ld1 _ _ _ n _, a | .st1 _ _ _ n _, a | .ld4r _ n _, a => if a.pub n then some a else none
  | .cmpImm n _, a => some { a with flags := a.pub n }
  | .subsImm d n _, a | .addsImm d n _, a => some { a.set d (a.pub n) with flags := a.pub n }
  | .andImm d n _ _, a => some (a.set d (a.pub n))
  | .neg d n, a | .movReg d n, a => some (a.set d (a.pub n))
  | .adcZr d n, a => some (a.set d (a.pub n && a.flags))
  | .ldpPost t1 t2 n _, a => if a.pub n then some ((a.set t1 false).set t2 false) else none
  | .ldrbReg t n m, a => if a.pub n && a.pub m then some (a.set t false) else none
  | .ldrbPreDec t n, a => if a.pub n then some (a.set t false) else none
  | .strbPostInc _ n, a => if a.pub n then some a else none
  | .umovB d _ _, a => some (a.set d false)
  | .stpDPre .., a | .stpD .., a | .ldpD .., a | .ldpDPost .., a => some a
  | _, _ => none

/-- Whether a branch on `c` goes the same way in both runs. -/
def condPub (a : Taint) : Rind.AArch64.Cond → Bool
  | .vg (.zero _ r) | .vg (.nonzero _ r) => a.pub r
  | .flags _ => a.flags

/-- A loop invariant: from `inv`, meet it with what the body `f` leaves
until the body keeps it, within `fuel` rounds; then what the body leaves,
if its condition is the same in both runs. -/
def loopFix (f : Taint → Option Taint) (c : Rind.AArch64.Cond) : Nat → Taint → Option Taint
  | 0, _ => none
  | fuel + 1, inv => (f inv).bind fun a' =>
    if inv.le a' then (if condPub a' c then some a' else none) else loopFix f c fuel (inv.meet a')

/-- What the runs of `c` agree on at its end, from `a`, or `none` if they
may leak differently. -/
def check (names : List String) : Prog Rind.AArch64.isa → Taint → Option Taint
  | .block is, a => is.foldlM (fun a i => step names i a) a
  | .seq c₁ c₂, a => (check names c₁ a).bind (check names c₂)
  | .ite c t e, a =>
    if condPub a c then (check names t a).bind fun at_ => (check names e a).map at_.meet else none
  | .loop body c, a => loopFix (check names body) c 64 a
  | _, _ => none

/-! ## Soundness -/

theorem ite_some {α : Type} {p : Prop} [Decidable p] {x y : α}
    (h : (if p then some x else none) = some y) : p ∧ x = y := by
  split at h <;> simp_all

theorem ite_none {α : Type} {p : Prop} [Decidable p] {o : Option α} {y : α}
    (h : (if p then o else none) = some y) : p ∧ o = some y := by
  split at h <;> simp_all

theorem Taint.set_self {a : Taint} {r : Reg} {b : Bool} (h : a.pub r = b) : a.set r b = a := by
  simp [Taint.set, h]

namespace AgreeV

variable {names : List String} {a : Taint} {g₁ g₂ : VG.AArch64.State}

/-- A write of the same value to a register the runs agree on. -/
theorem write_pub (h : AgreeV names a g₁ g₂) {d : Reg} (hd : a.pub d = true) {v₁ v₂ : BitVec 64}
    (hv : v₁ = v₂) : AgreeV names a (g₁.write .x d v₁) (g₂.write .x d v₂) := by
  have := h.write d (b := true) fun _ => hv
  rwa [Taint.set_self hd] at this

theorem setSp (h : AgreeV names a g₁ g₂) {p₁ p₂ : BitVec 64} (hp : p₁ = p₂) :
    AgreeV names a { g₁ with sp := p₁ } { g₂ with sp := p₂ } :=
  ⟨h.1, h.2.1, hp, h.2.2.2⟩

theorem advance (h : AgreeV names a g₁ g₂) {n : Reg} (hn : a.pub n = true) {b₁ b₂ : Addr}
    (hb : b₁ = b₂) (cnt : Nat) (post : Bool) :
    AgreeV names a (Rind.AArch64.advance g₁ n b₁ cnt post) (Rind.AArch64.advance g₂ n b₂ cnt post) := by
  unfold Rind.AArch64.advance
  split
  · exact h.write_pub hn (by rw [hb])
  · exact h

end AgreeV

theorem and_pub {a : Taint} {n m : Reg} (h : (a.pub n && a.pub m) = true) :
    a.pub n = true ∧ a.pub m = true := by simpa using h

theorem and3_pub {a : Taint} {n m : Reg} (h : (a.pub n && a.pub m && a.flags) = true) :
    a.pub n = true ∧ a.pub m = true ∧ a.flags = true := by simpa [Bool.and_assoc] using h

/-- `step_sound` for VG's instructions. -/
theorem vg_sound {names : List String} {a a' : Taint} {j : VG.AArch64.Instr}
    {g₁ g₂ g₁' g₂' : VG.AArch64.State} (h : step names (.vg j) a = some a')
    (hA : AgreeV names a g₁ g₂) (h₁ : VG.AArch64.exec j g₁ = some g₁')
    (h₂ : VG.AArch64.exec j g₂ = some g₂') :
    VG.AArch64.addrs j g₁ = VG.AArch64.addrs j g₂ ∧ AgreeV names a' g₁' g₂' := by
  cases j
  case vop o =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [VG.AArch64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨d₁, x₁⟩, -, rfl⟩ := h₁; obtain ⟨⟨d₂, x₂⟩, -, rfl⟩ := h₂
    exact ⟨rfl, hA.same (same_setV _ _ _) (same_setV _ _ _)⟩
  case align k =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA⟩
  case add sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.read (and_pub hp).1, hA.read (and_pub hp).2]⟩
  case sub sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.read (and_pub hp).1, hA.read (and_pub hp).2]⟩
  case mul sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.read (and_pub hp).1, hA.read (and_pub hp).2]⟩
  case umulh d n m =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.gpr (and_pub hp).1, hA.gpr (and_pub hp).2]⟩
  case extr sz d n m lsb =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.read (and_pub hp).1, hA.read (and_pub hp).2]⟩
  case adds sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.addWithCarry d fun hp =>
      ⟨hA.read (and_pub hp).1 _, hA.read (and_pub hp).2 _, rfl⟩⟩
  case subs sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.addWithCarry d fun hp =>
      ⟨hA.read (and_pub hp).1 _, by rw [hA.read (and_pub hp).2], rfl⟩⟩
  case adcs sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.addWithCarry d fun hp =>
      ⟨hA.read (and3_pub hp).1 _, hA.read (and3_pub hp).2.1 _, hA.c (and3_pub hp).2.2⟩⟩
  case sbcs sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.addWithCarry d fun hp =>
      ⟨hA.read (and3_pub hp).1 _, by rw [hA.read (and3_pub hp).2.1], hA.c (and3_pub hp).2.2⟩⟩
  case adc sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by
      rw [hA.read (and3_pub hp).1, hA.read (and3_pub hp).2.1, hA.c (and3_pub hp).2.2]⟩
  case csel sz d n m =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by
      rw [hA.read (and3_pub hp).1, hA.read (and3_pub hp).2.1, hA.c (and3_pub hp).2.2]⟩
  case cselc sz d n m cc =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by
      rw [hA.read (and3_pub hp).1, hA.read (and3_pub hp).2.1, hA.holds (and3_pub hp).2.2]⟩
  case subImm sz d n imm =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.read hp]⟩
  case lsr sz d n sh =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.read hp]⟩
  case movz sz d imm hw =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.write d fun _ => rfl⟩
  case adrSym d name =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [VG.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => hA.2.2.2 name (by simpa using hp)⟩
  case umov sz d n i =>
    cases sz <;> simp only [step, Option.some.injEq, reduceCtorEq] at h; subst h
    simp only [VG.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.write d fun hp => by simp at hp⟩
  case stp t1 t2 n off =>
    simp only [step] at h
    obtain ⟨hn, rfl⟩ := ite_some h
    simp only [VG.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.bind_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, hv₁⟩ := h₁; obtain ⟨u₂, hu₂, hv₂⟩ := h₂
    refine ⟨by simp only [VG.AArch64.addrs, hA.gpr hn], ?_⟩
    exact hA.same ((same_store hu₁).trans (same_store hv₁)) ((same_store hu₂).trans (same_store hv₂))
  all_goals simp [step] at h

theorem step_sound {names : List String} {a a' : Taint} {i : Rind.AArch64.Instr}
    {s₁ s₂ s₁' s₂' : Rind.AArch64.State} (h : step names i a = some a') (hA : Agree names a s₁ s₂)
    (h₁ : Rind.AArch64.exec i s₁ = some s₁') (h₂ : Rind.AArch64.exec i s₂ = some s₂') :
    Rind.AArch64.addrs i s₁ = Rind.AArch64.addrs i s₂ ∧ Agree names a' s₁' s₂' := by
  unfold Agree at hA ⊢
  cases i
  case vg j =>
    simp only [Rind.AArch64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨g₁, hg₁, rfl⟩ := h₁; obtain ⟨g₂, hg₂, rfl⟩ := h₂
    exact vg_sound h hA hg₁ hg₂
  case ld1 cnt ar t n post =>
    simp only [step] at h
    obtain ⟨hn, rfl⟩ := ite_some h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.gpr hn], ?_⟩
    exact (hA.same (same_ldVecs hu₁) (same_ldVecs hu₂)).advance hn (hA.gpr hn) _ _
  case st1 cnt ar t n post =>
    simp only [step] at h
    obtain ⟨hn, rfl⟩ := ite_some h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.gpr hn], ?_⟩
    exact (hA.same (same_stVecs hu₁) (same_stVecs hu₂)).advance hn (hA.gpr hn) _ _
  case ld4r t n post =>
    simp only [step] at h
    obtain ⟨hn, rfl⟩ := ite_some h
    simp only [Rind.AArch64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.gpr hn], ?_⟩
    have hB := hA.same (same_ldReps hu₁) (same_ldReps hu₂)
    cases post
    · exact hB
    · exact hB.write_pub hn (by rw [hA.gpr hn])
  case cmpImm n imm =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.flagsAdd fun hp => ⟨hA.gpr hp, rfl⟩⟩
  case subsImm d n imm =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.addWithCarry d fun hp => ⟨hA.gpr hp, rfl, rfl⟩⟩
  case addsImm d n imm =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.addWithCarry d fun hp => ⟨hA.gpr hp, rfl, rfl⟩⟩
  case andImm d n ones rot =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.gpr hp]⟩
  case adcZr d n =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by
      simp only [Bool.and_eq_true] at hp; rw [hA.gpr hp.1, hA.c hp.2]⟩
  case neg d m =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.gpr hp]⟩
  case movReg d m =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.write d fun hp => by rw [hA.gpr hp]⟩
  case ldpPost t1 t2 n imm =>
    simp only [step] at h
    obtain ⟨hn, rfl⟩ := ite_some h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨⟨h12, h1n, h2n, -⟩, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨x₁, -, y₁, -, rfl⟩ := h₁; obtain ⟨x₂, -, y₂, -, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.gpr hn], ?_⟩
    have hB := (hA.write t1 (b := false) (v₁ := x₁.setWidth 64) (v₂ := x₂.setWidth 64)
      (by simp)).write t2 (b := false) (v₁ := y₁.setWidth 64) (v₂ := y₂.setWidth 64) (by simp)
    refine hB.write_pub ?_ (by rw [hA.gpr hn])
    simp [Taint.pub_set, Ne.symm h2n, Ne.symm h1n, hn]
  case ldrbReg t n m =>
    simp only [step] at h
    obtain ⟨hp, rfl⟩ := ite_some h
    simp only [Rind.AArch64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨x₁, -, rfl⟩ := h₁; obtain ⟨x₂, -, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.gpr (and_pub hp).1, hA.gpr (and_pub hp).2], ?_⟩
    exact hA.write32 t
  case ldrbPreDec t n =>
    simp only [step] at h
    obtain ⟨hn, rfl⟩ := ite_some h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨x₁, -, rfl⟩ := h₁; obtain ⟨x₂, -, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.gpr hn], ?_⟩
    exact (hA.write_pub hn (by rw [hA.gpr hn])).write32 t
  case strbPostInc t n =>
    simp only [step] at h
    obtain ⟨hn, rfl⟩ := ite_some h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.gpr hn], ?_⟩
    exact (hA.same (same_store hu₁) (same_store hu₂)).write_pub hn (by rw [hA.gpr hn])
  case umovB d n i =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.write32 d⟩
  case stpDPre t1 t2 imm =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.2.2.1], ?_⟩
    exact (hA.same (same_stD hu₁) (same_stD hu₂)).setSp (by rw [hA.2.2.1])
  case stpD t1 t2 off =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    exact ⟨by simp only [Rind.AArch64.addrs, hA.2.2.1], hA.same (same_stD hu₁) (same_stD hu₂)⟩
  case ldpD t1 t2 off =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    exact ⟨by simp only [Rind.AArch64.addrs, hA.2.2.1], hA.same (same_ldD hu₁) (same_ldD hu₂)⟩
  case ldpDPost t1 t2 imm =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.AArch64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.AArch64.addrs, hA.2.2.1], ?_⟩
    exact (hA.same (same_ldD hu₁) (same_ldD hu₂)).setSp (by rw [hA.2.2.1])
  all_goals simp [step] at h

theorem eval_eq {names : List String} {a : Taint} {c : Rind.AArch64.Cond} {s₁ s₂ : Rind.AArch64.State}
    (hc : condPub a c = true) (hA : Agree names a s₁ s₂) :
    Rind.AArch64.isa.eval c s₁ = Rind.AArch64.isa.eval c s₂ := by
  cases c with
  | vg c =>
    cases c <;> simp only [condPub] at hc <;> simp [VG.AArch64.eval, hA.read hc]
  | flags cc => simp only [condPub] at hc; simp [hA.holds hc cc]

theorem block_sound {names : List String} :
    ∀ {is : List Rind.AArch64.Instr} {a a' : Taint} {s₁ s₂ s₁' s₂' : Rind.AArch64.State} {t₁ t₂ : List Leak},
      is.foldlM (fun a i => step names i a) a = some a' → Agree names a s₁ s₂ →
      execBlock Rind.AArch64.isa is s₁ = some (s₁', t₁) →
      execBlock Rind.AArch64.isa is s₂ = some (s₂', t₂) →
      t₁ = t₂ ∧ Agree names a' s₁' s₂'
  | [], a, a', s₁, s₂, s₁', s₂', t₁, t₂, h, hA, h₁, h₂ => by
    simp only [List.foldlM, pure, Option.some.injEq] at h
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; subst h
    exact ⟨rfl, hA⟩
  | i :: is, a, a', s₁, s₂, s₁', s₂', t₁, t₂, h, hA, h₁, h₂ => by
    simp only [List.foldlM, bind, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    simp only [execBlock] at h₁ h₂
    split at h₁
    · simp at h₁
    rename_i u₁ hu₁
    split at h₂
    · simp at h₂
    rename_i u₂ hu₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨⟨v₁, l₁⟩, hv₁, he₁⟩ := h₁
    obtain ⟨⟨v₂, l₂⟩, hv₂, he₂⟩ := h₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨hadr, hB⟩ := step_sound hb hA hu₁ hu₂
    obtain ⟨hl, hA'⟩ := block_sound h hB hv₁ hv₂
    refine ⟨?_, ?_⟩
    · rw [← he₁.2, ← he₂.2, hl]; exact congrArg (fun l => List.map Leak.addr l ++ l₂) hadr
    · rw [← he₁.1, ← he₂.1]; exact hA'

theorem loopFix_sound {f : Taint → Option Taint} {c : Rind.AArch64.Cond} :
    ∀ {fuel : Nat} {a a' : Taint}, loopFix f c fuel a = some a' →
      ∃ inv, inv.le a = true ∧ f inv = some a' ∧ inv.le a' = true ∧ condPub a' c = true
  | 0, a, a', h => by simp [loopFix] at h
  | fuel + 1, a, a', h => by
    simp only [loopFix, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    split at h
    · rename_i hle
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        refine ⟨a, ?_, hb, hle, hc⟩
        simp only [Taint.le, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true']
        refine ⟨Nat.and_self _, ?_⟩
        cases a.flags <;> simp
      · simp at h
    · obtain ⟨inv, h₁, h₂, h₃, h₄⟩ := loopFix_sound h
      exact ⟨inv, Taint.le_trans h₁ (Taint.meet_le_left _ _), h₂, h₃, h₄⟩

theorem check_sound {names : List String} :
    ∀ {c : Prog Rind.AArch64.isa} {a a' : Taint}, check names c a = some a' →
      ∀ {s₁ s₂ s₁' s₂' : Rind.AArch64.State} {t₁ t₂ : List Leak}, Agree names a s₁ s₂ →
        Exec Rind.AArch64.isa c s₁ t₁ s₁' → Exec Rind.AArch64.isa c s₂ t₂ s₂' →
        t₁ = t₂ ∧ Agree names a' s₁' s₂'
  | .block is, a, a', h, s₁, s₂, s₁', s₂', t₁, t₂, hA, e₁, e₂ => by
    cases e₁ with | block x₁ => cases e₂ with | block x₂ => exact block_sound h hA x₁ x₂
  | .seq c₁ c₂, a, a', h, s₁, s₂, s₁', s₂', t₁, t₂, hA, e₁, e₂ => by
    simp only [check, Option.bind_eq_some_iff] at h
    obtain ⟨b, hb, h⟩ := h
    cases e₁ with | seq x₁ y₁ => cases e₂ with | seq x₂ y₂ =>
    obtain ⟨ht, hB⟩ := check_sound hb hA x₁ x₂
    obtain ⟨ht', hA'⟩ := check_sound h hB y₁ y₂
    exact ⟨by rw [ht, ht'], hA'⟩
  | .ite c t e, a, a', h, s₁, s₂, s₁', s₂', t₁, t₂, hA, e₁, e₂ => by
    simp only [check] at h
    split at h
    · rename_i hc
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨at_, hat, ae, hae, rfl⟩ := h
      have hev := eval_eq hc hA
      cases e₁ with
      | iteT c₁ x₁ =>
        cases e₂ with
        | iteT c₂ x₂ =>
          obtain ⟨ht, hA'⟩ := check_sound hat hA x₁ x₂
          exact ⟨by rw [ht], AgreeV.mono hA' (Taint.meet_le_left _ _)⟩
        | iteF c₂ x₂ => rw [hev, c₂] at c₁; simp at c₁
      | iteF c₁ x₁ =>
        cases e₂ with
        | iteT c₂ x₂ => rw [hev, c₂] at c₁; simp at c₁
        | iteF c₂ x₂ =>
          obtain ⟨ht, hA'⟩ := check_sound hae hA x₁ x₂
          exact ⟨by rw [ht], AgreeV.mono hA' (Taint.meet_le_right _ _)⟩
    · simp at h
  | .loop body c, a, a', h, s₁, s₂, s₁', s₂', t₁, t₂, hA, e₁, e₂ => by
    simp only [check] at h
    obtain ⟨inv, hinv, hbody, hle, hc⟩ := loopFix_sound h
    have hI : Agree names inv s₁ s₂ := AgreeV.mono hA hinv
    clear hA h
    generalize hp : (Code.loop body c : Prog Rind.AArch64.isa) = p at e₁
    induction e₁ generalizing s₂ t₂ with
    | loopExit x₁ c₁ =>
      cases hp
      cases e₂ with
      | loopExit x₂ c₂ =>
        obtain ⟨ht, hA'⟩ := check_sound hbody hI x₁ x₂
        exact ⟨by rw [ht], hA'⟩
      | loopNext x₂ c₂ _ =>
        obtain ⟨-, hA'⟩ := check_sound hbody hI x₁ x₂
        rw [eval_eq hc hA', c₂] at c₁; simp at c₁
    | loopNext x₁ c₁ _ _ ih =>
      cases hp
      cases e₂ with
      | loopExit x₂ c₂ =>
        obtain ⟨-, hA'⟩ := check_sound hbody hI x₁ x₂
        rw [eval_eq hc hA', c₂] at c₁; simp at c₁
      | loopNext x₂ c₂ y₂ =>
        obtain ⟨ht, hA'⟩ := check_sound hbody hI x₁ x₂
        obtain ⟨ht', hA''⟩ := ih _ _ y₂ (AgreeV.mono hA' hle) rfl
        exact ⟨by rw [ht, ht'], hA''⟩
    | _ => cases hp
  | .call .., _, _, h, _, _, _, _, _, _, _, _, _ => by simp [check] at h
  | .frame .., _, _, h, _, _, _, _, _, _, _, _, _ => by simp [check] at h
  | .icall .., _, _, h, _, _, _, _, _, _, _, _, _ => by simp [check] at h

/-- Where `check` succeeds from `a`, `c` is constant-time for any two runs,
both finishing without a fault, from states that agree on what `a` names,
the stack pointer, and the statics `names`. -/
theorem constantTime_of_check {names : List String} {c : Prog Rind.AArch64.isa} {a a' : Taint}
    (h : check names c a = some a') : ConstantTime Rind.AArch64.isa (fun _ => True) (Agree names a) c :=
  fun _ _ _ _ _ _ _ _ hA e₁ e₂ => (check_sound h hA e₁ e₂).1

end rind.aarch64.taint
