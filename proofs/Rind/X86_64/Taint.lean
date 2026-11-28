import RindIsa.X86_64

open VG VG.X86_64 Rind.X86_64

/-!
# A constant-time check for programs in rind's x86_64 model

`check` follows a program of rind's extension of VG's x86_64 model
(`RindIsa/X86_64.lean`) through which general-purpose registers, and whether
CF and ZF, SF, and OF, hold the same values in any two runs that start out
agreeing on a set of them and on some statics' addresses (`Agree`). It
fails at a memory access whose address, or a branch whose condition, it
cannot show is the same in both runs, at a loop whose invariant it does not
find within its fuel, and at any instruction it does not know. It treats
every vector register and every byte of memory as different in the two
runs, so a value loaded from memory is too. CF stands apart from the other
three because `dec` and `inc` keep it: a count's `dec` then `jg` after a
carry chain on secrets branches on public flags.

`constantTime_of_check`: where `check` succeeds, the program is
constant-time (`ConstantTime`) for `Agree` of the registers it started with:
it compares two runs that both finish without a fault. Running `check` on
a program of thousands of instructions is a computation the kernel checks
(`decide +kernel`), so the proof of each program is one line, and rests on
no axiom beyond Lean's. It is `Rind/Aarch64/Taint.lean`'s check, for x86_64.
-/

namespace rind.x86_64.taint

/-- A register's bit in `Taint.regs`. -/
def idx : Reg → Nat
  | .rax => 0 | .rcx => 1 | .rdx => 2 | .rbx => 3 | .rsp => 4 | .rbp => 5 | .rsi => 6 | .rdi => 7
  | .r8 => 8 | .r9 => 9 | .r10 => 10 | .r11 => 11 | .r12 => 12 | .r13 => 13 | .r14 => 14
  | .r15 => 15

theorem idx_inj {r r' : Reg} (h : idx r = idx r') : r = r' := by
  cases r <;> cases r' <;> simp_all [idx]

/-- What two runs are known to agree on: the general-purpose registers whose
bits `regs` sets, by `idx`, CF if `cf`, and ZF, SF, and OF if `zso`. -/
structure Taint where
  regs : Nat
  cf : Bool
  zso : Bool
  deriving DecidableEq, Repr

namespace Taint

/-- Whether the runs agree on `r`. -/
def pub (a : Taint) (r : Reg) : Bool := a.regs.testBit (idx r)

/-- `a`, agreeing on `r` if `b` and not otherwise. -/
def set (a : Taint) (r : Reg) (b : Bool) : Taint :=
  if a.pub r = b then a else { a with regs := a.regs ^^^ 2 ^ idx r }

/-- `a`, agreeing on CF if `c` and on ZF, SF, and OF if `z`. -/
def flags (a : Taint) (c z : Bool) : Taint := { a with cf := c, zso := z }

/-- What both `a` and `b` agree on. -/
def meet (a b : Taint) : Taint := ⟨a.regs &&& b.regs, a.cf && b.cf, a.zso && b.zso⟩

/-- Whether `b` agrees on all `a` does. -/
def le (a b : Taint) : Bool :=
  (a.regs &&& b.regs == a.regs) && (!a.cf || b.cf) && (!a.zso || b.zso)

theorem pub_set (a : Taint) (r r' : Reg) (b : Bool) :
    (a.set r b).pub r' = if r' = r then b else a.pub r' := by
  unfold set
  split
  · split <;> simp_all
  · simp only [pub, Nat.testBit_xor, Nat.testBit_two_pow]
    split
    · subst r'; cases b <;> simp_all [pub]
    · have : idx r ≠ idx r' := fun h => by simp_all [idx_inj h]
      simp [this]

@[simp] theorem cf_set (a : Taint) (r : Reg) (b : Bool) : (a.set r b).cf = a.cf := by
  unfold set; split <;> rfl

@[simp] theorem zso_set (a : Taint) (r : Reg) (b : Bool) : (a.set r b).zso = a.zso := by
  unfold set; split <;> rfl

@[simp] theorem pub_flags (a : Taint) (c z : Bool) (r : Reg) : (a.flags c z).pub r = a.pub r := rfl

theorem pub_le {a b : Taint} (h : a.le b = true) {r : Reg} (hr : a.pub r = true) : b.pub r = true := by
  simp only [le, Bool.and_eq_true, beq_iff_eq] at h
  have := congrArg (·.testBit (idx r)) h.1.1
  simp only [Nat.testBit_and] at this
  simp only [pub] at hr ⊢
  simp_all

theorem cf_le {a b : Taint} (h : a.le b = true) (hf : a.cf = true) : b.cf = true := by
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.1.2 with h | h <;> simp_all

theorem zso_le {a b : Taint} (h : a.le b = true) (hf : a.zso = true) : b.zso = true := by
  simp only [le, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h.2 with h | h <;> simp_all

theorem le_refl (a : Taint) : a.le a = true := by
  simp only [le, Nat.and_self, beq_self_eq_true, Bool.true_and]
  cases a.cf <;> cases a.zso <;> rfl

theorem meet_le_left (a b : Taint) : (a.meet b).le a = true := by
  simp only [le, meet, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨Nat.eq_of_testBit_eq fun i => ?_, ?_⟩, ?_⟩
  · simp only [Nat.testBit_and]; cases a.regs.testBit i <;> simp
  · cases a.cf <;> simp
  · cases a.zso <;> simp

theorem meet_le_right (a b : Taint) : (a.meet b).le b = true := by
  simp only [le, meet, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨⟨Nat.eq_of_testBit_eq fun i => ?_, ?_⟩, ?_⟩
  · simp only [Nat.testBit_and]; cases a.regs.testBit i <;> cases b.regs.testBit i <;> simp
  · cases a.cf <;> cases b.cf <;> simp
  · cases a.zso <;> cases b.zso <;> simp

theorem le_trans {a b c : Taint} (h₁ : a.le b = true) (h₂ : b.le c = true) : a.le c = true := by
  simp only [le, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true'] at h₁ h₂ ⊢
  refine ⟨⟨Nat.eq_of_testBit_eq fun i => ?_, ?_⟩, ?_⟩
  · have e₁ := congrArg (·.testBit i) h₁.1.1
    have e₂ := congrArg (·.testBit i) h₂.1.1
    simp only [Nat.testBit_and] at e₁ e₂ ⊢
    cases ha : a.regs.testBit i <;> cases hb : b.regs.testBit i <;> simp_all
  · rcases h₁.1.2 with h | h <;> rcases h₂.1.2 with h' | h' <;> simp_all
  · rcases h₁.2 with h | h <;> rcases h₂.2 with h' | h' <;> simp_all

theorem set_self {a : Taint} {r : Reg} {b : Bool} (h : a.pub r = b) : a.set r b = a := by
  simp [set, h]

end Taint

/-- Whether the runs agree on a memory operand's address: on its base and
index registers. -/
def memPub (a : Taint) (m : MemOp) : Bool :=
  a.pub m.base && match m.index with
    | none => true
    | some i => a.pub i

/-- Whether the runs agree on the address of rind's memory operand: as
`memPub`, or the static's address, which they agree on for `names`. -/
def memPubR (names : List String) (a : Taint) : Rind.X86_64.Mem → Bool
  | .op m => memPub a m
  | .sym s => names.contains s.name

/-- Whether the runs agree on a source operand's address, if it has one. -/
def srcAddr (a : Taint) : Src → Bool
  | .mem m => memPub a m
  | _ => true

/-- Whether the runs agree on a source operand's value: a register they
agree on, or an immediate; memory they are taken to differ in. -/
def srcVal (a : Taint) : Src → Bool
  | .reg r => a.pub r
  | .imm _ => true
  | .mem _ => false

/-- Two VG states agree on what `a` names and the addresses of the statics
`names`. -/
def AgreeV (names : List String) (a : Taint) (g₁ g₂ : VG.X86_64.State) : Prop :=
  (∀ r, a.pub r = true → g₁.gpr r = g₂.gpr r) ∧
  (a.cf = true → g₁.cf = g₂.cf) ∧
  (a.zso = true → g₁.zf = g₂.zf ∧ g₁.sf = g₂.sf ∧ g₁.of = g₂.of) ∧
  ∀ n ∈ names, g₁.syms n = g₂.syms n

/-- Two states of rind's model agree on what `a` names and the addresses of
the statics `names`. -/
def Agree (names : List String) (a : Taint) (s₁ s₂ : Rind.X86_64.State) : Prop :=
  AgreeV names a s₁.vg s₂.vg

/-- `g'` keeps `g`'s general-purpose registers, flags, and statics: it
differs at most in vector registers and memory. -/
structure Same (g g' : VG.X86_64.State) : Prop where
  gpr : g'.gpr = g.gpr
  cf : g'.cf = g.cf
  zf : g'.zf = g.zf
  sf : g'.sf = g.sf
  of : g'.of = g.of
  syms : g'.syms = g.syms

theorem Same.refl (g : VG.X86_64.State) : Same g g := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Same.trans {g g' g'' : VG.X86_64.State} (h : Same g g') (h' : Same g' g'') : Same g g'' :=
  ⟨h'.gpr.trans h.gpr, h'.cf.trans h.cf, h'.zf.trans h.zf, h'.sf.trans h.sf, h'.of.trans h.of,
    h'.syms.trans h.syms⟩

theorem same_setXmm (g : VG.X86_64.State) (r : XReg) (x : BitVec 128) : Same g (g.setXmm r x) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_setV (g : VG.X86_64.State) (l : VLen) (r : XReg) (x y : BitVec 128) :
    Same g (g.setV l r x y) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_xop (g : VG.X86_64.State) (o : XOp) : Same g (o.exec g) := by
  cases o <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_vop (g : VG.X86_64.State) (o : VOp) : Same g (o.exec g) := by
  cases o
  case vinserti128 => simp only [VOp.exec]; split <;> exact same_setV _ _ _ _ _
  all_goals exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_store64 {g g' : VG.X86_64.State} {a : Addr} {v : BitVec 64}
    (h : g.store64 a v = some g') : Same g g' := by
  simp only [VG.X86_64.State.store64] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_store8 {g g' : VG.X86_64.State} {a : Addr} {v : BitVec 8}
    (h : g.store8 a v = some g') : Same g g' := by
  simp only [VG.X86_64.State.store8] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_store128 {g g' : VG.X86_64.State} {a : Addr} {v : BitVec 128}
    (h : g.store128 a v = some g') : Same g g' := by
  simp only [VG.X86_64.State.store128] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem same_store256 {g g' : VG.X86_64.State} {a : Addr} {v : BitVec 256}
    (h : g.store256 a v = some g') : Same g g' := by
  simp only [VG.X86_64.State.store256] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `moveSp` moves `rsp` to `v` and changes no other register, flag, or
static. -/
theorem moveSp_vg {s s' : Rind.X86_64.State} {v : Addr} (h : moveSp s v = some s') :
    Same (s.vg.setReg .rsp v) s'.vg := by
  simp only [moveSp, Option.bind_eq_some_iff] at h
  obtain ⟨n, -, h⟩ := h
  split at h
  · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · split at h
    · simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    · simp at h

namespace AgreeV

variable {names : List String} {a : Taint} {g₁ g₂ : VG.X86_64.State}

theorem same (h : AgreeV names a g₁ g₂) {g₁' g₂' : VG.X86_64.State} (h₁ : Same g₁ g₁')
    (h₂ : Same g₂ g₂') : AgreeV names a g₁' g₂' := by
  obtain ⟨hg, hc, hz, hsy⟩ := h
  refine ⟨fun r hr => ?_, fun hf => ?_, fun hf => ?_, fun n hn => ?_⟩
  · rw [h₁.gpr, h₂.gpr]; exact hg r hr
  · rw [h₁.cf, h₂.cf]; exact hc hf
  · rw [h₁.zf, h₂.zf, h₁.sf, h₂.sf, h₁.of, h₂.of]; exact hz hf
  · rw [h₁.syms, h₂.syms]; exact hsy n hn

theorem mono {b : Taint} (h : AgreeV names b g₁ g₂) (hab : a.le b = true) : AgreeV names a g₁ g₂ :=
  ⟨fun r hr => h.1 r (Taint.pub_le hab hr), fun hf => h.2.1 (Taint.cf_le hab hf),
    fun hf => h.2.2.1 (Taint.zso_le hab hf), h.2.2.2⟩

theorem gpr (h : AgreeV names a g₁ g₂) {r : Reg} (hr : a.pub r = true) : g₁.gpr r = g₂.gpr r :=
  h.1 r hr

theorem cf (h : AgreeV names a g₁ g₂) (hf : a.cf = true) : g₁.cf = g₂.cf := h.2.1 hf

theorem zso (h : AgreeV names a g₁ g₂) (hf : a.zso = true) :
    g₁.zf = g₂.zf ∧ g₁.sf = g₂.sf ∧ g₁.of = g₂.of := h.2.2.1 hf

theorem sym (h : AgreeV names a g₁ g₂) {n : String} (hn : names.contains n = true) :
    g₁.syms n = g₂.syms n :=
  h.2.2.2 n (by simpa using hn)

theorem ea (h : AgreeV names a g₁ g₂) {m : MemOp} (hm : memPub a m = true) : g₁.ea m = g₂.ea m := by
  simp only [memPub, Bool.and_eq_true] at hm
  simp only [VG.X86_64.State.ea]
  cases hi : m.index with
  | none => simp [h.gpr hm.1]
  | some i => rw [hi] at hm; simp [h.gpr hm.1, h.gpr hm.2]

theorem eaR (h : AgreeV names a g₁ g₂) {m : Rind.X86_64.Mem} (hm : memPubR names a m = true) :
    m.ea g₁ = m.ea g₂ := by
  cases m with
  | op m => exact h.ea hm
  | sym s => simp only [Rind.X86_64.Mem.ea, h.sym hm]

theorem readSrc (h : AgreeV names a g₁ g₂) {src : Src} (hs : srcVal a src = true) :
    VG.X86_64.readSrc g₁ src = VG.X86_64.readSrc g₂ src := by
  cases src with
  | reg r => simp [VG.X86_64.readSrc, h.gpr hs]
  | imm v => rfl
  | mem m => simp [srcVal] at hs

theorem srcAddrs (h : AgreeV names a g₁ g₂) {src : Src} (hs : srcAddr a src = true) :
    VG.X86_64.srcAddrs g₁ src = VG.X86_64.srcAddrs g₂ src := by
  cases src with
  | mem m => simp [VG.X86_64.srcAddrs, h.ea hs]
  | _ => rfl

theorem setReg (h : AgreeV names a g₁ g₂) (d : Reg) {b : Bool} {v₁ v₂ : BitVec 64}
    (hv : b = true → v₁ = v₂) : AgreeV names (a.set d b) (g₁.setReg d v₁) (g₂.setReg d v₂) := by
  obtain ⟨hg, hc, hz, hsy⟩ := h
  refine ⟨fun r hr => ?_, fun hf => hc (by simpa using hf), fun hf => hz (by simpa using hf), hsy⟩
  rw [Taint.pub_set] at hr
  simp only [VG.X86_64.State.setReg]
  split <;> simp_all

theorem setFlags (h : AgreeV names a g₁ g₂) {c z : Bool} {cf₁ cf₂ of₁ of₂ zf₁ zf₂ sf₁ sf₂ : Option Bool}
    (hc : c = true → cf₁ = cf₂) (hz : z = true → of₁ = of₂ ∧ zf₁ = zf₂ ∧ sf₁ = sf₂) :
    AgreeV names (a.flags c z) (g₁.setFlags cf₁ of₁ zf₁ sf₁) (g₂.setFlags cf₂ of₂ zf₂ sf₂) := by
  obtain ⟨hg, -, -, hsy⟩ := h
  refine ⟨hg, fun hf => hc hf, fun hf => ?_, hsy⟩
  obtain ⟨h1, h2, h3⟩ := hz hf
  exact ⟨h2, h3, h1⟩

/-- An arithmetic or logic result `r` and its flags, written to `d`: the
runs agree on both if `p`. -/
theorem arith (h : AgreeV names a g₁ g₂) (d : Reg) {p : Bool} {r₁ r₂ : BitVec 64}
    {c₁ c₂ o₁ o₂ : Bool} (hp : p = true → r₁ = r₂ ∧ c₁ = c₂ ∧ o₁ = o₂) :
    AgreeV names ((a.flags p p).set d p) ((arithFlags g₁ r₁ c₁ o₁).setReg d r₁)
      ((arithFlags g₂ r₂ c₂ o₂).setReg d r₂) :=
  (h.setFlags (fun hp' => by rw [(hp hp').2.1]) fun hp' => by
    obtain ⟨rfl, rfl, rfl⟩ := hp hp'; exact ⟨rfl, rfl, rfl⟩).setReg d fun hp' => (hp hp').1

/-- `arith` for an operation that writes no register, `cmp` and `test`. -/
theorem arithFlags (h : AgreeV names a g₁ g₂) {p : Bool} {r₁ r₂ : BitVec 64} {c₁ c₂ o₁ o₂ : Bool}
    (hp : p = true → r₁ = r₂ ∧ c₁ = c₂ ∧ o₁ = o₂) :
    AgreeV names (a.flags p p) (VG.X86_64.arithFlags g₁ r₁ c₁ o₁)
      (VG.X86_64.arithFlags g₂ r₂ c₂ o₂) :=
  h.setFlags (fun hp' => by rw [(hp hp').2.1]) fun hp' => by
    obtain ⟨rfl, rfl, rfl⟩ := hp hp'; exact ⟨rfl, rfl, rfl⟩

/-- Flags, then a register: the runs agree on CF if `c`, on ZF, SF, and OF
if `z`, and on `d` if `p`. -/
theorem flagsReg (h : AgreeV names a g₁ g₂) (d : Reg) {c z p : Bool}
    {cf₁ cf₂ of₁ of₂ zf₁ zf₂ sf₁ sf₂ : Option Bool} {v₁ v₂ : BitVec 64}
    (hc : c = true → cf₁ = cf₂) (hz : z = true → of₁ = of₂ ∧ zf₁ = zf₂ ∧ sf₁ = sf₂)
    (hv : p = true → v₁ = v₂) :
    AgreeV names ((a.flags c z).set d p) ((g₁.setFlags cf₁ of₁ zf₁ sf₁).setReg d v₁)
      ((g₂.setFlags cf₂ of₂ zf₂ sf₂).setReg d v₂) :=
  (h.setFlags hc hz).setReg d hv

/-- An arithmetic result of any width `r` and its flags, then `v` written
to `d`: the runs agree on all of them if `p`. -/
theorem arithW (h : AgreeV names a g₁ g₂) (d : Reg) {p : Bool} {w : Nat} {r₁ r₂ : BitVec w}
    {v₁ v₂ : BitVec 64} {c₁ c₂ o₁ o₂ : Bool} (hp : p = true → r₁ = r₂ ∧ v₁ = v₂ ∧ c₁ = c₂ ∧ o₁ = o₂) :
    AgreeV names ((a.flags p p).set d p) ((VG.X86_64.arithFlags g₁ r₁ c₁ o₁).setReg d v₁)
      ((VG.X86_64.arithFlags g₂ r₂ c₂ o₂).setReg d v₂) :=
  h.flagsReg d (fun hp' => by rw [(hp hp').2.2.1]) (fun hp' => by
    obtain ⟨rfl, -, rfl, rfl⟩ := hp hp'; exact ⟨rfl, rfl, rfl⟩) fun hp' => (hp hp').2.1

/-- `arithFlags` of any width. -/
theorem arithFlagsW (h : AgreeV names a g₁ g₂) {p : Bool} {w : Nat} {r₁ r₂ : BitVec w}
    {c₁ c₂ o₁ o₂ : Bool} (hp : p = true → r₁ = r₂ ∧ c₁ = c₂ ∧ o₁ = o₂) :
    AgreeV names (a.flags p p) (VG.X86_64.arithFlags g₁ r₁ c₁ o₁)
      (VG.X86_64.arithFlags g₂ r₂ c₂ o₂) :=
  h.setFlags (fun hp' => by rw [(hp hp').2.1]) fun hp' => by
    obtain ⟨rfl, rfl, rfl⟩ := hp hp'; exact ⟨rfl, rfl, rfl⟩

theorem readSrc32 (h : AgreeV names a g₁ g₂) {src : Src} (hs : srcVal a src = true) :
    VG.X86_64.readSrc32 g₁ src = VG.X86_64.readSrc32 g₂ src := by
  cases src with
  | reg r => simp [VG.X86_64.readSrc32, h.gpr hs]
  | imm v => rfl
  | mem m => simp [srcVal] at hs

/-- `if c then` a write of `t` to `d` `else` nothing, as a write. -/
theorem setReg_ite (g : VG.X86_64.State) (d : Reg) (c : Bool) (t : BitVec 64) :
    (if c then g.setReg d t else g) = g.setReg d (if c then t else g.gpr d) := by
  cases c
  · simp only [Bool.false_eq_true, ite_false, VG.X86_64.State.setReg]
    cases g; simp only [VG.X86_64.State.mk.injEq, and_true]
    funext r; split <;> simp_all
  · rfl

/-- A write of the same value to a register the runs agree on. -/
theorem setReg_pub (h : AgreeV names a g₁ g₂) {d : Reg} (hd : a.pub d = true) {v₁ v₂ : BitVec 64}
    (hv : v₁ = v₂) : AgreeV names a (g₁.setReg d v₁) (g₂.setReg d v₂) := by
  have := h.setReg d (b := true) fun _ => hv
  rwa [Taint.set_self hd] at this

end AgreeV

/-! ## The check -/

/-- Whether a branch on VG's condition `c` goes the same way in both runs. -/
def vgCondPub (a : Taint) : VG.X86_64.Cond → Bool
  | .e | .ne => a.zso
  | .b | .ae => a.cf

/-- Whether a branch on `c` goes the same way in both runs. -/
def condPub (a : Taint) : Rind.X86_64.Cond → Bool
  | .vg c => vgCondPub a c
  | .a | .be => a.cf && a.zso
  | .g | .ge | .l | .le => a.zso
  | .rcxz | .rcxnz => a.pub .rcx

/-- What VG's arithmetic and logic instruction `op` of `d` and `src` leaves
the runs agreeing on, from `a`. -/
def aluStep (op : AluOp) (d : Reg) (src : Src) (a : Taint) : Option Taint :=
  if srcAddr a src then
    let p := a.pub d && srcVal a src && (if op = .adc ∨ op = .sbb then a.cf else true)
    some (if op = .cmp ∨ op = .test then a.flags p p else (a.flags p p).set d p)
  else none

/-- What VG's instruction leaves the runs agreeing on, from `a`; `none` if
its addresses may differ, or for an instruction `step` does not know. A
value from memory or a vector register is taken to differ. -/
def vgStep (names : List String) : VG.X86_64.Instr → Taint → Option Taint
  | .mov d src, a => if srcAddr a src then some (a.set d (srcVal a src)) else none
  | .store m _, a => if memPub a m then some a else none
  | .alu op d src, a => aluStep op d src a
  | .alu32 op d src, a => aluStep op d src a
  | .shift .ror _ _, _ => none
  | .shift _ d _, a => some (a.flags (a.pub d) (a.pub d))
  | .mul r, a =>
    let p := a.pub .rax && a.pub r
    some (((a.flags p p).set .rax p).set .rdx p)
  | .imul d r, a | .shld d r _, a =>
    let p := a.pub d && a.pub r
    some ((a.flags p p).set d p)
  | .mulx hi lo src, a =>
    if srcAddr a src then
      let p := a.pub .rdx && srcVal a src
      some ((a.set lo p).set hi p)
    else none
  | .cmov c d src, a =>
    if srcAddr a src then some (a.set d (a.pub d && srcVal a src && vgCondPub a c)) else none
  | .movzx8 d m, a => if memPub a m then some (a.set d false) else none
  | .movqR d _, a => some (a.set d false)
  | .leaSym d n, a => some (a.set d (names.contains n))
  | .xop _, a | .vop _, a => some a
  | .movdquLoad _ m, a | .movdquStore m _, a | .vmovdquLoad _ _ m, a | .vmovdquStore _ m _, a
  | .vbroadcasti128 _ m, a | .vbinLoad _ _ _ _ m, a => if memPub a m then some a else none
  | _, _ => none

/-- What an instruction leaves the runs agreeing on, from `a`; `none` if
its addresses may differ, or for an instruction `step` does not know. -/
def step (names : List String) : Rind.X86_64.Instr → Taint → Option Taint
  | .vg i, a => vgStep names i a
  | .push _, a => if a.pub .rsp then some a else none
  | .pop r, a => if a.pub .rsp then some (a.set r false) else none
  | .aluRsp _ _, a => some (a.flags (a.pub .rsp) (a.pub .rsp))
  | .lea d m, a => some (a.set d (memPub a m))
  | .leaSym d m, a => some (a.set d (names.contains m.name))
  | .dec d, a | .inc d, a => some (a.flags a.cf (a.pub d))
  | .shrd d r _, a =>
    let p := a.pub d && a.pub r
    some ((a.flags p p).set d p)
  | .cmov c d r, a => some (a.set d (a.pub d && a.pub r && condPub a c))
  | .movdqaLoad _ m, a | .movdqaStore m _, a | .vmovdqaStore _ m _, a | .pinsrb _ m _, a
  | .pextrb m _ _, a => if memPub a m then some a else none
  | .xload _ _ m, a | .vmovdqaLoad _ _ m, a => if memPubR names a m then some a else none
  | .vbinSym _ _ _ _ m, a => if names.contains m.name then some a else none
  | .pextrq d _ _, a => some (a.set d false)
  | .align _, a => some a
  | _, _ => none

/-- A loop invariant: from `inv`, meet it with what the body `f` leaves
until the body keeps it, within `fuel` rounds; then what the body leaves,
if its condition is the same in both runs. -/
def loopFix (f : Taint → Option Taint) (c : Rind.X86_64.Cond) : Nat → Taint → Option Taint
  | 0, _ => none
  | fuel + 1, inv => (f inv).bind fun a' =>
    if inv.le a' then (if condPub a' c then some a' else none) else loopFix f c fuel (inv.meet a')

/-- What the runs of `c` agree on at its end, from `a`, or `none` if they
may leak differently. -/
def check (names : List String) : Prog Rind.X86_64.isa → Taint → Option Taint
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

theorem and_pub {a b : Bool} (h : (a && b) = true) : a = true ∧ b = true := by simpa using h

theorem and3_pub {a b c : Bool} (h : (a && b && c) = true) : a = true ∧ b = true ∧ c = true := by
  simpa [Bool.and_assoc] using h

section
variable {names : List String} {a : Taint} {g₁ g₂ : VG.X86_64.State}

theorem vgCond_eq (hA : AgreeV names a g₁ g₂) {c : VG.X86_64.Cond} (hc : vgCondPub a c = true) :
    VG.X86_64.eval c g₁ = VG.X86_64.eval c g₂ := by
  cases c <;> simp only [vgCondPub] at hc
  · simp [VG.X86_64.eval, (hA.zso hc).1]
  · simp [VG.X86_64.eval, (hA.zso hc).1]
  · simp [VG.X86_64.eval, hA.cf hc]
  · simp [VG.X86_64.eval, hA.cf hc]

theorem cond_eq (hA : AgreeV names a g₁ g₂) {c : Rind.X86_64.Cond} (hc : condPub a c = true) :
    Rind.X86_64.eval c g₁ = Rind.X86_64.eval c g₂ := by
  cases c with
  | vg c => exact vgCond_eq hA hc
  | a | be =>
    obtain ⟨h1, h2⟩ := and_pub hc
    simp [Rind.X86_64.eval, hA.cf h1, (hA.zso h2).1]
  | g | ge | l | le =>
    obtain ⟨hz, hs, ho⟩ := hA.zso hc
    simp [Rind.X86_64.eval, hz, hs, ho]
  | rcxz | rcxnz => simp [Rind.X86_64.eval, hA.gpr hc]

/-- `aluStep`'s soundness, for VG's 64-bit and 32-bit forms alike, from
what each computes once it has read its source. -/
theorem alu_sound {op : AluOp} {d : Reg} {src : Src} {a' : Taint} {g₁' g₂' : VG.X86_64.State}
    (h : aluStep op d src a = some a') (hA : AgreeV names a g₁ g₂)
    (h₁ : execAlu op d src g₁ = some g₁') (h₂ : execAlu op d src g₂ = some g₂') :
    AgreeV names a' g₁' g₂' := by
  simp only [aluStep] at h
  obtain ⟨-, rfl⟩ := ite_some h
  simp only [execAlu, Option.bind_eq_some_iff] at h₁ h₂
  obtain ⟨b₁, hb₁, h₁⟩ := h₁; obtain ⟨b₂, hb₂, h₂⟩ := h₂
  have hv : (a.pub d && srcVal a src) = true → g₁.gpr d = g₂.gpr d ∧ b₁ = b₂ := fun hp => by
    obtain ⟨hd, hs⟩ := and_pub hp
    refine ⟨hA.gpr hd, ?_⟩
    have := hA.readSrc hs; rw [hb₁, hb₂] at this; exact Option.some.inj this
  cases op <;> simp only [Option.some.injEq, Option.map_eq_some_iff, reduceCtorEq, or_false,
    or_self, ite_true, ite_false] at h₁ h₂ ⊢
  case add =>
    subst h₁ h₂
    exact hA.arith d fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  case adc =>
    obtain ⟨c₁, hc₁, rfl⟩ := h₁; obtain ⟨c₂, hc₂, rfl⟩ := h₂
    exact hA.arith d fun hp => by
      obtain ⟨hp', hc⟩ := and_pub hp
      obtain ⟨e1, e2⟩ := hv hp'
      have := hA.cf hc; rw [hc₁, hc₂] at this; cases Option.some.inj this
      rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  case sub =>
    subst h₁ h₂
    exact hA.arith d fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  case sbb =>
    obtain ⟨c₁, hc₁, rfl⟩ := h₁; obtain ⟨c₂, hc₂, rfl⟩ := h₂
    exact hA.arith d fun hp => by
      obtain ⟨hp', hc⟩ := and_pub hp
      obtain ⟨e1, e2⟩ := hv hp'
      have := hA.cf hc; rw [hc₁, hc₂] at this; cases Option.some.inj this
      rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  case cmp =>
    subst h₁ h₂
    exact hA.arithFlags fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  case test =>
    subst h₁ h₂
    exact hA.arithFlags fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  all_goals
    subst h₁ h₂
    exact hA.arith d fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩

/-- `aluStep`'s soundness for VG's 32-bit forms. -/
theorem alu32_sound {op : AluOp} {d : Reg} {src : Src} {a' : Taint} {g₁' g₂' : VG.X86_64.State}
    (h : aluStep op d src a = some a') (hA : AgreeV names a g₁ g₂)
    (h₁ : execAlu32 op d src g₁ = some g₁') (h₂ : execAlu32 op d src g₂ = some g₂') :
    AgreeV names a' g₁' g₂' := by
  simp only [aluStep] at h
  obtain ⟨-, rfl⟩ := ite_some h
  simp only [execAlu32, Option.bind_eq_some_iff] at h₁ h₂
  obtain ⟨b₁, hb₁, h₁⟩ := h₁; obtain ⟨b₂, hb₂, h₂⟩ := h₂
  have hv : (a.pub d && srcVal a src) = true → g₁.gpr d = g₂.gpr d ∧ b₁ = b₂ := fun hp => by
    obtain ⟨hd, hs⟩ := and_pub hp
    refine ⟨hA.gpr hd, ?_⟩
    have := hA.readSrc32 hs; rw [hb₁, hb₂] at this; exact Option.some.inj this
  cases op <;> simp only [Option.some.injEq, Option.map_eq_some_iff, reduceCtorEq, or_false,
    or_self, ite_true, ite_false, VG.X86_64.State.setReg32] at h₁ h₂ ⊢
  case adc =>
    obtain ⟨c₁, hc₁, rfl⟩ := h₁; obtain ⟨c₂, hc₂, rfl⟩ := h₂
    exact hA.arithW d fun hp => by
      obtain ⟨hp', hc⟩ := and_pub hp
      obtain ⟨e1, e2⟩ := hv hp'
      have := hA.cf hc; rw [hc₁, hc₂] at this; cases Option.some.inj this
      rw [e1, e2]; exact ⟨rfl, rfl, rfl, rfl⟩
  case sbb =>
    obtain ⟨c₁, hc₁, rfl⟩ := h₁; obtain ⟨c₂, hc₂, rfl⟩ := h₂
    exact hA.arithW d fun hp => by
      obtain ⟨hp', hc⟩ := and_pub hp
      obtain ⟨e1, e2⟩ := hv hp'
      have := hA.cf hc; rw [hc₁, hc₂] at this; cases Option.some.inj this
      rw [e1, e2]; exact ⟨rfl, rfl, rfl, rfl⟩
  case cmp =>
    subst h₁ h₂
    exact hA.arithFlagsW fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  case test =>
    subst h₁ h₂
    exact hA.arithFlagsW fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl⟩
  all_goals
    subst h₁ h₂
    exact hA.arithW d fun hp => by
      have hp' : (a.pub d && srcVal a src) = true := by simpa using hp
      obtain ⟨e1, e2⟩ := hv hp'; rw [e1, e2]; exact ⟨rfl, rfl, rfl, rfl⟩

/-- `vgStep`'s soundness: the runs access the same addresses, and agree on
what it says after. -/
theorem vg_sound {a' : Taint} {j : VG.X86_64.Instr} {g₁' g₂' : VG.X86_64.State}
    (h : vgStep names j a = some a') (hA : AgreeV names a g₁ g₂)
    (h₁ : VG.X86_64.exec j g₁ = some g₁') (h₂ : VG.X86_64.exec j g₂ = some g₂') :
    VG.X86_64.addrs j g₁ = VG.X86_64.addrs j g₂ ∧ AgreeV names a' g₁' g₂' := by
  cases j
  case mov d src =>
    simp only [vgStep] at h; obtain ⟨hs, rfl⟩ := ite_some h
    simp only [VG.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, hv₁, rfl⟩ := h₁; obtain ⟨v₂, hv₂, rfl⟩ := h₂
    refine ⟨by simp only [VG.X86_64.addrs]; exact hA.srcAddrs hs, hA.setReg d fun hp => ?_⟩
    have := hA.readSrc hp; rw [hv₁, hv₂] at this; exact Option.some.inj this
  case store m r =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [VG.X86_64.exec] at h₁ h₂
    exact ⟨by simp only [VG.X86_64.addrs, hA.ea hm], hA.same (same_store64 h₁) (same_store64 h₂)⟩
  case alu op d src =>
    simp only [vgStep] at h
    simp only [VG.X86_64.exec] at h₁ h₂
    refine ⟨?_, alu_sound h hA h₁ h₂⟩
    simp only [aluStep] at h; obtain ⟨hs, -⟩ := ite_some h
    simp only [VG.X86_64.addrs]; exact hA.srcAddrs hs
  case alu32 op d src =>
    simp only [vgStep] at h
    simp only [VG.X86_64.exec] at h₁ h₂
    refine ⟨?_, alu32_sound h hA h₁ h₂⟩
    simp only [aluStep] at h; obtain ⟨hs, -⟩ := ite_some h
    simp only [VG.X86_64.addrs]; exact hA.srcAddrs hs
  case shift op d n =>
    cases op
    · simp [vgStep] at h
    all_goals
      simp only [vgStep, Option.some.injEq] at h; subst h
      simp only [VG.X86_64.exec, execShift] at h₁ h₂
      obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
      refine ⟨rfl, ?_⟩
      rw [← Taint.set_self (a := a.flags (a.pub d) (a.pub d)) (r := d) rfl]
      exact hA.flagsReg d (fun hp => by rw [hA.gpr hp]) (fun hp => by rw [hA.gpr hp]; exact ⟨rfl, rfl, rfl⟩)
        (fun hp => by rw [hA.gpr hp])
  case mul r =>
    simp only [vgStep, Option.some.injEq] at h; subst h
    simp only [VG.X86_64.exec, execMul, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    refine ⟨rfl, ?_⟩
    have hp : (a.pub .rax && a.pub r) = true → (g₁.gpr .rax).toNat * (g₁.gpr r).toNat =
        (g₂.gpr .rax).toNat * (g₂.gpr r).toNat := fun hp => by
      rw [hA.gpr (and_pub hp).1, hA.gpr (and_pub hp).2]
    refine ((hA.setFlags (fun h => by rw [hp h]) fun h => by rw [hp h]; exact ⟨rfl, rfl, rfl⟩).setReg
      .rax fun h => by rw [hp h]).setReg .rdx fun h => by rw [hp h]
  case imul d r =>
    simp only [vgStep, Option.some.injEq] at h; subst h
    simp only [VG.X86_64.exec, execImul, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    refine ⟨rfl, hA.flagsReg d ?_ ?_ ?_⟩ <;> intro hp <;>
      simp only [hA.gpr (and_pub hp).1, hA.gpr (and_pub hp).2, and_self]
  case shld d r n =>
    simp only [vgStep, Option.some.injEq] at h; subst h
    simp only [VG.X86_64.exec, execShld] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    refine ⟨rfl, hA.flagsReg d ?_ ?_ ?_⟩ <;> intro hp <;>
      simp only [hA.gpr (and_pub hp).1, hA.gpr (and_pub hp).2, and_self]
  case mulx hi lo src =>
    simp only [vgStep] at h; obtain ⟨hs, rfl⟩ := ite_some h
    refine ⟨by simp only [VG.X86_64.addrs]; exact hA.srcAddrs hs, ?_⟩
    simp only [VG.X86_64.exec, execMulx] at h₁ h₂
    cases src with
    | imm _ => simp at h₁
    | reg r =>
      simp only [Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨b₁, hb₁, rfl⟩ := h₁; obtain ⟨b₂, hb₂, rfl⟩ := h₂
      have hp : (a.pub .rdx && srcVal a (.reg r)) = true →
          (g₁.gpr .rdx).toNat * b₁.toNat = (g₂.gpr .rdx).toNat * b₂.toNat := fun hp => by
        have := hA.readSrc (and_pub hp).2; rw [hb₁, hb₂] at this
        rw [hA.gpr (and_pub hp).1, Option.some.inj this]
      exact (hA.setReg lo fun h => by rw [hp h]).setReg hi fun h => by rw [hp h]
    | mem m =>
      simp only [Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨b₁, hb₁, rfl⟩ := h₁; obtain ⟨b₂, hb₂, rfl⟩ := h₂
      exact (hA.setReg lo fun h => by simp [srcVal] at h).setReg hi fun h => by simp [srcVal] at h
  case cmov c d src =>
    simp only [vgStep] at h; obtain ⟨hs, rfl⟩ := ite_some h
    refine ⟨by simp only [VG.X86_64.addrs]; exact hA.srcAddrs hs, ?_⟩
    simp only [VG.X86_64.exec, execCmov] at h₁ h₂
    cases src with
    | imm _ => simp at h₁
    | _ =>
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
      obtain ⟨t₁, ht₁, b₁, hb₁, rfl⟩ := h₁; obtain ⟨t₂, ht₂, b₂, hb₂, rfl⟩ := h₂
      rw [AgreeV.setReg_ite, AgreeV.setReg_ite]
      refine hA.setReg d fun hp => ?_
      obtain ⟨hd, hs', hc⟩ := and3_pub hp
      have et := hA.readSrc hs'; rw [ht₁, ht₂] at et
      have ec := vgCond_eq hA hc; rw [hb₁, hb₂] at ec
      rw [Option.some.inj et, Option.some.inj ec, hA.gpr hd]
  case movzx8 d m =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [VG.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, -, rfl⟩ := h₁; obtain ⟨v₂, -, rfl⟩ := h₂
    exact ⟨by simp only [VG.X86_64.addrs, hA.ea hm], hA.setReg d fun h => by simp at h⟩
  case movqR d r =>
    simp only [vgStep, Option.some.injEq] at h; subst h
    simp only [VG.X86_64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.setReg d fun h => by simp at h⟩
  case leaSym d n =>
    simp only [vgStep, Option.some.injEq] at h; subst h
    simp only [VG.X86_64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.setReg d fun h => hA.sym h⟩
  case xop o =>
    simp only [vgStep, Option.some.injEq] at h; subst h
    simp only [VG.X86_64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.same (same_xop _ _) (same_xop _ _)⟩
  case vop o =>
    simp only [vgStep, Option.some.injEq] at h; subst h
    simp only [VG.X86_64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA.same (same_vop _ _) (same_vop _ _)⟩
  case movdquLoad d m =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [VG.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, -, rfl⟩ := h₁; obtain ⟨v₂, -, rfl⟩ := h₂
    exact ⟨by simp only [VG.X86_64.addrs, hA.ea hm], hA.same (same_setXmm _ _ _) (same_setXmm _ _ _)⟩
  case movdquStore m r =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [VG.X86_64.exec] at h₁ h₂
    exact ⟨by simp only [VG.X86_64.addrs, hA.ea hm], hA.same (same_store128 h₁) (same_store128 h₂)⟩
  case vmovdquLoad l d m =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    refine ⟨by simp only [VG.X86_64.addrs, hA.ea hm], ?_⟩
    cases l <;> simp only [VG.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂ <;>
      obtain ⟨v₁, -, rfl⟩ := h₁ <;> obtain ⟨v₂, -, rfl⟩ := h₂ <;>
      exact hA.same (same_setV _ _ _ _ _) (same_setV _ _ _ _ _)
  case vmovdquStore l m r =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    refine ⟨by simp only [VG.X86_64.addrs, hA.ea hm], ?_⟩
    cases l <;> simp only [VG.X86_64.exec] at h₁ h₂
    · exact hA.same (same_store128 h₁) (same_store128 h₂)
    · exact hA.same (same_store256 h₁) (same_store256 h₂)
  case vbroadcasti128 d m =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [VG.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, -, rfl⟩ := h₁; obtain ⟨v₂, -, rfl⟩ := h₂
    exact ⟨by simp only [VG.X86_64.addrs, hA.ea hm], hA.same (same_setV _ _ _ _ _) (same_setV _ _ _ _ _)⟩
  case vbinLoad op l d x m =>
    simp only [vgStep] at h; obtain ⟨hm, rfl⟩ := ite_some h
    refine ⟨by simp only [VG.X86_64.addrs, hA.ea hm], ?_⟩
    cases l <;> simp only [VG.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂ <;>
      obtain ⟨v₁, -, rfl⟩ := h₁ <;> obtain ⟨v₂, -, rfl⟩ := h₂ <;>
      exact hA.same (same_setV _ _ _ _ _) (same_setV _ _ _ _ _)
  all_goals simp [vgStep] at h

end

/-- `dec` and `inc` keep CF. -/
theorem decIncFlags (g : VG.X86_64.State) (r : BitVec 64) (o : Bool) :
    ({ VG.X86_64.arithFlags g r false o with cf := g.cf } : VG.X86_64.State) =
      g.setFlags g.cf (some o) (some (r == 0)) (some r.msb) := rfl

/-- `moveSp`'s result, from states that agree as `a` says and to the same
`rsp` if the runs agree on it. -/
theorem moveSp_agree {names : List String} {a : Taint} {s₁ s₂ s₁' s₂' : Rind.X86_64.State}
    {v₁ v₂ : Addr} (hA : Agree names a s₁ s₂) (hv : a.pub .rsp = true → v₁ = v₂)
    (h₁ : moveSp s₁ v₁ = some s₁') (h₂ : moveSp s₂ v₂ = some s₂') : Agree names a s₁' s₂' := by
  have := AgreeV.setReg hA .rsp (b := a.pub .rsp) hv
  rw [Taint.set_self rfl] at this
  exact this.same (moveSp_vg h₁) (moveSp_vg h₂)

theorem step_sound {names : List String} {a a' : Taint} {i : Rind.X86_64.Instr}
    {s₁ s₂ s₁' s₂' : Rind.X86_64.State} (h : step names i a = some a') (hA : Agree names a s₁ s₂)
    (h₁ : Rind.X86_64.exec i s₁ = some s₁') (h₂ : Rind.X86_64.exec i s₂ = some s₂') :
    Rind.X86_64.addrs i s₁ = Rind.X86_64.addrs i s₂ ∧ Agree names a' s₁' s₂' := by
  unfold Agree at hA ⊢
  cases i
  case vg j =>
    simp only [Rind.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨g₁, hg₁, rfl⟩ := h₁; obtain ⟨g₂, hg₂, rfl⟩ := h₂
    exact vg_sound h hA hg₁ hg₂
  case push r =>
    simp only [step] at h; obtain ⟨hsp, rfl⟩ := ite_some h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none (p := ¬r = .rsp) (by simpa using h₁)
    obtain ⟨-, h₂⟩ := ite_none (p := ¬r = .rsp) (by simpa using h₂)
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨u₁, hu₁, g₁, hg₁, rfl⟩ := h₁; obtain ⟨u₂, hu₂, g₂, hg₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.X86_64.addrs, hA.gpr hsp], ?_⟩
    have := moveSp_agree hA (fun _ => by rw [hA.gpr hsp]) hu₁ hu₂
    exact AgreeV.same this (same_store64 hg₁) (same_store64 hg₂)
  case pop r =>
    simp only [step] at h; obtain ⟨hsp, rfl⟩ := ite_some h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none (p := ¬r = .rsp) (by simpa using h₁)
    obtain ⟨-, h₂⟩ := ite_none (p := ¬r = .rsp) (by simpa using h₂)
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, -, u₁, hu₁, rfl⟩ := h₁; obtain ⟨v₂, -, u₂, hu₂, rfl⟩ := h₂
    refine ⟨by simp only [Rind.X86_64.addrs, hA.gpr hsp], ?_⟩
    exact (moveSp_agree hA (fun _ => by rw [hA.gpr hsp]) hu₁ hu₂).setReg r fun h => by simp at h
  case aluRsp op v =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨hop, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.bind_eq_some_iff] at h₁ h₂
    obtain ⟨g₁, hg₁, h₁⟩ := h₁; obtain ⟨g₂, hg₂, h₂⟩ := h₂
    refine ⟨rfl, ?_⟩
    have hs : aluStep op .rsp (.imm v) a =
        some ((a.flags (a.pub .rsp) (a.pub .rsp)).set .rsp (a.pub .rsp)) := by
      rcases hop with rfl | rfl <;> simp [aluStep, srcAddr, srcVal]
    have hg := alu_sound hs hA (by simpa [VG.X86_64.exec] using hg₁) (by simpa [VG.X86_64.exec] using hg₂)
    have hF : Agree names (a.flags (a.pub .rsp) (a.pub .rsp))
        { s₁ with vg := s₁.vg.setFlags g₁.cf g₁.of g₁.zf g₁.sf }
        { s₂ with vg := s₂.vg.setFlags g₂.cf g₂.of g₂.zf g₂.sf } :=
      hA.setFlags (fun hp => hg.cf (by simpa [Taint.flags] using hp)) fun hp => by
        obtain ⟨e1, e2, e3⟩ := hg.zso (by simpa [Taint.flags] using hp); exact ⟨e3, e1, e2⟩
    exact moveSp_agree hF (fun hp => hg.gpr (by simpa [Taint.pub_set] using hp)) h₁ h₂
  case lea d m =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec] at h₁ h₂
    split at h₁ <;> simp only [Option.some.injEq, reduceCtorEq] at h₁
    split at h₂ <;> simp only [Option.some.injEq, reduceCtorEq] at h₂
    subst h₁ h₂
    exact ⟨rfl, hA.setReg d fun hm => hA.ea hm⟩
  case leaSym d m =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec] at h₁ h₂
    split at h₁ <;> simp only [Option.some.injEq, reduceCtorEq] at h₁
    split at h₂ <;> simp only [Option.some.injEq, reduceCtorEq] at h₂
    subst h₁ h₂
    exact ⟨rfl, hA.setReg d fun hm => hA.eaR (m := .sym m) hm⟩
  case dec d =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [decIncFlags, decIncFlags, ← Taint.set_self (a := a.flags a.cf (a.pub d)) (r := d) rfl]
    exact hA.flagsReg d (fun hc => hA.cf hc) (fun hp => by rw [hA.gpr hp]; exact ⟨rfl, rfl, rfl⟩)
      (fun hp => by rw [hA.gpr hp])
  case inc d =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    refine ⟨rfl, ?_⟩
    dsimp only
    rw [decIncFlags, decIncFlags, ← Taint.set_self (a := a.flags a.cf (a.pub d)) (r := d) rfl]
    exact hA.flagsReg d (fun hc => hA.cf hc) (fun hp => by rw [hA.gpr hp]; exact ⟨rfl, rfl, rfl⟩)
      (fun hp => by rw [hA.gpr hp])
  case shrd d r n =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    refine ⟨rfl, hA.flagsReg d ?_ ?_ ?_⟩ <;> intro hp <;>
      simp only [hA.gpr (and_pub hp).1, hA.gpr (and_pub hp).2, and_self]
  case cmov c d r =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨b₁, hb₁, rfl⟩ := h₁; obtain ⟨b₂, hb₂, rfl⟩ := h₂
    refine ⟨rfl, ?_⟩
    have e : ∀ (s : Rind.X86_64.State) (b : Bool),
        (if b then { s with vg := s.vg.setReg d (s.vg.gpr r) } else s).vg =
          s.vg.setReg d (if b then s.vg.gpr r else s.vg.gpr d) := fun s b => by
      rw [← AgreeV.setReg_ite]; cases b <;> rfl
    rw [e, e]
    refine hA.setReg d fun hp => ?_
    obtain ⟨hd, hr, hc⟩ := and3_pub hp
    have ec := cond_eq hA hc; rw [hb₁, hb₂] at ec
    rw [Option.some.inj ec, hA.gpr hd, hA.gpr hr]
  case movdqaLoad d m =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, -, rfl⟩ := h₁; obtain ⟨v₂, -, rfl⟩ := h₂
    exact ⟨by simp only [Rind.X86_64.addrs, hA.ea hm], hA.same (same_setXmm _ _ _) (same_setXmm _ _ _)⟩
  case movdqaStore m r =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨g₁, hg₁, rfl⟩ := h₁; obtain ⟨g₂, hg₂, rfl⟩ := h₂
    exact ⟨by simp only [Rind.X86_64.addrs, hA.ea hm], hA.same (same_store128 hg₁) (same_store128 hg₂)⟩
  case vmovdqaStore l m r =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    refine ⟨by simp only [Rind.X86_64.addrs, hA.ea hm], ?_⟩
    cases l <;> simp only [Rind.X86_64.exec] at h₁ h₂ <;>
      obtain ⟨-, h₁⟩ := ite_none h₁ <;> obtain ⟨-, h₂⟩ := ite_none h₂ <;>
      simp only [Option.map_eq_some_iff] at h₁ h₂ <;>
      obtain ⟨g₁, hg₁, rfl⟩ := h₁ <;> obtain ⟨g₂, hg₂, rfl⟩ := h₂
    · exact hA.same (same_store128 hg₁) (same_store128 hg₂)
    · exact hA.same (same_store256 hg₁) (same_store256 hg₂)
  case pinsrb d m i =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, -, rfl⟩ := h₁; obtain ⟨v₂, -, rfl⟩ := h₂
    exact ⟨by simp only [Rind.X86_64.addrs, hA.ea hm], hA.same (same_setXmm _ _ _) (same_setXmm _ _ _)⟩
  case pextrb m r i =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨g₁, hg₁, rfl⟩ := h₁; obtain ⟨g₂, hg₂, rfl⟩ := h₂
    exact ⟨by simp only [Rind.X86_64.addrs, hA.ea hm], hA.same (same_store8 hg₁) (same_store8 hg₂)⟩
  case xload op d m =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, h₁⟩ := ite_none h₁; obtain ⟨-, h₂⟩ := ite_none h₂
    simp only [Option.map_eq_some_iff] at h₁ h₂
    obtain ⟨v₁, -, rfl⟩ := h₁; obtain ⟨v₂, -, rfl⟩ := h₂
    exact ⟨by simp only [Rind.X86_64.addrs, hA.eaR hm], hA.same (same_setXmm _ _ _) (same_setXmm _ _ _)⟩
  case vmovdqaLoad l d m =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    refine ⟨by simp only [Rind.X86_64.addrs, hA.eaR hm], ?_⟩
    cases l <;> simp only [Rind.X86_64.exec] at h₁ h₂ <;>
      obtain ⟨-, h₁⟩ := ite_none h₁ <;> obtain ⟨-, h₂⟩ := ite_none h₂ <;>
      simp only [Option.map_eq_some_iff] at h₁ h₂ <;>
      obtain ⟨v₁, -, rfl⟩ := h₁ <;> obtain ⟨v₂, -, rfl⟩ := h₂ <;>
      exact hA.same ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  case vbinSym op l d x m =>
    simp only [step] at h; obtain ⟨hm, rfl⟩ := ite_some h
    refine ⟨by simp only [Rind.X86_64.addrs, hA.eaR (m := .sym m) hm], ?_⟩
    cases l <;> simp only [Rind.X86_64.exec, Option.map_eq_some_iff] at h₁ h₂ <;>
      obtain ⟨g₁, ⟨v₁, -, rfl⟩, rfl⟩ := h₁ <;> obtain ⟨g₂, ⟨v₂, -, rfl⟩, rfl⟩ := h₂ <;>
      exact hA.same ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  case pextrq d r i =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec] at h₁ h₂
    obtain ⟨-, rfl⟩ := ite_some h₁; obtain ⟨-, rfl⟩ := ite_some h₂
    exact ⟨rfl, hA.setReg d fun h => by simp at h⟩
  case align n =>
    simp only [step, Option.some.injEq] at h; subst h
    simp only [Rind.X86_64.exec, Option.some.injEq] at h₁ h₂; subst h₁ h₂
    exact ⟨rfl, hA⟩
  all_goals simp [step] at h

theorem eval_eq {names : List String} {a : Taint} {c : Rind.X86_64.Cond} {s₁ s₂ : Rind.X86_64.State}
    (hc : condPub a c = true) (hA : Agree names a s₁ s₂) :
    Rind.X86_64.isa.eval c s₁ = Rind.X86_64.isa.eval c s₂ :=
  cond_eq hA hc

theorem block_sound {names : List String} :
    ∀ {is : List Rind.X86_64.Instr} {a a' : Taint} {s₁ s₂ s₁' s₂' : Rind.X86_64.State} {t₁ t₂ : List Leak},
      is.foldlM (fun a i => step names i a) a = some a' → Agree names a s₁ s₂ →
      execBlock Rind.X86_64.isa is s₁ = some (s₁', t₁) →
      execBlock Rind.X86_64.isa is s₂ = some (s₂', t₂) →
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

theorem loopFix_sound {f : Taint → Option Taint} {c : Rind.X86_64.Cond} :
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
        exact ⟨a, Taint.le_refl a, hb, hle, hc⟩
      · simp at h
    · obtain ⟨inv, h₁, h₂, h₃, h₄⟩ := loopFix_sound h
      exact ⟨inv, Taint.le_trans h₁ (Taint.meet_le_left _ _), h₂, h₃, h₄⟩

theorem check_sound {names : List String} :
    ∀ {c : Prog Rind.X86_64.isa} {a a' : Taint}, check names c a = some a' →
      ∀ {s₁ s₂ s₁' s₂' : Rind.X86_64.State} {t₁ t₂ : List Leak}, Agree names a s₁ s₂ →
        Exec Rind.X86_64.isa c s₁ t₁ s₁' → Exec Rind.X86_64.isa c s₂ t₂ s₂' →
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
    generalize hp : (Code.loop body c : Prog Rind.X86_64.isa) = p at e₁
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
both finishing without a fault, from states that agree on what `a` names
and the statics `names`. -/
theorem constantTime_of_check {names : List String} {c : Prog Rind.X86_64.isa} {a a' : Taint}
    (h : check names c a = some a') : ConstantTime Rind.X86_64.isa (fun _ => True) (Agree names a) c :=
  fun _ _ _ _ _ _ _ _ hA e₁ e₂ => (check_sound h hA e₁ e₂).1

end rind.x86_64.taint
