module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# Taint tracking through stack frames, for returning without residue (x86-64)

`rtaint` is the x86-64 taint analysis (`X86_64.taint`) extended to the stack
a function uses: the `stack` bytes below the stack pointer on entry (the
*window*). It follows the frames code allocates (`alloc` and `free`; frames
of pushed registers are not handled) as writable regions at the head of `wr`,
whose public bytes it keeps as bit masks (`pb`), and the calls and
returns of the code, whose return addresses it keeps apart from the frames
(`ras`). It keeps the window index of each frame's base (`fw`), so that after
a return, whose stack pointer the base analysis forgets as a call does, it
knows the stack pointer again as an offset into the innermost frame
(`spBase`), and stores through it after a call reach that frame's bytes. The bytes of the window outside every writable region are equal in
both runs but those of `sec` (a bit mask of window indices from its base, the
stack pointer on entry minus `stack`): when a frame is freed, its bytes that
are not public are added to `sec`. So at the end of a function, the bytes of its
window that may differ between two runs are those `sec` lists: those its
code must zero to leave no residue.

Instructions are the base analysis's (`X86_64.taint.step`), with the same
soundness proof (no instruction's step changes what it knows of the regions'
lengths, `baseStep_lens`), and must not write the stack pointer; `ResidueTaintSound.lean`
proves the rest. On top of it, the analysis knows:

* upper bounds of registers (`ub`), from constants, `and` with a constant,
  and `cmp x, d; cmovb d, x`, which keeps the bound of `d`;
* which bytes of the writable regions are public (`pb`), byte by byte: the
  base analysis's slots, as one bit mask for each region, so that a store or
  a load costs the kernel a few operations on `Nat` whatever the frame holds
  (a list of slots is scanned at each, and a frame has hundreds). The base
  analysis's own slots stay empty;
* which regions an indexed store may reach: one whose base register points
  into a region and whose index register is bounded writes only within
  `[lo, hi)` of that region, and leaves its other bytes public;
* pointers kept in public slots (`mb`): a 64-bit store of a register holding
  an address in a region, reloaded later, holds it again;
* zeroing idioms (`xor r, r`, `pxor x, x`) and vector stores of public
  registers;
* the stack arguments (the argument area, `an` bytes from 8 above the stack
  pointer on entry): which of their bytes are public (`sa`), and which hold
  the address of a region (`sp`), so that a load of one through the stack
  pointer (`argOff`) gives a public value or a pointer. The code cannot
  write them: they are in no writable region (`aFree`), and above the window,
  which they do not wrap around into (`aTop`).
-/

@[expose] public section

namespace VG.X86_64.RTaint

open VG.X86_64 VG.X86_64.Taint

/-! ## Sets of bytes as bit masks

As `RegSet`, with the `Nat` functions themselves (`Nat.lor`, not `|||`),
which spares the kernel unfolding the instances; the lemmas state them with
`Nat.testBit`. -/

/-- The `w` low bits. -/
def ones (w : Nat) : Nat := Nat.sub (Nat.pow 2 w) 1

/-- `b` with its `w` bits from bit `d` set. -/
def bset (b d w : Nat) : Nat := Nat.lor b (Nat.shiftLeft (ones w) d)

/-- `b` with its `w` bits from bit `d` cleared. -/
def bclr (b d w : Nat) : Nat := Nat.xor b (Nat.land b (Nat.shiftLeft (ones w) d))

/-- The `w` bits of `b` from bit `d` are all set. -/
def btest (b d w : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight b d) (ones w)) (ones w)

/-- Every bit of `a` is set in `b`. -/
def bsub (a b : Nat) : Bool := Nat.beq (Nat.land a b) a

theorem testBit_ones (w k : Nat) : (ones w).testBit k = decide (k < w) := Nat.testBit_two_pow_sub_one w k

/-- Bit `k` is one of the `w` bits from bit `d`, as `Nat.testBit_shiftLeft` and as an interval. -/
theorem bit_range (d w k : Nat) :
    (decide (k ≥ d) && decide (k - d < w)) = (decide (d ≤ k) && decide (k < d + w)) := by
  by_cases h : d ≤ k
  · simp only [ge_iff_le, h, decide_true, Bool.true_and, decide_eq_decide]; omega
  · simp only [ge_iff_le, h, decide_false, Bool.false_and]

theorem testBit_bset (b d w k : Nat) :
    (bset b d w).testBit k = (b.testBit k || (decide (d ≤ k) && decide (k < d + w))) := by
  show (b ||| ones w <<< d).testBit k = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, testBit_ones, bit_range]

theorem testBit_bclr (b d w k : Nat) :
    (bclr b d w).testBit k = (b.testBit k && !(decide (d ≤ k) && decide (k < d + w))) := by
  show (b ^^^ (b &&& ones w <<< d)).testBit k = _
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftLeft, testBit_ones, bit_range]
  cases b.testBit k <;> cases (decide (d ≤ k) && decide (k < d + w)) <;> rfl

theorem btest_bit {b d w k : Nat} (h : btest b d w = true) (h₁ : d ≤ k) (h₂ : k < d + w) : b.testBit k = true := by
  have e : (b >>> d &&& ones w) = ones w := Nat.eq_of_beq_eq_true h
  have := congrArg (·.testBit (k - d)) e
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones, show k - d < w by omega, decide_true,
    Bool.and_true, show d + (k - d) = k by omega] at this
  exact this

theorem bsub_bit {a b k : Nat} (h : bsub a b = true) (hk : a.testBit k = true) : b.testBit k = true := by
  have e : (a &&& b) = a := Nat.eq_of_beq_eq_true h
  rw [← e, Nat.testBit_and, Bool.and_eq_true] at hk
  exact hk.2

/-- Index `j` is in the set `sec`. -/
def InSec (sec : Nat) (j : Nat) : Prop := sec.testBit j = true

/-! ### A bit mask for each writable region -/

def pbGetC (l : List Nat) (i : Nat) : Nat := l.getD i 0

/-- The mask of region `i` (`0` past the end of the list). -/
@[implemented_by pbGetC] def pbGet (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun n _ => ih n) i) l i

def pbModC (f : Nat → Nat) : List Nat → Nat → List Nat
  | [], _ => []
  | a :: l, 0 => f a :: l
  | a :: l, i + 1 => a :: pbModC f l i

/-- `l`, with `f` applied to the mask of region `i`. -/
@[implemented_by pbModC] def pbMod (f : Nat → Nat) (l : List Nat) (i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a tl ih i => Nat.rec (motive := fun _ => List Nat) (f a :: tl) (fun n _ => a :: ih n) i) l i

/-- No byte of any region. -/
def pbZero (l : List Nat) : List Nat := KList.map (fun _ => 0) l

def pbMeetC : List Nat → List Nat → List Nat
  | a :: as, b :: bs => Nat.land a b :: pbMeetC as bs
  | _, _ => []

/-- The bytes of both. -/
@[implemented_by pbMeetC] def pbMeet (as bs : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun _ => [])
    (fun a _ ih bs => List.casesOn (motive := fun _ => List Nat) bs [] fun b bs' => Nat.land a b :: ih bs') as bs

def pbLeC : List Nat → List Nat → Bool
  | [], _ => true
  | a :: as, [] => Nat.beq a 0 && pbLeC as []
  | a :: as, b :: bs => bsub a b && pbLeC as bs

/-- Every byte of `as` is one of `bs`. -/
@[implemented_by pbLeC] def pbLe (as bs : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun _ => true)
    (fun a _ ih bs => List.casesOn (motive := fun _ => Bool) bs (Nat.beq a 0 && ih []) fun b bs' =>
      bsub a b && ih bs') as bs

theorem pbGet_nil (i : Nat) : pbGet [] i = 0 := rfl

theorem pbGet_cons_zero (a : Nat) (l : List Nat) : pbGet (a :: l) 0 = a := rfl

theorem pbGet_cons_succ (a : Nat) (l : List Nat) (i : Nat) : pbGet (a :: l) (i + 1) = pbGet l i := rfl

theorem pbGet_tail (l : List Nat) (i : Nat) : pbGet l.tail i = pbGet l (i + 1) := by cases l <;> rfl

theorem pbGet_eq : ∀ (l : List Nat) (i : Nat), pbGet l i = l.getD i 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => pbGet_eq l i

theorem pbMod_cons_zero (f : Nat → Nat) (a : Nat) (l : List Nat) : pbMod f (a :: l) 0 = f a :: l := rfl

theorem pbMod_cons_succ (f : Nat → Nat) (a : Nat) (l : List Nat) (i : Nat) :
    pbMod f (a :: l) (i + 1) = a :: pbMod f l i := rfl

theorem pbGet_ge : ∀ {l : List Nat} {i : Nat}, l.length ≤ i → pbGet l i = 0
  | [], _, _ => rfl
  | _ :: l, _ + 1, h => pbGet_ge (l := l) (Nat.le_of_succ_le_succ h)

theorem pbGet_mod (f : Nat → Nat) : ∀ (l : List Nat) (i j : Nat),
    pbGet (pbMod f l i) j = if j = i ∧ i < l.length then f (pbGet l i) else pbGet l j
  | [], _, _ => by simp [pbMod, pbGet_nil]
  | a :: l, 0, 0 => by simp [pbMod_cons_zero, pbGet_cons_zero]
  | a :: l, 0, j + 1 => by simp [pbMod_cons_zero, pbGet_cons_succ]
  | a :: l, i + 1, 0 => by simp [pbMod_cons_succ, pbGet_cons_zero]
  | a :: l, i + 1, j + 1 => by
    rw [pbMod_cons_succ, pbGet_cons_succ, pbGet_mod f l i j]
    simp [pbGet_cons_succ]

theorem pbGet_zero : ∀ (l : List Nat) (i : Nat), pbGet (pbZero l) i = 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, i + 1 => pbGet_zero l i

theorem pbGet_meet : ∀ (as bs : List Nat) (i : Nat), pbGet (pbMeet as bs) i = pbGet as i &&& pbGet bs i
  | [], _, _ => by simp [pbMeet, pbGet_nil]
  | _ :: _, [], _ => by simp [pbMeet, pbGet_nil]
  | _ :: _, _ :: _, 0 => rfl
  | _ :: as, _ :: bs, i + 1 => pbGet_meet as bs i

theorem pbLe_bit : ∀ {as bs : List Nat}, pbLe as bs = true → ∀ {i k : Nat},
    (pbGet as i).testBit k = true → (pbGet bs i).testBit k = true
  | [], _, _, _, _, hk => by simp [pbGet_nil] at hk
  | a :: as, [], h, i, k, hk => by
    have h' : (Nat.beq a 0 && pbLe as []) = true := h
    rw [Bool.and_eq_true] at h'
    cases i with
    | zero => rw [pbGet_cons_zero, Nat.eq_of_beq_eq_true h'.1] at hk; simp at hk
    | succ i => exact pbLe_bit h'.2 (i := i) hk
  | a :: as, b :: bs, h, i, k, hk => by
    have h' : (bsub a b && pbLe as bs) = true := h
    rw [Bool.and_eq_true] at h'
    cases i with
    | zero => exact bsub_bit h'.1 hk
    | succ i => exact pbLe_bit h'.2 (i := i) hk

/-! ## The domain -/

structure FT where
  /-- `false`: nothing is known (`meet` of incompatible taints). -/
  ok : Bool
  t : Taint.T
  /-- How many of the writable regions, at their head, are frames. -/
  nfr : Nat
  /-- The stack pointer on entry minus the current one. -/
  depth : Nat
  /-- The bytes of the window below the current stack pointer. -/
  room : Nat
  /-- Window indices that may differ between the runs, outside writable
  regions: bit `j` for index `j`. -/
  sec : Nat
  /-- Window indices of the return addresses of the calls in progress, innermost first. -/
  ras : List Nat
  /-- Upper bounds of registers' values, in both runs. -/
  ub : List (Reg × Nat) := []
  /-- The flags are those of `cmp a, b` (64-bit), in both runs. -/
  fl : Option (Reg × Reg) := none
  /-- `(i, d, j, k)`: the 8 bytes at offset `d` of region `i` hold the address
  of byte `k` of region `j`, in both runs. -/
  mb : List (Nat × Nat × Nat × Nat) := []
  /-- The window index of the base of each frame, innermost first. -/
  fw : List Nat := []
  /-- The length of the argument area: the stack arguments, from 8 bytes above
  the stack pointer on entry (above the return address). -/
  an : Nat := 0
  /-- `(o, n)`: the `n` bytes at offset `o` of the argument area are the same
  in both runs. -/
  sa : List (Nat × Nat) := []
  /-- `(o, i, k)`: the 8 bytes at offset `o` of the argument area hold the
  address of byte `k` of region `i`, in both runs. -/
  sp : List (Nat × Nat × Nat) := []
  /-- Bit `k` of the mask of region `i`: byte `k` of region `i` is the same
  in both runs. -/
  pb : List Nat := []
  deriving DecidableEq

def ofWordsC (l : List Nat) : Nat := l.foldr (fun w n => Nat.lor w (Nat.shiftLeft n 64)) 0

/-- The number whose 64-bit words are `l`, the lowest first. -/
@[implemented_by ofWordsC] def ofWords (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun w _ ih => Nat.lor w (Nat.shiftLeft ih 64)) l

/-- The 64-bit words of `n`, the lowest first (`fuel` of them at most). -/
def wordsOf : Nat → Nat → List Nat
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else n % 2 ^ 64 :: wordsOf fuel (n / 2 ^ 64)

/-- A bit mask as a literal for the kernel: one of 64 bits or more as
`ofWords` of its words. Lean hashes a `Nat` literal by its low 64 bits, and
the kernel keeps what it has evaluated by hash: the taints of a hint
(`taint_decide`) that differ only in the high bits of a mask, a frame's
bytes past its first 64, would hash alike with everything computed from
them, and the kernel compare those terms in full at every step (four times
the time of a check, where a function is called from many such taints). -/
def maskExpr (n : Nat) : Lean.Expr :=
  if n < 2 ^ 64 then Lean.toExpr n
  else Lean.mkApp (.const ``ofWords []) (Lean.toExpr (wordsOf (n.log2 / 64 + 1) n))

instance : Lean.ToExpr FT where
  toExpr τ := Lean.mkAppN (.const ``FT.mk [])
    #[Lean.toExpr τ.ok, Lean.toExpr τ.t, Lean.toExpr τ.nfr, Lean.toExpr τ.depth, Lean.toExpr τ.room,
      maskExpr τ.sec, Lean.toExpr τ.ras, Lean.toExpr τ.ub, Lean.toExpr τ.fl, Lean.toExpr τ.mb, Lean.toExpr τ.fw,
      Lean.toExpr τ.an, Lean.toExpr τ.sa, Lean.toExpr τ.sp,
      τ.pb.foldr (fun n e => Lean.mkApp3 (.const ``List.cons [0]) (.const ``Nat []) (maskExpr n) e)
        (Lean.mkApp (.const ``List.nil [0]) (.const ``Nat []))]
  toTypeExpr := .const ``FT []

/-- The base of the window. -/
def wb (s : State) (τ : FT) : Addr := s.gpr .rsp - BitVec.ofNat 64 τ.room

/-- The address of window index `j`. -/
def wa (s : State) (τ : FT) (j : Nat) : Addr := wb s τ + BitVec.ofNat 64 j

/-- The 8 bytes at window index `j`. -/
def raSlot (s : State) (τ : FT) (j : Nat) : Region := ⟨wa s τ j, 8⟩

/-- The address of byte `o` of the argument area: the stack pointer on entry
plus `8 + o`, as an index past the window. -/
def aa (s : State) (τ : FT) (o : Nat) : Addr := wa s τ (τ.room + τ.depth + 8 + o)

/-- What `τ` says of one state alone. -/
structure One (τ : FT) (s : State) : Prop where
  ub : ∀ p ∈ τ.ub, (s.gpr p.1).toNat ≤ p.2
  fl : ∀ a b, τ.fl = some (a, b) → s.cf = some (decide ((s.gpr a).toNat < (s.gpr b).toNat))
  mb : ∀ e ∈ τ.mb, s.mem.readW (byteAddr s e.1 e.2.1) 64 = (region s e.2.2.1).base + BitVec.ofNat 64 e.2.2.2
  sp : ∀ e ∈ τ.sp, s.mem.readW (aa s τ e.1) 64 = (region s e.2.1).base + BitVec.ofNat 64 e.2.2

/-- The bytes of the argument area that `sa` says are public are the same in
both runs. -/
def SaEq (τ : FT) (s₁ s₂ : State) : Prop :=
  ∀ e ∈ τ.sa, ∀ k, e.1 ≤ k → k < e.1 + e.2 → s₁.mem (aa s₁ τ k) = s₂.mem (aa s₂ τ k)

/-- The bytes of the writable regions that `pb` says are public are within
the lengths the base analysis knows, and the same in both runs. -/
def PbEq (τ : FT) (s₁ s₂ : State) : Prop :=
  ∀ i k, (pbGet τ.pb i).testBit k = true →
    k < τ.t.lens.getD i 0 ∧ s₁.mem (byteAddr s₁ i k) = s₂.mem (byteAddr s₂ i k)

structure RInv (τ : FT) (s₁ s₂ : State) : Prop where
  base : Taint.Agree τ.t s₁ s₂
  rsp : s₁.gpr .rsp = s₂.gpr .rsp
  unk : s₁.unknowns = s₂.unknowns
  wr : s₁.wr = s₂.wr
  lens : τ.t.lens = [] → s₁.wr = []
  nfr : τ.nfr ≤ s₁.wr.length
  room : τ.room ≤ (s₁.gpr .rsp).toNat
  top : (s₁.gpr .rsp).toNat + τ.depth < 2 ^ 64
  frames : ∀ i < τ.nfr, Region.Sub (region s₁ i) ⟨s₁.gpr .rsp, τ.depth⟩
  others : ∀ i, τ.nfr ≤ i → i < s₁.wr.length →
    (region s₁ i).Disjoint ⟨wb s₁ τ, τ.room + τ.depth⟩
  rasIn : ∀ j ∈ τ.ras, τ.room ≤ j ∧ j + 8 ≤ τ.room + τ.depth
  rasSorted : τ.ras.Pairwise fun a b => a + 8 ≤ b
  rasFr : ∀ j ∈ τ.ras, ∀ i < τ.nfr, (region s₁ i).Disjoint (raSlot s₁ τ j)
  dead : ∀ j < τ.room + τ.depth, ¬ InSec τ.sec j →
    (∀ r ∈ s₁.wr, ¬ r.Contains (wa s₁ τ j) 1) → s₁.mem (wa s₁ τ j) = s₂.mem (wa s₂ τ j)
  mbFit : ∀ e ∈ τ.mb, e.2.1 + 8 ≤ τ.t.lens.getD e.1 0
  one₁ : One τ s₁
  one₂ : One τ s₂
  fw : ∀ i (h : i < τ.fw.length), (region s₁ i).base = wa s₁ τ τ.fw[i]
  aTop : 0 < τ.an → (s₁.gpr .rsp).toNat + τ.depth + 8 + τ.an ≤ 2 ^ 64
  aFree : ∀ k < τ.an, ∀ r ∈ s₁.wr, ¬ r.Contains (aa s₁ τ k) 1
  saFit : ∀ e ∈ τ.sa, e.1 + e.2 ≤ τ.an
  saEq : SaEq τ s₁ s₂
  spFit : ∀ e ∈ τ.sp, e.1 + 8 ≤ τ.an
  pb : PbEq τ s₁ s₂

def Agree (τ : FT) (s₁ s₂ : State) : Prop := τ.ok = true → RInv τ s₁ s₂

/-- No knowledge. -/
def none' : FT := ⟨false, {regs := .empty, flags := false}, 0, 0, 0, 0, [], [], none, [], [], 0, [], [], []⟩

/-! ## Transfer functions -/

/-- The bound of `r`, if known. -/
def ubOf (l : List (Reg × Nat)) (r : Reg) : Option Nat := (l.find? (·.1 == r)).map (·.2)

/-- Bounds after an instruction that writes the registers `clobbers` says. -/
def ubKill (l : List (Reg × Nat)) (i : Instr) : List (Reg × Nat) := l.filter fun p => !Taint.clobbers i p.1

/-- The bound an instruction gives the register it writes, if any. -/
def ubNew (τ : FT) : Instr → Option (Reg × Nat)
  | .mov d (.imm v) => if v.msb then none else some (d, v.toNat)
  | .mov32 d (.imm v) => some (d, v.toNat)
  | .alu .and d (.imm v) => if v.msb then none else some (d, v.toNat)
  | .alu32 .and d (.imm v) => some (d, v.toNat)
  | .cmov .b d (.reg x) =>
    if τ.fl == some (x, d) then (ubOf τ.ub d).map (d, ·) else none
  | _ => none

/-- The bytes `[lo, hi)` of region `ri` that a store through `m` of `w` bytes
may write, if its base register points into region `ri` and its index
register is bounded. -/
def idxRange (τ : FT) (m : MemOp) (w : Nat) : Option (Nat × Nat × Nat) :=
  match m.index with
  | some x =>
    match τ.t.bases.find? (·.1 == m.base), ubOf τ.ub x with
    | some (_, ri, k), some B =>
      if m.scale = 1 ∧ 0 ≤ m.disp ∧ k + m.disp.toNat + B + w ≤ τ.t.lens.getD ri 0 then
        some (ri, k + m.disp.toNat, k + m.disp.toNat + B + w)
      else none
    | _, _ => none
  | none => none

/-- The bytes `[lo, hi)` of region `ri` a store may write, if known. -/
def storeRange (τ : FT) (m : MemOp) (w : Nat) : Option (Nat × Nat × Nat) :=
  match addrOf τ.t m with
  | some (ri, d) => if d + w ≤ τ.t.lens.getD ri 0 then some (ri, d, d + w) else none
  | none => idxRange τ m w

def mbKill (mb : List (Nat × Nat × Nat × Nat)) (ri lo hi : Nat) : List (Nat × Nat × Nat × Nat) :=
  mb.filter fun e => e.1 != ri || e.2.1 + 8 ≤ lo || hi ≤ e.2.1

def mbAfter (τ : FT) (i : Instr) : List (Nat × Nat × Nat × Nat) :=
  match storeW i with
  | some (m, w) =>
    match storeRange τ m w with
    | some (ri, lo, hi) =>
      let kept := mbKill τ.mb ri lo hi
      match i with
      | .store _ r =>
        match τ.t.bases.find? (·.1 == r), addrOf τ.t m with
        | some (_, pj, pk), some _ => (ri, lo, pj, pk) :: kept
        | _, _ => kept
      | _ => kept
    | none => []
  | none => if writesMem i then [] else τ.mb

/-- The value a store writes is public: a register (or its low bytes) the
base analysis says is, or an SSE register `xregs` says is. -/
def storePub (t : Taint.T) : Instr → Bool
  | .store _ r | .store8 _ r => pub t r
  | .movdquStore _ x => xpub t x
  | _ => false

/-- The base taint after a store whose index register is bounded: only the
slots of `[lo, hi)` of region `ri` are dropped (none if the value is public). -/
def idxStore (t : Taint.T) (ri lo hi : Nat) (p : Bool) : Taint.T :=
  { t with slots := if p then t.slots else t.slots.filter fun sl => sl.1 != ri || hi ≤ sl.2.1 || sl.2.1 + sl.2.2 ≤ lo }

/-- The base taint after a store the base analysis is less precise about:
an indexed store whose index register is bounded, or a vector store of a
public register. -/
def special (τ : FT) (i : Instr) : Option Taint.T :=
  match i with
  | .store m _ | .store8 m _ | .movdquStore m _ =>
    match m.index, storeW i with
    | some _, some (_, w) =>
      match idxRange τ m w with
      | some (ri, lo, hi) => if memPub τ.t m then some (idxStore τ.t ri lo hi (storePub τ.t i)) else none
      | none => none
    | none, _ =>
      match i with
      | .movdquStore m x => if xpub τ.t x then storeStep τ.t m 16 true else none
      | _ => none
    | _, _ => none
  | _ => none

/-- What the analysis adds to the base analysis's taint `t'` after `i`:
zeroing idioms, and loads of pointers from public slots. -/
def post (τ : FT) (i : Instr) (t' : Taint.T) : Taint.T :=
  match i with
  | .alu .xor d (.reg d') | .alu32 .xor d (.reg d') =>
    if d == d' then { t' with regs := t'.regs.insert d } else t'
  | .xop (.bin .pxor x x') => if x == x' then { t' with xregs := t'.xregs.insert x } else t'
  | .mov d (.mem m) =>
    match addrOf τ.t m with
    | some (ri, o) =>
      match τ.mb.find? (fun e => e.1 == ri && e.2.1 == o) with
      | some e => { t' with bases := (d, e.2.2.1, e.2.2.2) :: t'.bases }
      | none => t'
    | none => t'
  | _ => t'

/-- The offset into the argument area of a memory operand `[rsp + disp]`,
if it is at or above the argument area. -/
def argOff (τ : FT) (m : MemOp) : Option Nat :=
  if m.base = .rsp ∧ m.index = none ∧ ((τ.depth + 8 : Nat) : Int) ≤ m.disp then
    some (m.disp.toNat - (τ.depth + 8))
  else none

/-- The `w` bytes at offset `o` of the argument area are the same in both runs. -/
def saPub (τ : FT) (o w : Nat) : Bool := τ.sa.any fun e => e.1 ≤ o && o + w ≤ e.1 + e.2

/-- What the analysis adds to the taint `t'` after a load from the argument
area: a public value, or a pointer into a region. -/
def argPost (τ : FT) (i : Instr) (t' : Taint.T) : Taint.T :=
  match i with
  | .mov d (.mem m) =>
    match argOff τ m with
    | some o =>
      let t'' := if saPub τ o 8 then { t' with regs := t'.regs.insert d } else t'
      match τ.sp.find? (·.1 == o) with
      | some e => { t'' with bases := (d, e.2.1, e.2.2) :: t''.bases }
      | none => t''
    | none => t'
  | .mov32 d (.mem m) =>
    match argOff τ m with
    | some o => if saPub τ o 4 then { t' with regs := t'.regs.insert d } else t'
    | none => t'
  | _ => t'

/-- The `w` bytes at `m` are bytes of a region that `pb` says are public. -/
def pbPub (τ : FT) (m : MemOp) (w : Nat) : Bool :=
  match addrOf τ.t m with
  | some (i, d) => btest (pbGet τ.pb i) d w
  | none => false

/-- What the analysis adds to the taint `t'` after a load of public bytes of
a region (the base analysis's `loadPub`, of `pb`). -/
def pbPost (τ : FT) (i : Instr) (t' : Taint.T) : Taint.T :=
  match i with
  | .mov d (.mem m) => if pbPub τ m 8 then { t' with regs := t'.regs.insert d } else t'
  | .mov32 d (.mem m) => if pbPub τ m 4 then { t' with regs := t'.regs.insert d } else t'
  | .cmov _ d (.mem m) =>
    if pbPub τ m 8 && pub τ.t d && τ.t.flags then { t' with regs := t'.regs.insert d } else t'
  | _ => t'

/-- The base taint after `i`. -/
def baseStep (τ : FT) (i : Instr) : Option Taint.T :=
  match special τ i with
  | some t' => some t'
  | none => (X86_64.taint.step τ.t i).map fun t' => pbPost τ i (argPost τ i (post τ i t'))

/-- A store of a public value that leaves every byte public as it was: the
stores of a public register, and the vector stores of one that `special`
handles. -/
def stPub (τ : FT) : Instr → Bool
  | .store _ r | .store32 _ r | .store8 _ r | .store16 _ r => pub τ.t r
  | .movdquStore m x => xpub τ.t x && (m.index.isNone || (idxRange τ m 16).isSome)
  | _ => false

/-- The memory operand of a masked store, which writes within the 64 bytes at it. -/
def kStoreOp : Instr → Option MemOp
  | .kStore m _ _ | .kStore8 m _ _ => some m
  | _ => none

/-- The public bytes of the regions after `i`: a store of a public value
makes the bytes it writes public, if the analysis knows which they are, and
any other store makes secret the bytes it may write. -/
def pbAfter (τ : FT) (i : Instr) : List Nat :=
  match storeW i with
  | some (m, w) =>
    if stPub τ i then
      match addrOf τ.t m with
      | some (r, d) => if d + w ≤ τ.t.lens.getD r 0 then pbMod (bset · d w) τ.pb r else τ.pb
      | none => τ.pb
    else
      match storeRange τ m w with
      | some (ri, lo, hi) => pbMod (bclr · lo (hi - lo)) τ.pb ri
      | none => pbZero τ.pb
  | none =>
    if writesMem i then
      match (kStoreOp i).bind (storeRange τ · 64) with
      | some (ri, lo, hi) => pbMod (bclr · lo (hi - lo)) τ.pb ri
      | none => pbZero τ.pb
    else τ.pb

/-- The flags after `i`: those of `cmp a, b` (64-bit), or nothing known. -/
def flOf : Instr → Option (Reg × Reg)
  | .alu .cmp a (.reg b) => some (a, b)
  | _ => none

def step (τ : FT) (i : Instr) : Option FT :=
  if τ.ok && !isa.writesSp i then
    match baseStep τ i with
    | some t' =>
      some { τ with
        -- The public bytes are `pb`'s: the base analysis's slots stay empty.
        t := if writesMem i then { t' with slots := [] } else t'
        ub := (ubNew τ i).toList ++ ubKill τ.ub i
        fl := flOf i
        mb := mbAfter τ i
        pb := pbAfter τ i }
    | none => none
  else none

def meet (τ₁ τ₂ : FT) : FT :=
  if τ₁.ok && τ₂.ok && τ₁.nfr == τ₂.nfr && τ₁.depth == τ₂.depth && τ₁.room == τ₂.room &&
      τ₁.ras == τ₂.ras && τ₁.t.lens == τ₂.t.lens && τ₁.fw == τ₂.fw && τ₁.an == τ₂.an then
    { τ₁ with
      t := Taint.meet τ₁.t τ₂.t
      sec := Nat.lor τ₁.sec τ₂.sec
      ub := τ₁.ub.filterMap fun p => (ubOf τ₂.ub p.1).map fun n => (p.1, max p.2 n)
      fl := if τ₁.fl == τ₂.fl then τ₁.fl else none
      mb := τ₁.mb.filter (τ₂.mb.contains ·)
      sa := τ₁.sa.filter (τ₂.sa.contains ·)
      sp := τ₁.sp.filter (τ₂.sp.contains ·)
      pb := pbMeet τ₁.pb τ₂.pb }
  else none'

def le (τ σ : FT) : Bool :=
  !τ.ok || (σ.ok && τ.nfr == σ.nfr && τ.depth == σ.depth && τ.room == σ.room && τ.ras == σ.ras &&
    Taint.leK τ.t σ.t && bsub σ.sec τ.sec &&
    τ.ub.all (fun p => (ubOf σ.ub p.1).any (· ≤ p.2)) &&
    (τ.fl.isNone || τ.fl == σ.fl) && τ.mb.all (σ.mb.contains ·) && τ.fw == σ.fw && τ.an == σ.an &&
    τ.sa.all (σ.sa.contains ·) && τ.sp.all (σ.sp.contains ·) && pbLe τ.pb σ.pb)

/-- The base taint after a write of the stack pointer by a call or a return. -/
def killSp (t : Taint.T) : Taint.T := { t with bases := kill t .rsp, lo := .empty }

def callF (τ : FT) : Option FT :=
  if τ.ok && 8 ≤ τ.room then
    some ⟨true, killSp τ.t, τ.nfr, τ.depth + 8, τ.room - 8, τ.sec, (τ.room - 8) :: τ.ras,
      τ.ub.filter (·.1 != .rsp), none, τ.mb, τ.fw, τ.an, τ.sa, τ.sp, τ.pb⟩
  else none

/-- The stack pointer after a return, as an offset into the innermost frame
(region 0) if it is at or above that frame's base: the window index of the
stack pointer is then `room + 8`. -/
def spBase (τ : FT) : List (Reg × Nat × Nat) :=
  match τ.fw.head? with
  | some a => if a ≤ τ.room + 8 then [(.rsp, 0, τ.room + 8 - a)] else []
  | none => []

def retF (τ : FT) : Option FT :=
  if τ.ok && τ.ras.head? == some τ.room && 8 ≤ τ.depth then
    some ⟨true, { killSp τ.t with bases := spBase τ ++ kill τ.t .rsp }, τ.nfr, τ.depth - 8, τ.room + 8,
      τ.sec, τ.ras.tail, τ.ub.filter (·.1 != .rsp), none, τ.mb, τ.fw, τ.an, τ.sa, τ.sp, τ.pb⟩
  else none

/-- The base taint with a frame of `b` bytes pushed at the head of the
writable regions. -/
def shiftIn (t : Taint.T) (b : Nat) : Taint.T :=
  { t with
    lens := b :: t.lens
    bases := (.rsp, 0, 0) :: (kill t .rsp).map fun p => (p.1, p.2.1 + 1, p.2.2)
    slots := t.slots.map fun sl => (sl.1 + 1, sl.2)
    lo := .empty }

/-- The base taint with the frame at the head of the writable regions popped. -/
def shiftOut (t : Taint.T) : Taint.T :=
  { t with
    lens := t.lens.tail
    bases := (kill t .rsp).filterMap fun p => if p.2.1 = 0 then none else some (p.1, p.2.1 - 1, p.2.2)
    slots := t.slots.filterMap fun sl => if sl.1 = 0 then none else some (sl.1 - 1, sl.2)
    lo := .empty }

/-- The public bytes of a new frame of `b` bytes at window index `a`: those
`sec` does not list. -/
def frameBits (sec a b : Nat) : Nat := Nat.xor (ones b) (Nat.land (Nat.shiftRight sec a) (ones b))

theorem testBit_frameBits (sec a b k : Nat) :
    (frameBits sec a b).testBit k = (decide (k < b) && !sec.testBit (a + k)) := by
  show (ones b ^^^ (sec >>> a &&& ones b)).testBit k = _
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_shiftRight, testBit_ones]
  cases decide (k < b) <;> cases sec.testBit (a + k) <;> rfl

/-- `sec`, with the bytes of a frame of `b` bytes at window index `a` that
are not public (`p`, the mask of the frame). -/
def secFree (sec p a b : Nat) : Nat := Nat.lor sec (Nat.shiftLeft (Nat.xor (ones b) (Nat.land p (ones b))) a)

theorem testBit_secFree (sec p a b j : Nat) :
    (secFree sec p a b).testBit j =
      (sec.testBit j || (decide (a ≤ j) && (decide (j - a < b) && !p.testBit (j - a)))) := by
  show (sec ||| (ones b ^^^ (p &&& ones b)) <<< a).testBit j = _
  rw [Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_xor, Nat.testBit_and, testBit_ones]
  cases decide (j - a < b) <;> cases p.testBit (j - a) <;> rfl

def pushF (τ : FT) : Instr → Option FT
  | .alloc b =>
    if τ.ok && 0 < b && b < 4096 && b % 8 == 0 && b ≤ τ.room then
      some ⟨true, shiftIn τ.t b, τ.nfr + 1, τ.depth + b, τ.room - b, τ.sec,
        τ.ras, τ.ub.filter (·.1 != .rsp), none, τ.mb.map fun e => (e.1 + 1, e.2.1, e.2.2.1 + 1, e.2.2.2),
        (τ.room - b) :: τ.fw, τ.an, τ.sa, τ.sp.map fun e => (e.1, e.2.1 + 1, e.2.2),
        frameBits τ.sec (τ.room - b) b :: τ.pb⟩
    else none
  | _ => none

def popF (τ : FT) : Instr → Option FT
  | .free b =>
    if τ.ok && 1 ≤ τ.nfr && τ.t.lens.head? == some b && b ≤ τ.depth && τ.ras.all (τ.room + b ≤ ·) then
      let sec' := secFree τ.sec (pbGet τ.pb 0) τ.room b
      let mb' := τ.mb.filterMap fun e =>
        if e.1 = 0 ∨ e.2.2.1 = 0 then none else some (e.1 - 1, e.2.1, e.2.2.1 - 1, e.2.2.2)
      let sp' := τ.sp.filterMap fun e => if e.2.1 = 0 then none else some (e.1, e.2.1 - 1, e.2.2)
      some ⟨true, shiftOut τ.t, τ.nfr - 1, τ.depth - b, τ.room + b, sec', τ.ras,
        τ.ub.filter (·.1 != .rsp), none, mb', τ.fw.tail, τ.an, τ.sa, sp', τ.pb.tail⟩
    else none
  | _ => none

/-! ## Evaluation by the kernel

The kernel evaluates `step`, `le` and `meet` at every instruction, hint and
join of a check (`VG.Taint.check`). `stepF`, `leF` and `meetF` are the same
functions (`ResidueTaintSound.lean` proves each equal to its model, so the
analysis and its results are the same) written for the kernel:

* `stepFn i` classifies the instruction `i` before the taint is substituted,
  as the base analysis's `Taint.stepKDFn` does, so that the kernel unfolds
  the matches on `i` once per instruction rather than once per check of it.
  Most instructions (`isPlain`) need none of what the analysis adds to the
  base analysis: their step is the base step (`fastFn`), with the bounds of
  the register they write dropped. Stores without an index register set or
  clear bits of `pb` and need the pointers in slots (`fastStore`); loads
  (`mov r, [m]`, 64 or 32 bits, and `cmovcc r, [m]`) test bits of `pb`, and
  need `post` only when a slot holds a pointer (`fastLoad`), and `argPost`
  only when the argument area has public or pointer bytes; constants, `mul`,
  `mulx`, `and` with a constant and `cmov` of a register only change bounds
  (`fastU`); a zeroing `xor` or `pxor`, a `cmp` and a `cmovb` add to the base
  step what `fastG` is given. `stepFn1 i` is `stepFn i` with one match on `i`
  in place of its four (`isa.writesSp`, `isPlain`, `Taint.dstOf` and its
  own), and `stepFn1K`, which the kernel evaluates, is `stepFn1` with the
  cases of that match closed (`inline_match%`).
* Every step gives a taint that is evaluated, and whose fields it does not
  change are the terms they were (`Taint.forceT`, `forceList`; `slowFn` for
  the instructions without a step of their own), so that the kernel finds
  again a step it has made from the same taint: see `Taint.stepKeep`.
* `leF` and `meetF` compare numbers with `Nat.beq` and walk lists with
  `List.rec`; the base analysis's slots, which stay empty, they compare in
  one pass (`subl`, `eqs3`).

As in `VG.KList`, the functions written with `List.rec`, which Lean's
compiler does not compile, are `@[implemented_by]` the library's functions
they equal, for the hints computed in compiled code (`keep_for%`,
`taint_decide`); the kernel checks what those compute. -/

/-- An instruction's transfer function, independent of the incoming taint
(`Taint.Step` for the residue analysis). -/
structure RStep where
  run : FT → Option FT

/-- Instructions whose step is the base analysis's alone: no store, no load
into a register (`pbPost`, `post`, `argPost`), no bound (`ubNew`) or flags
(`flOf`), no zeroing idiom, and no write of registers other than
`Taint.dstOf`'s. -/
def isPlain : Instr → Bool
  | .store .. | .store32 .. | .store8 .. | .store16 .. | .movdquStore .. | .vmovdquStore ..
  | .vmovdqu32Store .. | .evStore .. | .e5ExtractStore .. | .stmxcsr _ | .kStore .. | .kStore8 .. => false
  | .mov _ (.mem _) | .mov _ (.imm _) | .mov32 _ (.imm _) | .mov32 _ (.mem _) => false
  | .alu .and _ (.imm _) | .alu32 .and _ (.imm _) => false
  | .alu .xor d (.reg d') | .alu32 .xor d (.reg d') => d != d'
  | .alu .cmp _ (.reg _) => false
  | .xop (.bin .pxor _ _) => false
  | .cmov .. | .mul _ | .mulx .. => false
  | .push _ | .pop .. | .alloc _ | .free _ | .callr _ => false
  | _ => true

/-- `ubKill ub i`, for an `i` that writes the register `d` alone. -/
def ubDrop (d : Option Reg) (ub : List (Reg × Nat)) : List (Reg × Nat) :=
  match ub, d with
  | [], _ => []
  | ub, some d => KList.filter (fun p => !regEq p.1 d) ub
  | ub, none => ub

def natsEqC (a b : List Nat) : Bool := a == b

/-- `a == b`, with `List.rec` and `Nat.beq`. -/
@[implemented_by natsEqC] def natsEq (a b : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.casesOn (motive := fun _ => Bool) b true fun _ _ => false)
    (fun x _ ih b => List.casesOn (motive := fun _ => Bool) b false fun y b' => Nat.beq x y && ih b') a b

/-- `k l`, with the list `l` evaluated to its first cell. -/
def forceList {α β : Type} (l : List β) (k : List β → α) : α :=
  List.casesOn (motive := fun _ => α) l (k []) (fun a as => k (a :: as))

/-- `k o`, with the option `o` evaluated. -/
def forceOpt {α β : Type} (o : Option β) (k : Option β → α) : α :=
  Option.casesOn (motive := fun _ => α) o (k none) (fun a => k (some a))

/-- `k t`, with every field of `t` evaluated (`Taint.forceT`; the lists to
their first cell). -/
def forceTAll {α : Type} (t : Taint.T) (k : Taint.T → α) : α :=
  match t with
  | ⟨rg, f, l, b, sl, lo, x⟩ =>
    forceList l fun l => forceList b fun b => forceList sl fun sl => lo.force fun lo =>
      Taint.forceT ⟨rg, f, l, b, sl, lo, x⟩ k

/-- `b` (`keepNats_eq`), but the term `a` when they are equal: masks that a
step computes again as they were stay the terms they were (`pbModKeep`). -/
def keepNats (a b : List Nat) : List Nat := bif natsEq b a then a else b

/-- `step · i`, giving a taint that is evaluated, and whose fields `step`
does not change are the terms they were (`slowFn_run`). -/
def slowFn (i : Instr) : RStep := ⟨fun τ =>
  match τ with
  | ⟨_, _, nfr, depth, room, sec, ras, _, _, _, fw, an, sa, sp, pb⟩ =>
    match step τ i with
    | some τ' =>
      forceTAll τ'.t fun t' => forceList τ'.ub fun ub' => forceOpt τ'.fl fun fl' => forceList τ'.mb fun mb' =>
        forceList (keepNats pb τ'.pb) fun pb' =>
          some ⟨true, t', nfr, depth, room, sec, ras, ub', fl', mb', fw, an, sa, sp, pb'⟩
    | none => none⟩

/-- `b.run t` (`runF_eq`), evaluated (`Taint.forceT`). It is a function of
the base taint alone: the kernel finds it again, evaluated, at a step from a
taint that differs from one it has met only in what this analysis adds to
the base analysis's (the masks of a caller's frame, the bounds), as the
steps of a function are at each of its calls. Forced in the step itself, the
base taint was evaluated again at each of them. -/
def runF (b : Taint.Step) (t : Taint.T) : Option Taint.T :=
  match b.run t with
  | some t' => Taint.forceT t' some
  | none => none

/-- `step` of an instruction `isPlain` says is, whose base step is `b` and
which writes the register `d`. -/
def fastFn (b : Taint.Step) (d : Option Reg) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, mb, fw, an, sa, sp, pb⟩ =>
    bif ok then
      match runF b t with
      | some t' =>
        forceList (ubDrop d ub) fun ub' =>
          some ⟨true, t', nfr, depth, room, sec, ras, ub', none, mb, fw, an, sa, sp, pb⟩
      | none => none
    else none⟩

/-- `mbAfter` of a store of `w` bytes at `m`, without an index register, from
the register `src` if a 64-bit store. No slot holds a pointer in most code,
and most stores are not of one: then nothing is looked up. -/
def mbStore (t : Taint.T) (mb : List (Nat × Nat × Nat × Nat)) (m : MemOp) (w : Nat) (src : Option Reg) :
    List (Nat × Nat × Nat × Nat) :=
  match mb, src with
  | [], none => []
  | [], some r =>
    match KList.find? (fun p => regEq p.1 r) t.bases with
    | some (_, pj, pk) =>
      match Taint.addrOfK t m with
      | some (ri, d) => bif Nat.ble (d + w) (t.lens.getD ri 0) then [(ri, d, pj, pk)] else []
      | none => []
    | none => []
  | mb, src =>
    match Taint.addrOfK t m with
    | some (ri, d) =>
      bif Nat.ble (d + w) (t.lens.getD ri 0) then
        let kept := KList.filter (fun e => !Nat.beq e.1 ri || Nat.ble (e.2.1 + 8) d || Nat.ble (d + w) e.2.1) mb
        match src with
        | some r =>
          match KList.find? (fun p => regEq p.1 r) t.bases with
          | some (_, pj, pk) => (ri, d, pj, pk) :: kept
          | none => kept
        | none => kept
      else []
    | none => []

/-- The taint `t` with the vector register `x` public. -/
def insX (x : XReg) (t : Taint.T) : Taint.T :=
  match t with
  | ⟨rg, f, l, b, sl, lo, xr⟩ => ⟨rg, f, l, b, sl, lo, xr.insert x⟩

/-- `pbMod f l i` (`pbModKeep_eq`), but `l` itself when `f` leaves the mask
of region `i` as it is: a store to bytes that are already secret, as most
are, then gives the masks it had, and the kernel finds again the steps it
has made from that taint (a callee's, at each of its calls). -/
def pbModKeep (f : Nat → Nat) (l : List Nat) (i : Nat) : List Nat :=
  bif Nat.beq (f (pbGet l i)) (pbGet l i) then l else pbMod f l i

/-- `pbAfter` of a store of `w` bytes at `m`, without an index register, of
a public value iff `p`. -/
def pbStore (t : Taint.T) (pb : List Nat) (m : MemOp) (w : Nat) (p : Bool) : List Nat :=
  match Taint.addrOfK t m with
  | some (i, d) =>
    bif Nat.ble (d + w) (t.lens.getD i 0) then
      bif p then pbModKeep (fun b => bset b d w) pb i else pbModKeep (fun b => bclr b d w) pb i
    else bif p then pb else keepNats pb (pbZero pb)
  | none => bif p then pb else keepNats pb (pbZero pb)

/-- `step` of a store of `w` bytes at `m`, without an index register, of a
value that is public iff `p` (of a public register), from the register `src`
if a 64-bit store. -/
def fastStore (m : MemOp) (w : Nat) (p : Taint.T → Bool) (src : Option Reg) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, mb, fw, an, sa, sp, pb⟩ =>
    bif ok then
      bif memPub t m then
        match t with
        | ⟨rg, f, l, b, _, lo, x⟩ =>
          forceList (mbStore t mb m w src) fun mb' => forceList (pbStore t pb m w (p t)) fun pb' =>
            some ⟨true, ⟨rg, f, l, b, [], lo, x⟩, nfr, depth, room, sec, ras, ub, none, mb', fw, an, sa, sp, pb'⟩
      else none
    else none⟩

/-- `mbAfter` of a store of `w` bytes at `m` that is not `mov [m], r`. -/
def mbStoreI (τ : FT) (m : MemOp) (w : Nat) : List (Nat × Nat × Nat × Nat) :=
  match τ.mb with
  | [] => []
  | mb =>
    match storeRange τ m w with
    | some (ri, lo, hi) => mbKill mb ri lo hi
    | none => []

/-- `pbAfter` of a store of `w` bytes at `m` of a secret value. -/
def pbStoreI (τ : FT) (m : MemOp) (w : Nat) : List Nat :=
  match storeRange τ m w with
  | some (ri, lo, hi) => pbModKeep (fun b => bclr b lo (Nat.sub hi lo)) τ.pb ri
  | none => keepNats τ.pb (pbZero τ.pb)

/-- `step` of a store of `w` bytes at `m` of a secret value, with an index
register: as `fastStore`, with the range of the bytes it may write
(`storeRange`, the model's). -/
def fastStoreI (m : MemOp) (w : Nat) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, _, fw, an, sa, sp, _⟩ =>
    bif ok then
      bif memPub t m then
        match t with
        | ⟨rg, f, l, b, _, lo, x⟩ =>
          forceList (mbStoreI τ m w) fun mb' => forceList (pbStoreI τ m w) fun pb' =>
            some ⟨true, ⟨rg, f, l, b, [], lo, x⟩, nfr, depth, room, sec, ras, ub, none, mb', fw, an, sa, sp, pb'⟩
      else none
    else none⟩

/-- `step` of an instruction that adds to the base step `b` only the bounds
`u` gives (`ubNew` and `ubKill`). -/
def fastU (b : Taint.Step) (u : List (Reg × Nat) → List (Reg × Nat)) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, mb, fw, an, sa, sp, pb⟩ =>
    bif ok then
      match runF b t with
      | some t' =>
        forceList (u ub) fun ub' =>
          some ⟨true, t', nfr, depth, room, sec, ras, ub', none, mb, fw, an, sa, sp, pb⟩
      | none => none
    else none⟩

/-- `ubKill ub i`, for an `i` that writes the registers `a` and `b` alone
(`mul`, `mulx`). -/
def ubDrop2 (a b : Reg) (ub : List (Reg × Nat)) : List (Reg × Nat) :=
  match ub with
  | [] => []
  | ub => KList.filter (fun p => !(regEq p.1 a || regEq p.1 b)) ub

/-- The taint `t` with the register `d` public. -/
def insReg (d : Reg) (t : Taint.T) : Taint.T :=
  match t with
  | ⟨rg, f, l, b, sl, lo, x⟩ => ⟨rg.insert d, f, l, b, sl, lo, x⟩

/-- `pbPub`, with `Taint.addrOfK`. -/
def pbPubK (t : Taint.T) (pb : List Nat) (m : MemOp) (w : Nat) : Bool :=
  match Taint.addrOfK t m with
  | some (i, d) => btest (pbGet pb i) d w
  | none => false

/-- `step` of a load `i` of `w` bytes at `m` into `d` (`mov d, [m]`, 64 or
32 bits, or `cmovcc d, [m]`), whose base step is `b`: `post` only if a slot
holds a pointer (`mb`), `argPost` only if the analysis knows of public or
pointer bytes in the argument area (`sa`, `sp`), `pbPost` (whose load of
public bytes gives a public value if `c`), and nothing else but the base
step. -/
def fastLoad (b : Taint.Step) (d : Reg) (m : MemOp) (w : Nat) (c : Taint.T → Bool) (i : Instr) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, _, mb, fw, an, sa, sp, pb⟩ =>
    bif ok then
      match b.run t with
      | some t' =>
        let t₁ := match mb with | [] => t' | _ => post τ i t'
        let t₂ := match sa, sp with | [], [] => t₁ | _, _ => argPost τ i t₁
        Taint.forceT (bif pbPubK t pb m w && c t then insReg d t₂ else t₂) fun t₃ =>
          forceList (ubDrop (some d) ub) fun ub' =>
            some ⟨true, t₃, nfr, depth, room, sec, ras, ub', none, mb, fw, an, sa, sp, pb⟩
      | none => none
    else none⟩

/-- `ubOf`, with `KList` and `regEq`. -/
def ubOfK (l : List (Reg × Nat)) (r : Reg) : Option Nat := (KList.find? (fun p => regEq p.1 r) l).map (·.2)

/-- `step` of an instruction that adds to the base step `b` the taint `pf`
makes of its taint (`post`), the flags `fl'` (`flOf`) and the bounds `u`
gives from the flags and the bounds before (`ubNew` and `ubKill`). -/
def fastG (b : Taint.Step) (pf : Taint.T → Taint.T) (fl' : Option (Reg × Reg))
    (u : Option (Reg × Reg) → List (Reg × Nat) → List (Reg × Nat)) : RStep := ⟨fun τ =>
  match τ with
  | ⟨ok, t, nfr, depth, room, sec, ras, ub, fl, mb, fw, an, sa, sp, pb⟩ =>
    bif ok then
      match b.run t with
      | some t' =>
        Taint.forceT (pf t') fun t' => forceList (u fl ub) fun ub' =>
          some ⟨true, t', nfr, depth, room, sec, ras, ub', fl', mb, fw, an, sa, sp, pb⟩
      | none => none
    else none⟩

/-- The bounds after `cmovb d, x`: `d` keeps its bound if the flags are those
of `cmp x, d` (`ubNew`). -/
def cmovUb (d x : Reg) (fl : Option (Reg × Reg)) (ub : List (Reg × Nat)) : List (Reg × Nat) :=
  match fl with
  | some (a, b) =>
    bif regEq a x && regEq b d then
      match ubOfK ub d with
      | some n => (d, n) :: ubDrop (some d) ub
      | none => ubDrop (some d) ub
    else ubDrop (some d) ub
  | none => ubDrop (some d) ub

/-- `step · i`, classifying `i` first. -/
def stepFn (i : Instr) : RStep :=
  bif isa.writesSp i then ⟨fun _ => none⟩
  else bif isPlain i then fastFn (Taint.stepKDFn i) (Taint.dstOf i)
  else match i with
    | .store m r => bif m.index.isNone then fastStore m 8 (pub · r) (some r) else ⟨(step · i)⟩
    | .store32 m r => bif m.index.isNone then fastStore m 4 (pub · r) none else ⟨(step · i)⟩
    | .store8 m r => bif m.index.isNone then fastStore m 1 (pub · r) none else ⟨(step · i)⟩
    | .store16 m r => bif m.index.isNone then fastStore m 2 (pub · r) none else ⟨(step · i)⟩
    | .movdquStore m x => bif m.index.isNone then fastStore m 16 (xpub · x) none else ⟨(step · i)⟩
    | .vmovdquStore .l128 m _ => bif m.index.isNone then fastStore m 16 (fun _ => false) none else fastStoreI m 16
    | .vmovdquStore .l256 m _ => bif m.index.isNone then fastStore m 32 (fun _ => false) none else fastStoreI m 32
    | .vmovdqu32Store m _ => bif m.index.isNone then fastStore m 64 (fun _ => false) none else fastStoreI m 64
    | .evStore m _ | .e5ExtractStore m _ _ =>
      bif m.index.isNone then fastStore m 32 (fun _ => false) none else fastStoreI m 32
    | .stmxcsr m => bif m.index.isNone then fastStore m 4 (fun _ => false) none else fastStoreI m 4
    | .mov d (.mem m) => fastLoad (Taint.stepKDFn i) d m 8 (fun _ => true) i
    | .mov32 d (.mem m) => fastLoad (Taint.stepKDFn i) d m 4 (fun _ => true) i
    | .cmov _ d (.mem m) => fastLoad (Taint.stepKDFn i) d m 8 (fun t => pub t d && t.flags) i
    | .cmov .b d (.reg x) => fastG (Taint.stepKDFn i) id none (cmovUb d x)
    | .cmov _ d _ => fastU (Taint.stepKDFn i) (ubDrop (some d))
    | .alu .and d (.imm v) =>
      fastU (Taint.stepKDFn i) fun ub => bif v.msb then ubDrop (some d) ub else (d, v.toNat) :: ubDrop (some d) ub
    | .alu32 .and d (.imm v) => fastU (Taint.stepKDFn i) fun ub => (d, v.toNat) :: ubDrop (some d) ub
    | .alu .cmp a (.reg b) => fastG (Taint.stepKDFn i) id (some (a, b)) fun _ ub => ubDrop (some a) ub
    | .alu .xor d (.reg _) | .alu32 .xor d (.reg _) =>
      fastG (Taint.stepKDFn i) (insReg d) none fun _ ub => ubDrop (some d) ub
    | .xop (.bin .pxor x x') =>
      bif x == x' then fastG (Taint.stepKDFn i) (insX x) none fun _ ub => ub
      else fastG (Taint.stepKDFn i) id none fun _ ub => ub
    | .mov d (.imm v) =>
      fastU (Taint.stepKDFn i) fun ub => bif v.msb then ubDrop (some d) ub else (d, v.toNat) :: ubDrop (some d) ub
    | .mov32 d (.imm v) => fastU (Taint.stepKDFn i) fun ub => (d, v.toNat) :: ubDrop (some d) ub
    | .mul _ => fastU (Taint.stepKDFn i) (ubDrop2 .rax .rdx)
    | .mulx hi lo _ => fastU (Taint.stepKDFn i) (ubDrop2 hi lo)
    | _ => ⟨(step · i)⟩

/-- `some d == some .rsp`, what `isa.writesSp` is of an instruction whose
destination is `d`, by the registers' indices (`isSp_eq`). -/
def isSp (d : Reg) : Bool := regEq d .rsp

/-- `d == .rsp`, by the registers' indices (`isSpR_eq`). -/
def isSpR (d : Reg) : Bool := regEq d .rsp

/-- `stepFn`, classifying the instruction once (`stepFn1_eq`). `stepFn` asks
`isa.writesSp`, `isPlain` and `Taint.dstOf` of an instruction, and then
matches on it, and each is a match on `Instr`, whose three hundred
constructors make one cost the kernel from 65 to 350 µs: more than the step
itself of an instruction that only writes a register. Here one match gives
all four: the destination, for `isa.writesSp` and `Taint.dstOf`, and whether
the instruction is plain, by its place among the patterns. -/
def stepFn1 (i : Instr) : RStep :=
  match i with
  | .store m r => bif m.index.isNone then fastStore m 8 (pub · r) (some r) else slowFn i
  | .store32 m r => bif m.index.isNone then fastStore m 4 (pub · r) none else slowFn i
  | .store8 m r => bif m.index.isNone then fastStore m 1 (pub · r) none else slowFn i
  | .store16 m r => bif m.index.isNone then fastStore m 2 (pub · r) none else slowFn i
  | .mov d (.mem m) => bif isSp d then ⟨fun _ => none⟩ else fastLoad (Taint.stepKeepFn i) d m 8 (fun _ => true) i
  | .mov32 d (.mem m) =>
    bif isSp d then ⟨fun _ => none⟩ else fastLoad (Taint.stepKeepFn i) d m 4 (fun _ => true) i
  | .mov d (.imm v) =>
    bif isSp d then ⟨fun _ => none⟩ else
      fastU (Taint.stepKeepFn i) fun ub => bif v.msb then ubDrop (some d) ub else (d, v.toNat) :: ubDrop (some d) ub
  | .mov32 d (.imm v) =>
    bif isSp d then ⟨fun _ => none⟩ else fastU (Taint.stepKeepFn i) fun ub => (d, v.toNat) :: ubDrop (some d) ub
  | .mul _ => fastU (Taint.stepKeepFn i) (ubDrop2 .rax .rdx)
  | .mulx hi lo _ =>
    bif isSpR hi || isSpR lo then ⟨fun _ => none⟩ else fastU (Taint.stepKeepFn i) (ubDrop2 hi lo)
  | .alu .and d (.imm v) =>
    bif isSp d then ⟨fun _ => none⟩ else
      fastU (Taint.stepKeepFn i) fun ub => bif v.msb then ubDrop (some d) ub else (d, v.toNat) :: ubDrop (some d) ub
  | .alu32 .and d (.imm v) =>
    bif isSp d then ⟨fun _ => none⟩ else fastU (Taint.stepKeepFn i) fun ub => (d, v.toNat) :: ubDrop (some d) ub
  | .alu .cmp a (.reg b) =>
    bif isSp a then ⟨fun _ => none⟩ else
      fastG (Taint.stepKeepFn i) id (some (a, b)) fun _ ub => ubDrop (some a) ub
  | .cmov .b d (.reg x) =>
    bif isSp d then ⟨fun _ => none⟩ else fastG (Taint.stepKeepFn i) id none (cmovUb d x)
  | .cmov _ d (.mem m) =>
    bif isSp d then ⟨fun _ => none⟩ else fastLoad (Taint.stepKeepFn i) d m 8 (fun t => pub t d && t.flags) i
  | .cmov _ d _ => bif isSp d then ⟨fun _ => none⟩ else fastU (Taint.stepKeepFn i) (ubDrop (some d))
  | .xop (.bin .pxor x x') =>
    bif x == x' then fastG (Taint.stepKeepFn i) (insX x) none fun _ ub => ub
    else fastG (Taint.stepKeepFn i) id none fun _ ub => ub
  | .movdquStore m x => bif m.index.isNone then fastStore m 16 (xpub · x) none else slowFn i
  | .vmovdquStore .l128 m _ => bif m.index.isNone then fastStore m 16 (fun _ => false) none else fastStoreI m 16
  | .vmovdquStore .l256 m _ => bif m.index.isNone then fastStore m 32 (fun _ => false) none else fastStoreI m 32
  | .vmovdqu32Store m _ => bif m.index.isNone then fastStore m 64 (fun _ => false) none else fastStoreI m 64
  | .evStore m _ | .e5ExtractStore m _ _ =>
    bif m.index.isNone then fastStore m 32 (fun _ => false) none else fastStoreI m 32
  | .stmxcsr m => bif m.index.isNone then fastStore m 4 (fun _ => false) none else fastStoreI m 4
  -- Not plain, and without a step of their own.
  | .kStore .. | .kStore8 .. | .push _ | .pop .. | .alloc _ | .free _ | .callr _ =>
    bif isa.writesSp i then ⟨fun _ => none⟩ else slowFn i
  -- Plain or not by their operands.
  | .alu .xor d (.reg d') | .alu32 .xor d (.reg d') =>
    bif isSp d then ⟨fun _ => none⟩ else
      bif d != d' then fastFn (Taint.stepKeepFn i) (some d)
      else fastG (Taint.stepKeepFn i) (insReg d) none fun _ ub => ubDrop (some d) ub
  -- Plain, writing the register `d`.
  | .mov d _ | .mov32 d _ | .alu _ d _ | .alu32 _ d _ | .shift32 _ d _ | .bswap32 d
  | .rorx32 d .. | .andn32 d .. | .rorx d .. | .andn d .. | .movzx8 d _ | .movzx16 d _ | .bswap d | .shift _ d _
  | .shiftCl _ d | .shiftx _ d .. | .movImm64 d _ | .leaSym d _ | .adcx d _ | .adox d _
  | .vpmovmskb _ d _ | .vpcmpltuw d .. | .movqR d _ | .imul d _ | .imul3 d .. | .shld d .. | .btr d _
  | .aluTbl _ d .. => bif isSp d then ⟨fun _ => none⟩ else fastFn (Taint.stepKeepFn i) (some d)
  -- Plain, writing no general-purpose register.
  | _ => fastFn (Taint.stepKeepFn i) none

/-- `stepFn1`, with its cases closed (`inline_match%`, `stepFn1K_eq`). -/
def stepFn1K : Instr → RStep := inline_match% stepFn1 Taint.stepKeepFn Taint.stepKDFn Taint.xopStepFn

/-- `step`, for the kernel (`stepF_eq`). -/
def stepF (τ : FT) (i : Instr) : Option FT := (stepFn1K i).run τ

/-- `a = b`, for pairs, slots and pointers in slots. -/
def eq2 (a b : Nat × Nat) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2

def eq3 (a b : Nat × Nat × Nat) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2 b.2.2

def eq4 (a b : Nat × Nat × Nat × Nat) : Bool :=
  Nat.beq a.1 b.1 && Nat.beq a.2.1 b.2.1 && Nat.beq a.2.2.1 b.2.2.1 && Nat.beq a.2.2.2 b.2.2.2

def sublC : List (Nat × Nat × Nat) → List (Nat × Nat × Nat) → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if eq3 a b then sublC as bs else sublC (a :: as) bs

/-- `as` is a sublist of `bs` (in order), in one pass over both. -/
@[implemented_by sublC] def subl (as bs : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool)
    (fun as => List.casesOn (motive := fun _ => Bool) as true fun _ _ => false)
    (fun b _ ih as => List.casesOn (motive := fun _ => Bool) as true fun a as' =>
      bif eq3 a b then ih as' else ih as) bs as

/-- `as.all (bs.contains ·)`, in one pass if `as` is a sublist of `bs`. -/
def slotsLe (as bs : List (Nat × Nat × Nat)) : Bool := subl as bs || KList.all as (mem3 · bs)

/-- `Taint.leK`, with `slotsLe`. -/
def leKF (τ σ : Taint.T) : Bool :=
  τ.regs.subset σ.regs && (!τ.flags || σ.flags) && natsEq τ.lens σ.lens &&
    KList.all τ.bases (memB · σ.bases) && slotsLe τ.slots σ.slots && τ.lo.subset σ.lo &&
    τ.xregs.subset σ.xregs

/-- `le`, for the kernel (`leF_eq`). -/
def leF (τ σ : FT) : Bool :=
  !τ.ok || (σ.ok && Nat.beq τ.nfr σ.nfr && Nat.beq τ.depth σ.depth && Nat.beq τ.room σ.room &&
    natsEq τ.ras σ.ras && leKF τ.t σ.t && bsub σ.sec τ.sec &&
    KList.all τ.ub (fun p => (ubOfK σ.ub p.1).any (Nat.ble · p.2)) &&
    (τ.fl.isNone || τ.fl == σ.fl) && KList.all τ.mb (fun e => KList.any σ.mb (eq4 e)) && natsEq τ.fw σ.fw &&
    Nat.beq τ.an σ.an && KList.all τ.sa (fun e => KList.any σ.sa (eq2 e)) && KList.all τ.sp (mem3 · σ.sp) &&
    pbLe τ.pb σ.pb)

def eqs3C (as bs : List (Nat × Nat × Nat)) : Bool := as == bs

/-- `as = bs`, for slots. -/
@[implemented_by eqs3C] def eqs3 (as bs : List (Nat × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (Nat × Nat × Nat) → Bool)
    (fun bs => List.casesOn (motive := fun _ => Bool) bs true fun _ _ => false)
    (fun a _ ih bs => List.casesOn (motive := fun _ => Bool) bs false fun b bs' => eq3 a b && ih bs') as bs

/-- `Taint.meet`, keeping the slots as they are when both sides have the same. -/
def meetT (τ₁ τ₂ : Taint.T) : Taint.T :=
  match τ₁, τ₂ with
  | ⟨r₁, f₁, l₁, b₁, s₁, lo₁, x₁⟩, ⟨r₂, f₂, l₂, b₂, s₂, lo₂, x₂⟩ =>
    bif natsEq l₁ l₂ then
      ⟨r₁.inter r₂, f₁ && f₂, l₁, KList.filter (memB · b₂) b₁,
        bif eqs3 s₁ s₂ then s₁ else KList.filter (mem3 · s₂) s₁, lo₁.inter lo₂, x₁.inter x₂⟩
    else ⟨r₁.inter r₂, f₁ && f₂, [], KList.filter (memB · b₂) b₁, [], lo₁.inter lo₂, x₁.inter x₂⟩

/-- `meet`, for the kernel (`meetF_eq`). -/
def meetF (τ₁ τ₂ : FT) : FT :=
  bif τ₁.ok && τ₂.ok && Nat.beq τ₁.nfr τ₂.nfr && Nat.beq τ₁.depth τ₂.depth && Nat.beq τ₁.room τ₂.room &&
      natsEq τ₁.ras τ₂.ras && natsEq τ₁.t.lens τ₂.t.lens && natsEq τ₁.fw τ₂.fw && Nat.beq τ₁.an τ₂.an then
    { τ₁ with
      t := meetT τ₁.t τ₂.t
      sec := Nat.lor τ₁.sec τ₂.sec
      ub := τ₁.ub.filterMap fun p => (ubOfK τ₂.ub p.1).map fun n => (p.1, max p.2 n)
      fl := if τ₁.fl == τ₂.fl then τ₁.fl else none
      mb := KList.filter (fun e => KList.any τ₂.mb (eq4 e)) τ₁.mb
      sa := KList.filter (fun e => KList.any τ₂.sa (eq2 e)) τ₁.sa
      sp := KList.filter (mem3 · τ₂.sp) τ₁.sp
      pb := pbMeet τ₁.pb τ₂.pb }
  else none'

end VG.X86_64.RTaint
