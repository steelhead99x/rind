module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubChecks
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueTaintSound
public import VerifiedGarbage.Proof.Framework.X86_64.Scrub
public import VerifiedGarbage.Proof.Framework.Lit
public import VerifiedGarbage.Proof.Framework.Taint
public meta import Lean.Meta.Eval
public meta import Lean.Elab.Term
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.Offset

/-!
# The residue analysis decides what `scrub` wipes (x86-64)

`init sig stack` is where the residue analysis (`RTaint.rtaint`) starts on
a function of signature `sig`: everything in the registers is the same in
both runs (`Outside 0`), the writable regions are its writable buffers (of
their lengths, if fixed, and their addresses in the argument registers),
its window is the `stack` bytes below the stack pointer, which hold the
same bytes in both runs, and of its stack arguments, those the contract
says are public are the same in both runs (`saOf`), and those that are
writable buffers hold their addresses (`spAux`) (`init_agree`). If the
analysis of its code ends with the window as it started, the window's bytes the analysis cannot show
equal in both runs are those `sec` lists; `scrub` then need wipe only the
16-byte granules that hold them (`keepOf`), and `resOk_of_check` gives
`Verified.scrub` the rest (`Scrub.ResOk`).
-/

@[expose] public section

namespace VG.X86_64.RScrub

open VG.X86_64 VG.X86_64.Taint VG.X86_64.RTaint VG.X86_64.Scrub VG.Impl.Scrub.X86_64

/-! ## Where the analysis starts -/

/-- The word index and length (`0` if not fixed) of each writable buffer of
the parameters, the first at word `w`. -/
def wrInfo : List (String × Param) → Nat → List (Nat × Nat)
  | [], _ => []
  | (_, .int ..) :: ps, w => wrInfo ps (w + 1)
  | (_, .array m e n) :: ps, w => (if m then [(w, n * e.size)] else []) ++ wrInfo ps (w + 1)
  | (_, .slice m _ _) :: ps, w => (if m then [(w, 0)] else []) ++ wrInfo ps (w + 2)
  | (_, .slices ..) :: ps, w => wrInfo ps (w + 2)
  | (_, .table _) :: ps, w => wrInfo ps (w + 1)

/-- The argument registers holding the address of writable buffer `i`, `i + 1`, …. -/
def basesAux : List (Nat × Nat) → Nat → List (Reg × Nat × Nat)
  | [], _ => []
  | q :: qs, i => (match argRegs[q.1]? with | some r => [(r, i, 0)] | none => []) ++ basesAux qs (i + 1)

def allRegs : RegSet Reg := RegSet.ofList
  [.rax, .rcx, .rdx, .rbx, .rsp, .rbp, .rsi, .rdi, .r8, .r9, .r10, .r11, .r12, .r13, .r14, .r15]

def allX : RegSet XReg := RegSet.ofList
  [.xmm0, .xmm1, .xmm2, .xmm3, .xmm4, .xmm5, .xmm6, .xmm7,
   .xmm8, .xmm9, .xmm10, .xmm11, .xmm12, .xmm13, .xmm14, .xmm15]

/-- The widths of the argument words of `sig`. -/
def widths (sig : Sig) : List Nat := (sig.words 64).map (·.bits 64)

/-- The number of argument words passed on the stack. -/
def nStack (sig : Sig) : Nat := (widths sig).length - argRegs.length

/-- The bytes of the argument area that are public: those of each public
argument passed on the stack, as many as its width. -/
def saOf (sig : Sig) : List (Nat × Nat) :=
  (List.range (nStack sig)).filterMap fun k =>
    if (sig.params.flatMap (·.2.pubs)).getD (argRegs.length + k) false then
      some (8 * k, min 8 ((widths sig).getD (argRegs.length + k) 64 / 8))
    else none

/-- The stack arguments holding the address of writable buffer `i`, `i + 1`, …. -/
def spAux : List (Nat × Nat) → Nat → List (Nat × Nat × Nat)
  | [], _ => []
  | q :: qs, i =>
    (if argRegs.length ≤ q.1 then [(8 * (q.1 - argRegs.length), i, 0)] else []) ++ spAux qs (i + 1)

/-- The bytes of `pubs` (`(i, o, n)`: the `n` bytes at offset `o` of writable
buffer `i`), as a bit mask for each of `n` buffers. -/
def pbInit (n : Nat) (pubs : List (Nat × Nat × Nat)) : List Nat :=
  (List.range n).map fun i => pubs.foldl (fun b sl => if sl.1 = i then bset b sl.2.1 sl.2.2 else b) 0

theorem pbInit_bit {n : Nat} {pubs : List (Nat × Nat × Nat)} {i k : Nat}
    (h : (pbGet (pbInit n pubs) i).testBit k = true) :
    ∃ sl ∈ pubs, sl.1 = i ∧ sl.2.1 ≤ k ∧ k < sl.2.1 + sl.2.2 := by
  have fold : ∀ (l : List (Nat × Nat × Nat)) (b : Nat),
      (l.foldl (fun b sl => if sl.1 = i then bset b sl.2.1 sl.2.2 else b) b).testBit k = true →
      b.testBit k = true ∨ ∃ sl ∈ l, sl.1 = i ∧ sl.2.1 ≤ k ∧ k < sl.2.1 + sl.2.2 := by
    intro l
    induction l with
    | nil => exact fun b h => .inl h
    | cons sl l ih =>
      intro b h
      rcases ih _ h with h | ⟨q, hq, h⟩
      · dsimp only at h
        split at h
        · rename_i h0
          rw [testBit_bset, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h
          rcases h with h | h
          · exact .inl h
          · exact .inr ⟨sl, List.mem_cons_self, h0, h⟩
        · exact .inl h
      · exact .inr ⟨q, List.mem_cons_of_mem _ hq, h⟩
  rw [pbGet_eq, pbInit, List.getD_eq_getElem?_getD, List.getElem?_map] at h
  by_cases hi : i < n
  · rw [List.getElem?_range hi, Option.map_some, Option.getD_some] at h
    rcases fold pubs 0 h with h | h
    · simp only [Nat.zero_testBit, Bool.false_eq_true] at h
    · exact h
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega_using [hi]), Option.map_none, Option.getD_none] at h
    simp only [Nat.zero_testBit, Bool.false_eq_true] at h

/-- Where the analysis of a function of signature `sig` starts. -/
def init (sig : Sig) (stack : Nat) (pubs : List (Nat × Nat × Nat) := []) : FT :=
  let ws := wrInfo sig.params 0
  let t : Taint.T := ⟨allRegs, true, ws.map (·.2), basesAux ws 0, [], .empty, allX⟩
  ⟨true, t, 0, 0, stack, 0, [], [], none, [], [], 8 * nStack sig, saOf sig, spAux ws 0, pbInit ws.length pubs⟩

/-- The writable buffers. -/
def wrOf (ps : List (String × Param)) (vs : List (BitVec 64)) : List Region :=
  ((Sig.bufs ps vs).filter (·.2)).map (·.1)

theorem wr_info : ∀ (ps : List (String × Param)) (vs : List (BitVec 64)) (w : Nat),
    vs.length = (ps.flatMap (·.2.words 64)).length →
    List.Forall₂ (fun r l => l ≤ r.len) (wrOf ps vs) ((wrInfo ps w).map (·.2)) ∧
    ∀ i (h : i < (wrInfo ps w).length), w ≤ ((wrInfo ps w)[i]).1 ∧ ((wrInfo ps w)[i].1 - w) < vs.length ∧
      ((wrOf ps vs).getD i ⟨0, 0⟩).base = vs.getD ((wrInfo ps w)[i].1 - w) 0
  | [], vs, w, _ => ⟨by simp [wrOf, Sig.bufs, wrInfo], fun i h => by simp [wrInfo] at h⟩
  | (_, p) :: ps, vs, w, hl => by
    cases p with
    | int ty pb =>
      obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp [Param.words] at hl
        | cons v vs => exact ⟨v, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega_using [hl]
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 1) (by omega_using [hl])
      refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
      simp only [wrInfo] at h ⊢
      obtain ⟨a, b, c⟩ := h2 i h
      refine ⟨by omega_using [a], by simp; omega_using [b], ?_⟩
      simp only [wrOf, Sig.bufs] at c ⊢
      rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega_using [a]]
      simp
    | array m e n =>
      obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp [Param.words] at hl
        | cons v vs => exact ⟨v, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega_using [hl]
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 1) (by omega_using [hl])
      cases m with
      | false =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h ⊢
        obtain ⟨a, b, c⟩ := h2 i h
        refine ⟨by omega_using [a], by simp; omega_using [b], ?_⟩
        simp only [wrOf, Sig.bufs, List.filter_cons, Bool.false_eq_true, ↓reduceIte] at c ⊢
        rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega_using [a]]
        simp
      | true =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, ↓reduceIte, List.singleton_append, List.length_cons] at h ⊢
        cases i with
        | zero => simp [wrOf, Sig.bufs]
        | succ i =>
          obtain ⟨a, b, c⟩ := h2 i (by omega_using [h])
          refine ⟨by simp; omega_using [a], by simp; omega_using [b], ?_⟩
          simp only [wrOf, Sig.bufs, List.filter_cons, ↓reduceIte, List.map_cons, List.getD_cons_succ,
            List.getElem_cons_succ] at c ⊢
          rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega_using [a]]
          simp
    | slice m e len =>
      obtain ⟨v, l, vs, rfl⟩ : ∃ v l vs', vs = v :: l :: vs' := by
        match vs with
        | [] => simp [Param.words] at hl
        | [_] => simp [Param.words] at hl
        | v :: l :: vs => exact ⟨v, l, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega_using [hl]
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 2) (by omega_using [hl])
      cases m with
      | false =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, Bool.false_eq_true, ↓reduceIte, List.nil_append] at h ⊢
        obtain ⟨a, b, c⟩ := h2 i h
        refine ⟨by omega_using [a], by simp; omega_using [b], ?_⟩
        simp only [wrOf, Sig.bufs, List.filter_cons, Bool.false_eq_true, ↓reduceIte] at c ⊢
        rw [c, show (wrInfo ps (w + 2))[i].1 - w = (wrInfo ps (w + 2))[i].1 - (w + 2) + 1 + 1 by omega_using [a]]
        simp
      | true =>
        refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
        simp only [wrInfo, ↓reduceIte, List.singleton_append, List.length_cons] at h ⊢
        cases i with
        | zero => simp [wrOf, Sig.bufs]
        | succ i =>
          obtain ⟨a, b, c⟩ := h2 i (by omega_using [h])
          refine ⟨by simp; omega_using [a], by simp; omega_using [b], ?_⟩
          simp only [wrOf, Sig.bufs, List.filter_cons, ↓reduceIte, List.map_cons, List.getD_cons_succ,
            List.getElem_cons_succ] at c ⊢
          rw [c, show (wrInfo ps (w + 2))[i].1 - w = (wrInfo ps (w + 2))[i].1 - (w + 2) + 1 + 1 by omega_using [a]]
          simp
    | slices e count =>
      obtain ⟨v, l, vs, rfl⟩ : ∃ v l vs', vs = v :: l :: vs' := by
        match vs with
        | [] => simp [Param.words] at hl
        | [_] => simp [Param.words] at hl
        | v :: l :: vs => exact ⟨v, l, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega_using [hl]
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 2) (by omega_using [hl])
      refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
      simp only [wrInfo] at h ⊢
      obtain ⟨a, b, c⟩ := h2 i h
      refine ⟨by omega_using [a], by simp; omega_using [b], ?_⟩
      simp only [wrOf, Sig.bufs] at c ⊢
      rw [c, show (wrInfo ps (w + 2))[i].1 - w = (wrInfo ps (w + 2))[i].1 - (w + 2) + 1 + 1 by omega_using [a]]
      simp
    | table n =>
      obtain ⟨v, vs, rfl⟩ : ∃ v vs', vs = v :: vs' := by
        cases vs with
        | nil => simp [Param.words] at hl
        | cons v vs => exact ⟨v, vs, rfl⟩
      replace hl : vs.length = (ps.flatMap (·.2.words 64)).length := by
        simp only [List.flatMap_cons, Param.words, List.length_append, List.length_cons, List.length_nil] at hl ⊢
        omega_using [hl]
      obtain ⟨h1, h2⟩ := wr_info ps vs (w + 1) (by omega_using [hl])
      refine ⟨by simpa [wrOf, Sig.bufs, wrInfo] using h1, fun i h => ?_⟩
      simp only [wrInfo] at h ⊢
      obtain ⟨a, b, c⟩ := h2 i h
      refine ⟨by omega_using [a], by simp; omega_using [b], ?_⟩
      simp only [wrOf, Sig.bufs] at c ⊢
      rw [c, show (wrInfo ps (w + 1))[i].1 - w = (wrInfo ps (w + 1))[i].1 - (w + 1) + 1 by omega_using [a]]
      simp

theorem basesAux_mem : ∀ {qs : List (Nat × Nat)} {i : Nat} {p : Reg × Nat × Nat}, p ∈ basesAux qs i →
    ∃ j, ∃ h : j < qs.length, argRegs[qs[j].1]? = some p.1 ∧ p.2 = (i + j, 0)
  | [], _, _, h => by simp [basesAux] at h
  | q :: qs, i, p, h => by
    simp only [basesAux, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i r hr
        simp only [List.mem_singleton] at h; subst h
        exact ⟨0, by simp, by simpa using hr, by simp⟩
      · cases h
    · obtain ⟨j, hj, h1, h2⟩ := basesAux_mem h
      exact ⟨j + 1, by simp; omega_using [hj], by simpa using h1, by rw [h2]; congr 1; omega_using []⟩

theorem abi_vals {ws : List Nat} {f : State → List (BitVec 64)} (h : abi.args ws = some f) {w : Nat}
    (hw : w < ws.length) {r : Reg} (hr : argRegs[w]? = some r) (s : State) : (f s).getD w 0 = s.gpr r := by
  have h6 : w < 6 := by
    have : w < argRegs.length := by
      rcases Nat.lt_or_ge w argRegs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hr; cases hr
    exact this
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hr
  simp only [abi] at h
  split at h <;> cases h
  · simp [List.getD_eq_getElem?_getD, hw, List.getElem?_eq_getElem hlt]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left, hlt]

/-! ## The argument area at the start -/

theorem spAux_mem : ∀ {qs : List (Nat × Nat)} {i : Nat} {e : Nat × Nat × Nat}, e ∈ spAux qs i →
    ∃ j, ∃ h : j < qs.length, argRegs.length ≤ qs[j].1 ∧ e = (8 * (qs[j].1 - argRegs.length), i + j, 0)
  | [], _, _, h => by simp [spAux] at h
  | q :: qs, i, e, h => by
    simp only [spAux, List.mem_append] at h
    rcases h with h | h
    · split at h
      · rename_i hq
        simp only [List.mem_singleton] at h; subst h
        exact ⟨0, by simp, hq, by simp⟩
      · cases h
    · obtain ⟨j, hj, h1, h2⟩ := spAux_mem h
      exact ⟨j + 1, by simp; omega_using [hj], by simpa using h1, by
        rw [h2, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 j]⟩

/-- The value of a stack argument. -/
theorem abi_stack_vals {ws : List Nat} {f : State → List (BitVec 64)} (h : abi.args ws = some f) {k : Nat}
    (hk : argRegs.length + k < ws.length) (s : State) : (f s).getD (argRegs.length + k) 0 = stackArg s k := by
  simp only [abi] at h
  split at h
  · rename_i hl; omega
  · cases h
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp only [List.length_map, Nat.add_sub_cancel_left, List.getElem?_map, List.getElem?_range (by omega_using [hk] : k < ws.length - argRegs.length), Option.map_some, Option.getD_some]

/-- `aa` at `init`: the stack pointer on entry plus `8 + o`. -/
theorem aa_init (sig : Sig) (stack : Nat) (pubs : List (Nat × Nat × Nat)) (s : State) (o : Nat) :
    aa s (init sig stack pubs) o = s.gpr .rsp + BitVec.ofNat 64 (8 + o) := by
  simp only [aa, wa, wb, init]
  rw [show stack + 0 + 8 + o = stack + (8 + o) by omega_using [], BitVec.ofNat_add stack (8 + o), ← BitVec.add_assoc,
    BitVec.sub_add_cancel]

/-- Byte `j` of a 64-bit little-endian word. -/
theorem readW64_byte (m : Mem) (a : Addr) {j : Nat} (hj : j < 8) :
    m (a + BitVec.ofNat 64 j) = (m.readW a 64).extractLsb' (8 * j) 8 := by
  rw [← Mem.extractLsb'_read m a (n := 8) hj]
  simp only [Mem.readW]
  rfl

/-- The bytes of two words that agree on their low `w` bits. -/
theorem byte_of_setWidth {x y : BitVec 64} {w j : Nat} (h : x.setWidth w = y.setWidth w) (hj : 8 * j + 8 ≤ w) :
    x.extractLsb' (8 * j) 8 = y.extractLsb' (8 * j) 8 := by
  ext i hi
  have := congrArg (fun z => z.getLsbD (8 * j + i)) h
  simp only [BitVec.getLsbD_setWidth, show 8 * j + i < w by omega_using [hj, hi], decide_true, Bool.true_and] at this
  simp only [BitVec.getElem_extractLsb']
  exact this

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- What the precondition gives of the writable regions. -/
theorem init_wf (hA : ScrubAbi A) {pubs : List (Nat × Nat × Nat)} {s : State} (h : (sig.contract A pre post wa stack leak).pre s) :
    Wf (init sig stack pubs).t s ∧ List.Forall₂ (fun r l => l ≤ r.len) s.wr (init sig stack pubs).t.lens := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals hvals
  obtain ⟨-, -, hwr, hpw, -, hbnd, -⟩ := h
  have hl : (vals s).length = (sig.params.flatMap (·.2.words 64)).length := by
    rw [hA.argsLen _ _ hvals s, List.length_map]
    show (sig.params.flatMap (·.2.words A.ptrBits)).length = _
    rw [hA.ptrBits]
  -- The writable regions are the writable buffers.
  have hw : s.wr = wrOf sig.params (vals s) := by
    rw [← hA.wr, hwr]
    simp only [List.filter_append, List.map_append, wrOf]
    have e1 : (List.map (fun r => (r, false)) (Sig.lists A.ptrBits (A.mem s) sig.params (vals s))).filter (·.2) = [] := by
      simp
    have e2 : ((A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa))).filter (·.2) = [] := by
      rw [List.filter_eq_nil_iff]
      intro a ha
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
      simp [hA.argRo _ _ b hb]
    rw [e1, e2]; simp
  obtain ⟨hF, hI⟩ := wr_info sig.params (vals s) 0 hl
  refine ⟨⟨fun _ => ⟨hw ▸ hF, ?_, ?_⟩, fun p hp => ?_⟩, hw ▸ hF⟩
  · rw [hw]
    have h1 := (hpw.sublist (List.sublist_append_left _ _)).sublist
      (List.sublist_append_left (Sig.bufs sig.params (vals s)) _)
    have h2 := h1.sublist (List.filter_sublist (p := (·.2)))
    exact List.pairwise_map.mpr (h2.imp_of_mem fun ha _ h => h (by simp [(List.mem_filter.mp ha).2]))
  · intro r hr
    rw [hw] at hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    have := hbnd a (List.mem_append_left _ (List.mem_filter.mp ha).1)
    rw [hA.ptrBits] at this
    omega_using [this]
  · obtain ⟨j, hj, hr, hp2⟩ := basesAux_mem hp
    obtain ⟨-, hlt, hb⟩ := hI j hj
    rw [hp2]
    simp only [Nat.zero_add, Nat.sub_zero] at hb hlt ⊢
    have hv : (vals s).getD (wrInfo sig.params 0)[j].1 0 = s.gpr p.1 := by
      have := hA.args ((sig.words A.ptrBits).map (·.bits A.ptrBits))
      rw [hvals] at this
      exact abi_vals this.symm (by rw [← hA.argsLen _ _ hvals s]; exact hlt) hr s
    rw [← hv, ← hb]
    simp [region, hw, BitVec.add_zero]

theorem widths_eq (hA : ScrubAbi A) (sig : Sig) :
    (sig.words A.ptrBits).map (·.bits A.ptrBits) = widths sig := by
  rw [hA.ptrBits]; rfl

theorem nStack_argArea (sig : Sig) (s : State) (hn : 0 < nStack sig) :
    abi.argArea (widths sig) s = [(⟨stackArgAddr s 0, 8 * nStack sig⟩, false)] := by
  simp only [nStack] at hn
  simp only [abi, nStack, show ¬ ((widths sig).length - argRegs.length = 0) by omega_using [hn], ↓reduceIte]

/-- What the precondition gives of the argument area: it does not wrap, and
no writable region holds a byte of it. -/
theorem pre_argArea (hA : ScrubAbi A) {s : State} (h : (sig.contract A pre post wa stack leak).pre s) :
    (0 < nStack sig → (s.gpr .rsp).toNat + 8 + 8 * nStack sig ≤ 2 ^ 64) ∧
    ∀ k < 8 * nStack sig, ∀ r ∈ s.wr, ¬ r.Contains (s.gpr .rsp + BitVec.ofNat 64 (8 + k)) 1 := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals hvals
  obtain ⟨hwf, -, hwr, hpw, -⟩ := h
  rw [widths_eq hA] at hwf hwr hpw
  have h6 : argRegs.length = 6 := rfl
  have htop : 0 < nStack sig → (s.gpr .rsp).toNat + 8 + 8 * nStack sig ≤ 2 ^ 64 := fun hn => by
    have := hA.wfAbi _ _ _ hwf
    simp only [abi] at this
    split at this
    · rename_i hl; simp only [nStack] at hn; omega
    · have := this.2; simp only [nStack] at hn ⊢; omega_using [this]
  refine ⟨htop, fun k hk r hr => ?_⟩
  · have hn : 0 < nStack sig := by omega_using [hk]
    rw [← hA.wr, hwr, hA.argArea, nStack_argArea sig s hn] at hr
    rw [hA.argArea, nStack_argArea sig s hn] at hpw
    simp only [List.map_cons, List.map_nil, Bool.false_and] at hr hpw
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨ha, ha2⟩ := List.mem_filter.mp ha
    rcases List.mem_append.mp ha with ha | ha
    · have hd := (List.pairwise_append.mp hpw).2.2 a ha _ (List.mem_singleton_self _) (by simp [ha2])
      intro hc
      refine hd _ hc ?_
      simp only [stackArgAddr]
      rw [show 8 + k = 8 * (0 + 1) + k by omega_using [], ← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc]
      exact Offset.contains_base _ (by omega_using [hk]) (by have := htop hn; omega_using [htop, hk])
    · simp only [List.mem_singleton] at ha; subst ha; simp at ha2

/-- The arguments' values, and the writable regions they give. -/
theorem pre_vals (hA : ScrubAbi A) {s : State} (h : (sig.contract A pre post wa stack leak).pre s) :
    ∃ vals, abi.args (widths sig) = some vals ∧ s.wr = wrOf sig.params (vals s) ∧
      (vals s).length = (sig.params.flatMap (·.2.words 64)).length := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals hvals
  obtain ⟨-, -, hwr, -⟩ := h
  have hl : (vals s).length = (sig.params.flatMap (·.2.words 64)).length := by
    rw [hA.argsLen _ _ hvals s, List.length_map]
    show (sig.params.flatMap (·.2.words A.ptrBits)).length = _
    rw [hA.ptrBits]
  refine ⟨vals, by rw [← hA.args, ← widths_eq hA]; exact hvals, ?_, hl⟩
  rw [← hA.wr, hwr]
  simp only [List.filter_append, List.map_append, wrOf]
  have e1 : (List.map (fun r => (r, false)) (Sig.lists A.ptrBits (A.mem s) sig.params (vals s))).filter (·.2) = [] := by
    simp
  have e2 : ((A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
      (fun (r, w) => (r, w && wa))).filter (·.2) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    simp [hA.argRo _ _ b hb]
  rw [e1, e2]; simp

/-- The stack arguments `init` says hold the addresses of writable buffers do. -/
theorem init_sp (hA : ScrubAbi A) {pubs : List (Nat × Nat × Nat)} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) :
    (∀ e ∈ (init sig stack pubs).sp, s.mem.readW (aa s (init sig stack pubs) e.1) 64 =
      (region s e.2.1).base + BitVec.ofNat 64 e.2.2) ∧
    ∀ e ∈ (init sig stack pubs).sp, e.1 + 8 ≤ (init sig stack pubs).an := by
  obtain ⟨vals, hv, hw, hl⟩ := pre_vals hA h
  have hwl : (widths sig).length = (sig.params.flatMap (·.2.words 64)).length := by
    simp [widths, Sig.words]
  have key : ∀ e ∈ (init sig stack pubs).sp, ∃ j, ∃ hj : j < (wrInfo sig.params 0).length,
      argRegs.length ≤ (wrInfo sig.params 0)[j].1 ∧ (wrInfo sig.params 0)[j].1 < (vals s).length ∧
      e = (8 * ((wrInfo sig.params 0)[j].1 - argRegs.length), j, 0) := by
    intro e he
    simp only [init] at he
    obtain ⟨j, hj, h6, rfl⟩ := spAux_mem he
    obtain ⟨-, hlt, -⟩ := (wr_info sig.params (vals s) 0 hl).2 j hj
    exact ⟨j, hj, h6, by simpa using hlt, by simp⟩
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨j, hj, h6, hlt, rfl⟩ := key e he
    obtain ⟨-, -, hb⟩ := (wr_info sig.params (vals s) 0 hl).2 j hj
    simp only [Nat.sub_zero] at hb
    have hk : argRegs.length + ((wrInfo sig.params 0)[j].1 - argRegs.length) < (widths sig).length := by
      omega_using [hl, hwl, h6, hlt]
    have hs := abi_stack_vals hv hk s
    rw [Nat.add_sub_cancel' h6] at hs
    simp only
    rw [aa_init, region, hw, hb, hs, BitVec.add_zero, stackArg, stackArgAddr,
      show 8 + 8 * ((wrInfo sig.params 0)[j].1 - argRegs.length) =
        8 * ((wrInfo sig.params 0)[j].1 - argRegs.length + 1) by omega_using []]
  · obtain ⟨j, hj, h6, hlt, rfl⟩ := key e he
    simp only [init, nStack]
    omega_using [hl, hwl, h6, hlt]

/-- The public stack arguments are the same in both runs, in the bits of their width. -/
theorem pub_stack (hA : ScrubAbi A) {s₁ s₂ : State} (hp : (sig.contract A pre post wa stack leak).pub s₁ s₂)
    {k : Nat} (hk : k < nStack sig)
    (hpk : (sig.params.flatMap (·.2.pubs)).getD (argRegs.length + k) false = true) :
    (stackArg s₁ k).setWidth ((widths sig).getD (argRegs.length + k) 64) =
      (stackArg s₂ k).setWidth ((widths sig).getD (argRegs.length + k) 64) := by
  simp only [Sig.contract] at hp
  split at hp
  · exact hp.elim
  rename_i vals hvals
  have := hp.2.1 _ hpk
  rw [widths_eq hA] at this hvals
  rw [hA.args] at hvals
  simp only [nStack] at hk
  rwa [abi_stack_vals hvals (by omega_using [hk]), abi_stack_vals hvals (by omega_using [hk])] at this

/-- The bytes of the argument area that `init` says are public are. -/
theorem init_sa (hA : ScrubAbi A) {pubs : List (Nat × Nat × Nat)} {s₁ s₂ : State}
    (hp : (sig.contract A pre post wa stack leak).pub s₁ s₂) :
    SaEq (init sig stack pubs) s₁ s₂ ∧ ∀ e ∈ (init sig stack pubs).sa, e.1 + e.2 ≤ (init sig stack pubs).an := by
  have key : ∀ e ∈ (init sig stack pubs).sa, ∃ k < nStack sig,
      (sig.params.flatMap (·.2.pubs)).getD (argRegs.length + k) false = true ∧
      e = (8 * k, min 8 ((widths sig).getD (argRegs.length + k) 64 / 8)) := by
    intro e he
    simp only [init, saOf, List.mem_filterMap, List.mem_range] at he
    obtain ⟨k, hk, he⟩ := he
    split at he
    · rename_i hpk; cases he; exact ⟨k, hk, hpk, rfl⟩
    · cases he
  refine ⟨fun e he j h1 h2 => ?_, fun e he => ?_⟩
  · obtain ⟨k, hk, hpk, rfl⟩ := key e he
    simp only at h1 h2
    have hb := byte_of_setWidth (j := j - 8 * k) (pub_stack hA hp hk hpk) (by
      have := Nat.min_le_right 8 ((widths sig).getD (argRegs.length + k) 64 / 8)
      omega_using [h1, h2])
    have ha : ∀ s : State, aa s (init sig stack pubs) j = stackArgAddr s k + BitVec.ofNat 64 (j - 8 * k) := by
      intro s
      rw [aa_init, stackArgAddr, BitVec.add_assoc, BitVec.ofNat_add_ofNat]
      congr 2; omega_using [h1]
    have hj : j - 8 * k < 8 := by have := Nat.min_le_left 8 ((widths sig).getD (argRegs.length + k) 64 / 8); omega_using [h2]
    rw [ha, ha, readW64_byte s₁.mem (stackArgAddr s₁ k) hj, readW64_byte s₂.mem (stackArgAddr s₂ k) hj]
    exact hb
  · obtain ⟨k, hk, -, rfl⟩ := key e he
    simp only [init]
    have := Nat.min_le_left 8 ((widths sig).getD (argRegs.length + k) 64 / 8)
    omega_using [hk]

/-- The bytes `pubs` lists (`(i, o, n)`: the `n` bytes at offset `o` of writable buffer `i`) are
the same in two runs whose entry states agree on what the contract says is public. -/
def PubOk (k : Contract isa) (pubs : List (Nat × Nat × Nat)) : Prop :=
  ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ →
    ∀ sl ∈ pubs, ∀ j, sl.2.1 ≤ j → j < sl.2.1 + sl.2.2 → s₁.mem (byteAddr s₁ sl.1 j) = s₂.mem (byteAddr s₂ sl.1 j)

/-- Every range of `pubs` lies in its buffer, as the signature gives its length. -/
def pubsFit (sig : Sig) (pubs : List (Nat × Nat × Nat)) : Bool :=
  pubs.all fun sl => sl.2.1 + sl.2.2 ≤ ((wrInfo sig.params 0).map (·.2)).getD sl.1 0

theorem init_agree (hA : ScrubAbi A) {pubs : List (Nat × Nat × Nat)} (hfit : pubsFit sig pubs = true)
    (hpub : PubOk (sig.contract A pre post wa stack leak) pubs)
    {s₁ s₂ : State} (h₁ : (sig.contract A pre post wa stack leak).pre s₁)
    (h₂ : (sig.contract A pre post wa stack leak).pre s₂) (ho : Outside 0 s₁ s₂)
    (hp : (sig.contract A pre post wa stack leak).pub s₁ s₂)
    (hu : s₁.unknowns = s₂.unknowns) : Agree (init sig stack pubs) s₁ s₂ := by
  intro _
  have hag := hpub s₁ s₂ h₁ h₂ hp ho
  obtain ⟨hrd, hwr, hg, hrax, hcf, hzf, hsf, hof, hx, -, -, -, -, -, hm⟩ := ho
  have hgr : ∀ r, s₁.gpr r = s₂.gpr r := fun r => by
    by_cases h : r = .rax
    · subst h; simpa using hrax
    · exact hg r h
  obtain ⟨wf₁, hF⟩ := init_wf (stack := stack) (pubs := pubs) hA h₁
  have wf₂ := (init_wf (stack := stack) (pubs := pubs) hA h₂).1
  obtain ⟨hst, hdis⟩ := contract_pre_scrub hA h₁
  have hne : ∀ r ∈ s₁.rd ++ s₁.wr, (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint r := by
    intro r hr
    by_cases h0 : stack = 0
    · intro a ha; subst h0; simp [Region.Contains] at ha
    · exact (hdis r hr).2 h0
  have hrsp := (s₁.gpr .rsp).isLt
  refine ⟨⟨⟨fun r _ => hgr r, fun _ => ⟨hcf, hzf, hsf, hof⟩⟩, fun _ => hwr, wf₁, wf₂,
      fun _ h => (by cases h), fun _ h => (by cases h), noLo, fun r _ => (by rw [hx])⟩,
    hgr .rsp, hu, hwr, ?_, Nat.zero_le _, ?_, (by simp [init]; omega_using []), fun _ h => absurd h (Nat.not_lt_zero _), ?_,
    fun _ h => (by cases h), List.Pairwise.nil, fun _ h => (by cases h), ?_, fun _ h => (by cases h),
    ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h), (init_sp hA h₁).1⟩,
    ⟨fun _ h => (by cases h), fun _ _ h => (by cases h), fun _ h => (by cases h), (init_sp hA h₂).1⟩,
    fun _ h => absurd h (Nat.not_lt_zero _),
    fun h => by have := (pre_argArea hA h₁).1 (by simp only [init] at h; omega_using [h]); simp only [init]; omega_using [this],
    fun k hk r hr => by rw [aa_init]; exact (pre_argArea hA h₁).2 k hk r hr,
    (init_sa hA hp).2, (init_sa hA hp).1, (init_sp hA h₁).2, ?_⟩
  rotate_right
  · intro i k hk
    obtain ⟨sl, hsl, rfl, h1, h2⟩ := pbInit_bit hk
    simp only [pubsFit, List.all_eq_true, decide_eq_true_eq] at hfit
    exact ⟨by have := hfit sl hsl; simp only [init]; omega_using [h2, this], hag sl hsl k h1 h2⟩
  · intro h
    rw [h] at hF
    exact List.eq_nil_of_length_eq_zero (forall₂_length hF)
  · simp only [init]; rcases hst with h | h <;> omega_using [h]
  · intro i _ hi
    simp only [init, wb, Nat.add_zero]
    rw [region_getElem hi]
    exact Region.Disjoint.symm (hne _ (List.mem_append_right _ (List.getElem_mem _)))
  · intro j hj _ hw
    simp only [init, Nat.add_zero] at hj
    rw [← wa_eq (hgr .rsp)]
    apply hm
    intro r hr hc
    simp only [RTaint.wa, wb, init] at hc
    exact hne r hr _ (Offset.contains_base _ (by omega_using [hj]) (by omega_using [hst, hj])) hc

/-- What `resOk_of_check` checks of the analysis's last taint: the window as
it started, and every byte of it `sec` lists in a granule `ks` lists. -/
def resOkB (τ : FT) (stack : Nat) (ks cs : List Nat) : Bool :=
  τ.ok && τ.room == stack && τ.depth == 0 &&
    (List.range stack).all fun j => cov ks cs j || !τ.sec.testBit j

/-- The granules `wipe ks cs` may zero, as offsets from the bottom of the
`cs.sum` bytes and widths. -/
def granules : List Nat → List (Nat × Nat)
  | [] => []
  | b :: bs => ((List.range (b / 16)).map fun t => (bs.sum + b % 16 + 16 * t, 16)) ++
    (if b % 16 = 8 then [(bs.sum, 8)] else []) ++ granules bs

/-- The bytes of the granules `gs` that `ks` lists, as a bit mask. -/
def covMask (ks : List Nat) (gs : List (Nat × Nat)) : Nat :=
  gs.foldr (fun g m => bif KList.any ks (Nat.beq g.1) then bset m g.1 g.2 else m) 0

theorem covMask_bit {ks : List Nat} : ∀ {gs : List (Nat × Nat)} {j : Nat}, (covMask ks gs).testBit j = true →
    ∃ g ∈ gs, g.1 ∈ ks ∧ g.1 ≤ j ∧ j < g.1 + g.2
  | [], j, h => by simp only [covMask, List.foldr_nil, Nat.zero_testBit, Bool.false_eq_true] at h
  | g :: gs, j, h => by
    have h' : (bif KList.any ks (Nat.beq g.1) then bset (covMask ks gs) g.1 g.2 else covMask ks gs).testBit j =
        true := h
    cases hk : KList.any ks (Nat.beq g.1) with
    | false =>
      rw [hk, Bool.cond_false] at h'
      obtain ⟨g', hg', r⟩ := covMask_bit h'
      exact ⟨g', List.mem_cons_of_mem _ hg', r⟩
    | true =>
      rw [hk, Bool.cond_true, testBit_bset, Bool.or_eq_true] at h'
      rcases h' with h' | h'
      · obtain ⟨g', hg', r⟩ := covMask_bit h'
        exact ⟨g', List.mem_cons_of_mem _ hg', r⟩
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at h'
        rw [KList.any_eq, List.any_eq_true] at hk
        obtain ⟨x, hx, e⟩ := hk
        exact ⟨g, List.mem_cons_self, Nat.eq_of_beq_eq_true e ▸ hx, h'.1, h'.2⟩

theorem granules_le : ∀ {cs : List Nat} {g : Nat × Nat}, g ∈ granules cs → g.1 + g.2 ≤ cs.sum
  | [], g, h => by simp only [granules, List.not_mem_nil] at h
  | b :: bs, g, h => by
    simp only [granules, List.mem_append, List.mem_map, List.mem_range] at h
    rw [List.sum_cons]
    rcases h with (⟨t, ht, rfl⟩ | h) | h
    · show bs.sum + b % 16 + 16 * t + 16 ≤ b + bs.sum
      omega
    · split at h
      · rw [List.mem_singleton] at h
        subst h
        show bs.sum + 8 ≤ b + bs.sum
        omega
      · exact absurd h List.not_mem_nil
    · have := granules_le h
      omega

/-- `wipe ks cs` zeroes the bytes of a granule that `ks` lists. -/
theorem cov_of_granule {ks : List Nat} : ∀ {cs : List Nat} {g : Nat × Nat} {j : Nat}, g ∈ granules cs →
    g.1 ∈ ks → g.1 ≤ j → j < g.1 + g.2 → cov ks cs j = true
  | [], g, j, h, _, _, _ => by simp only [granules, List.not_mem_nil] at h
  | b :: bs, g, j, h, hk, h₁, h₂ => by
    simp only [granules, List.mem_append, List.mem_map, List.mem_range] at h
    rw [cov]
    rcases h with (⟨t, ht, rfl⟩ | h) | h
    · replace h₁ : bs.sum + b % 16 + 16 * t ≤ j := h₁
      replace h₂ : j < bs.sum + b % 16 + 16 * t + 16 := h₂
      rw [ite_eq_right (by omega), Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega, ?_⟩
      rw [covC, ite_eq_right (by omega),
        show bs.sum + b % 16 + 16 * ((j - bs.sum - b % 16) / 16) = bs.sum + b % 16 + 16 * t by omega]
      exact List.contains_iff_mem.mpr hk
    · split at h
      · rename_i h8
        rw [List.mem_singleton] at h
        subst h
        replace h₁ : bs.sum ≤ j := h₁
        replace h₂ : j < bs.sum + 8 := h₂
        rw [ite_eq_right (by omega), Bool.and_eq_true, decide_eq_true_eq]
        refine ⟨by omega, ?_⟩
        rw [covC, ite_eq_left (by omega), Bool.and_eq_true, beq_iff_eq]
        exact ⟨h8, List.contains_iff_mem.mpr hk⟩
      · exact absurd h List.not_mem_nil
    · have hle := granules_le h
      rw [ite_eq_left (by omega)]
      exact cov_of_granule h hk h₁ h₂

/-- `resOkB`, as one comparison of bit masks: the bytes that `sec` lists,
among the bytes of the granules that `ks` lists (`covMask`), rather than a
question of `cov` for every byte of the window (`stack` of them), or for
every byte `sec` lists, each a walk of `ks` (half a second in the kernel for
a function whose frame holds five hundred secret bytes). -/
def resOkF (τ : FT) (stack : Nat) (ks cs : List Nat) : Bool :=
  τ.ok && τ.room == stack && τ.depth == 0 &&
    bsub (Nat.mod τ.sec (Nat.pow 2 stack)) (covMask ks (granules cs))

theorem resOkB_of_resOkF {τ : FT} {stack : Nat} {ks cs : List Nat} (h : resOkF τ stack ks cs = true) :
    resOkB τ stack ks cs = true := by
  simp only [resOkF, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ho, hr⟩, hd⟩, hs⟩ := h
  simp only [resOkB, ho, hr, hd, Bool.true_and, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true']
  intro j hj
  cases hb : τ.sec.testBit j
  · exact .inr rfl
  · have hm : (τ.sec % 2 ^ stack).testBit j = true := by
      rw [Nat.testBit_mod_two_pow, hb, decide_eq_true hj]; rfl
    obtain ⟨g, hg, hk, h₁, h₂⟩ := covMask_bit (bsub_bit hs hm)
    exact .inl (cov_of_granule hg hk h₁ h₂)

/-- `(o.any (resOkF · stack ks cs))` gives `resOkB`'s. -/
theorem any_resOkB {o : Option FT} {stack : Nat} {ks cs : List Nat}
    (h : o.any (resOkF · stack ks cs) = true) : o.any (resOkB · stack ks cs) = true := by
  cases o with
  | none => cases h
  | some τ => exact resOkB_of_resOkF h

/-- The analysis of the code, from `init`, proves the bytes of the window
outside the granules `ks` the same in both runs. -/
theorem resOk_of_check {c : Prog isa} {ks cs : List Nat} {pubs : List (Nat × Nat × Nat)} (hA : ScrubAbi A)
    (hv : Verified target c (sig.contract A pre post wa stack leak)) (hcs : cs.sum = stack)
    {h : VG.Taint.Hint FT}
    (hfit : pubsFit sig pubs = true) (hpub : PubOk (sig.contract A pre post wa stack leak) pubs)
    (hc : (VG.Taint.check rtaint (init sig stack pubs) c h).any (resOkB · stack ks cs) = true) :
    ResOk c (sig.contract A pre post wa stack leak) stack ks cs := by
  obtain ⟨τf, hτ, hb⟩ : ∃ τf, VG.Taint.check rtaint (init sig stack pubs) c h = some τf ∧
      resOkB τf stack ks cs = true := by
    cases h' : VG.Taint.check rtaint (init sig stack pubs) c h with
    | none => rw [h'] at hc; cases hc
    | some τf => rw [h'] at hc; exact ⟨τf, rfl, hc⟩
  simp only [resOkB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true'] at hb
  obtain ⟨⟨⟨hok, hroom⟩, hdep⟩, hcov⟩ := hb
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu _ e₁ e₂ x hx hw
  obtain ⟨-, ha⟩ := VG.Taint.check_sound (A := rtaint) hτ (init_agree hA hfit hpub h₁ h₂ ho hp hu) e₁ e₂
  have inv := ha hok
  obtain ⟨hcor, -, -⟩ := hv
  have hsp : u₁.gpr .rsp = s₁.gpr .rsp := by
    obtain ⟨t', u', he', hab, -⟩ := hcor s₁ h₁
    obtain ⟨-, rfl⟩ := Exec.det e₁ he'
    exact hab.1 .rsp (by decide)
  have hwr : u₁.wr = s₁.wr := (Exec.rdwr e₁).2
  obtain ⟨hst, hdis⟩ := contract_pre_scrub hA h₁
  have hj : (x - (s₁.gpr .rsp - BitVec.ofNat 64 stack)).toNat < stack := by
    simp only [Region.Contains] at hx; omega_using [hx]
  generalize hJ : (x - (s₁.gpr .rsp - BitVec.ofNat 64 stack)).toNat = j at hj
  have hxe : x = RTaint.wa u₁ τf j := by
    simp only [RTaint.wa, wb, hroom, hsp, ← hJ, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have hcj : cov ks cs j = false := by
    cases h' : cov ks cs j
    · rfl
    · exact absurd ⟨hcs ▸ hx, by rw [hcs, hJ]; exact h'⟩ hw
  have hns : ¬ InSec τf.sec j := by
    intro hin
    rcases hcov j hj with h | h
    · rw [hcj] at h; cases h
    · rw [show τf.sec.testBit j = true from hin] at h; cases h
  have hfree : ∀ r ∈ u₁.wr, ¬ r.Contains (RTaint.wa u₁ τf j) 1 := by
    intro r hr hc
    rw [hwr] at hr
    rw [← hxe] at hc
    exact (hdis r (List.mem_append_right _ hr)).2 (by omega_using [hj]) x hx hc
  have := inv.dead j (by rw [hroom, hdep]; omega_using [hj]) hns hfree
  have e2 : RTaint.wa u₂ τf j = RTaint.wa u₁ τf j := by simp only [RTaint.wa, wb, inv.rsp]
  rw [e2, ← hxe] at this
  exact this

end

/-! ## The granules to wipe -/

/-- The granules of `wipe _ cs` that hold a byte `sec` lists. -/
def keepOf (sec : Nat) (cs : List Nat) : List Nat :=
  (granules cs).filterMap fun g => if (sec >>> g.1) % 2 ^ g.2 ≠ 0 then some g.1 else none

/-! ## Registrations -/

/-- `resOk_of_check` for a registration. -/
theorem resOk_reg {api : Api} (r : Registration api target) (ks : List Nat) {pubs : List (Nat × Nat × Nat)}
    (hfit : pubsFit api.sig pubs = true) (hpub : PubOk r.contract pubs) {h : VG.Taint.Hint FT}
    (hc : (VG.Taint.check rtaint (init api.sig r.stack pubs) r.code h).any (resOkB · r.stack ks (chunks r.stack)) = true) :
    ResOk r.code r.contract r.stack ks (chunks r.stack) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpub
  rw [e] at hv hp ⊢
  exact resOk_of_check (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (chunks_sum r.stack) hfit hp hc

theorem pubOk_nil (k : Contract isa) : PubOk k [] := fun _ _ _ _ _ _ _ h => absurd h List.not_mem_nil

/-- `resOk_reg`, with no bytes of the buffers known public, from the analysis
ending as `resOkF` checks (which the kernel evaluates faster than `resOkB`). -/
theorem resOk_reg0 {api : Api} (r : Registration api target) (ks : List Nat) {h : VG.Taint.Hint FT}
    (hc : (VG.Taint.check rtaint (init api.sig r.stack) r.code h).any (resOkF · r.stack ks (chunks r.stack)) = true) :
    ResOk r.code r.contract r.stack ks (chunks r.stack) :=
  resOk_reg r ks (pubs := []) rfl (pubOk_nil _) (any_resOkB hc)

/-- The granules of `r.stack` bytes of stack that `scrub` must wipe after
the code `code` of signature `sig`, from the analysis (none if it fails,
which the check then rejects). -/
def keepFor (sig : Sig) (stack : Nat) (code : Prog isa) (pubs : List (Nat × Nat × Nat) := []) : List Nat :=
  match VG.Taint.hint rtaint 256 (init sig stack pubs) code with
  | some (τ, _) => keepOf τ.sec (chunks stack)
  | none => []

theorem mxClassFrom_ok : ∀ (c : Prog isa) (k : List (String × Prog isa × Unit × Option MxC)),
    (∀ e ∈ k, e.2.2.2 = mxClass e.2.1) →
      (mxClassFrom c k).1 = mxClass c ∧ ∀ e ∈ (mxClassFrom c k).2, e.2.2.2 = mxClass e.2.1
  | .block _, _, hk => ⟨rfl, hk⟩
  | .seq a b, k, hk => by
    obtain ⟨ha, ka⟩ := mxClassFrom_ok a k hk
    obtain ⟨hb, kb⟩ := mxClassFrom_ok b _ ka
    simp only [mxClassFrom, mxClass, ← ha, ← hb]
    split
    · exact ⟨rfl, hk⟩
    · cases hx : (mxClassFrom a k).1 with
      | none => exact ⟨rfl, ka⟩
      | some x =>
        cases hy : (mxClassFrom b (mxClassFrom a k).2).1 with
        | none => exact ⟨rfl, kb⟩
        | some y => exact ⟨rfl, kb⟩
  | .ite _ t e, k, hk => by
    obtain ⟨ha, ka⟩ := mxClassFrom_ok t k hk
    obtain ⟨hb, kb⟩ := mxClassFrom_ok e _ ka
    simp only [mxClassFrom, mxClass, ← ha, ← hb]
    cases hx : (mxClassFrom t k).1 with
    | none => exact ⟨rfl, ka⟩
    | some x =>
      cases hy : (mxClassFrom e (mxClassFrom t k).2).1 with
      | none => exact ⟨rfl, kb⟩
      | some y => exact ⟨rfl, kb⟩
  | .loop b _, k, hk => mxClassFrom_ok b k hk
  | .call n b, k, hk =>
    Code.memoCall_ok (n := n) (run := fun _ => mxClassFrom b k) (spec := fun c _ => mxClass c) hk (mxClassFrom_ok b k hk)
  | .frame i b j, k, hk => by
    obtain ⟨hb, kb⟩ := mxClassFrom_ok b k hk
    simp only [mxClassFrom, mxClass]
    split
    · exact ⟨hb, kb⟩
    · exact ⟨rfl, hk⟩
  | .icall i n b nx, k, hk => by
    obtain ⟨ha, ka⟩ := Code.memoCall_ok (n := n) (run := fun _ => mxClassFrom b k) (spec := fun c _ => mxClass c) hk
      (mxClassFrom_ok b k hk)
    obtain ⟨hb, kb⟩ := mxClassFrom_ok nx _ ka
    simp only [mxClassFrom, mxClass]
    split
    · exact ⟨rfl, hk⟩
    · simp only [← ha, ← hb]
      cases hx : (Code.memoCall n b () k fun _ => mxClassFrom b k).1 with
      | none => exact ⟨rfl, ka⟩
      | some x =>
        cases hy : (mxClassFrom nx (Code.memoCall n b () k fun _ => mxClassFrom b k).2).1 with
        | none => exact ⟨rfl, kb⟩
        | some y => exact ⟨rfl, kb⟩

theorem mxClassOnce_eq (c : Prog isa) : mxClassOnce c = mxClass c :=
  (mxClassFrom_ok c [] fun _ h => by cases h).1

/-- The level `scrub` clears the vector registers at for `code`: `pxor` if
nothing in it writes bits 511:128 of a vector register, else `vpxor`
(`Instr.vecLevelR`: whatever it does to MXCSR, which `withScrub` asks of
separately). -/
def levelFor (code : Prog isa) : VecLevel :=
  if levelLeROnce VecLevel.sse.level code then .sse else .avx

theorem levelFor_ne (code : Prog isa) : levelFor code ≠ .evex := by
  unfold levelFor; split <;> exact VecLevel.noConfusion

/-- The residue analysis of the code `code` of signature `sig`, whose frames
and calls use `stack` bytes, from `init` with the bytes `pubs` of its buffers
public: the granules `ks` that `scrub` wipes, and the analysis's success
(`resOk_of_check`), which the kernel checks (`taint_decide`). -/
structure Analysed (sig : Sig) (stack : Nat) (pubs : List (Nat × Nat × Nat)) (code : Prog isa) where
  ks : List Nat
  ok : ∃ h : VG.Taint.Hint FT,
    (VG.Taint.check rtaint (init sig stack pubs) code h).any (resOkB · stack ks (chunks stack)) = true

/-- `Analysed.ok`, from the analysis with a hint `taint_decide` finds, ending
as `resOkF` checks (which the kernel evaluates faster than `resOkB`). -/
theorem Analysed.ok_of {sig : Sig} {stack : Nat} {pubs : List (Nat × Nat × Nat)} {code : Prog isa}
    (ks : List Nat) {h : VG.Taint.Hint FT}
    (hc : (VG.Taint.check rtaint (init sig stack pubs) code h).any (resOkF · stack ks (chunks stack)) = true) :
    ∃ h : VG.Taint.Hint FT,
      (VG.Taint.check rtaint (init sig stack pubs) code h).any (resOkB · stack ks (chunks stack)) = true :=
  ⟨h, any_resOkB hc⟩

/-- `r`, returning without secret residue (`scrubRegM`), given the residue
analysis of its code (`Analysed`) and if `scrub`'s side conditions hold (code
that loads MXCSR leaving in it a function of MXCSR on entry, `mxClass`, as
Intel's MCDT prologue and epilogue do);
otherwise `r` itself, which then has no proof (`Registration.residue`), as
the emitter allows only of what `ci/residue_allowlist.txt` lists. A caller
generic over the implementations of a function (`Generic/`) takes the
analysis of each of its instances from the implementation, `none` for one
the analysis does not handle. -/
def withScrub {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (pubs : List (Nat × Nat × Nat)) (hpub : PubOk r.contract pubs)
    (a : Option (Analysed api.sig r.stack pubs r.code)) : Registration api target :=
  match a with
  | none => r
  | some a =>
    let v := levelFor r.code
    if hfit : pubsFit api.sig pubs = true then
    if hd : r.code.x86_64Depth ≤ r.stack then
    if hst : r.stack + 8 < 2 ^ 64 then
    if h8 : r.stack % 8 = 0 then
    if hlv : levelLeROnce v.level r.code = true then
    if hmx : (mxClassOnce r.code).isSome = true then
    if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
        api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
    if hw : r.written = [] then
      scrubRegM r v a.ks hd hst h8 ((Code.allOnce_eq _ r.code).symm.trans hlv) (mxClassOnce_eq r.code ▸ hmx) hrb hpost
        (by obtain ⟨_, hc⟩ := a.ok; exact resOk_reg r a.ks hfit hpub hc) hw (levelFor_ne _)
    else r else r else r else r else r else r else r else r

/-- `withScrub`, for code whose two runs leave the same bytes in its stack
but the granules `ks` (`hres`), proven of the code rather than by the
residue analysis (as `X86_64.Scrub.resOk_of_leaves` gives it from what the
code leaves run by run): `r` followed by the clearing of those granules,
returning without secret residue (`scrubRegM`), if `scrub`'s side
conditions hold; otherwise `r` itself, which then has no proof. -/
def withScrubRes {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (ks : List Nat) (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) : Registration api target :=
  let v := levelFor r.code
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : r.code.allOnce (fun i => decide (i.vecLevelR ≤ v.level)) = true then
  if hmx : (mxClassOnce r.code).isSome = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
    scrubRegM r v ks hd hst h8 ((Code.allOnce_eq _ r.code).symm.trans hlv) (mxClassOnce_eq r.code ▸ hmx) hrb hpost
      hres hw (levelFor_ne _)
  else r else r else r else r else r else r else r

end VG.X86_64.RScrub

/-! ## The code of a check, as a literal

`taint_decide` has the kernel evaluate the literal of any code that has one
(`rw_lit`), but not of code it reaches through a structure with proofs about
it (`Lit.reaches`: rewriting inside one would change the types of its
proofs): a registration's `r.code`, as `resOk_reg0` states its check, or the
functions of a variant (`MdHash`, `StreamFn`). The kernel then builds the
code from the functions that generate it, and what it walks are their
terms: two instructions that are the same after evaluation are different
terms, each met for the first time (`stepFn1K`, a third of a millisecond),
and no step is found again. Here the code of such a check is evaluated in
compiled code and the check stated of that literal, with the literals of the
functions it calls (as `materialize_code` writes one): the kernel compares
the code with it once, by evaluation, and the analysis walks a literal. A
check of such code is proven by `taint_decide_lit`, not `taint_decide`. -/

namespace VG.X86_64.RScrub

open Lean Meta Elab Tactic

/-- Whether the code `c` is reached through a structure with proofs among
its fields, which `rw_lit` does not unfold, and names no literal: code that
`rw_lit` leaves, all of it, to the functions that generate it. (Code of
which it finds the literals of some functions stays as it leaves it: the
literal of ML-DSA's key preparation, whose polynomial arithmetic it does not
find, gained nothing and cost a comparison.) -/
meta def hiddenCode (c : Expr) : MetaM Bool := do
  if c.hasLooseBVars || c.hasFVar || c.hasMVar then return false
  let env ← getEnv
  let cs := c.getUsedConstants
  if cs.any (· matches .str _ "lit") then return false
  for k in cs do
    if let some info := env.find? k then
      if ← Lit.hasProofFields info.type.getForallBody.getAppFn then return true
  return false

/-- The closed code `c` as a literal, calling the literals of the code
materialized so far (as `Lit.materialize` writes `N.lit`), and a proof that
`c` is that literal: by evaluation, then each function called rewritten to
its literal. -/
meta def codeLit (c : Expr) : MetaM (Expr × Expr) := do
  let ty ← inferType c
  let codeTy ← whnfD ty
  unless codeTy.isAppOfArity ``Code 2 do throwError "taint_decide: {c} is not code: {ty}"
  let codeTy := mkApp2 (mkConst ``Code) (← whnfD codeTy.appFn!.appArg!) (← whnfD codeTy.appArg!)
  let inst ← synthInstance (mkApp (mkConst ``ToExpr [0]) codeTy)
  let v ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``ToExpr.toExpr [0]) codeTy inst c)
  -- The code materialized so far, written out in full.
  let mut lits : Array (Name × Expr) := #[]
  let mut expanded : Std.HashMap Name Expr := {}
  for g in Lit.litNames (← getEnv) do
    let lhs ← Lit.lhsOf g
    if (← isDefEq (← inferType lhs) ty) then
      let (e, m) ← (Lit.expandLit g).run expanded
      expanded := m
      lits := lits.push (g, e)
  let (abs, gs) ← (Lit.abstractCalls lits v).run #[]
  let lhss ← gs.mapM Lit.lhsOf
  -- `abs` with the `i`-th callee (marked `.bvar (1000000 + i)`) replaced by `f i`.
  let fill (f : Nat → Expr) : Expr :=
    abs.replace fun e => match e with
      | .bvar k => if 1000000 ≤ k then some (f (k - 1000000)) else none
      | _ => none
  let eqTy (rhs : Expr) := mkApp3 (mkConst ``Eq [1]) ty c rhs
  -- `c = abs[callees]` by evaluation, then each callee rewritten to its literal.
  let mut prf := mkApp2 (mkConst ``Eq.refl [1]) ty c
  for i in [0:gs.size] do
    let motive := Expr.lam `x ty
      (eqTy ((fill fun j => if j < i then mkConst (gs[j]! ++ `lit)
        else if j == i then .bvar 0 else lhss[j]!))) .default
    prf := mkApp4 (mkConst ``Eq.mp [0])
      (mkApp motive lhss[i]!) (mkApp motive (mkConst (gs[i]! ++ `lit)))
      (mkApp6 (mkConst ``congrArg [1, 1]) ty (mkSort 0) lhss[i]!
        (mkConst (gs[i]! ++ `lit)) motive (mkConst (gs[i]! ++ `lit_eq))) prf
  return (ShareCommon.shareCommon' (fill fun i => mkConst (gs[i]! ++ `lit)), ShareCommon.shareCommon' prf)

/-- `taint_decide` (`VG.taintDecideAt`), but that after `rw_lit` a check of
code that `rw_lit` has left to the functions that generate it (`hiddenCode`)
is stated of the code's literal (`codeLit`) before the kernel evaluates it. -/
meta def taintDecideLit (chunkSize : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let some chk := (← instantiateMVars (← g.getType)).find? (·.isAppOfArity ``VG.Taint.check 5)
    | throwError "taint_decide_lit: the goal is not an equation about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  unless h.isMVar do throwError "taint_decide_lit: the hint is already given"
  let tT ← whnfD (mkApp2 (mkConst ``VG.Taint.T) m a)
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``VG.Taint.Hint.toExprNS) tT instT
    (mkApp5 (mkConst ``VG.Taint.hintOfSize) m a chunkSize τ c))
  h.mvarId!.assign hv
  evalTactic (← `(tactic| rw_lit))
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let some chk := tgt.find? (·.isAppOfArity ``VG.Taint.check 5)
    | throwError "taint_decide_lit: the goal is not an equation about `Taint.check A τ c h`"
  let c := chk.getArg! 3
  if ← hiddenCode c then
    let (lit, prf) ← codeLit c
    let ty ← inferType c
    let motive ← withLocalDeclD `y ty fun y =>
      mkLambdaFVars #[y] (tgt.replace fun t => if t == c then some y else none)
    replaceMainGoal [← g.replaceTargetEq (tgt.replace fun t => if t == c then some lit else none)
      (mkApp6 (mkConst ``congrArg [1, 1]) ty (mkSort 0) c lit motive prf)]
  evalTactic (← `(tactic| decide +kernel))

/-- `taint_decide_lit`: `taint_decide` for a check of the residue analysis
of code that `rw_lit` cannot see (`hiddenCode`: a registration's `r.code`, as
`resOk_reg0` states its check, the functions of a variant), which it states
of the code's literal (`codeLit`) before the kernel evaluates it. On any
other code it is `taint_decide`. -/
elab "taint_decide_lit" : tactic => withMainContext do
  let saved ← saveState
  try
    taintDecideLit (mkNatLit 1024)
  catch _ =>
    -- Discard the failed attempt's hint assignment before constructing another.
    saved.restore
    taintDecideLit (mkConst ``VG.Taint.chunk)

end VG.X86_64.RScrub

/-- `keep_for% sig stack code`: `RScrub.keepFor sig stack code`, computed in
compiled code, as a literal (for the kernel, which then checks it with the
analysis, `RScrub.resOk_reg`, rather than computing it too). -/
syntax "keep_for% " term:max term:max term:max (term:max)? : term

open Lean Elab Term Meta in
elab_rules : term
  | `(keep_for% $sig $stack $code $[$pubs]?) => do
  let e ← match pubs with
    | some p => elabTerm (← `(VG.X86_64.RScrub.keepFor $sig $stack $code $p)) none
    | none => elabTerm (← `(VG.X86_64.RScrub.keepFor $sig $stack $code)) none
  synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let v ← unsafe evalExpr (List Nat) (← inferType e) e
  return toExpr v

