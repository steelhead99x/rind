module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.Covers
public import Batteries.Data.List.Basic
public import VerifiedGarbage.Proof.Framework.Mem

/-!
# Inlining verified code, on any ISA

The code of a verified function can be inlined into another function whose
state permits more memory. Running code from a state that permits more
(`RegionModel.widen`) gives the same result, and code never writes outside
the regions its state permits (`RegionModel.regions`). `RegionModel.inline`
combines the two: a run from a state with narrower permissions is a run from
the state itself. `wp_narrow`, `verified_narrowTo` and `trace_narrow` apply
it to the correctness and constant-time parts of a `Verified` proof, and
`relCT_call` (`RelCT.lean`) to two runs of a call.

These are proved once from what a `RegionModel` states of each step of an
ISA's semantics (`exec`, `call`, `ret`, a frame's `push` and `pop`); each
ISA's `Inline.lean` gives its model, and states these theorems about its
own states. `Exec.keep` is the same induction for a value that every
instruction keeps (a register no instruction writes), given how calls and
frames keep it.
-/

@[expose] public section

namespace VG

variable {M : ISA}

/-- What the inlining theory needs of the permissions of an ISA's states:
which regions a state may read and write and its memory, how to change the
permissions, and how each step of the semantics depends on them. -/
structure RegionModel (M : ISA) where
  rd : M.State → List Region
  wr : M.State → List Region
  mem : M.State → Mem
  /-- `s`, permitted to read `r` and write `w` instead. -/
  withRegions : M.State → List Region → List Region → M.State
  rd_with (s : M.State) (r w : List Region) : rd (withRegions s r w) = r
  wr_with (s : M.State) (r w : List Region) : wr (withRegions s r w) = w
  mem_with (s : M.State) (r w : List Region) : mem (withRegions s r w) = mem s
  with_self (s : M.State) : withRegions s (rd s) (wr s) = s
  with_with (s : M.State) (r w r' w' : List Region) :
    withRegions (withRegions s r w) r' w' = withRegions s r' w'
  /-- An instruction keeps the permissions, and writes only within `wr`. -/
  exec_regions {i : M.Instr} {s s' : M.State} : M.exec i s = some s' →
    rd s' = rd s ∧ wr s' = wr s ∧ Frame (wr s) (mem s) (mem s')
  /-- An instruction runs the same with more permissions. -/
  exec_widen {i : M.Instr} {s s' : M.State} {r w : List Region} :
    Covers (rd s ++ wr s) (r ++ w) → Covers (wr s) w → M.exec i s = some s' →
    M.exec i (withRegions s r w) = some (withRegions s' r w)
  addrs_with (i : M.Instr) (s : M.State) (r w : List Region) :
    M.addrs i (withRegions s r w) = M.addrs i s
  eval_with (c : M.Cond) (s : M.State) (r w : List Region) : M.eval c (withRegions s r w) = M.eval c s
  callAddrs_with (s : M.State) (r w : List Region) : M.callAddrs (withRegions s r w) = M.callAddrs s
  retAddrs_with (s : M.State) (r w : List Region) : M.retAddrs (withRegions s r w) = M.retAddrs s
  /-- An indirect call calls the same address, and each function is at the
  same address, with other permissions. -/
  icall_with (i : M.Instr) (s : M.State) (r w : List Region) :
    M.icall i (withRegions s r w) = M.icall i s := by intros; rfl
  fnAddr_with (s : M.State) (r w : List Region) (n : String) :
    M.fnAddr (withRegions s r w) n = M.fnAddr s n := by intros; rfl
  call_widen {s s' : M.State} : M.call s = some s' →
    rd s' = rd s ∧ wr s' = wr s ∧ ∀ r w, M.call (withRegions s r w) = some (withRegions s' r w)
  ret_widen {s₁ s₂ s' : M.State} : M.ret s₁ s₂ = some s' →
    rd s' = rd s₂ ∧ wr s' = wr s₂ ∧
      ∀ r w, M.ret (withRegions s₁ r w) (withRegions s₂ r w) = some (withRegions s' r w)
  /-- A frame's push adds its region at the head of `wr`. -/
  push_widen {i : M.Instr} {s s₁ : M.State} : M.push i s = some s₁ →
    ∃ f, rd s₁ = rd s ∧ wr s₁ = f :: wr s ∧
      ∀ r w, M.push i (withRegions s r w) = some (withRegions s₁ r (f :: w))
  /-- A frame's pop removes the region at the head of `wr`. -/
  pop_widen {j : M.Instr} {s₁ s₂ s' : M.State} : M.pop j s₁ s₂ = some s' →
    wr s₂ = wr s₁ ∧ rd s' = rd s₂ ∧ wr s' = (wr s₂).tail ∧
      ∀ r w, w.head? = (wr s₁).head? →
        M.pop j (withRegions s₁ r w) (withRegions s₂ r w) = some (withRegions s' r w.tail)

theorem execBlock_keep {α : Type} (get : M.State → α) {ok : M.Instr → Prop}
    (hexec : ∀ {i s s'}, ok i → M.exec i s = some s' → get s' = get s)
    {is : List M.Instr} (hc : ∀ i ∈ is, ok i) {s s' : M.State} {t : List Leak}
    (h : execBlock M is s = some (s', t)) : get s' = get s := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    rw [h.1]
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [ih (fun i hi => hc i (List.mem_cons_of_mem _ hi)) h2, hexec (hc i (List.mem_cons_self ..)) he]

/-- A value `get` that every instruction satisfying `ok` keeps, that every
frame whose pop satisfies `ok` restores, and (unless the code makes no call)
that every call restores, is the same after code whose instructions all
satisfy `ok`. -/
theorem Exec.keep {α : Type} (get : M.State → α) {ok : M.Instr → Prop}
    (hexec : ∀ {i s s'}, ok i → M.exec i s = some s' → get s' = get s)
    (hframe : ∀ {i j s s₁ s₂ s'}, ok j → M.push i s = some s₁ → M.pop j s₁ s₂ = some s' →
      get s₂ = get s₁ → get s' = get s)
    {c : Prog M} (hc : ∀ i ∈ instrs c, ok i)
    (hcall : c.noCalls = true ∨ ∀ s s₁ s₂ s', M.call s = some s₁ → M.ret s₁ s₂ = some s' →
      get s₂ = get s₁ → get s' = get s)
    {s s' : M.State} {t : List Leak} (h : Exec M c s t s') : get s' = get s := by
  induction h with
  | block h => exact execBlock_keep get hexec hc h
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true] at hcall
    rw [ih₂ (fun i hi => hc i (List.mem_append_right _ hi)) (hcall.imp And.right id),
      ih₁ (fun i hi => hc i (List.mem_append_left _ hi)) (hcall.imp And.left id)]
  | iteT _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hcall
    exact ih (fun i hi => hc i (List.mem_append_left _ hi)) (hcall.imp And.left id)
  | iteF _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hcall
    exact ih (fun i hi => hc i (List.mem_append_right _ hi)) (hcall.imp And.right id)
  | loopExit _ _ ih => exact ih hc hcall
  | loopNext _ _ _ ih₁ ih₂ => rw [ih₂ hc hcall, ih₁ hc hcall]
  | call hc₁ _ hr ih =>
    rcases hcall with hn | hk
    · simp [Code.noCalls] at hn
    · exact hk _ _ _ _ hc₁ hr (ih hc (.inr hk))
  | frame hp _ hq ih =>
    rcases hcall with hn | hk
    · simp [Code.noCalls] at hn
    · exact hframe (hc _ (by simp [instrs])) hp hq (ih (fun i hi => hc i (by simp [instrs, hi])) (.inr hk))
  | icall _ hc₁ _ hr ih =>
    rcases hcall with hn | hk
    · simp [Code.noCalls] at hn
    · exact hk _ _ _ _ hc₁ hr
        (ih (fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_left _ hi))) (.inr hk))
  | icallNext _ _ _ ih =>
    rcases hcall with hn | hk
    · simp [Code.noCalls] at hn
    · exact ih (fun i hi => hc i (List.mem_cons_of_mem _ (List.mem_append_right _ hi))) (.inr hk)

namespace RegionModel

variable (R : RegionModel M)

theorem execBlock_regions {is : List M.Instr} {s s' : M.State} {t : List Leak}
    (h : execBlock M is s = some (s', t)) :
    R.rd s' = R.rd s ∧ R.wr s' = R.wr s ∧ Frame (R.wr s) (R.mem s) (R.mem s') := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, Frame.refl _ _⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw, hf⟩ := R.exec_regions he
    obtain ⟨hr', hw', hf'⟩ := ih h2
    exact ⟨hr'.trans hr, hw'.trans hw, hf.trans (hw ▸ hf')⟩

/-- The permissions never change. -/
theorem rdwr {c : Prog M} {s s' : M.State} {t : List Leak} (h : Exec M c s t s') :
    R.rd s' = R.rd s ∧ R.wr s' = R.wr s := by
  refine Prod.mk.inj (Exec.keep (fun s => (R.rd s, R.wr s)) (ok := fun _ => True)
    (fun _ he => ?_) (fun _ hp hq e => ?_) (fun _ _ => trivial) (.inr fun _ _ _ _ hc hr e => ?_) h)
  · obtain ⟨r, w, -⟩ := R.exec_regions he; rw [r, w]
  · obtain ⟨f, r₁, w₁, -⟩ := R.push_widen hp
    obtain ⟨w₂, r₂, w₃, -⟩ := R.pop_widen hq
    simp only [Prod.mk.injEq] at e ⊢
    rw [r₂, w₃, e.1, w₂, r₁, w₁]; exact ⟨rfl, rfl⟩
  · obtain ⟨r₁, w₁, -⟩ := R.call_widen hc
    obtain ⟨r₂, w₂, -⟩ := R.ret_widen hr
    simp only [Prod.mk.injEq] at e ⊢
    rw [r₂, w₂, e.1, e.2, r₁, w₁]; exact ⟨rfl, rfl⟩

/-- Calls and returns change no memory. -/
def CallsKeepMem : Prop :=
  ∀ s s₁ s₂ s', M.call s = some s₁ → M.ret s₁ s₂ = some s' → R.mem s₁ = R.mem s ∧ R.mem s' = R.mem s₂

/-- Code without frames, and without calls unless calls change no memory,
changes memory only within the regions it may write (a frame's push stores
below the stack pointer, and so may a call). -/
theorem regions {c : Prog M} {s s' : M.State} {t : List Leak} (h : Exec M c s t s')
    (hn : c.noFrames = true) (hcall : c.noCalls = true ∨ R.CallsKeepMem) :
    R.rd s' = R.rd s ∧ R.wr s' = R.wr s ∧ Frame (R.wr s) (R.mem s) (R.mem s') := by
  induction h with
  | block h => exact R.execBlock_regions h
  | seq _ _ ih₁ ih₂ =>
    simp only [Code.noFrames, Code.noCalls, Bool.and_eq_true] at hn hcall
    obtain ⟨r₁, w₁, f₁⟩ := ih₁ hn.1 (hcall.imp And.left id)
    obtain ⟨r₂, w₂, f₂⟩ := ih₂ hn.2 (hcall.imp And.right id)
    exact ⟨r₂.trans r₁, w₂.trans w₁, f₁.trans (w₁ ▸ f₂)⟩
  | iteT _ _ ih =>
    simp only [Code.noFrames, Code.noCalls, Bool.and_eq_true] at hn hcall
    exact ih hn.1 (hcall.imp And.left id)
  | iteF _ _ ih =>
    simp only [Code.noFrames, Code.noCalls, Bool.and_eq_true] at hn hcall
    exact ih hn.2 (hcall.imp And.right id)
  | loopExit _ _ ih => exact ih hn hcall
  | loopNext _ _ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁, f₁⟩ := ih₁ hn hcall; obtain ⟨r₂, w₂, f₂⟩ := ih₂ hn hcall
    exact ⟨r₂.trans r₁, w₂.trans w₁, f₁.trans (w₁ ▸ f₂)⟩
  | call hc _ hr ih =>
    rcases hcall with hcall | hk
    · simp [Code.noCalls] at hcall
    obtain ⟨r₁, w₁, -⟩ := R.call_widen hc
    obtain ⟨r₂, w₂, -⟩ := R.ret_widen hr
    obtain ⟨m₁, m₂⟩ := hk _ _ _ _ hc hr
    obtain ⟨r, w, f⟩ := ih hn (.inr hk)
    refine ⟨r₂.trans (r.trans r₁), w₂.trans (w.trans w₁), ?_⟩
    rw [m₂, ← m₁, ← w₁]; exact f
  | frame => simp [Code.noFrames] at hn
  | icall _ hc _ hr ih =>
    rcases hcall with hcall | hk
    · simp [Code.noCalls] at hcall
    simp only [Code.noFrames, Bool.and_eq_true] at hn
    obtain ⟨r₁, w₁, -⟩ := R.call_widen hc
    obtain ⟨r₂, w₂, -⟩ := R.ret_widen hr
    obtain ⟨m₁, m₂⟩ := hk _ _ _ _ hc hr
    obtain ⟨r, w, f⟩ := ih hn.1 (.inr hk)
    refine ⟨r₂.trans (r.trans r₁), w₂.trans (w.trans w₁), ?_⟩
    rw [m₂, ← m₁, ← w₁]; exact f
  | icallNext _ _ _ ih =>
    rcases hcall with hcall | hk
    · simp [Code.noCalls] at hcall
    exact ih (by simp only [Code.noFrames, Bool.and_eq_true] at hn ⊢; exact hn.2) (.inr hk)

theorem execBlock_widen {is : List M.Instr} {s s' : M.State} {t : List Leak} {r w : List Region}
    (hc : Covers (R.rd s ++ R.wr s) (r ++ w)) (hw : Covers (R.wr s) w)
    (h : execBlock M is s = some (s', t)) :
    execBlock M is (R.withRegions s r w) = some (R.withRegions s' r w, t) := by
  induction is generalizing s t with
  | nil =>
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | cons i is ih =>
    simp only [execBlock] at h
    split at h <;> [cases h; skip]
    rename_i s₁ he
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨⟨s₂, t₂⟩, h2, heq⟩ := h
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    obtain ⟨hr, hw', -⟩ := R.exec_regions he
    have := ih (s := s₁) (by rwa [hr, hw']) (by rwa [hw']) h2
    simp only [execBlock]
    rw [R.exec_widen hc hw he]
    simp only [this, Option.map_some, R.addrs_with]

/-- Running from a state that permits more memory. -/
theorem widen {c : Prog M} {s s' : M.State} {t : List Leak} {r w : List Region}
    (h : Exec M c s t s') (hc : Covers (R.rd s ++ R.wr s) (r ++ w)) (hw : Covers (R.wr s) w) :
    Exec M c (R.withRegions s r w) t (R.withRegions s' r w) := by
  induction h generalizing r w with
  | block h => exact .block (R.execBlock_widen hc hw h)
  | seq h₁ _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁⟩ := R.rdwr h₁
    exact .seq (ih₁ hc hw) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | iteT he _ ih => exact .iteT ((R.eval_with _ _ _ _).trans he) (ih hc hw)
  | iteF he _ ih => exact .iteF ((R.eval_with _ _ _ _).trans he) (ih hc hw)
  | loopExit _ he ih => exact .loopExit (ih hc hw) ((R.eval_with _ _ _ _).trans he)
  | loopNext h₁ he _ ih₁ ih₂ =>
    obtain ⟨r₁, w₁⟩ := R.rdwr h₁
    exact .loopNext (ih₁ hc hw) ((R.eval_with _ _ _ _).trans he) (ih₂ (by rwa [r₁, w₁]) (by rwa [w₁]))
  | @call n _ _ _ _ _ _ hc₁ _ hr ih =>
    obtain ⟨r₁, w₁, hc'⟩ := R.call_widen hc₁
    obtain ⟨-, -, hr'⟩ := R.ret_widen hr
    have := Exec.call (name := n) (hc' r w) (ih (by rwa [r₁, w₁]) (by rwa [w₁])) (hr' r w)
    rwa [R.callAddrs_with, R.retAddrs_with] at this
  | frame hp _ hq ih =>
    obtain ⟨f, r₁, w₁, hp'⟩ := R.push_widen hp
    obtain ⟨-, -, -, hq'⟩ := R.pop_widen hq
    have hb := ih (r := r) (w := f :: w) (by rw [r₁, w₁]; exact Covers.push f hc)
      (by rw [w₁]; exact Covers.push (xs := []) (xs' := []) f hw)
    have := Exec.frame (hp' r w) hb (hq' r (f :: w) (by rw [w₁]; rfl))
    rwa [R.addrs_with, R.addrs_with, List.tail_cons] at this
  | @icall i n _ nx s₀ _ _ _ _ hi hc₁ _ hr ih =>
    obtain ⟨r₁, w₁, hc'⟩ := R.call_widen hc₁
    obtain ⟨-, -, hr'⟩ := R.ret_widen hr
    have hi' : M.icall i (R.withRegions s₀ r w) = some (M.fnAddr (R.withRegions s₀ r w) n) := by
      rw [R.icall_with, R.fnAddr_with]; exact hi
    have := Exec.icall (next := nx) hi' (hc' r w) (ih (by rwa [r₁, w₁]) (by rwa [w₁])) (hr' r w)
    rwa [R.addrs_with, R.fnAddr_with, R.callAddrs_with, R.retAddrs_with] at this
  | icallNext hi hne _ ih =>
    exact .icallNext (by rw [R.icall_with]; exact hi) (by rw [R.fnAddr_with]; exact hne) (ih hc hw)

/-- Inlining: a run from `s` with its permissions narrowed to `r` and `w`,
which those of `s` cover, is a run from `s`, to the same state with the
permissions of `s`. -/
theorem inline {c : Prog M} {s s₁ : M.State} {r w : List Region} {t : List Leak}
    (he : Exec M c (R.withRegions s r w) t s₁)
    (hc : Covers (r ++ w) (R.rd s ++ R.wr s)) (hw : Covers w (R.wr s)) :
    Exec M c s t (R.withRegions s₁ (R.rd s) (R.wr s)) ∧
      R.withRegions (R.withRegions s₁ (R.rd s) (R.wr s)) r w = s₁ := by
  obtain ⟨hr, hwr⟩ := R.rdwr he
  rw [R.rd_with] at hr
  rw [R.wr_with] at hwr
  have he' := R.widen he (r := R.rd s) (w := R.wr s) (by rwa [R.rd_with, R.wr_with])
    (by rwa [R.wr_with])
  rw [R.with_with, R.with_self] at he'
  exact ⟨he', by rw [R.with_with, ← hr, ← hwr, R.with_self]⟩

/-- The run of `inline` changes memory only within `w`. -/
theorem inline_frame {c : Prog M} {s s₁ : M.State} {r w : List Region} {t : List Leak}
    (he : Exec M c (R.withRegions s r w) t s₁) (hn : c.noFrames = true)
    (hcall : c.noCalls = true ∨ R.CallsKeepMem) :
    Frame w (R.mem s) (R.mem (R.withRegions s₁ (R.rd s) (R.wr s))) := by
  have hf := (R.regions he hn hcall).2.2
  rwa [R.wr_with, R.mem_with, ← R.mem_with s₁ (R.rd s) (R.wr s)] at hf

/-- Running code proven on narrower permissions: if, from `s` with its
permissions narrowed to `r` and `w`, the code terminates in a state
satisfying `P`, then from `s` it terminates in a state that has the
permissions of `s`, differs from it in memory only within `w`, and, narrowed
likewise, satisfies `P`. -/
theorem wp_narrow {c : Prog M} {s : M.State} {r w : List Region} {P : M.State → Prop}
    (h : WP M c (R.withRegions s r w) P)
    (hc : Covers (r ++ w) (R.rd s ++ R.wr s)) (hw : Covers w (R.wr s))
    (hn : c.noFrames = true) (hcall : c.noCalls = true ∨ R.CallsKeepMem) {Q : M.State → Prop}
    (hQ : ∀ t s', Exec M c s t s' → R.rd s' = R.rd s → R.wr s' = R.wr s →
      Frame w (R.mem s) (R.mem s') → P (R.withRegions s' r w) → Q s') : WP M c s Q := by
  obtain ⟨t, s₁, he, hp⟩ := h
  obtain ⟨he', e⟩ := R.inline he hc hw
  exact ⟨t, _, he', hQ _ _ he' (R.rd_with ..) (R.wr_with ..) (R.inline_frame he hn hcall) (by rwa [e])⟩

/-- The trace of a run of verified code, with more permissions than its
contract gives it, is that of the run its contract describes. -/
theorem trace_narrow {c : Prog M} {Pre : M.State → Prop} {Post : M.State → M.State → Prop}
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s' ∧ Post s s')
    {s : M.State} {r w : List Region} (hpre : Pre (R.withRegions s r w))
    (hc : Covers (r ++ w) (R.rd s ++ R.wr s)) (hw : Covers w (R.wr s)) {t : List Leak} {s' : M.State}
    (he : Exec M c s t s') :
    ∃ s'', Exec M c (R.withRegions s r w) t s'' := by
  obtain ⟨t', s'', he', -⟩ := hv _ hpre
  obtain ⟨rfl, -⟩ := Exec.det he (R.inline he' hc hw).1
  exact ⟨_, he'⟩

end RegionModel

/-- Moving a proof to a contract `k'` whose states permit more: `k` may
read `rd s` and write `wr s`, which the regions of `k'` cover. The code runs
as it does from the narrowed state, with the same trace and result. -/
theorem RegionModel.verified_narrowTo {T : Target} (R : RegionModel T.isa)
    (habi : ∀ s s₁ r w, T.abiPreserved (R.withRegions s r w) s₁ →
      T.abiPreserved s (R.withRegions s₁ (R.rd s) (R.wr s)))
    {c : Prog T.isa} {k k' : Contract T.isa} (h : Verified T c k)
    (rd wr : T.isa.State → List Region)
    (hpre : ∀ s, k'.pre s → k.pre (R.withRegions s (rd s) (wr s)))
    (hc : ∀ s, k'.pre s → Covers (rd s ++ wr s) (R.rd s ++ R.wr s))
    (hw : ∀ s, k'.pre s → Covers (wr s) (R.wr s))
    (hpost : ∀ s s', k'.pre s →
      k.post (R.withRegions s (rd s) (wr s)) (R.withRegions s' (rd s) (wr s)) → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ →
      k.pub (R.withRegions s₁ (rd s₁) (wr s₁)) (R.withRegions s₂ (rd s₂) (wr s₂)))
    (hsat : ∃ s, k'.pre s) : Verified T c k' := by
  refine h.of_narrow (fun s => R.withRegions s (rd s) (wr s)) (fun s s₁ => R.withRegions s₁ (R.rd s) (R.wr s))
    hpre (fun s t s₁ hs he => (R.inline he (hc s hs) (hw s hs)).1)
    (fun s t s₁ hs he ha hq => ⟨habi _ _ _ _ ha, hpost s _ hs ?_⟩) hpub hsat
  rwa [(R.inline he (hc s hs) (hw s hs)).2]

/-- `verified_narrowTo`, narrowing only the writable regions, to regions
that the state's extend (same bases, at least as long). -/
theorem RegionModel.verified_widen {T : Target} (R : RegionModel T.isa)
    (habi : ∀ s s₁ r w, T.abiPreserved (R.withRegions s r w) s₁ →
      T.abiPreserved s (R.withRegions s₁ (R.rd s) (R.wr s)))
    {c : Prog T.isa} {k k' : Contract T.isa} (h : Verified T c k)
    (wr : T.isa.State → List Region)
    (hpre : ∀ s, k'.pre s → k.pre (R.withRegions s (R.rd s) (wr s)))
    (hwr : ∀ s, k'.pre s → List.Forall₂ Region.Prefix (wr s) (R.wr s))
    (hpost : ∀ s s', k'.pre s →
      k.post (R.withRegions s (R.rd s) (wr s)) (R.withRegions s' (R.rd s) (wr s)) → k'.post s s')
    (hpub : ∀ s₁ s₂, k'.pre s₁ → k'.pre s₂ → k'.pub s₁ s₂ →
      k.pub (R.withRegions s₁ (R.rd s₁) (wr s₁)) (R.withRegions s₂ (R.rd s₂) (wr s₂)))
    (hsat : ∃ s, k'.pre s) : Verified T c k' :=
  have hw : ∀ s, k'.pre s → Covers (wr s) (R.wr s) := fun s hs _ _ => InRegions.of_prefix (hwr s hs)
  R.verified_narrowTo habi h R.rd wr hpre (fun s hs => (Covers.refl _).append (hw s hs)) hw
    hpost hpub hsat

end VG
