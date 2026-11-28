module

public import VerifiedGarbage.Proof.Framework.Semantics
public import VerifiedGarbage.Proof.Framework.KernelList
public import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.Basic
public import Lean.Meta.Eval
public meta import Lean.Meta.Eval
public import VerifiedGarbage.Proof.Framework.Lit

/-!
# Constant time by taint tracking

A `Taint M` is a sound, executable information-flow analysis for the ISA `M`:
an abstract domain `T` of "which parts of the state are public", a relation
`Agree τ s₁ s₂` ("the two states agree on everything `τ` says is public"),
and a transfer function for instructions that fails (`none`) whenever an
instruction would leak (through the addresses it accesses) something that is
not public. `Taint.check` lifts it to structured code; `Taint.constantTime`
turns a successful check into `ConstantTime`, which can then be established
for a whole program by evaluation (`taint_decide`).

The kernel is a slow evaluator, so `check` does not search for loop
invariants itself: it is given a `Hint` with every loop's invariant, and the
analysis at every `seq` and at bounded intervals within a block, and only
checks that they are sound (`le`). `Taint.hint` computes such a hint by
running the search in compiled code, and `taint_decide` has the kernel check
the analysis with it. A wrong hint can only make the check fail.
-/

@[expose] public section

namespace VG

structure Taint (M : ISA) where
  T : Type
  Agree : T → M.State → M.State → Prop
  step : T → M.Instr → Option T
  step_sound : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → step τ i = some τ' →
    M.exec i s₁ = some s₁' → M.exec i s₂ = some s₂' →
    M.addrs i s₁ = M.addrs i s₂ ∧ Agree τ' s₁' s₂'
  /-- The condition only depends on public data. -/
  condPub : T → M.Cond → Bool
  cond_sound : ∀ {τ c s₁ s₂}, Agree τ s₁ s₂ → condPub τ c = true → M.eval c s₁ = M.eval c s₂
  /-- Something public in both. -/
  meet : T → T → T
  meet_left : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₁ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  meet_right : ∀ {τ₁ τ₂ s₁ s₂}, Agree τ₂ s₁ s₂ → Agree (meet τ₁ τ₂) s₁ s₂
  /-- `le τ σ`: everything public in `τ` is public in `σ`. -/
  le : T → T → Bool
  le_sound : ∀ {τ σ s₁ s₂}, le τ σ = true → Agree σ s₁ s₂ → Agree τ s₁ s₂
  /-- The analysis of a call instruction (`none` if it would leak). -/
  call : T → Option T
  call_sound : ∀ {τ τ' s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → call τ = some τ' →
    M.call s₁ = some s₁' → M.call s₂ = some s₂' → M.callAddrs s₁ = M.callAddrs s₂ ∧ Agree τ' s₁' s₂'
  /-- The analysis of a called function's return instruction. -/
  ret : T → Option T
  ret_sound : ∀ {τ τ' a₁ a₂ b₁ b₂ c₁ c₂}, Agree τ b₁ b₂ → ret τ = some τ' →
    M.ret a₁ b₁ = some c₁ → M.ret a₂ b₂ = some c₂ → M.retAddrs b₁ = M.retAddrs b₂ ∧ Agree τ' c₁ c₂
  /-- The analysis of a frame's push (`none` if it would leak). -/
  push : T → M.Instr → Option T
  push_sound : ∀ {τ τ' i s₁ s₂ s₁' s₂'}, Agree τ s₁ s₂ → push τ i = some τ' →
    M.push i s₁ = some s₁' → M.push i s₂ = some s₂' → M.addrs i s₁ = M.addrs i s₂ ∧ Agree τ' s₁' s₂'
  /-- The analysis of a frame's pop (`none` if it would leak). -/
  pop : T → M.Instr → Option T
  pop_sound : ∀ {τ τ' j a₁ a₂ b₁ b₂ c₁ c₂}, Agree τ b₁ b₂ → pop τ j = some τ' →
    M.pop j a₁ b₁ = some c₁ → M.pop j a₂ b₂ = some c₂ → M.addrs j b₁ = M.addrs j b₂ ∧ Agree τ' c₁ c₂

namespace Taint

/-- `filter p l` for a domain's step, but `l` itself when `p` keeps every
element. A step that rebuilds a list it does not change (e.g. the public
slots, on a secret store that overlaps none) makes the kernel build and
then walk a new copy at every later access. -/
def filterKeep {α : Type} (p : α → Bool) (l : List α) : List α :=
  bif KList.all l p then l else KList.filter p l

theorem filterKeep_eq {α : Type} (p : α → Bool) (l : List α) : filterKeep p l = l.filter p := by
  unfold filterKeep
  cases h : KList.all l p
  · exact KList.filter_eq p l
  · rw [KList.all_eq, List.all_eq_true] at h
    exact (List.filter_eq_self.mpr h).symm

/-- Precomputed results of the analysis, for `check`: each block's interval and
intermediate taints, the taint between parts of a `seq`, and loop invariants.
The checker validates every interval; choosing its size changes no soundness
requirement. -/
inductive Hint (T : Type) where
  | block (mids : List T) (chunkSize : Nat := 256)
  | seq (mid : T) (h₁ h₂ : Hint T)
  | ite (h₁ h₂ : Hint T)
  | loop (inv : T) (h : Hint T)
  | call (h : Hint T)
  | frame (h : Hint T)
  deriving Lean.ToExpr

/-- `toExpr` of a hint, compiled once here: `taint_decide` evaluates a call of
it, where `toExpr` of the hint's type would otherwise be specialized to the
analysis, and compiled again, at every check. -/
@[nospecialize] def Hint.toExprNS {T : Type} [Lean.ToExpr T] (h : Hint T) : Lean.Expr :=
  Lean.toExpr h

variable {M : ISA} (A : Taint M)

/-- `checkBlock`, for compiled code. -/
def checkBlockC : A.T → List M.Instr → Option A.T
  | τ, [] => some τ
  | τ, i :: is => (A.step τ i).bind (checkBlockC · is)

/-- The analysis of a block. The kernel evaluates this for every instruction
checked, so it is a `List.rec`, which the kernel evaluates faster than
structural recursion (compiled to `brecOn`). Lean's compiler does not compile
`List.rec`: compiled code (`hint`) runs `checkBlockC`. -/
@[implemented_by checkBlockC] def checkBlock (τ : A.T) (is : List M.Instr) : Option A.T :=
  List.rec (motive := fun _ => A.T → Option A.T) some (fun i _ ih τ => (A.step τ i).bind ih) is τ

/-- The fallback interval, also used by summary and batch checks. Every hint
requires the kernel to evaluate the analysis and compare it with the hint.
Larger intervals reduce those checks, but can exhaust the recursion depth in
some blocks, so `taintDecide` retries this interval if a larger one fails. -/
def chunk : Nat := 256

/-- The analysis of a block, weakened to `mids` after every `chunkSize` instructions. -/
def checkChunks (chunkSize : Nat) : A.T → List M.Instr → List A.T → Option A.T
  | τ, is, [] => A.checkBlock τ is
  | τ, is, m :: ms => (A.checkBlock τ (KList.take chunkSize is)).bind fun τ' =>
    if A.le m τ' then checkChunks chunkSize m (KList.drop chunkSize is) ms else none

/-- The analysis of structured code, given a hint. -/
def check : A.T → Prog M → Hint A.T → Option A.T
  | τ, .block is, .block ms chunkSize => checkChunks A chunkSize τ is ms
  | τ, .seq c₁ c₂, .seq mid h₁ h₂ =>
    (check τ c₁ h₁).bind fun τ' => if A.le mid τ' then check mid c₂ h₂ else none
  | τ, .ite c t e, .ite h₁ h₂ =>
    if A.condPub τ c then
      (check τ t h₁).bind fun τ₁ => (check τ e h₂).map fun τ₂ => A.meet τ₁ τ₂
    else none
  | τ, .loop body c, .loop σ h =>
    if A.le σ τ then
      (check σ body h).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
    else none
  | τ, .call _ body, .call h => (A.call τ).bind fun τ₁ => (check τ₁ body h).bind A.ret
  | τ, .frame i body j, .frame h =>
    (A.push τ i).bind fun τ₁ => (check τ₁ body h).bind fun τ₂ => A.pop τ₂ j
  | _, _, _ => none

/-! ## Computing hints

Nothing here needs to be sound: `check` checks the hint. -/

/-- The hints for a block: the analysis after every `chunkSize` instructions but the last. -/
def chunkHints (chunkSize : Nat) : A.T → List M.Instr → Nat → List A.T
  | _, _, 0 => []
  | τ, is, n + 1 =>
    if is.length ≤ chunkSize then [] else
    match A.checkBlock τ (is.take chunkSize) with
    | some τ' => τ' :: chunkHints chunkSize τ' (is.drop chunkSize) n
    | none => []

/-- How many times the search for a loop invariant weakens its candidate. -/
def loopFuel : Nat := 4

/-- The analysis of structured code, with its hint. A loop's invariant is
found by starting from the taint on entry and, while the body does not keep
public everything the candidate says is public (or leaves the loop condition
secret), weakening the candidate to what is public both before and after the
body. -/
def hint (chunkSize : Nat) : A.T → Prog M → Option (A.T × Hint A.T)
  | τ, .block is => (A.checkBlock τ is).map fun τ' => (τ', .block (chunkHints A chunkSize τ is is.length) chunkSize)
  | τ, .seq c₁ c₂ =>
    (hint chunkSize τ c₁).bind fun (τ₁, h₁) => (hint chunkSize τ₁ c₂).map fun (τ₂, h₂) => (τ₂, .seq τ₁ h₁ h₂)
  | τ, .ite _ t e =>
    (hint chunkSize τ t).bind fun (τ₁, h₁) => (hint chunkSize τ e).map fun (τ₂, h₂) => (A.meet τ₁ τ₂, .ite h₁ h₂)
  | τ, .loop body c => go c (hint chunkSize · body) loopFuel τ
  | τ, .call _ body =>
    (A.call τ).bind fun τ₁ => (hint chunkSize τ₁ body).bind fun (τ₂, h) => (A.ret τ₂).map (·, .call h)
  | τ, .frame i body j =>
    (A.push τ i).bind fun τ₁ => (hint chunkSize τ₁ body).bind fun (τ₂, h) => (A.pop τ₂ j).map (·, .frame h)
  -- `check` does not handle indirect calls.
  | _, .icall .. => none
where
  go (c : M.Cond) (body : A.T → Option (A.T × Hint A.T)) :
      Nat → A.T → Option (A.T × Hint A.T)
    | 0, _ => none
    | n + 1, σ => (body σ).bind fun (σ', h) =>
      if A.le σ σ' && A.condPub σ' c then some (σ', .loop σ h) else go c body n (A.meet σ σ')

/-- The hint for `c` from `τ` (any hint, if the analysis fails). -/
@[nospecialize] def hintOfSize (chunkSize : Nat) (τ : A.T) (c : Prog M) : Hint A.T :=
  ((hint A chunkSize τ c).map (·.2)).getD (.block [] chunkSize)

/-- A hint using the fallback interval, for summary and batch callers. -/
def hintOf (τ : A.T) (c : Prog M) : Hint A.T := hintOfSize A chunk τ c

/-! ## Soundness -/

variable {A}

theorem checkBlock_sound {is : List M.Instr} {τ τ' : A.T} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ : List Leak} (h : A.checkBlock τ is = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : execBlock M is s₁ = some (s₁', t₁)) (e₂ : execBlock M is s₂ = some (s₂', t₂)) :
    t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction is generalizing τ s₁ s₂ t₁ t₂ with
  | nil =>
    simp only [checkBlock, Option.some.injEq] at h
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, rfl⟩ := e₁; obtain ⟨rfl, rfl⟩ := e₂; subst h; exact ⟨rfl, ha⟩
  | cons i is ih =>
    simp only [checkBlock, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, hs, hr⟩ := h
    simp only [execBlock] at e₁ e₂
    split at e₁ <;> rename_i h₁ <;> [cases e₁; skip]
    split at e₂ <;> rename_i h₂ <;> [cases e₂; skip]
    rename_i s₁₁ _ s₂₁
    simp only [Option.map_eq_some_iff, Prod.exists] at e₁ e₂
    obtain ⟨_, u₁, e₁, he₁⟩ := e₁
    obtain ⟨_, u₂, e₂, he₂⟩ := e₂
    simp only [Prod.mk.injEq] at he₁ he₂
    obtain ⟨rfl, rfl⟩ := he₁; obtain ⟨rfl, rfl⟩ := he₂
    obtain ⟨hadd, ha₁⟩ := A.step_sound ha hs h₁ h₂
    obtain ⟨ht, ha'⟩ := ih hr ha₁ e₁ e₂
    exact ⟨by rw [hadd, ht], ha'⟩

theorem execBlock_split {is : List M.Instr} {s s' : M.State} {t : List Leak} (n : Nat)
    (e : execBlock M is s = some (s', t)) :
    ∃ s₁ u₁ u₂, execBlock M (is.take n) s = some (s₁, u₁) ∧
      execBlock M (is.drop n) s₁ = some (s', u₂) ∧ t = u₁ ++ u₂ := by
  rw [← List.take_append_drop n is, execBlock_append] at e
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at e
  obtain ⟨⟨s₁, u₁⟩, e₁, ⟨s₂, u₂⟩, e₂, rfl, rfl⟩ := e
  exact ⟨s₁, u₁, u₂, e₁, e₂, rfl⟩

theorem checkChunks_sound {chunkSize : Nat} {ms : List A.T} {is : List M.Instr} {τ τ' : A.T}
    {s₁ s₂ s₁' s₂' : M.State} {t₁ t₂ : List Leak} (h : A.checkChunks chunkSize τ is ms = some τ')
    (ha : A.Agree τ s₁ s₂) (e₁ : execBlock M is s₁ = some (s₁', t₁))
    (e₂ : execBlock M is s₂ = some (s₂', t₂)) : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  induction ms generalizing τ is s₁ s₂ t₁ t₂ with
  | nil => exact checkBlock_sound h ha e₁ e₂
  | cons m ms ih =>
    simp only [checkChunks, KList.take_eq, KList.drop_eq, Option.bind_eq_some_iff] at h
    obtain ⟨τ₁, h₁, h₂⟩ := h
    split at h₂ <;> [rename_i hle; cases h₂]
    obtain ⟨_, _, _, a₁, b₁, rfl⟩ := execBlock_split chunkSize e₁
    obtain ⟨_, _, _, a₂, b₂, rfl⟩ := execBlock_split chunkSize e₂
    obtain ⟨rfl, ha₁⟩ := checkBlock_sound h₁ ha a₁ a₂
    obtain ⟨rfl, ha₂⟩ := ih h₂ (A.le_sound hle ha₁) b₁ b₂
    exact ⟨rfl, ha₂⟩

theorem check_sound {c : Prog M} {τ τ' : A.T} {hc : Hint A.T} {s₁ s₂ s₁' s₂' : M.State}
    {t₁ t₂ : List Leak} (h : A.check τ c hc = some τ') (ha : A.Agree τ s₁ s₂)
    (e₁ : Exec M c s₁ t₁ s₁') (e₂ : Exec M c s₂ t₂ s₂') : t₁ = t₂ ∧ A.Agree τ' s₁' s₂' := by
  -- `check` reduces by evaluation on each pair of constructors: no equation lemmas (whose
  -- generation, for its catch-all case, costs seconds) are needed.
  induction e₁ generalizing τ τ' hc s₂ t₂ s₂' with
  | block h₁ =>
    cases hc with
    | block ms chunkSize =>
      have h : A.checkChunks chunkSize τ _ ms = some τ' := h
      cases e₂ with
      | block h₂ => exact checkChunks_sound h ha h₁ h₂
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @seq c₁ c₂ _ _ _ _ _ _ _ ih₁ ih₂ =>
    cases hc with
    | seq mid g₁ g₂ =>
      have h : ((A.check τ c₁ g₁).bind fun τ' => if A.le mid τ' then A.check mid c₂ g₂ else none) =
        some τ' := h
      cases e₂ with
      | seq a b =>
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨τ₁, h₁, h₂⟩ := h
        split at h₂ <;> [rename_i hle; cases h₂]
        obtain ⟨rfl, ha₁⟩ := ih₁ h₁ ha a
        obtain ⟨rfl, ha₂⟩ := ih₂ h₂ (A.le_sound hle ha₁) b
        exact ⟨rfl, ha₂⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @iteT cnd t e _ _ _ hc' _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ t g₁).bind fun τ₁ => (A.check τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, _, rfl⟩ := h
      cases e₂ with
      | iteT _ b => obtain ⟨rfl, hq⟩ := ih h₁ ha b; exact ⟨rfl, A.meet_left hq⟩
      | iteF hc'' _ => rw [← A.cond_sound ha hp, hc'] at hc''; cases hc''
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @iteF cnd t e _ _ _ hc' _ ih =>
    cases hc with
    | ite g₁ g₂ =>
      have h : (if A.condPub τ cnd then
          (A.check τ t g₁).bind fun τ₁ => (A.check τ e g₂).map fun τ₂ => A.meet τ₁ τ₂
        else none) = some τ' := h
      split at h <;> [rename_i hp; cases h]
      simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨τ₁, _, τ₂, h₂, rfl⟩ := h
      cases e₂ with
      | iteT hc'' _ => rw [← A.cond_sound ha hp, hc'] at hc''; cases hc''
      | iteF _ b => obtain ⟨rfl, hq⟩ := ih h₂ ha b; exact ⟨rfl, A.meet_right hq⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopExit body c _ _ _ _ hc' ih =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a _ => obtain ⟨rfl, hq⟩ := ih hb' hσ a; exact ⟨rfl, hq⟩
      | loopNext a hc'' _ =>
        obtain ⟨_, ha₁⟩ := ih hb' hσ a
        rw [← A.cond_sound ha₁ hl.2, hc'] at hc''; cases hc''
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @loopNext body c _ _ _ _ _ _ hc' _ ih₁ ih₂ =>
    cases hc with
    | loop σ hb =>
      have h : (if A.le σ τ then
          (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
        else none) = some τ' := h
      split at h <;> [rename_i hστ; cases h]
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨σ', hb', h'⟩ := h
      split at h' <;> [rename_i hl; cases h']
      cases h'
      simp only [Bool.and_eq_true] at hl
      have hσ := A.le_sound hστ ha
      cases e₂ with
      | loopExit a hc'' =>
        obtain ⟨_, ha₁⟩ := ih₁ hb' hσ a
        rw [← A.cond_sound ha₁ hl.2, hc'] at hc''; cases hc''
      | loopNext a _ b =>
        obtain ⟨rfl, ha₁⟩ := ih₁ hb' hσ a
        have hloop : A.check τ' (.loop body c) (.loop σ hb) = some τ' := by
          show (if A.le σ τ' then
            (A.check σ body hb).bind fun σ' => if A.le σ σ' && A.condPub σ' c then some σ' else none
            else none) = some τ'
          simp only [hl.1, hl.2, hb', Option.bind_some, Bool.and_self, ite_true]
        obtain ⟨rfl, ha₂⟩ := ih₂ hloop ha₁ b
        exact ⟨rfl, ha₂⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @call _ body _ _ _ _ _ hc₁ _ hr ih =>
    cases hc with
    | call hb =>
      have h : ((A.call τ).bind fun τ₁ => (A.check τ₁ body hb).bind A.ret) = some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | call hc₂ b hr₂ =>
        obtain ⟨ha₁, ha₁'⟩ := A.call_sound ha h₁ hc₁ hc₂
        obtain ⟨rfl, ha₂⟩ := ih h₂ ha₁' b
        obtain ⟨ha₃, ha₃'⟩ := A.ret_sound ha₂ h₃ hr hr₂
        exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  | @frame i j body _ _ _ _ _ hp₁ _ hq ih =>
    cases hc with
    | frame hb =>
      have h : ((A.push τ i).bind fun τ₁ => (A.check τ₁ body hb).bind fun τ₂ => A.pop τ₂ j) =
        some τ' := h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨τ₁, h₁, τ₂, h₂, h₃⟩ := h
      cases e₂ with
      | frame hp₂ b hq₂ =>
        obtain ⟨ha₁, ha₁'⟩ := A.push_sound ha h₁ hp₁ hp₂
        obtain ⟨rfl, ha₂⟩ := ih h₂ ha₁' b
        obtain ⟨ha₃, ha₃'⟩ := A.pop_sound ha₂ h₃ hq hq₂
        exact ⟨by rw [ha₁, ha₃], ha₃'⟩
    | _ => have h' : (none : Option A.T) = some τ' := h; cases h'
  -- `check` fails on an indirect call.
  | icall | icallNext => cases hc <;> (have h' : (none : Option A.T) = some τ' := h; cases h')

/-- A successful check proves constant time, for any `Pub` under which the
initial states agree on what the initial taint says is public. -/
theorem constantTime {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (τ : A.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂) {hc : Hint A.T}
    (h : (A.check τ c hc).isSome = true) : ConstantTime M Pre Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂
  obtain ⟨τ', hc⟩ := Option.isSome_iff_exists.mp h
  exact (check_sound hc (hpub _ _ h₁ h₂ hp) e₁ e₂).1

/-- `constantTime` from a check that succeeds for some hint, the form
`taint_decide_sum` proves: for term-mode proofs, which do not name the hint. -/
theorem constantTime_of_exists {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    (τ : A.T) (hpub : ∀ s₁ s₂, Pre s₁ → Pre s₂ → Pub s₁ s₂ → A.Agree τ s₁ s₂)
    (h : ∃ hc : Hint A.T, (A.check τ c hc).isSome = true) : ConstantTime M Pre Pub c :=
  let ⟨_, h⟩ := h
  constantTime τ hpub h

/-- Apply `f` to every taint of a hint. -/
def Hint.map {T U : Type} (f : T → U) : Hint T → Hint U
  | .block ms chunkSize => .block (ms.map f) chunkSize
  | .seq m h₁ h₂ => .seq (f m) (h₁.map f) (h₂.map f)
  | .ite h₁ h₂ => .ite (h₁.map f) (h₂.map f)
  | .loop i h => .loop (f i) (h.map f)
  | .call h => .call (h.map f)
  | .frame h => .frame (h.map f)

end Taint

open Lean Meta Elab Tactic in
/-- `taint_decide`, with the taints of the hint weakened by `w`, if given. -/
meta def taintDecideAt (chunkSize : Expr) (name : String) (w : Option Term) : TacticM Unit := do
  let g ← getMainGoal
  let some (_, lhs, _) := (← instantiateMVars (← g.getType)).eq?
    | throwError "{name}: the goal is not an equation about `Taint.check A τ c h`"
  let some chk := lhs.find? (·.isAppOfArity ``Taint.check 5)
    | throwError "{name}: the goal is not an equation about `Taint.check A τ c h`"
  let args := chk.getAppArgs
  let (m, a, τ, c, h) := (args[0]!, args[1]!, args[2]!, args[3]!, args[4]!)
  let tT ← whnfD (mkApp2 (mkConst ``Taint.T) m a)
  let mut hint := mkApp5 (mkConst ``Taint.hintOfSize) m a chunkSize τ c
  if let some w := w then
    unless h.isMVar do throwError "{name}: the hint is already given"
    let wv ← Term.elabTermEnsuringType w (← mkArrow tT tT)
    Term.synthesizeSyntheticMVarsNoPostponing
    hint := mkApp4 (mkConst ``Taint.Hint.map) tT tT (← instantiateMVars wv) hint
  let instT ← synthInstance (mkApp (mkConst ``ToExpr [0]) tT)
  let hv ← unsafe evalExpr Expr (mkConst ``Expr) (mkApp3 (mkConst ``Taint.Hint.toExprNS) tT instT hint)
  if h.isMVar then h.mvarId!.assign hv
  -- The kernel evaluates the literal of any code that has one (`materialize_code`).
  evalTactic (← `(tactic| lit_decide))

open Lean Elab Tactic in
/-- Try larger hint intervals, retaining the original bounded check as a fallback. -/
meta def taintDecide (name : String) (w : Option Term) : TacticM Unit := do
  let saved ← saveState
  try
    taintDecideAt (mkNatLit 1024) name w
  catch _ =>
    -- Discard the failed attempt's hint assignment before constructing another.
    saved.restore
    taintDecideAt (mkConst ``Taint.chunk) name w

/-- Proves `(Taint.check A τ c ?hint).isSome = true`, or any decidable
equation whose left side contains `Taint.check A τ c ?hint` (e.g. a property of
the resulting taint): computes the hint (`Taint.hintOf`, in compiled code) and
then has the kernel evaluate the goal, with each code constant that has a
literal (`materialize_code`) rewritten to it. The domain `A.T` needs a `ToExpr`
instance. -/
elab "taint_decide" : tactic => taintDecide "taint_decide" none

/-- `taint_decide`, with the taints of the hint weakened by `w : A.T → A.T`
(computed in compiled code, like the hint).

`Taint.check` accepts any hint whose taints are at most what the analysis
computes (`le`): at every `chunkSize` instructions of a block, between the parts
of a `seq` and at every loop, the analysis continues from the hint's taint.
So a hint may forget public facts that the rest of the code never uses. The
kernel is a slow evaluator, and the cost of each instruction grows with the
size of the taint (e.g. the x86 analysis's list of public memory slots, which
a table of constants stored on the stack fills), so forgetting them can make
the kernel's check several times faster. Nothing about `w` needs to be sound:
a hint it weakens too much only makes the check fail. -/
elab "taint_decide_weak " w:term : tactic => taintDecide "taint_decide_weak" (some w)

/-! ## The match on the instruction, with its cases closed

A function of an instruction is a `match`, which Lean compiles to a matcher:
a function of the instruction and of the match's alternatives. The kernel
unfolds it at every instruction it has not met before, which builds a term
of every case of the matcher around the alternatives it was given, to keep
one: a third of a millisecond for a match on `Instr`, and the step of a
plain instruction is two of them (x86-64's `RTaint.stepFn1` and `stepKeepFn`).
`inline_match% f g …` is `f` as a `casesOn` whose minor premises are closed
terms, the alternatives themselves with the matches of `f` (and of the
functions `g …` it applies to the instruction) on that constructor resolved:
the kernel then only keeps the one it needs. Where a pattern looks into an
argument of the constructor (`.mov d (.mem m)`), the case is a `casesOn` of
that argument in turn. -/

namespace InlineMatch
open Lean Meta

/-- Whether `n` is a matcher, a `casesOn` or a sparse `casesOn`. -/
meta def isCaseFn (env : Environment) (n : Name) : Bool :=
  Lean.Meta.isMatcherCore env n || isCasesOnRecursor env n ||
    (match n with | .str _ s => s.startsWith "_sparseCasesOn" | _ => false)

/-- `e`, with the applications of the functions `fs` to constructors unfolded and reduced. -/
meta partial def reduceCalls (fs : Array Name) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    let .const g _ := x.getAppFn | return .continue
    unless fs.contains g do return .continue
    let args := x.getAppArgs
    if args.isEmpty then return .continue
    let .const c _ := args.back!.getAppFn | return .continue
    unless (← getEnv).find? c matches some (.ctorInfo _) do return .continue
    let some x' ← unfoldDefinition? x | return .continue
    return .visit (← whnfCore x'.headBeta))

/-- The free variables of inductive types that are arguments of the constructor
applications `es`, in order. -/
meta partial def ctorFVars (es : Array Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  for e in es do
    if e.isFVar then
      let t ← whnfD (← inferType e)
      if let .const n _ := t.getAppFn then
        if let some (.inductInfo iv) := (← getEnv).find? n then
          if iv.ctors.length ≥ 2 && !iv.isRec then out := out.push e
    else if let .const c _ := e.getAppFn then
      if (← getEnv).find? c matches some (.ctorInfo _) then
        out := out ++ (← ctorFVars e.getAppArgs)
  return out

/-- `e`, a value of the type `β` that may be a match stuck on free variables of
its discriminant: as a tree of `casesOn` on them, the match resolved in each branch. -/
meta partial def build (fs : Array Name) (β : Expr) (u : Level) (e : Expr) : Nat → MetaM Expr
  | 0 => return e
  | fuel + 1 => do
    let e ← whnfCore e
    let .const h _ := e.getAppFn | return e
    unless isCaseFn (← getEnv) h do return e
    for x in ← ctorFVars e.getAppArgs do
      let t ← whnfD (← inferType x)
      let .const ind _ := t.getAppFn | continue
      let some (.inductInfo iv) := (← getEnv).find? ind | continue
      let mut progress := false
      let mut minors := #[]
      for c in iv.ctors do
        let cinfo ← getConstInfoCtor c
        let (m, p) ← forallTelescope (← instantiateForall cinfo.type t.getAppArgs) fun ys _ => do
          let e' ← whnfCore (← reduceCalls fs (e.replaceFVar x (mkAppN (mkAppN (mkConst c) t.getAppArgs) ys)))
          let p := match e'.getAppFn with
            | .const h' _ => !(h' == h && e'.getAppNumArgs == e.getAppNumArgs)
            | _ => true
          return (← mkLambdaFVars ys (← build fs β u e' fuel), p)
        minors := minors.push m
        progress := progress || p
      if progress then
        return mkAppN (mkApp2 (mkConst (ind ++ `casesOn) [u]) (Expr.lam `_ t β .default) x) minors
    return e

end InlineMatch

open Lean Meta Elab Term InlineMatch in
@[inherit_doc InlineMatch.build]
elab "inline_match% " f:ident gs:ident* : term => liftMetaM do
  let fn ← realizeGlobalConstNoOverload f
  let fs := (← gs.mapM fun g => realizeGlobalConstNoOverload g).push fn
  let .forallE _ dom cod _ := (← getConstInfo fn).type | throwError "inline_match%: {fn} is not a function"
  let .const ind _ := dom.getAppFn | throwError "inline_match%: the domain of {fn} is not an inductive type"
  let some (.inductInfo iv) := (← getEnv).find? ind
    | throwError "inline_match%: the domain of {fn} is not an inductive type"
  let u ← getLevel cod
  let minors ← iv.ctors.toArray.mapM fun c => do
    forallTelescope (← getConstInfoCtor c).type fun xs _ => do
      let e ← reduceCalls fs (mkApp (mkConst fn) (mkAppN (mkConst c) xs))
      mkLambdaFVars xs (← build fs cod u e 3)
  return Expr.lam `i dom
    (mkAppN (mkApp2 (mkConst (ind ++ `casesOn) [u]) (Expr.lam `_ dom cod .default) (.bvar 0)) minors) .default

end VG
