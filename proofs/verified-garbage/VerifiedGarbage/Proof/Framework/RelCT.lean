module

public import VerifiedGarbage.Proof.Framework.Taint
public import VerifiedGarbage.Proof.Framework.Inline

/-!
# Constant time by relating two runs

The taint analysis (`Taint.lean`) proves constant time from the code alone,
so it forgets any public value that makes a round trip through memory it
cannot track, e.g. a callee-saved register saved and restored by a callee
that also stores secrets through pointers of unknown length.

`RelCT P c Q` states constant time for two runs related by `P`, and relates
their final states by `Q`. The relations may carry what the correctness
proof knows about each run (`RelCT.wp`, by determinism), such as the values
of registers, so a public value is public again as soon as correctness
determines it. Pieces of code whose timing the taint analysis can establish
are proved with `RelCT.taint`, and the pieces are put together with `seq`
and `loop`. A call of verified code is related by `RegionModel.relCT_call`:
the callee's run from its contract's narrower permissions is the actual run
(`Inline.lean`), and the callee is constant time.
-/

@[expose] public section

namespace VG

variable {M : ISA}

/-- Any two runs of `c` from states related by `P` leak the same trace and
end in states related by `Q`. -/
def RelCT (M : ISA) (P : M.State → M.State → Prop) (c : Prog M)
    (Q : M.State → M.State → Prop) : Prop :=
  ∀ s₁ s₂ t₁ t₂ s₁' s₂', P s₁ s₂ → Exec M c s₁ t₁ s₁' → Exec M c s₂ t₂ s₂' →
    t₁ = t₂ ∧ Q s₁' s₂'

namespace RelCT

theorem constantTime {Pre : M.State → Prop} {Pub : M.State → M.State → Prop} {c : Prog M}
    {Q : M.State → M.State → Prop} (h : RelCT M (fun s₁ s₂ => Pre s₁ ∧ Pre s₂ ∧ Pub s₁ s₂) c Q) :
    ConstantTime M Pre Pub c :=
  fun _ _ _ _ _ _ h₁ h₂ hp e₁ e₂ => (h _ _ _ _ _ _ ⟨h₁, h₂, hp⟩ e₁ e₂).1

theorem mono {P P' Q Q' : M.State → M.State → Prop} {c : Prog M} (h : RelCT M P c Q)
    (hp : ∀ s₁ s₂, P' s₁ s₂ → P s₁ s₂) (hq : ∀ s₁ s₂, Q s₁ s₂ → Q' s₁ s₂) : RelCT M P' c Q' :=
  fun _ _ _ _ _ _ h' e₁ e₂ =>
    let ⟨ht, hq'⟩ := h _ _ _ _ _ _ (hp _ _ h') e₁ e₂
    ⟨ht, hq _ _ hq'⟩

/-- What each run satisfies by correctness holds of the final states. -/
theorem wp {P Q : M.State → M.State → Prop} {c : Prog M} {F₁ F₂ : M.State → Prop}
    (h : RelCT M P c Q) (hw : ∀ s₁ s₂, P s₁ s₂ → WP M c s₁ F₁ ∧ WP M c s₂ F₂) :
    RelCT M P c fun s₁ s₂ => Q s₁ s₂ ∧ F₁ s₁ ∧ F₂ s₂ := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨_, u₁, f₁, g₁⟩, ⟨_, u₂, f₂, g₂⟩⟩ := hw _ _ hp
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht, hq, g₁, g₂⟩

/-- As `wp`, for a postcondition that also depends on the initial state:
the final states are related through initial states related by `P`. -/
theorem wpDep {P Q : M.State → M.State → Prop} {c : Prog M} {F : M.State → M.State → Prop}
    (h : RelCT M P c Q) (hw : ∀ s₁ s₂, P s₁ s₂ → WP M c s₁ (F s₁) ∧ WP M c s₂ (F s₂)) :
    RelCT M P c fun s₁' s₂' => Q s₁' s₂' ∧ ∃ σ₁ σ₂, P σ₁ σ₂ ∧ F σ₁ s₁' ∧ F σ₂ s₂' := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  obtain ⟨ht, hq⟩ := h _ _ _ _ _ _ hp e₁ e₂
  obtain ⟨⟨_, u₁, f₁, g₁⟩, ⟨_, u₂, f₂, g₂⟩⟩ := hw _ _ hp
  obtain ⟨-, rfl⟩ := Exec.det e₁ f₁
  obtain ⟨-, rfl⟩ := Exec.det e₂ f₂
  exact ⟨ht, hq, _, _, hp, g₁, g₂⟩

/-- Two cases, proved separately. -/
theorem or {P₁ P₂ Q : M.State → M.State → Prop} {c : Prog M} (h₁ : RelCT M P₁ c Q)
    (h₂ : RelCT M P₂ c Q) : RelCT M (fun s₁ s₂ => P₁ s₁ s₂ ∨ P₂ s₁ s₂) c Q :=
  fun _ _ _ _ _ _ hp e₁ e₂ => hp.elim (h₁ _ _ _ _ _ _ · e₁ e₂) (h₂ _ _ _ _ _ _ · e₁ e₂)

/-- A family of cases, proved for each. -/
theorem exists_ {α : Sort _} {P : α → M.State → M.State → Prop} {Q : M.State → M.State → Prop}
    {c : Prog M} (h : ∀ x, RelCT M (P x) c Q) : RelCT M (fun s₁ s₂ => ∃ x, P x s₁ s₂) c Q :=
  fun _ _ _ _ _ _ ⟨x, hp⟩ e₁ e₂ => h x _ _ _ _ _ _ hp e₁ e₂

/-- Runs that never start from states related by `P`. -/
theorem of_false {P Q : M.State → M.State → Prop} {c : Prog M} (h : ∀ s₁ s₂, ¬ P s₁ s₂) :
    RelCT M P c Q :=
  fun _ _ _ _ _ _ hp _ _ => absurd hp (h _ _)

theorem seq {P R Q : M.State → M.State → Prop} {c₁ c₂ : Prog M} (h₁ : RelCT M P c₁ R)
    (h₂ : RelCT M R c₂ Q) : RelCT M P (.seq c₁ c₂) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | seq a₁ b₁ =>
    cases e₂ with
    | seq a₂ b₂ =>
      obtain ⟨rfl, hr⟩ := h₁ _ _ _ _ _ _ hp a₁ a₂
      obtain ⟨rfl, hq⟩ := h₂ _ _ _ _ _ _ hr b₁ b₂
      exact ⟨rfl, hq⟩

/-- A branch whose condition agrees in both runs; each branch may assume it
was taken. -/
theorem ite {P Q : M.State → M.State → Prop} {c : M.Cond} {t e : Prog M}
    (hc : ∀ s₁ s₂, P s₁ s₂ → M.eval c s₁ = M.eval c s₂)
    (ht : RelCT M (fun s₁ s₂ => P s₁ s₂ ∧ M.eval c s₁ = some true) t Q)
    (he : RelCT M (fun s₁ s₂ => P s₁ s₂ ∧ M.eval c s₁ = some false) e Q) :
    RelCT M P (.ite c t e) Q := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  have hce := hc _ _ hp
  cases e₁ with
  | iteT c₁ a₁ =>
    cases e₂ with
    | iteT _ a₂ => obtain ⟨rfl, hq⟩ := ht _ _ _ _ _ _ ⟨hp, c₁⟩ a₁ a₂; exact ⟨rfl, hq⟩
    | iteF c₂ _ => rw [hce, c₂] at c₁; cases c₁
  | iteF c₁ a₁ =>
    cases e₂ with
    | iteT c₂ _ => rw [hce, c₂] at c₁; cases c₁
    | iteF _ a₂ => obtain ⟨rfl, hq⟩ := he _ _ _ _ _ _ ⟨hp, c₁⟩ a₁ a₂; exact ⟨rfl, hq⟩

/-- A loop, with an invariant indexed by a measure that decreases on every
iteration that loops back; the condition must agree in both runs. -/
theorem loop {body : Prog M} {c : M.Cond} {Q : M.State → M.State → Prop}
    (I : Nat → M.State → M.State → Prop)
    (hstep : ∀ n, RelCT M (I n) body fun s₁ s₂ => M.eval c s₁ = M.eval c s₂ ∧
      (M.eval c s₁ = some false → Q s₁ s₂) ∧ (M.eval c s₁ = some true → ∃ m < n, I m s₁ s₂))
    (n : Nat) : RelCT M (I n) (.loop body c) Q := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
    cases e₁ with
    | loopExit b₁ c₁ =>
      cases e₂ with
      | loopExit b₂ c₂ =>
        obtain ⟨rfl, -, hq, -⟩ := hstep n _ _ _ _ _ _ hp b₁ b₂
        exact ⟨rfl, hq c₁⟩
      | loopNext b₂ c₂ _ =>
        obtain ⟨-, hc, -, -⟩ := hstep n _ _ _ _ _ _ hp b₁ b₂
        rw [c₁, c₂] at hc; cases hc
    | loopNext b₁ c₁ r₁ =>
      cases e₂ with
      | loopExit b₂ c₂ =>
        obtain ⟨-, hc, -, -⟩ := hstep n _ _ _ _ _ _ hp b₁ b₂
        rw [c₁, c₂] at hc; cases hc
      | loopNext b₂ c₂ r₂ =>
        obtain ⟨rfl, -, -, hi⟩ := hstep n _ _ _ _ _ _ hp b₁ b₂
        obtain ⟨m, hm, hi⟩ := hi c₁
        obtain ⟨rfl, hq⟩ := ih m hm _ _ _ _ _ _ hi r₁ r₂
        exact ⟨rfl, hq⟩

/-- Code the taint analysis proves constant time, from states that agree on
what the initial taint says is public. -/
theorem taint {A : Taint M} {P : M.State → M.State → Prop} {c : Prog M} (τ : A.T)
    (hp : ∀ s₁ s₂, P s₁ s₂ → A.Agree τ s₁ s₂) {hc : Taint.Hint A.T}
    (h : (A.check τ c hc).isSome = true) : RelCT M P c fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hP e₁ e₂
  obtain ⟨τ', hc'⟩ := Option.isSome_iff_exists.mp h
  exact ⟨(Taint.check_sound hc' (hp _ _ hP) e₁ e₂).1, trivial⟩

end RelCT

namespace RegionModel

variable (R : RegionModel M)

/-- Two runs of a call of verified code leak the same trace when, from the
states the call instructions leave, the callee's contract holds in both
(narrowed to regions that those states' regions cover), its public data
agrees, and so do the addresses the call and return instructions access. -/
theorem relCT_call {n : String} {c : Prog M} {Pre : M.State → Prop}
    {Post : M.State → M.State → Prop} {Pub : M.State → M.State → Prop}
    (hv : ∀ s, Pre s → ∃ t s', Exec M c s t s' ∧ Post s s')
    (hct : ConstantTime M Pre Pub c) {P : M.State → M.State → Prop}
    (hP : ∀ s₁ s₂ e₁ e₂, P s₁ s₂ → M.call s₁ = some e₁ → M.call s₂ = some e₂ →
      ∃ r₁ w₁ r₂ w₂ : List Region,
        Pre (R.withRegions e₁ r₁ w₁) ∧ Pre (R.withRegions e₂ r₂ w₂) ∧
        Pub (R.withRegions e₁ r₁ w₁) (R.withRegions e₂ r₂ w₂) ∧
        Covers (r₁ ++ w₁) (R.rd e₁ ++ R.wr e₁) ∧ Covers w₁ (R.wr e₁) ∧
        Covers (r₂ ++ w₂) (R.rd e₂ ++ R.wr e₂) ∧ Covers w₂ (R.wr e₂) ∧
        M.callAddrs s₁ = M.callAddrs s₂ ∧
        ∀ x₁ x₂ y₁ y₂, M.ret e₁ x₁ = some y₁ → M.ret e₂ x₂ = some y₂ →
          M.retAddrs x₁ = M.retAddrs x₂) :
    RelCT M P (.call n c) fun _ _ => True := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' hp e₁ e₂
  cases e₁ with
  | call h₁ b₁ r₁ =>
    cases e₂ with
    | call h₂ b₂ r₂ =>
      obtain ⟨_, _, _, _, p₁, p₂, hpub, c₁, w₁, c₂, w₂, ha, hr⟩ := hP _ _ _ _ hp h₁ h₂
      obtain ⟨_, n₁⟩ := R.trace_narrow hv p₁ c₁ w₁ b₁
      obtain ⟨_, n₂⟩ := R.trace_narrow hv p₂ c₂ w₂ b₂
      rw [ha, hct _ _ _ _ _ _ p₁ p₂ hpub n₁ n₂, hr _ _ _ _ r₁ r₂]
      exact ⟨rfl, trivial⟩

end RegionModel

end VG
