module

public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPaths
public import VerifiedGarbage.Proof.Framework.CodeOnce
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.Syms

/-!
# The vectors' upper halves in two runs of the same path (x86-64)

Two runs of the same code whose traces agree, one a prefix of the other's
continuation, take the same path: their blocks leak as many addresses
whatever the state (`addrs_length`), so the traces split alike, and each
branch, loop test and indirect call is observed (a branch's direction, the
address an indirect call calls, which is the function of the chain whose
address it is, the same in both runs if their functions' addresses are).
Along that path, the upper halves of `zmm0`–`zmm15` (`ymmHi`, `zmmHi`)
agree after code that keeps them (level 0, `Instr.vecLevel`) if they agreed
before it, and after `vzeroupper`, which zeroes them, whatever they were.
`up` follows this through the code (`up c true`: they agree at the end if
they agreed at the start), so that code of the baseline ISA that calls,
through tables of functions, functions with AVX instructions that end with
`vzeroupper` leaves the upper halves as its caller left them, or zero, the
same in two runs that take the same path (`lock`).
-/

@[expose] public section

namespace VG.X86_64.UpperLock

open VG VG.X86_64

/-- The upper halves of `zmm0`–`zmm15` agree. -/
def UA (s₁ s₂ : State) : Prop := s₁.ymmHi = s₂.ymmHi ∧ s₁.zmmHi = s₂.zmmHi

theorem stepI_mono {a a' : Bool} (h : a = true → a' = true) (i : Instr) (hs : stepI a i = true) :
    stepI a' i = true := by
  unfold stepI at hs ⊢
  split
  · rfl
  · simp only [Bool.and_eq_true] at hs ⊢; exact ⟨h hs.1, hs.2⟩

theorem foldl_stepI_mono : ∀ (is : List Instr) {a a' : Bool}, (a = true → a' = true) →
    is.foldl stepI a = true → is.foldl stepI a' = true
  | [], _, _, h, hs => h hs
  | i :: is, _, _, h, hs => foldl_stepI_mono is (stepI_mono h i) hs

/-- The upper halves agree after `c` from a start at which they agree, if
they do from one at which they need not: so a loop's body, which `up` runs
once, ends every iteration with them agreeing. -/
theorem up_mono : ∀ (c : Prog isa) {a a' : Bool}, (a = true → a' = true) → up c a = true → up c a' = true
  | .block is, _, _, h, hs => foldl_stepI_mono is h hs
  | .seq x y, _, _, h, hs => up_mono y (up_mono x h) hs
  | .ite _ t e, _, _, h, hs => by
    simp only [up, Bool.and_eq_true] at hs ⊢; exact ⟨up_mono t h hs.1, up_mono e h hs.2⟩
  | .loop b _, _, _, h, hs => up_mono b h hs
  | .call _ b, _, _, h, hs => up_mono b h hs
  | .frame _ b _, _, _, h, hs => up_mono b h hs
  | .icall _ _ b n, _, _, h, hs => by
    simp only [up, Bool.and_eq_true] at hs ⊢; exact ⟨up_mono b h hs.1, up_mono n h hs.2⟩

theorem upFrom_ok : ∀ (c : Prog isa) (a : Bool) (k : List (String × Prog isa × Bool × Bool)),
    (∀ e ∈ k, e.2.2.2 = up e.2.1 e.2.2.1) →
      (upFrom c a k).1 = up c a ∧ ∀ e ∈ (upFrom c a k).2, e.2.2.2 = up e.2.1 e.2.2.1
  | .block _, _, _, hk => ⟨rfl, hk⟩
  | .seq x y, a, k, hk => by
    obtain ⟨hx, kx⟩ := upFrom_ok x a k hk
    obtain ⟨hy, ky⟩ := upFrom_ok y (upFrom x a k).1 _ kx
    exact ⟨by rw [upFrom, hy, hx, up], ky⟩
  | .ite _ t e, a, k, hk => by
    obtain ⟨ht, kt⟩ := upFrom_ok t a k hk
    obtain ⟨he, ke⟩ := upFrom_ok e a _ kt
    exact ⟨by rw [upFrom, he, ht, up], ke⟩
  | .loop b _, a, k, hk => upFrom_ok b a k hk
  | .call n b, a, k, hk =>
    Code.memoCall_ok (n := n) (run := fun _ => upFrom b a k) (spec := up) hk (upFrom_ok b a k hk)
  | .frame _ b _, a, k, hk => upFrom_ok b a k hk
  | .icall _ n b nx, a, k, hk => by
    obtain ⟨hb, kb⟩ := Code.memoCall_ok (n := n) (run := fun _ => upFrom b a k) (spec := up) hk (upFrom_ok b a k hk)
    obtain ⟨hn, kn⟩ := upFrom_ok nx a _ kb
    exact ⟨by rw [upFrom, hn, hb, up], kn⟩

theorem upOnce_eq (c : Prog isa) (a : Bool) : upOnce c a = up c a :=
  (upFrom_ok c a [] fun _ h => by cases h).1

theorem exec_ua {i : Instr} {a : Bool} {s₁ s₂ s₁' s₂' : State} (e₁ : exec i s₁ = some s₁')
    (e₂ : exec i s₂ = some s₂') (h : stepI a i = true) (hu : a = true → UA s₁ s₂) : UA s₁' s₂' := by
  by_cases hz : i = .vop .vzeroupper
  · subst hz
    simp only [exec, VOp.exec, Option.some.injEq] at e₁ e₂
    subst e₁ e₂
    exact ⟨rfl, rfl⟩
  · have h' : a = true ∧ i.vecLevel = 0 := by
      unfold stepI at h; split at h
      · exact absurd rfl hz
      · simpa using h
    have k₁ := Residue.exec_vkeep (by omega) e₁
    have k₂ := Residue.exec_vkeep (by omega) e₂
    rw [h'.2] at k₁ k₂
    obtain ⟨y₁, z₁⟩ := k₁.2.2.2 rfl
    obtain ⟨y₂, z₂⟩ := k₂.2.2.2 rfl
    obtain ⟨y, z⟩ := hu h'.1
    exact ⟨by rw [y₁, y₂, y], by rw [z₁, z₂, z]⟩

theorem execBlock_ua : ∀ {is : List Instr} {a : Bool} {s₁ s₂ s₁' s₂' : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (s₁', t₁) → execBlock isa is s₂ = some (s₂', t₂) →
    is.foldl stepI a = true → (a = true → UA s₁ s₂) → UA s₁' s₂'
  | [], a, s₁, s₂, s₁', s₂', t₁, t₂, e₁, e₂, h, hu => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at e₁ e₂
    obtain ⟨rfl, -⟩ := e₁
    obtain ⟨rfl, -⟩ := e₂
    exact hu h
  | i :: is, a, s₁, s₂, s₁', s₂', t₁, t₂, e₁, e₂, h, hu => by
    simp only [execBlock] at e₁ e₂
    split at e₁
    · cases e₁
    rename_i u₁ hx₁
    split at e₂
    · cases e₂
    rename_i u₂ hx₂
    obtain ⟨⟨v₁, w₁⟩, b₁, c₁⟩ := Option.map_eq_some_iff.mp e₁
    obtain ⟨⟨v₂, w₂⟩, b₂, c₂⟩ := Option.map_eq_some_iff.mp e₂
    simp only [Prod.mk.injEq] at c₁ c₂
    obtain ⟨rfl, -⟩ := c₁
    obtain ⟨rfl, -⟩ := c₂
    simp only [List.foldl_cons] at h
    refine execBlock_ua b₁ b₂ h fun ha => ?_
    exact exec_ua hx₁ hx₂ ha hu

/-! ## Traces -/

theorem append_cancel {α : Type} {a₁ a₂ b₁ b₂ : List α} (hl : a₁.length = a₂.length)
    (h : a₁ ++ b₁ = a₂ ++ b₂) : a₁ = a₂ ∧ b₁ = b₂ :=
  List.append_inj h hl

/-- The trace of an indirect call: the addresses its instruction reads, then the address it calls. -/
theorem icall_trace {i : Instr} {n : String} {b nx : Prog isa} {s s' : State} {t : List Leak}
    (e : Exec isa (.icall i n b nx) s t s') :
    ∃ a rest, isa.icall i s = some a ∧ t = (isa.addrs i s).map .addr ++ .addr a :: rest := by
  cases e with
  | icall h₁ _ _ _ => exact ⟨_, _, h₁, rfl⟩
  | icallNext _ _ e' => exact icall_trace e'

theorem call_ua {s s₁ : State} (h : isa.call s = some s₁) : s₁.ymmHi = s.ymmHi ∧ s₁.zmmHi = s.zmmHi := by
  simp only [isa, call, Option.some.injEq] at h; subst h; exact ⟨rfl, rfl⟩

theorem call_syms {s s₁ : State} (h : isa.call s = some s₁) : s₁.syms = s.syms := by
  simp only [isa, call, Option.some.injEq] at h; subst h; rfl

theorem ret_ua {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s'.ymmHi = s₂.ymmHi ∧ s'.zmmHi = s₂.zmmHi := by
  simp only [isa, ret] at h; split at h <;> cases h; exact ⟨rfl, rfl⟩

theorem ua_of {a₁ a₂ b₁ b₂ : State} (h₁ : b₁.ymmHi = a₁.ymmHi ∧ b₁.zmmHi = a₁.zmmHi)
    (h₂ : b₂.ymmHi = a₂.ymmHi ∧ b₂.zmmHi = a₂.zmmHi) (h : UA a₁ a₂) : UA b₁ b₂ :=
  ⟨by rw [h₁.1, h₂.1, h.1], by rw [h₁.2, h₂.2, h.2]⟩

theorem push_ua {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) :
    s₁.ymmHi = s.ymmHi ∧ s₁.zmmHi = s.zmmHi := by
  have := Residue.push_vk0 h
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨this.2.2.2.1, this.2.2.2.2⟩

theorem pop_ua {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s'.ymmHi = s₂.ymmHi ∧ s'.zmmHi = s₂.zmmHi := by
  have := Residue.pop_vk0 h
  simp only [Residue.vk0, Prod.mk.injEq] at this
  exact ⟨this.2.2.2.1, this.2.2.2.2⟩

theorem branch_ne {t₁ t₂ r₁ r₂ : List Leak} (h : .branch true :: t₁ ++ r₁ = .branch false :: t₂ ++ r₂) : False := by
  simp at h

/-- Two runs of `c` whose traces agree, extended by `r₁` and `r₂`, from
states whose functions called indirectly are at the same addresses: their
traces are the same, and the upper halves agree at the end if `up c a` and
they agreed at the start or `a` is false. -/
theorem lock {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ r₁ r₂ : List Leak}, Exec isa c s₂ t₂ s₂' → t₁ ++ r₁ = t₂ ++ r₂ →
      (∀ n ∈ inames c, s₁.syms n = s₂.syms n) →
      t₁ = t₂ ∧ ∀ a, up c a = true → (a = true → UA s₁ s₂) → UA s₁' s₂' := by
  induction e₁ with
  | block h₁ =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht _
    cases e₂ with
    | block h₂ =>
      have hl := (execBlock_length h₁).trans (execBlock_length h₂).symm
      exact ⟨(append_cancel hl ht).1, fun a hv hu => execBlock_ua h₁ h₂ hv hu⟩
  | seq x₁ y₁ ihx ihy =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | seq x₂ y₂ =>
      simp only [List.append_assoc] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨hx, ux⟩ := ihx x₂ ht fun n hn => hf n (.inl hn)
      subst hx
      have ht' := List.append_cancel_left ht
      obtain ⟨hy, uy⟩ := ihy y₂ ht' fun n hn => by
        rw [Exec.syms x₁, Exec.syms x₂]; exact hf n (.inr hn)
      subst hy
      exact ⟨rfl, fun a hv hu => uy _ hv fun h' => ux a h' hu⟩
  | iteT hc₁ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | iteT _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨h, u⟩ := ih x₂ ht fun n hn => hf n (.inl hn)
      subst h
      exact ⟨rfl, fun a hv hu => u a (by simp only [up, Bool.and_eq_true] at hv; exact hv.1) hu⟩
    | iteF _ _ => exact (branch_ne ht).elim
  | iteF hc₁ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | iteF _ x₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      simp only [inames, List.mem_append] at hf
      obtain ⟨h, u⟩ := ih x₂ ht fun n hn => hf n (.inr hn)
      subst h
      exact ⟨rfl, fun a hv hu => u a (by simp only [up, Bool.and_eq_true] at hv; exact hv.2) hu⟩
    | iteT _ _ => exact (branch_ne ht.symm).elim
  | loopExit x₁ hc₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, u⟩ := ih x₂ ht hf
      subst h
      exact ⟨rfl, fun a hv hu => u a hv hu⟩
    | loopNext x₂ _ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := ih x₂ ht hf
      subst h
      simp at ht
  | loopNext x₁ hc₁ l₁ ihx ihl =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | loopExit x₂ _ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, -⟩ := ihx x₂ ht hf
      subst h
      simp at ht
    | loopNext x₂ _ l₂ =>
      simp only [List.append_assoc] at ht
      obtain ⟨h, ux⟩ := ihx x₂ ht hf
      subst h
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨h', ul⟩ := ihl l₂ ht' fun n hn => by rw [Exec.syms x₁, Exec.syms x₂]; exact hf n hn
      subst h'
      exact ⟨rfl, fun a hv hu => ul true (up_mono _ (fun _ => rfl) hv) fun _ => ux a hv hu⟩
  | call hc₁ x₁ hr₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | call hc₂ x₂ hr₂ =>
      have ht0 := ht
      simp only [List.map_cons, List.map_nil, List.append_assoc,
        List.cons_append, List.cons.injEq] at ht
      obtain ⟨h, u⟩ := ih x₂ ht.2 fun n hn => by rw [call_syms hc₁, call_syms hc₂]; exact hf n hn
      subst h
      refine ⟨(append_cancel (by simp) ht0).1, fun a hv hu =>
        ua_of (ret_ua hr₁) (ret_ua hr₂) (u a hv fun ha => ua_of (call_ua hc₁) (call_ua hc₂) (hu ha))⟩
  | frame hp₁ x₁ hq₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | frame hp₂ x₂ hq₂ =>
      have ht0 := ht
      simp only [List.append_assoc] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      obtain ⟨h, u⟩ := ih x₂ ht fun n hn => by
        rw [push_syms hp₁, push_syms hp₂]; exact hf n hn
      subst h
      refine ⟨(append_cancel ?_ ht0).1, fun a hv hu =>
        ua_of (pop_ua hq₁) (pop_ua hq₂) (u a hv fun ha => ua_of (push_ua hp₁) (push_ua hp₂) (hu ha))⟩
      simp only [List.length_append, List.length_map, addrs_length _ _ State.zero]
  | icall hi₁ hc₁ x₁ hr₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    have hn := hf _ (List.mem_cons_self ..)
    cases e₂ with
    | icall hi₂ hc₂ x₂ hr₂ =>
      have ht0 := ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.map_cons, List.map_nil, List.cons_append,
        List.cons.injEq] at ht
      obtain ⟨h, u⟩ := ih x₂ ht.2.2 fun m hm => by
        rw [call_syms hc₁, call_syms hc₂]; exact hf m (by simp [inames, hm])
      subst h
      refine ⟨(append_cancel ?_ ht0).1, fun a hv hu =>
        ua_of (ret_ua hr₁) (ret_ua hr₂) (u a (by simp only [up, Bool.and_eq_true] at hv; exact hv.1)
          fun ha => ua_of (call_ua hc₁) (call_ua hc₂) (hu ha))⟩
      simp only [List.length_append, List.length_map, List.length_cons,
        addrs_length _ _ State.zero]
    | icallNext hi₂ hne₂ x₂ =>
      exfalso
      obtain ⟨a₂, rest, hi₂', ht₂⟩ := icall_trace x₂
      rw [hi₂] at hi₂'; cases hi₂'
      rw [ht₂] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₂
      rw [← ht.1, hn]
  | icallNext hi₁ hne₁ x₁ ih =>
    intro s₂ s₂' t₂ r₁ r₂ e₂ ht hf
    cases e₂ with
    | icallNext hi₂ hne₂ x₂ =>
      obtain ⟨h, u⟩ := ih x₂ ht fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
      exact ⟨h, fun a hv hu => u a ((Bool.and_eq_true _ _).mp hv).2 hu⟩
    | icall hi₂ hc₂ x₂ hr₂ =>
      exfalso
      obtain ⟨a₁, rest, hi₁', ht₁⟩ := icall_trace x₁
      rw [hi₁] at hi₁'; cases hi₁'
      rw [ht₁] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₁
      rw [ht.1]; exact (hf _ (List.mem_cons_self ..)).symm

end VG.X86_64.UpperLock
