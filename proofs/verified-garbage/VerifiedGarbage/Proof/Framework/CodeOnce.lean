module

public import VerifiedGarbage.TCB.Code

/-!
# Following the code of each function once

A check that follows structured code (`Code.all`; on x86-64, `UpperLock.up`,
`Mx.mx`, `mxClass`) goes through the code of a function once per call of it,
through every function that calls it: on code whose calls nest, most of what
it does it has done before, and the emitter, which evaluates these checks in
the interpreter for every function it scrubs, spent most of its time there.

`Code.memoCall` runs such a check on the code of a call (a direct one, or
the function of an indirect call) unless that code is the code of the last
call of the same function, with the same key (what else the check's answer
depends on), whose answer it then gives. The codes of two calls of a
function are usually the same value in memory, which `withPtrEqDecEq` finds
at once; otherwise `Code.dec` compares them, again at once wherever their
parts are the same values. A check written with it gives what the check
itself gives (`Code.memoCall_ok`): `Code.allOnce` is `Code.all`
(`Code.allOnce_eq`).
-/

@[expose] public section

namespace VG.Code.Once

deriving instance DecidableEq for Code

end VG.Code.Once

namespace VG

variable {I C : Type} [DecidableEq I] [DecidableEq C]

/-- `p ∧ q`, deciding `q` only if `p` holds. -/
@[inline] def Code.Once.andDec {p q : Prop} (dp : Decidable p) (dq : Unit → Decidable q) : Decidable (p ∧ q) :=
  match dp with
  | isTrue hp =>
    (match dq () with
    | isTrue hq => isTrue ⟨hp, hq⟩
    | isFalse hq => isFalse fun h => hq h.2)
  | isFalse hp => isFalse fun h => hp h.1

/-- Equality of codes, found at once for the same value in memory
(`withPtrEqDecEq`), at every level: two codes built alike from the same
functions' codes are compared only where they were built. -/
def Code.dec : (a b : Code I C) → Decidable (a = b)
  | .block is, .block js =>
    @decidable_of_decidable_of_eq _ _ (withPtrEqDecEq is js fun _ => inferInstance) (Code.block.injEq ..).symm
  | .seq a₁ a₂, .seq b₁ b₂ =>
    @decidable_of_decidable_of_eq _ _
      (Once.andDec (withPtrEqDecEq a₁ b₁ fun _ => Code.dec a₁ b₁) fun _ => withPtrEqDecEq a₂ b₂ fun _ => Code.dec a₂ b₂)
      (Code.seq.injEq ..).symm
  | .ite c t e, .ite c' t' e' =>
    @decidable_of_decidable_of_eq _ _
      (Once.andDec (inferInstance : Decidable (c = c')) fun _ =>
        Once.andDec (withPtrEqDecEq t t' fun _ => Code.dec t t') fun _ => withPtrEqDecEq e e' fun _ => Code.dec e e')
      (Code.ite.injEq ..).symm
  | .loop b c, .loop b' c' =>
    @decidable_of_decidable_of_eq _ _
      (Once.andDec (withPtrEqDecEq b b' fun _ => Code.dec b b') fun _ => (inferInstance : Decidable (c = c')))
      (Code.loop.injEq ..).symm
  | .call n b, .call n' b' =>
    @decidable_of_decidable_of_eq _ _
      (Once.andDec (inferInstance : Decidable (n = n')) fun _ => withPtrEqDecEq b b' fun _ => Code.dec b b')
      (Code.call.injEq ..).symm
  | .frame i b j, .frame i' b' j' =>
    @decidable_of_decidable_of_eq _ _
      (Once.andDec (inferInstance : Decidable (i = i')) fun _ =>
        Once.andDec (withPtrEqDecEq b b' fun _ => Code.dec b b') fun _ => (inferInstance : Decidable (j = j')))
      (Code.frame.injEq ..).symm
  | .icall i n b nx, .icall i' n' b' nx' =>
    @decidable_of_decidable_of_eq _ _
      (Once.andDec (inferInstance : Decidable (i = i')) fun _ =>
        Once.andDec (inferInstance : Decidable (n = n')) fun _ =>
          Once.andDec (withPtrEqDecEq b b' fun _ => Code.dec b b') fun _ =>
            withPtrEqDecEq nx nx' fun _ => Code.dec nx nx')
      (Code.icall.injEq ..).symm
  -- Different constructors.
  | a, b => (inferInstance : DecidableEq (Code I C)) a b

/-- Whether two codes are equal (`Code.dec`). -/
def Code.same (a b : Code I C) : Bool := (withPtrEqDecEq a b fun _ => Code.dec a b).decide

theorem Code.eq_of_same {a b : Code I C} (h : Code.same a b = true) : a = b :=
  @of_decide_eq_true _ (withPtrEqDecEq a b fun _ => Code.dec a b) h

section Memo

variable {β κ : Type} [DecidableEq κ]

/-- What `run` gives for the code `b` of a call of the function `n` with the
key `key`, and the calls it found, with this one: but, if the last call of
`n` with that key among the calls `k` (a call's function, code, key and
value) has the code `b`, its value, without running `run`. -/
def Code.memoCall (n : String) (b : Code I C) (key : κ) (k : List (String × Code I C × κ × β))
    (run : Unit → β × List (String × Code I C × κ × β)) : β × List (String × Code I C × κ × β) :=
  match k.find? (fun e => e.1 == n && e.2.2.1 == key) with
  | some e =>
    if Code.same b e.2.1 then (e.2.2.2, k)
    else
      let r := run ()
      (r.1, (n, b, key, r.1) :: r.2)
  | none =>
    let r := run ()
    (r.1, (n, b, key, r.1) :: r.2)

/-- `Code.memoCall` gives `spec`'s value, and calls with `spec`'s values, if
`run` does and the calls it is given have them. -/
theorem Code.memoCall_ok {spec : Code I C → κ → β} {n : String} {b : Code I C} {key : κ}
    {k : List (String × Code I C × κ × β)} {run : Unit → β × List (String × Code I C × κ × β)}
    (hk : ∀ e ∈ k, e.2.2.2 = spec e.2.1 e.2.2.1)
    (hr : (run ()).1 = spec b key ∧ ∀ e ∈ (run ()).2, e.2.2.2 = spec e.2.1 e.2.2.1) :
    (Code.memoCall n b key k run).1 = spec b key ∧
      ∀ e ∈ (Code.memoCall n b key k run).2, e.2.2.2 = spec e.2.1 e.2.2.1 := by
  have hn : ∀ e ∈ (n, b, key, (run ()).1) :: (run ()).2, e.2.2.2 = spec e.2.1 e.2.2.1 := fun e he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact hr.1
    · exact hr.2 e he
  unfold Code.memoCall
  split
  · rename_i e he
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    split
    · rename_i hs
      exact ⟨by rw [hk e (List.mem_of_find?_eq_some he), hp.2, ← Code.eq_of_same hs], hk⟩
    · exact ⟨hr.1, hn⟩
  · exact ⟨hr.1, hn⟩

end Memo

/-- `Code.all p c`, given calls with `Code.all p` of their code (`k`), with
those calls and the calls of `c` (`Code.memoCall`). -/
def Code.allFrom (p : I → Bool) : Code I C → List (String × Code I C × Unit × Bool) →
    Bool × List (String × Code I C × Unit × Bool)
  | .block is, k => (is.all p, k)
  | .seq a b, k =>
    let r := allFrom p a k
    if r.1 then allFrom p b r.2 else (false, r.2)
  | .ite _ t e, k =>
    let r := allFrom p t k
    if r.1 then allFrom p e r.2 else (false, r.2)
  | .loop b _, k => allFrom p b k
  | .call n b, k => Code.memoCall n b () k fun _ => allFrom p b k
  | .frame i b j, k => if p i && p j then allFrom p b k else (false, k)
  | .icall i n b nx, k =>
    if p i then
      let r := Code.memoCall n b () k fun _ => allFrom p b k
      if r.1 then allFrom p nx r.2 else (false, r.2)
    else (false, k)

theorem Code.allFrom_ok (p : I → Bool) : ∀ (c : Code I C) (k : List (String × Code I C × Unit × Bool)),
    (∀ e ∈ k, e.2.2.2 = e.2.1.all p) →
      (allFrom p c k).1 = c.all p ∧ ∀ e ∈ (allFrom p c k).2, e.2.2.2 = e.2.1.all p
  | .block is, k, hk => ⟨rfl, hk⟩
  | .seq a b, k, hk => by
    obtain ⟨ha, ka⟩ := allFrom_ok p a k hk
    simp only [allFrom, Code.all]
    split
    · rename_i h
      obtain ⟨hb, kb⟩ := allFrom_ok p b _ ka
      exact ⟨by rw [hb, ← ha, h, Bool.true_and], kb⟩
    · rename_i h
      exact ⟨by rw [← ha, Bool.not_eq_true _ |>.mp h, Bool.false_and], ka⟩
  | .ite _ t e, k, hk => by
    obtain ⟨ha, ka⟩ := allFrom_ok p t k hk
    simp only [allFrom, Code.all]
    split
    · rename_i h
      obtain ⟨hb, kb⟩ := allFrom_ok p e _ ka
      exact ⟨by rw [hb, ← ha, h, Bool.true_and], kb⟩
    · rename_i h
      exact ⟨by rw [← ha, Bool.not_eq_true _ |>.mp h, Bool.false_and], ka⟩
  | .loop b _, k, hk => allFrom_ok p b k hk
  | .call n b, k, hk =>
    Code.memoCall_ok (n := n) (run := fun _ => allFrom p b k) (spec := fun c _ => c.all p) hk (allFrom_ok p b k hk)
  | .frame i b j, k, hk => by
    obtain ⟨hb, kb⟩ := allFrom_ok p b k hk
    simp only [allFrom, Code.all]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      exact ⟨by rw [hb, h.1, h.2, Bool.true_and, Bool.and_true], kb⟩
    · rename_i h
      refine ⟨?_, hk⟩
      cases hi : p i <;> cases hj : p j <;> simp_all
  | .icall i n b nx, k, hk => by
    obtain ⟨hb, kb⟩ := Code.memoCall_ok (n := n) (run := fun _ => allFrom p b k) (spec := fun c _ => c.all p) hk
      (allFrom_ok p b k hk)
    simp only [allFrom, Code.all]
    split
    · rename_i hi
      split
      · rename_i h
        obtain ⟨hn, kn⟩ := allFrom_ok p nx _ kb
        exact ⟨by rw [hn, ← hb, hi, h, Bool.true_and, Bool.true_and], kn⟩
      · rename_i h
        exact ⟨by rw [← hb, Bool.not_eq_true _ |>.mp h, Bool.and_false, Bool.false_and], kb⟩
    · rename_i hi
      exact ⟨by rw [Bool.not_eq_true _ |>.mp hi, Bool.false_and, Bool.false_and], hk⟩

/-- `Code.all p c`, going through the code of each function `c` calls once. -/
def Code.allOnce (p : I → Bool) (c : Code I C) : Bool := (Code.allFrom p c []).1

theorem Code.allOnce_eq (p : I → Bool) (c : Code I C) : c.allOnce p = c.all p :=
  (Code.allFrom_ok p c [] fun _ h => by cases h).1

end VG
