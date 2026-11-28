import Rind.X86_64.RsaPrivate
import Rind.X86_64.RsaKey
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA private key loading on x86_64

`RsaPrivateKey::new` checks a key's components as aws-lc's `RSA_check_key`
does, all but primality, and computes the Montgomery constants the private
operation takes. `rsa_private_key_new_spec` proves that a key it returns
meets `PrivKeyInv`, which `private_op_spec` takes, and holds the values it
was given, and that those meet `CrtRelations`, RFC 8017's relations between
the components: `n = p·q`, `dP = d mod (p - 1)`, `dP·e ≡ 1 (mod p - 1)`, the
same for `q`, and `qInv < p` with `qInv·q ≡ 1 (mod p)`. Beyond the entry
guard and the inputs' representation (each within its width, its words above
that width zero, and `n`'s top word nonzero), it assumes that
`HaveAvx512ForRsa`'s CPU checks return, for AVX-512 IFMA and AVX512_FP16, and
that `MontProducts` holds at the wider prime's width. Where `IfmaCrt::new`
sets pyca/verified-garbage's AVX-512 IFMA CRT up, `precompute_spec` proves
its values against `VG.Spec.Rsa.privatePrecompute`, as `IfmaCrtInv` states.
It characterizes the keys `new` returns, not which inputs it accepts.
-/

namespace rind.x86_64

namespace PrivKey

/-! ## The `PosInt` helpers key loading runs -/

/-- `p`'s words above its width are zero: the whole array is its value. Every
`PosInt` rind makes keeps this. -/
def Clean {N : Usize} (p : low.posint.PosInt N) : Prop :=
  wordsNat p.words.val = wordsNat (lowWords p p.used)

theorem clean_lowWords {N : Usize} {p : low.posint.PosInt N} (hc : Clean p) (hu : p.used.val ≤ N.val)
    {k : Nat} (hk : p.used.val ≤ k) :
    wordsNat (lowWords p k) = wordsNat (lowWords p p.used) := by
  have hlt := wordsNat_lt' (lowWords p p.used)
  rw [lowWords_length p hu] at hlt
  have h : wordsNat (lowWords p k) = wordsNat p.words.val % 2 ^ (64 * k) := wordsNat_take_mod _ _
  rw [h, hc]
  exact Nat.mod_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The words of a clean value above its width are zeros. -/
theorem clean_drop {N : Usize} {p : low.posint.PosInt N} (hc : Clean p) (hu : p.used.val ≤ N.val) :
    p.words.val.drop p.used.val = List.replicate (N.val - p.used.val) 0#u64 := by
  have hsplit := wordsNat_take_drop p.words.val p.used.val
  have hlen : (p.words.val.take p.used.val).length = p.used.val := by simp; omega
  have h0 : wordsNat (p.words.val.drop p.used.val) = 0 := by
    have : wordsNat p.words.val = wordsNat (p.words.val.take p.used.val) := hc
    rw [hlen] at hsplit
    have hpos : 0 < 2 ^ (64 * p.used.val) := by positivity
    rcases Nat.mul_eq_zero.mp (show 2 ^ (64 * p.used.val) * wordsNat (p.words.val.drop p.used.val) = 0 by
      omega) with h | h
    · omega
    · exact h
  apply wordsNat_inj
  · simp
  · rw [h0, wordsNat_replicate_zero]

theorem wordsNat_take_add (l : List U64) (a b : Nat) :
    wordsNat (l.take (a + b)) = wordsNat (l.take a) + 2 ^ (64 * min a l.length) * wordsNat ((l.drop a).take b) := by
  rw [List.take_add, wordsNat_append]
  simp

theorem wordsNat_eq_zero_iff (l : List U64) : wordsNat l = 0 ↔ ∀ x ∈ l, x.val = 0 := by
  induction l with
  | nil => simp [wordsNat_nil]
  | cons y l ih =>
    rw [wordsNat_cons, List.forall_mem_cons, ← ih]
    have : (0 : Nat) < 2 ^ 64 := by norm_num
    constructor
    · intro h
      refine ⟨by omega, ?_⟩
      rcases Nat.mul_eq_zero.mp (show 2 ^ 64 * wordsNat l = 0 by omega) with h' | h'
      · omega
      · exact h'
    · rintro ⟨h1, h2⟩; rw [h1, h2]; simp

/-- `fit`'s loop zeroes the words from `words` to the width, and `high` is zero
just when they all were. -/
theorem fit_loop_spec {N : Usize} (w0 : List U64) (hw0 : w0.length = N.val) (words used : Usize)
    (huN : used.val ≤ N.val) (iter : core.ops.range.Range Usize)
    (a : Std.Array U64 N) (high : U64) (hend : iter.end = used) (hs1 : words.val ≤ iter.start.val)
    (hs2 : iter.start.val ≤ used.val)
    (ha : a.val = w0.take words.val ++ List.replicate (iter.start.val - words.val) 0#u64 ++
      w0.drop iter.start.val)
    (hh : high.val = 0 ↔ ∀ x ∈ (w0.drop words.val).take (iter.start.val - words.val), x.val = 0) :
    low.posint.PosInt.fit_loop iter a high ⦃ r =>
      r.1.val = w0.take words.val ++ List.replicate (used.val - words.val) 0#u64 ++ w0.drop used.val ∧
      (r.2.val = 0 ↔ ∀ x ∈ (w0.drop words.val).take (used.val - words.val), x.val = 0) ⦄ := by
  unfold low.posint.PosInt.fit_loop
  apply loop.spec_decr_nat (fun st => used.val - st.1.start.val)
    (fun st : core.ops.range.Range Usize × Std.Array U64 N × U64 =>
      st.1.end = used ∧ words.val ≤ st.1.start.val ∧ st.1.start.val ≤ used.val ∧
      st.2.1.val = w0.take words.val ++ List.replicate (st.1.start.val - words.val) 0#u64 ++
        w0.drop st.1.start.val ∧
      (st.2.2.val = 0 ↔ ∀ x ∈ (w0.drop words.val).take (st.1.start.val - words.val), x.val = 0))
  · rintro ⟨it, a, h⟩ ⟨he, hs1, hs2, ha, hh⟩
    simp only at he hs1 hs2 ha hh ⊢
    unfold low.posint.PosInt.fit_loop.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      simp only
      rw [he] at hlt hen
      have hj : it.start.val < w0.length := by omega
      set P := w0.take words.val ++ List.replicate (it.start.val - words.val) 0#u64 with hP
      have hpre : P.length = it.start.val := by rw [hP]; simp; omega
      have hav : a.val = P ++ w0[it.start.val]'hj :: w0.drop (it.start.val + 1) := by
        rw [ha, List.drop_eq_getElem_cons hj]
      have hal : it.start.val < a.val.length := by
        rw [hav]; simp only [List.length_append, List.length_cons, List.length_drop, hpre]; omega
      step as ⟨x, hx⟩
      have hxv : x = w0[it.start.val]'hj := by
        rw [hx]
        simp only [List.getElem_of_eq hav]
        rw [List.getElem_append_right (le_of_eq hpre)]
        simp [hpre]
      step as ⟨h1, hh1, _⟩
      step as ⟨a1, ha1⟩
      have hn : it'.start.val - words.val = (it.start.val - words.val) + 1 := by omega
      refine ⟨by rw [hen], by omega, by omega, ?_, ?_, by omega⟩
      · rw [ha1, Std.Array.set_val_eq, hav, List.set_append_right _ _ (le_of_eq hpre), hpre,
          Nat.sub_self, List.set_cons_zero, hn, hst, List.replicate_succ', hP]
        simp
      · rw [hn, List.take_add_one, hh1, UScalar.val_or, Nat.or_eq_zero_iff, hh]
        have hget : (w0.drop words.val)[it.start.val - words.val]? = some (w0[it.start.val]'hj) := by
          rw [List.getElem?_drop]
          simp [show words.val + (it.start.val - words.val) = it.start.val by omega, hj]
        rw [hget, ← hxv]
        simp [or_imp, forall_and]
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      have hu : it.start.val = used.val := by rw [he] at hlt; omega
      rw [hu] at ha hh
      exact ⟨ha, hh⟩
  · exact ⟨hend, hs1, hs2, ha, hh⟩

/-- `fit`'s loop over an empty range changes nothing. -/
theorem fit_loop_empty {N : Usize} (iter : core.ops.range.Range Usize) (a : Std.Array U64 N) (high : U64)
    (h : ¬ iter.start.val < iter.end.val) :
    low.posint.PosInt.fit_loop iter a high ⦃ r => r.1 = a ∧ r.2 = high ⦄ := by
  unfold low.posint.PosInt.fit_loop
  apply loop.spec_decr_nat (fun _ => 0)
    (fun st : core.ops.range.Range Usize × Std.Array U64 N × U64 => st = (iter, a, high))
  · rintro ⟨it, a', h'⟩ hst
    simp only [Prod.mk.injEq] at hst
    obtain ⟨rfl, rfl, rfl⟩ := hst
    unfold low.posint.PosInt.fit_loop.body
    step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
    subst ho'
    simp [WP.spec_ok]
  · rfl

/-- `fit` sets a clean value's width to `words`, keeping its value modulo
`2^(64·words)`, and returns whether the value fits there. -/
theorem fit_spec {N : Usize} (self : low.posint.PosInt N) (words : Usize) (hw : words.val ≤ N.val)
    (hu : self.used.val ≤ N.val) (hc : Clean self) :
    low.posint.PosInt.fit self words ⦃ r => r.2.used = words ∧ Clean r.2 ∧
      wordsNat (lowWords r.2 words) = wordsNat (lowWords self self.used) % 2 ^ (64 * words.val) ∧
      (r.1 = true ↔ wordsNat (lowWords self self.used) < 2 ^ (64 * words.val)) ⦄ := by
  unfold low.posint.PosInt.fit
  have hwN : (words ≤ N) = true := by simp; scalar_tac
  simp only [massert, hwN, ↓reduceIte, bind_ok]
  have hw0 : self.words.val.length = N.val := by simp
  have hz := clean_drop hc hu
  set V := wordsNat (lowWords self self.used) with hV
  have hVlt : V < 2 ^ (64 * self.used.val) := by
    have := wordsNat_lt' (lowWords self self.used); rwa [lowWords_length self hu] at this
  have htake : wordsNat (self.words.val.take words.val) = V % 2 ^ (64 * words.val) := by
    rw [wordsNat_take_mod, hc]
  by_cases hwu : words.val ≤ self.used.val
  · step with fit_loop_spec self.words.val hw0 words self.used hu
      { start := words, «end» := self.used } self.words 0#u64 rfl le_rfl hwu
      (by simp) (by simp) as ⟨a, high, ha, hh⟩
    have ha' : a.val = self.words.val.take words.val ++ List.replicate (N.val - words.val) 0#u64 := by
      rw [ha, hz, List.append_assoc, List.replicate_append_replicate]; congr 2; omega
    have hlow : lowWords ({ words := a, used := words } : low.posint.PosInt N) words =
        self.words.val.take words.val := by
      show a.val.take words.val = _
      rw [ha', List.take_append_of_le_length (by simp; omega), List.take_of_length_le (by simp)]
    have hh0 : high = 0#u64 ↔ high.val = 0 := by
      constructor
      · intro h; rw [h]; rfl
      · intro h; exact (UScalar.eq_equiv high 0#u64).mpr (by rw [h]; rfl)
    refine ⟨?_, by rw [hlow, htake], ?_⟩
    · show wordsNat a.val = wordsNat (lowWords ({ words := a, used := words } : low.posint.PosInt N) words)
      rw [hlow, ha', wordsNat_append, wordsNat_replicate_zero, mul_zero, add_zero]
    · have hsplit := wordsNat_take_add self.words.val words.val (self.used.val - words.val)
      rw [show words.val + (self.used.val - words.val) = self.used.val by omega,
        Nat.min_eq_left (by omega)] at hsplit
      have hVu : V = wordsNat (self.words.val.take self.used.val) := rfl
      rw [← hVu] at hsplit
      have hwlt := wordsNat_lt' (self.words.val.take words.val)
      rw [List.length_take, Nat.min_eq_left (by omega)] at hwlt
      simp only [decide_eq_true_eq]
      rw [hh0, hh, ← wordsNat_eq_zero_iff]
      constructor
      · intro h0; rw [hsplit, h0]; omega
      · intro hlt
        by_contra hne
        have : 2 ^ (64 * words.val) ≤ 2 ^ (64 * words.val) * wordsNat ((self.words.val.drop words.val).take
            (self.used.val - words.val)) := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hne)
        omega
  · step with fit_loop_empty { start := words, «end» := self.used } self.words 0#u64 (by simp; omega)
      as ⟨a, high, ha, hh⟩
    subst ha hh
    simp only
    have hmod : V % 2 ^ (64 * words.val) = V :=
      Nat.mod_eq_of_lt (lt_of_lt_of_le hVlt (Nat.pow_le_pow_right (by norm_num) (by omega)))
    refine ⟨?_, htake, ?_⟩
    · show wordsNat self.words.val = wordsNat (self.words.val.take words.val)
      rw [htake, hmod, hc]
    · constructor
      · intro _; rw [← hmod]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
      · intro _; rfl

/-! ## `reduce_even`: a value modulo an even modulus -/

/-- The value `reduce_even` holds, in `b` when `in_b` and in `a` otherwise. -/
def held {M : Usize} (a b : low.posint.PosInt M) (in_b : Bool) : low.posint.PosInt M :=
  if in_b then b else a

/-- What one step of `reduce_even` adds to its value `x`: `addend`'s value, at
width `k`, or `x` itself without one. -/
def addendVal {M : Usize} (k : Usize) (x : Nat) : Option (low.posint.PosInt M) → Nat
  | none => x
  | some y => wordsNat (lowWords y k)

/-- One step of `reduce_even` adds to its value, at `m`'s width, `addend` or
the value itself, modulo `m`, into the other of `a` and `b`. -/
theorem reduce_step_spec {M : Usize} (a b m : low.posint.PosInt M) (in_b : Bool)
    (addend : Option (low.posint.PosInt M)) (hk : m.used.val ≤ M.val)
    (ha : a.used = m.used) (hb : b.used = m.used)
    (hx : wordsNat (lowWords (held a b in_b) m.used) < wordsNat (lowWords m m.used))
    (hy : ∀ y, addend = some y → y.used = m.used ∧ wordsNat (lowWords y m.used) < wordsNat (lowWords m m.used)) :
    low.posint.PosInt.reduce_step a b in_b addend m ⦃ r =>
      r.1.used = m.used ∧ r.2.used = m.used ∧
      wordsNat (lowWords (held r.1 r.2 !in_b) m.used) =
        (wordsNat (lowWords (held a b in_b) m.used) +
          addendVal m.used (wordsNat (lowWords (held a b in_b) m.used)) addend) %
          wordsNat (lowWords m m.used) ⦄ := by
  unfold low.posint.PosInt.reduce_step low.posint.PosInt.as_mut_words low.posint.PosInt.as_words
  step as ⟨x, hs, hsl, hback⟩
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step as ⟨y, ht, htl, hback1⟩
  obtain ⟨t, back1⟩ := y
  dsimp only at *
  step as ⟨m1, hm1, hm1l⟩
  have hsv : s.val = lowWords a m.used := by simp [lowWords, hs, ha]
  have htv : t.val = lowWords b m.used := by simp [lowWords, ht, hb]
  have hmv : m1.val = lowWords m m.used := by simp [lowWords, hm1]
  rw [ha] at hsl
  rw [hb] at htl
  have hA := mont_into_post a m back hback hk
  have hB := mont_into_post b m back1 hback1 hk
  rw [ha]; rw [hb]
  cases in_b <;> cases addend <;>
    simp only [held, Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte, addendVal] at hx ⊢
  · step with bignum_modadd_spec t s s m1 (by rw [hsl, htl]) (by rw [hsl, htl]) (by rw [hm1l, htl])
      (by rw [hsv, hmv]; exact hx) (by rw [hsv, hmv]; exact hx) as ⟨b2, hb2l, hb2v⟩
    rw [(hB b2 (by rw [hb2l, htl])).1, hb2v, hsv, hmv]
  · rename_i y
    obtain ⟨hyu, hyv⟩ := hy y rfl
    step as ⟨s1, hs1, hs1l⟩
    have hs1v : s1.val = lowWords y m.used := by simp [lowWords, hs1, hyu]
    step with bignum_modadd_spec t s s1 m1 (by rw [hsl, htl]) (by rw [hs1l, hyu, htl]) (by rw [hm1l, htl])
      (by rw [hsv, hmv]; exact hx) (by rw [hs1v, hmv]; exact hyv) as ⟨b2, hb2l, hb2v⟩
    rw [(hB b2 (by rw [hb2l, htl])).1, hb2v, hsv, hs1v, hmv]
  · step with bignum_modadd_spec s t t m1 (by rw [hsl, htl]) (by rw [hsl, htl]) (by rw [hm1l, hsl])
      (by rw [htv, hmv]; exact hx) (by rw [htv, hmv]; exact hx) as ⟨a2, ha2l, ha2v⟩
    rw [(hA a2 (by rw [ha2l, hsl])).1, ha2v, htv, hmv]
  · rename_i y
    obtain ⟨hyu, hyv⟩ := hy y rfl
    step as ⟨s1, hs1, hs1l⟩
    have hs1v : s1.val = lowWords y m.used := by simp [lowWords, hs1, hyu]
    step with bignum_modadd_spec s t s1 m1 (by rw [htl, hsl]) (by rw [hs1l, hyu, hsl]) (by rw [hm1l, hsl])
      (by rw [htv, hmv]; exact hx) (by rw [hs1v, hmv]; exact hyv) as ⟨a2, ha2l, ha2v⟩
    rw [(hA a2 (by rw [ha2l, hsl])).1, ha2v, htv, hs1v, hmv]

/-- Doubling `Y mod M` modulo `M` is doubling `Y`. -/
theorem double_mod (Y M : Nat) : (Y % M + Y % M) % M = (Y + Y) % M := (Nat.add_mod Y Y M).symm

/-- `reduce_even`'s innermost loop doubles its value, modulo `m`, once for
each step left in `iter`. -/
theorem reduce_even_loop2_spec {M : Usize} (mw : Std.Array U64 M) (k : Usize)
    (iter : core.ops.range.Range Usize) (a b : low.posint.PosInt M) (in_b : Bool) (X : Nat)
    (hk : k.val ≤ M.val) (hM : 0 < wordsNat (mw.val.take k.val)) (ha : a.used = k) (hb : b.used = k)
    (hs : iter.start.val ≤ iter.end.val)
    (hv : wordsNat (lowWords (held a b in_b) k) = X * 2 ^ iter.start.val % wordsNat (mw.val.take k.val)) :
    low.posint.PosInt.reduce_even_loop0_loop0_loop0 iter mw k a b in_b ⦃ r =>
      r.1.used = k ∧ r.2.1.used = k ∧
      wordsNat (lowWords (held r.1 r.2.1 r.2.2) k) = X * 2 ^ iter.end.val % wordsNat (mw.val.take k.val) ⦄ := by
  unfold low.posint.PosInt.reduce_even_loop0_loop0_loop0
  set Mv := wordsNat (mw.val.take k.val) with hMv
  apply loop.spec_decr_nat (fun st => st.1.end.val - st.1.start.val)
    (fun st : core.ops.range.Range Usize × low.posint.PosInt M × low.posint.PosInt M × Bool =>
      st.1.end = iter.end ∧ st.1.start.val ≤ st.1.end.val ∧ st.2.1.used = k ∧ st.2.2.1.used = k ∧
      wordsNat (lowWords (held st.2.1 st.2.2.1 st.2.2.2) k) = X * 2 ^ st.1.start.val % Mv)
  · rintro ⟨it, a, b, in_b⟩ ⟨he, hs, ha, hb, hv⟩
    simp only at he hs ha hb hv ⊢
    unfold low.posint.PosInt.reduce_even_loop0_loop0_loop0.body
    by_cases hlt : it.start.val < it.end.val
    · step with core.iter.range.IteratorRange.next_Usize_some_spec as ⟨o, it', ho', hst, hen⟩
      subst ho'
      simp only
      have hm : ({ words := mw, used := k } : low.posint.PosInt M).used = k := rfl
      have hmv : wordsNat (lowWords ({ words := mw, used := k } : low.posint.PosInt M) k) = Mv := rfl
      step with reduce_step_spec a b { words := mw, used := k } in_b none hk ha hb
        (by rw [hmv, hv]; exact Nat.mod_lt _ hM) (by simp) as ⟨a', b', ha', hb', hv'⟩
      have hen' : it'.end.val = it.end.val := by rw [hen]
      refine ⟨by rw [hen, he], by omega, ha', hb', ?_, by omega⟩
      have hnot : (decide ¬in_b = true) = !in_b := by cases in_b <;> rfl
      rw [hnot, hv', hmv, addendVal, hv, double_mod, hst, pow_succ]
      congr 1; ring
    · step with core.iter.range.IteratorRange.next_Usize_none_spec as ⟨o, it', ho', hit⟩
      subst ho'
      simp only [WP.spec_ok]
      have hu : it.start.val = iter.end.val := by rw [← he]; omega
      rw [hu] at hv
      exact ⟨ha, hb, hv⟩
  · exact ⟨rfl, hs, ha, hb, hv⟩

/-- Shifting the next `b` bits of `w` into `Y`, modulo `M`. -/
theorem shift_in (Mv R0 w b e : Nat) (hbe : b * (e + 1) ≤ 64) :
    ((R0 * 2 ^ (64 - b * (e + 1)) + w / 2 ^ (b * (e + 1))) % Mv * 2 ^ b % Mv + w / 2 ^ (b * e) % 2 ^ b) % Mv =
      (R0 * 2 ^ (64 - b * e) + w / 2 ^ (b * e)) % Mv := by
  set Y := R0 * 2 ^ (64 - b * (e + 1)) + w / 2 ^ (b * (e + 1))
  rw [Nat.mod_add_mod]
  have h1 : (Y % Mv * 2 ^ b + w / 2 ^ (b * e) % 2 ^ b) % Mv = (Y * 2 ^ b + w / 2 ^ (b * e) % 2 ^ b) % Mv :=
    Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ (Nat.mod_modEq Y Mv))
  rw [h1]
  congr 1
  have h2 : 2 ^ (64 - b * (e + 1)) * 2 ^ b = 2 ^ (64 - b * e) := by
    rw [← pow_add]; congr 1; rw [Nat.mul_succ] at hbe ⊢; omega
  have h3 : w / 2 ^ (b * (e + 1)) = w / 2 ^ (b * e) / 2 ^ b := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.mul_succ]
  simp only [Y, add_mul, h3]
  rw [mul_assoc, h2, add_assoc, Nat.div_add_mod']

theorem rev_next_spec (r : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepUsize) r ⦃ o r' =>
      r'.iter.start = r.iter.start ∧
        (if r.iter.start.val < r.iter.end.val then o = some r'.iter.end ∧ r'.iter.end.val + 1 = r.iter.end.val
          else o = none) ⦄ := by
  unfold core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
  simp only [
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back, core.iter.range.StepUsize,
    core.iter.range.UScalarStep, core.iter.range.UScalarStep.backward_checked]
  by_cases hlt : r.iter.start.val < r.iter.end.val
  · have hb : liftFun2 core.cmp.impls.PartialOrdUsize.lt r.iter.start r.iter.end = ok true := by
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, hlt]
    have h1 : (1#usize).val ≤ r.iter.end.val := by simp; omega
    simp only [hb, bind_ok, ↓reduceIte, h1, ↓reduceDIte, hlt]
    simp [UScalar.ofNatCore_val_eq]; omega
  · have hb : liftFun2 core.cmp.impls.PartialOrdUsize.lt r.iter.start r.iter.end = ok false := by
      simp [liftFun2, core.cmp.impls.PartialOrdUsize.lt, hlt]
    simp [hb, hlt, WP.spec_ok]

/-- A value whose words above the first are zero is its first word. -/
theorem wordsNat_first {M : Usize} (p : low.posint.PosInt M) (x : U64) (k : Nat) (hk1 : 1 ≤ k)
    (hp : p.words.val = x :: List.replicate (M.val - 1) 0#u64) :
    wordsNat (lowWords p k) = x.val := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  simp only [lowWords, hp, List.take_succ_cons, wordsNat_cons, List.take_replicate, wordsNat_replicate_zero]
  simp

/-- `reduce_even`'s middle loop shifts the word `w` into its value `R0`,
`bits` at a time from the top, modulo `m`. -/
theorem reduce_even_loop1_spec {N M : Usize} (sw : Std.Array U64 N) (mw : Std.Array U64 M) (k bits j : Usize)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (a b addend : low.posint.PosInt M)
    (in_b : Bool) (R0 w : Nat)
    (hk : k.val ≤ M.val) (hk1 : 1 ≤ k.val) (hbits : bits.val = 64 ∨ bits.val = 1)
    (hbM : 2 ^ bits.val ≤ wordsNat (mw.val.take k.val)) (hjl : j.val < sw.val.length)
    (hw : (sw.val[j.val]'hjl).val = w)
    (hs : iter.iter.start.val = 0) (he : iter.iter.end.val * bits.val ≤ 64)
    (ha : a.used = k) (hb : b.used = k) (hau : addend.used = k)
    (had : addend.words.val.drop 1 = List.replicate (M.val - 1) 0#u64)
    (hv : wordsNat (lowWords (held a b in_b) k) =
      (R0 * 2 ^ (64 - bits.val * iter.iter.end.val) + w / 2 ^ (bits.val * iter.iter.end.val)) %
        wordsNat (mw.val.take k.val)) :
    low.posint.PosInt.reduce_even_loop0_loop0 iter sw mw k a b addend bits in_b j ⦃ r =>
      r.1.used = k ∧ r.2.1.used = k ∧ r.2.2.1.used = k ∧
      r.2.2.1.words.val.drop 1 = List.replicate (M.val - 1) 0#u64 ∧
      wordsNat (lowWords (held r.1 r.2.1 r.2.2.2) k) = (R0 * 2 ^ 64 + w) % wordsNat (mw.val.take k.val) ⦄ := by
  unfold low.posint.PosInt.reduce_even_loop0_loop0
  set Mv := wordsNat (mw.val.take k.val) with hMv
  have hM0 : 0 < Mv := lt_of_lt_of_le (Nat.two_pow_pos _) hbM
  have hb1 : 1 ≤ bits.val := by omega
  have hb64 : bits.val ≤ 64 := by omega
  apply loop.spec_decr_nat (fun st => st.1.iter.end.val)
    (fun st : core.iter.adapters.rev.Rev (core.ops.range.Range Usize) × low.posint.PosInt M ×
        low.posint.PosInt M × low.posint.PosInt M × Bool =>
      st.1.iter.start.val = 0 ∧ st.1.iter.end.val * bits.val ≤ 64 ∧
      st.2.1.used = k ∧ st.2.2.1.used = k ∧ st.2.2.2.1.used = k ∧
      st.2.2.2.1.words.val.drop 1 = List.replicate (M.val - 1) 0#u64 ∧
      wordsNat (lowWords (held st.2.1 st.2.2.1 st.2.2.2.2) k) =
        (R0 * 2 ^ (64 - bits.val * st.1.iter.end.val) + w / 2 ^ (bits.val * st.1.iter.end.val)) % Mv)
  · rintro ⟨it, a, b, addend, in_b⟩ ⟨hs, he, ha, hb, hau, had, hv⟩
    simp only at hs he ha hb hau had hv ⊢
    unfold low.posint.PosInt.reduce_even_loop0_loop0.body
    step with rev_next_spec as ⟨o, it1, hst, ho⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, he1⟩ := ho
      simp only
      set e := it1.iter.end.val with he_def
      have hbe : bits.val * (e + 1) ≤ 64 := by rw [he1, Nat.mul_comm]; exact he
      have hVlt : wordsNat (lowWords (held a b in_b) k) < Mv := by rw [hv]; exact Nat.mod_lt _ hM0
      step with reduce_even_loop2_spec mw k { start := 0#usize, «end» := bits } a b in_b
        (wordsNat (lowWords (held a b in_b) k)) hk (by rw [← hMv]; exact hM0) ha hb (by simp)
        (by show _ = _ * 2 ^ (0 : Nat) % _; rw [pow_zero, mul_one]; exact (Nat.mod_eq_of_lt hVlt).symm)
        as ⟨a3, b1, in_b1, ha3, hb1', hv3⟩
      step as ⟨i1, hi1⟩
      have hi1v : i1.val = w := by rw [hi1]; exact hw
      have heb : e * bits.val < 64 := by rw [Nat.mul_succ] at hbe; rw [Nat.mul_comm]; omega
      step as ⟨i2, hi2⟩
      step as ⟨i3, hi3, _⟩
      step as ⟨i4, hi4⟩
      step as ⟨i5, hi5, _⟩
      step as ⟨i6, hi6, _⟩
      step as ⟨a4, ha4⟩
      have hi5v : i5.val = 2 ^ bits.val - 1 := by
        rw [hi5, hi4]
        rcases hbits with h | h <;> rw [h] <;> decide
      have hi6v : i6.val = w / 2 ^ (bits.val * e) % 2 ^ bits.val := by
        rw [hi6, UScalar.val_and, hi3, hi5v, hi2, hi1v, Nat.shiftRight_eq_div_pow,
          Nat.and_two_pow_sub_one_eq_mod, Nat.mul_comm]
      have ha4v : a4.val = i6 :: List.replicate (M.val - 1) 0#u64 := by
        rw [ha4, Std.Array.set_val_eq]
        have hl := addend.words.property
        rcases hwd : addend.words.val with _ | ⟨x0, rest⟩
        · rw [hwd] at hl; simp only [List.length_nil] at hl; omega
        · rw [hwd] at had; simp only [List.drop_succ_cons, List.drop_zero] at had; subst had; simp
      have hadv : wordsNat (lowWords ({ words := a4, used := addend.used } : low.posint.PosInt M) k) = i6.val :=
        wordsNat_first _ i6 k hk1 ha4v
      have hV3 : wordsNat (lowWords (held a3 b1 in_b1) k) < Mv := by rw [hv3]; exact Nat.mod_lt _ hM0
      step with reduce_step_spec a3 b1 { words := mw, used := k } in_b1
        (some { words := a4, used := addend.used }) hk ha3 hb1' hV3
        (by
          intro y hy; cases hy
          exact ⟨hau, by rw [hadv, hi6v]; exact lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hbM⟩)
        as ⟨a5, b2, ha5, hb2, hv5⟩
      have hnot : (decide ¬in_b1 = true) = !in_b1 := by cases in_b1 <;> rfl
      refine ⟨by rw [hst]; exact hs, le_of_lt heb, ha5, hb2, hau, by rw [ha4v]; rfl, ?_, by omega⟩
      rw [hnot, hv5, addendVal, hadv, hi6v, hv3, hv, ← he1]
      exact shift_in Mv R0 w bits.val e hbe
    · obtain rfl := ho
      simp only [WP.spec_ok]
      have he0 : it.iter.end.val = 0 := by omega
      rw [he0, Nat.mul_zero, Nat.sub_zero, pow_zero, Nat.div_one] at hv
      exact ⟨ha, hb, hau, had, hv⟩
  · exact ⟨hs, he, ha, hb, hau, had, hv⟩

/-- The value of the words of `sw` from `e` up to `used`. -/
def topVal {N : Usize} (sw : Std.Array U64 N) (used e : Nat) : Nat :=
  wordsNat ((sw.val.take used).drop e)

theorem topVal_step {N : Usize} (sw : Std.Array U64 N) (used j : Nat) (hj : j < used) (hu : used ≤ N.val)
    (hjl : j < sw.val.length) :
    topVal sw used j = (sw.val[j]'hjl).val + 2 ^ 64 * topVal sw used (j + 1) := by
  unfold topVal
  have hlt : j < (sw.val.take used).length := by simp; omega
  rw [List.drop_eq_getElem_cons hlt, wordsNat_cons, List.getElem_take]

/-- `reduce_even`'s outer loop shifts in the words below `iter`'s end, one at
a time from the top, modulo `m`. -/
theorem reduce_even_loop0_spec {N M : Usize} (sw : Std.Array U64 N) (mw : Std.Array U64 M) (k bits : Usize)
    (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Usize)) (a b addend : low.posint.PosInt M)
    (in_b : Bool) (used : Nat)
    (hk : k.val ≤ M.val) (hk1 : 1 ≤ k.val) (hbits : bits.val = 64 ∨ bits.val = 1)
    (hbM : 2 ^ bits.val ≤ wordsNat (mw.val.take k.val)) (hu : used ≤ N.val)
    (hs : iter.iter.start.val = 0) (he : iter.iter.end.val ≤ used)
    (ha : a.used = k) (hb : b.used = k) (hau : addend.used = k)
    (had : addend.words.val.drop 1 = List.replicate (M.val - 1) 0#u64)
    (hv : wordsNat (lowWords (held a b in_b) k) = topVal sw used iter.iter.end.val % wordsNat (mw.val.take k.val)) :
    low.posint.PosInt.reduce_even_loop0 iter sw mw k a b addend bits in_b ⦃ r =>
      r.1.used = k ∧ r.2.1.used = k ∧
      wordsNat (lowWords (held r.1 r.2.1 r.2.2) k) = topVal sw used 0 % wordsNat (mw.val.take k.val) ⦄ := by
  unfold low.posint.PosInt.reduce_even_loop0
  set Mv := wordsNat (mw.val.take k.val) with hMv
  have hM0 : 0 < Mv := lt_of_lt_of_le (Nat.two_pow_pos _) hbM
  have hb1 : 1 ≤ bits.val := by omega
  have hbP : bits.val * (64 / bits.val) = 64 := by rcases hbits with h | h <;> rw [h]
  apply loop.spec_decr_nat (fun st => st.1.iter.end.val)
    (fun st : core.iter.adapters.rev.Rev (core.ops.range.Range Usize) × low.posint.PosInt M ×
        low.posint.PosInt M × low.posint.PosInt M × Bool =>
      st.1.iter.start.val = 0 ∧ st.1.iter.end.val ≤ used ∧
      st.2.1.used = k ∧ st.2.2.1.used = k ∧ st.2.2.2.1.used = k ∧
      st.2.2.2.1.words.val.drop 1 = List.replicate (M.val - 1) 0#u64 ∧
      wordsNat (lowWords (held st.2.1 st.2.2.1 st.2.2.2.2) k) = topVal sw used st.1.iter.end.val % Mv)
  · rintro ⟨it, a, b, addend, in_b⟩ ⟨hs, he, ha, hb, hau, had, hv⟩
    simp only at hs he ha hb hau had hv ⊢
    unfold low.posint.PosInt.reduce_even_loop0.body
    step with rev_next_spec as ⟨o, it1, hst, ho⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, he1⟩ := ho
      simp only
      set j := it1.iter.end with hj_def
      have hjl : j.val < sw.val.length := by have := sw.property; omega
      step as ⟨i1, hi1⟩
      step as ⟨iter2, hiter2⟩
      have hR0 : wordsNat (lowWords (held a b in_b) k) < Mv := by rw [hv]; exact Nat.mod_lt _ hM0
      have hw64 : (sw.val[j.val]'hjl).val < 2 ^ 64 := (sw.val[j.val]'hjl).hBounds
      step with reduce_even_loop1_spec sw mw k bits j iter2 a b addend in_b
        (wordsNat (lowWords (held a b in_b) k)) (sw.val[j.val]'hjl).val hk hk1 hbits hbM hjl rfl
        (by rw [hiter2]; rfl) (by rw [hiter2, hi1, Nat.mul_comm, hbP])
        ha hb hau had
        (by
          rw [hiter2, hi1, hbP, Nat.sub_self, pow_zero, mul_one, Nat.div_eq_of_lt hw64, add_zero]
          exact (Nat.mod_eq_of_lt hR0).symm)
        as ⟨a3, b1, addend1, in_b1, ha3, hb3, hau3, had3, hv3⟩
      have hjv : it1.iter.end.val = j.val := rfl
      refine ⟨by rw [hst]; exact hs, by omega, ha3, hb3, hau3, had3, ?_, by omega⟩
      rw [hv3, hv, ← he1, topVal_step sw used j.val (by omega) hu hjl]
      have hmod : (topVal sw used (j.val + 1) % Mv * 2 ^ 64 + (sw.val[j.val]'hjl).val) % Mv =
          (topVal sw used (j.val + 1) * 2 ^ 64 + (sw.val[j.val]'hjl).val) % Mv :=
        Nat.ModEq.add_right _ (Nat.ModEq.mul_right _ (Nat.mod_modEq _ _))
      rw [hmod]; congr 1; ring
    · obtain rfl := ho
      simp only [WP.spec_ok]
      have he0 : it.iter.end.val = 0 := by omega
      rw [he0] at hv
      exact ⟨ha, hb, hv⟩
  · exact ⟨hs, he, ha, hb, hau, had, hv⟩

/-- `reduce_even` reduces `self` modulo `m`, which may be even, given `m`'s
top word is nonzero and `m` is at least two. -/
theorem reduce_even_spec {N M : Usize} (self : low.posint.PosInt N) (m : low.posint.PosInt M)
    (hMN : M.val < N.val) (hk1 : 1 ≤ m.used.val) (hk : m.used.val ≤ M.val) (hu : self.used.val ≤ N.val)
    (htop : 2 ^ (64 * (m.used.val - 1)) ≤ wordsNat (lowWords m m.used))
    (h2 : 2 ≤ wordsNat (lowWords m m.used)) :
    low.posint.PosInt.reduce_even self m ⦃ r => r.used = m.used ∧
      wordsNat (lowWords r m.used) = wordsNat (lowWords self self.used) % wordsNat (lowWords m m.used) ⦄ := by
  unfold low.posint.PosInt.reduce_even low.posint.PosInt.zero
  have hMN' : (M < N) = true := by simp; scalar_tac
  simp only [massert, hMN', ↓reduceIte, bind_ok]
  step with clone_spec as ⟨b, hb⟩
  simp only [lift, bind_ok]
  set Mv := wordsNat (lowWords m m.used) with hMv
  set i := core.num.Usize.saturating_sub self.used (core.num.Usize.saturating_sub m.used 1#usize) with hi_def
  have hiv : i.val = self.used.val - (m.used.val - 1) := by
    rw [hi_def, usize_saturating_sub_val, usize_saturating_sub_val]; rfl
  step*
  case h0 => show i ≤ self.used; scalar_tac
  case h =>
    have hl : top.length ≤ m.used.val - 1 := by rw [top_post1, hiv]; omega
    have := Slice.len_val top
    show top.len ≤ M
    scalar_tac
  have hl : top.length ≤ m.used.val - 1 := by rw [top_post1, hiv]; omega
  rw [show (if m.used > 1#usize then ok (index_mut_back s1, 64#usize) else ok (index_mut_back s1, 1#usize) :
      Result (Std.Array U64 M × Usize)) =
      ok (index_mut_back s1, if m.used > 1#usize then 64#usize else 1#usize) by split <;> rfl]
  simp only [bind_ok]
  set bits := (if m.used > 1#usize then 64#usize else 1#usize) with hbits_def
  have hbits : bits.val = 64 ∨ bits.val = 1 := by rw [hbits_def]; split <;> simp
  have hbM : 2 ^ bits.val ≤ Mv := by
    rw [hbits_def]
    split
    · rename_i hgt
      have hgt' : 1 < m.used.val := by scalar_tac
      exact le_trans (Nat.pow_le_pow_right (by norm_num) (by show (64 : Nat) ≤ _; omega)) htop
    · simpa using h2
  have htl : top.val.length ≤ m.used.val - 1 := hl
  -- The top words, below `m`, start the value.
  have htopv : topVal self.words self.used.val i.val = wordsNat top.val := by
    rw [topVal, top_post, List.slice, List.drop_take, Array.val_to_slice]
  have htoplt : wordsNat top.val < Mv := by
    have := wordsNat_lt' top.val
    exact lt_of_lt_of_le (lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by omega))) htop
  have hav : wordsNat (lowWords ({ words := index_mut_back s1, used := m.used } : low.posint.PosInt M) m.used) =
      wordsNat top.val := by
    have hlen' : top.val.length ≤ M.val := by omega
    have hlenk : top.val.length ≤ m.used.val := by omega
    simp only [lowWords, s_post2, s1_post, Array.repeat_val, List.setSlice!, List.take_zero, List.nil_append,
      List.length_replicate, Nat.sub_zero]
    rw [Nat.min_eq_left hlen', List.take_length, Nat.zero_add, List.drop_replicate,
      List.take_append, List.take_of_length_le hlenk, wordsNat_append, List.take_replicate,
      wordsNat_replicate_zero, mul_zero, add_zero]
  step as ⟨iter, hiter⟩
  have hb' : b.used = m.used := by rw [hb]
  have hbd : b.words.val.drop 1 = List.replicate (M.val - 1) 0#u64 := by rw [hb]; simp [Array.repeat_val]
  step with reduce_even_loop0_spec self.words m.words m.used bits iter
    { words := index_mut_back s1, used := m.used } b b false self.used.val hk hk1 hbits hbM hu
    (by rw [hiter]; rfl) (by rw [hiter]; show i.val ≤ _; omega) rfl hb' hb' hbd
    (by
      simp only [held, Bool.false_eq_true, ↓reduceIte, hiter]
      rw [hav, htopv]; exact (Nat.mod_eq_of_lt htoplt).symm)
    as ⟨a2, b1, in_b, ha2, hb1, hv⟩
  have htop0 : topVal self.words self.used.val 0 = wordsNat (lowWords self self.used) := by
    simp [topVal, lowWords]
  rw [htop0] at hv
  cases in_b
  · simp only [held, Bool.false_eq_true, ↓reduceIte] at hv
    simp only [Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
    exact ⟨ha2, hv⟩
  · simp only [held, ↓reduceIte] at hv
    simp only [↓reduceIte, WP.spec_ok]
    exact ⟨hb1, hv⟩

/-! ## The other `PosInt` helpers key loading runs -/

theorem one_spec (N : Usize) (hN : 1 ≤ N.val) :
    low.posint.PosInt.one N ⦃ r => r.used.val = 1 ∧ r.words.val = 1#u64 :: List.replicate (N.val - 1) 0#u64 ⦄ := by
  unfold low.posint.PosInt.one low.posint.PosInt.zero
  step*
  refine ⟨rfl, ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, N.val = j + 1 := ⟨N.val - 1, by omega⟩
  simp [a_post, Array.repeat_val, hj, List.replicate_succ]

theorem sub_spec {N : Usize} (self b : low.posint.PosInt N) (hu : self.used.val ≤ N.val)
    (hle : wordsNat (lowWords b self.used) ≤ wordsNat (lowWords self self.used)) :
    low.posint.PosInt.sub self b ⦃ r => r.used = self.used ∧
      wordsNat (lowWords r self.used) = wordsNat (lowWords self self.used) - wordsNat (lowWords b self.used) ⦄ := by
  unfold low.posint.PosInt.sub low.posint.PosInt.zero low.posint.PosInt.as_mut_words
    low.posint.PosInt.as_words low.posint.PosInt.as_words_with_len_of
  step*
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step as ⟨s1, hs1, hs1l⟩
  step as ⟨s2, hs2, hs2l⟩
  have hs1v : s1.val = lowWords self self.used := by simp [lowWords, hs1]
  have hs2v : s2.val = lowWords b self.used := by simp [lowWords, hs2]
  step with bignum_optsub_spec s s1 s2 1#u64 (by rw [hs1l, x_post1]) (by rw [hs2l, x_post1])
    as ⟨s3, hs3l, hs3v⟩
  rw [ite_eq_right Nat.one_ne_zero, ite_eq_left (show wordsNat s2.val ≤ wordsNat s1.val by rw [hs1v, hs2v]; exact hle), hs1v, hs2v]
    at hs3v
  have hlw := (mont_into_post { self with words := Array.repeat N 0#u64 } self back x_post2 hu s3
    (by rw [hs3l, x_post1])).1
  rw [hlw, hs3v]

theorem word_spec (N : Usize) (w : U64) (hN : 1 ≤ N.val) :
    low.posint.PosInt.word N w ⦃ r => r.used.val = 1 ∧ r.words.val = w :: List.replicate (N.val - 1) 0#u64 ⦄ := by
  unfold low.posint.PosInt.word low.posint.PosInt.zero low.posint.PosInt.push_word
  have hN0 : ¬ (0#usize = N) := by intro h; rw [← h] at hN; simp at hN
  simp only [bind_ok, hN0, ↓reduceIte]
  step as ⟨a, ha⟩
  step as ⟨i, hi⟩
  simp only [bind_ok, core.result.Result.unwrap, WP.spec_ok]
  refine ⟨by rw [hi], ?_⟩
  obtain ⟨j, hj⟩ : ∃ j, N.val = j + 1 := ⟨N.val - 1, by omega⟩
  simp [ha, Array.repeat_val, hj, List.replicate_succ]

theorem montifier_spec {N : Usize} (self : low.posint.PosInt N) (hu : self.used.val ≤ N.val)
    (hodd : wordsNat (lowWords self self.used) % 2 = 1) :
    low.posint.PosInt.montifier self ⦃ r => r.used = self.used ∧
      wordsNat (lowWords r self.used) = 2 ^ (128 * self.used.val) % wordsNat (lowWords self self.used) ⦄ := by
  unfold low.posint.PosInt.montifier low.posint.PosInt.zero low.posint.PosInt.as_mut_words
    low.posint.PosInt.as_words
  step*
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step as ⟨s1, hs1, hs1l⟩
  step as ⟨y, hy, hyl, hyback⟩
  obtain ⟨t, back1⟩ := y
  dsimp only at *
  have hs1v : s1.val = lowWords self self.used := by simp [lowWords, hs1]
  step with bignum_montifier_spec s s1 t (by rw [hs1l, x_post1]) (by rw [hyl, x_post1])
    as ⟨s3, t3, hs3l, hs3v⟩
  have hv := hs3v (by rw [hs1v]; exact hodd)
  rw [hs1v, x_post1] at hv
  have hlw := (mont_into_post { self with words := Array.repeat N 0#u64 } self back x_post2 hu s3
    (by rw [hs3l, x_post1])).1
  rw [hlw, hv]

/-- A value's parity is its low word's. -/
theorem wordsNat_mod_two (l : List U64) (h : 0 < l.length) : wordsNat l % 2 = (l[0]'h).val % 2 := by
  cases l with
  | nil => simp at h
  | cons x l =>
    simp only [List.getElem_cons_zero, wordsNat_cons]
    rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 by norm_num, mul_assoc, Nat.add_mul_mod_self_left]

theorem is_even_spec {N : Usize} (self : low.posint.PosInt N) (hN : 1 ≤ N.val) (hc : Clean self) :
    low.posint.PosInt.is_even self ⦃ b => b = decide (wordsNat (lowWords self self.used) % 2 = 0) ⦄ := by
  unfold low.posint.PosInt.is_even
  step*
  have hl : 0 < self.words.val.length := by have := self.words.property; omega
  have hi1 : i1.val = i.val % 2 := by rw [i1_post, UScalar.val_and]; simp [Nat.and_one_is_mod]
  have hP : wordsNat (lowWords self self.used) % 2 = i.val % 2 := by
    rw [← hc, wordsNat_mod_two _ hl, i_post]
  rw [decide_eq_decide, UScalar.eq_equiv, hi1, hP]
  exact Iff.rfl

/-! ## `exponents_agree`: RFC 8017's relations between `d`, `dP`, and `e` -/

/-- `exponents_agree` checks that `dp` is `d mod (p - 1)` and an inverse of
`e` modulo `p - 1`, for a `p` of at least three whose top word is nonzero. -/
theorem exponents_agree_spec (p dp e : low.posint.PosInt 64#usize) (d : low.posint.PosInt 128#usize)
    (hpu1 : 1 ≤ p.used.val) (hpu : p.used.val ≤ 64)
    (htop : 2 ^ (64 * (p.used.val - 1)) < wordsNat (lowWords p p.used))
    (h3 : 3 ≤ wordsNat (lowWords p p.used))
    (hdu : d.used.val ≤ 128) (hdpu : dp.used.val ≤ 64) (heu : e.used.val ≤ 64) :
    mid.rsa_priv.exponents_agree p d dp e ⦃ b =>
      b = true ↔
        (wordsNat (lowWords d d.used) % (wordsNat (lowWords p p.used) - 1) = wordsNat (lowWords dp dp.used) ∧
          wordsNat (lowWords d d.used) % (wordsNat (lowWords p p.used) - 1) * wordsNat (lowWords e e.used) %
            (wordsNat (lowWords p p.used) - 1) = 1) ⦄ := by
  unfold mid.rsa_priv.exponents_agree
  set P := wordsNat (lowWords p p.used) with hP
  have h64 : (64#usize : Usize).val = 64 := rfl
  have h128 : (128#usize : Usize).val = 128 := rfl
  step with one_spec 64#usize (by rw [h64]; omega) as ⟨o, hou, how⟩
  have hov : wordsNat (lowWords o p.used) = 1 := wordsNat_first o 1#u64 p.used.val hpu1 how
  step with sub_spec p o (by rw [h64]; exact hpu) (by rw [hov]; omega) as ⟨p1, hp1u, hp1v⟩
  rw [hov] at hp1v
  have hp1v' : wordsNat (lowWords p1 p1.used) = P - 1 := by rw [hp1u]; exact hp1v
  step with reduce_even_spec d p1 (by rw [h64, h128]; omega) (by rw [hp1u]; exact hpu1)
    (by rw [hp1u, h64]; exact hpu) (by rw [h128]; exact hdu) (by rw [hp1v', hp1u]; omega)
    (by rw [hp1v']; omega) as ⟨dpp, hdppu, hdppv⟩
  rw [hp1v'] at hdppv
  have hdppu' : dpp.used.val = p.used.val := by rw [hdppu, hp1u]
  step with posint_mul_spec 128#usize dpp e (by rw [h64, h128]) (by rw [hdppu', h64]; exact hpu)
    (by rw [h64]; exact heu) as ⟨dpe, hdpeu, hdpev⟩
  step with equals_spec dpp dp (by rw [hdppu', h64]; exact hpu) (by rw [h64]; exact hdpu) as ⟨b, hb⟩
  step with reduce_even_spec dpe p1 (by rw [h64, h128]; omega) (by rw [hp1u]; exact hpu1)
    (by rw [hp1u, h64]; exact hpu) (by rw [h128, hdpeu]; omega) (by rw [hp1v', hp1u]; omega)
    (by rw [hp1v']; omega) as ⟨r1, hr1u, hr1v⟩
  rw [hp1v'] at hr1v
  step with fixed_one_spec p1 (by rw [hp1u]; exact hpu1) (by rw [hp1u, h64]; exact hpu) as ⟨o1, ho1u, ho1v⟩
  step with equals_spec r1 o1 (by rw [hr1u, hp1u, h64]; exact hpu) (by rw [ho1u, hp1u, h64]; exact hpu)
    as ⟨b1, hb1⟩
  have hdppv' : wordsNat (lowWords dpp dpp.used) = wordsNat (lowWords d d.used) % (P - 1) := by
    rw [hdppu]; exact hdppv
  rw [hb, hb1, hr1u, ho1u, ho1v, hr1v, hdpev, hdppv']
  simp

/-! ## `RsaPrivateKey::new` -/

theorem div_ceil_spec (a b : Usize) (hb : 0 < b.val) :
    core.num.Usize.div_ceil a b ⦃ r => r.val = (a.val + b.val - 1) / b.val ⦄ := by
  unfold core.num.Usize.div_ceil
  simp [show ¬ b.val = 0 by omega, WP.spec_ok, UScalar.ofNatCore_val_eq]

theorem contains_usize (lo hi x : Usize) :
    core.ops.range.RangeInclusive.contains core.cmp.PartialOrdUsize core.cmp.PartialOrdUsize
      core.cmp.PartialOrdUsize ⟨lo, hi, false⟩ x = ok (decide (lo.val ≤ x.val ∧ x.val ≤ hi.val)) := by
  by_cases h1 : lo.val ≤ x.val <;>
    simp [core.ops.range.RangeInclusive.contains, core.cmp.impls.PartialOrdUsize.le, liftFun2, h1]

/-! ## `IfmaCrt::new`: pyca/verified-garbage's CRT values -/

/-- `from_words` holds `words`, at most `N` of them, as a clean value of
their width. -/
theorem from_words_spec (N : Usize) (words : Slice U64) (hl : words.length ≤ N.val) :
    low.posint.PosInt.from_words N words ⦃ r => ∃ x, r = .Ok x ∧ x.used.val = words.length ∧
      lowWords x x.used = words.val ∧ Clean x ⦄ := by
  unfold low.posint.PosInt.from_words low.posint.PosInt.zero
  step*
  have hv : (index_mut_back s1).val = words.val ++ List.replicate (N.val - words.length) 0#u64 := by
    rw [s_post2, s1_post, Array.repeat_val]
    have := setSlice!_append [] (List.replicate words.length 0#u64) (List.replicate (N.val - words.length) 0#u64)
      words.val (by simp [Slice.length])
    rw [List.nil_append, ← List.replicate_add, Nat.add_sub_cancel' hl] at this
    simpa [Slice.length] using this
  have hlw : lowWords ({ words := index_mut_back s1, used := words.len } : low.posint.PosInt N)
      (words.len).val = words.val := by
    simp only [lowWords]
    rw [hv, Slice.len_val, List.take_left' rfl]
  refine ⟨_, rfl, by simp, hlw, ?_⟩
  unfold Clean
  rw [hlw]
  simp only
  rw [hv, wordsNat_append, wordsNat_replicate_zero, mul_zero, add_zero]

/-- `VG.Spec.Rsa.privatePrecompute` of an odd modulus of `2w` words, its top
word nonzero, and factors `P` and `Q` that fit `w` words, from 16: the
modulus's words and `R² mod N`'s, then `R_p² mod P`'s and `R_q² mod Q`'s,
`w` words each. -/
theorem private_precompute_eq (n nm pm qm : List U64) (P Q w : Nat) (hw : 16 ≤ w) (hw32 : w ≤ 32)
    (hn : n.length = 2 * w) (hnm : nm.length = 2 * w) (hpm : pm.length = w) (hqm : qm.length = w)
    (hodd : wordsNat n % 2 = 1) (htop : 2 ^ (64 * (2 * w - 1)) ≤ wordsNat n)
    (hpq : P * Q = wordsNat n) (hP : P < 2 ^ (64 * w)) (hQ : Q < 2 ^ (64 * w))
    (hnmv : wordsNat nm = 2 ^ (128 * (2 * w)) % wordsNat n)
    (hpmv : wordsNat pm = 2 ^ (128 * w) % P) (hqmv : wordsNat qm = 2 ^ (128 * w) % Q) :
    VG.Spec.Rsa.privatePrecompute (VG.Spec.Rsa.i2osp (wordsNat n) (octetLen (wordsNat n)))
        (VG.Spec.Rsa.i2osp P (8 * w)) (VG.Spec.Rsa.i2osp Q (8 * w)) =
      some ((n ++ nm ++ pm ++ qm).map (·.bv)) := by
  generalize hN : wordsNat n = N at *
  have hNw : N < 2 ^ (64 * (2 * w)) := by have := wordsNat_lt' n; rwa [hn, hN] at this
  have hsz1 := Nat.size_le.mpr hNw
  have hsz2 : 64 * (2 * w - 1) < N.size := Nat.lt_size.mpr htop
  have hk : (octetLen N + 7) / 8 = 2 * w := by unfold octetLen; omega
  have h256 : ∀ x, x < 2 ^ (64 * w) → x < 256 ^ (8 * w) := fun x hx => by
    rwa [show (256 : Nat) = 2 ^ 8 by rfl, ← pow_mul, show 8 * (8 * w) = 64 * w by ring]
  have hpw : VG.Spec.Rsa.primeWords (8 * w) = w := by
    unfold VG.Spec.Rsa.primeWords VG.Spec.Rsa.modulusWords; omega
  unfold VG.Spec.Rsa.privatePrecompute VG.Spec.Rsa.publicPrecompute VG.Spec.Rsa.primeR2
  simp only [vg_os2ip_i2osp _ _ (lt_256_octetLen N), vg_os2ip_i2osp _ _ (h256 P hP),
    vg_os2ip_i2osp _ _ (h256 Q hQ), vg_i2osp_length, hpq, vg_modulus_valid N hodd (by omega) (by omega),
    ↓reduceIte, Option.map_some, hpw, VG.Spec.Rsa.modulusWords, hk, List.map_append, Option.some.injEq]
  have e1 := vg_toWords_wordsNat n
  have e2 := vg_toWords_wordsNat nm
  have e3 := vg_toWords_wordsNat pm
  have e4 := vg_toWords_wordsNat qm
  rw [hN, hn] at e1
  rw [hnmv, hnm] at e2
  rw [hpmv, hpm] at e3
  rw [hqmv, hqm] at e4
  rw [e1, e2, e3, e4]

set_option maxHeartbeats 1000000 in
/-- `IfmaCrt::precompute` lays out pyca/verified-garbage's CRT values for an
odd modulus `n` of `2w` words, its top word nonzero, `R² mod n`'s words
`nm`, and primes `p` and `q` of `w` words each whose product is `n`. -/
theorem precompute_spec (n nm p q : Slice U64) (w : Nat) (hw16 : 16 ≤ w) (hw32 : w ≤ 32)
    (hpw : p.length = w) (hqw : q.length = w) (hn : n.length = 2 * w) (hnm : nm.length = 2 * w)
    (hnmv : wordsNat nm.val = 2 ^ (128 * (2 * w)) % wordsNat n.val) :
    low.x86_64.rsa_ifma.IfmaCrt.precompute n nm p q ⦃ r => ∀ c, r = some c →
      c.w.val = w ∧ c.pre.val.take (2 * w) = n.val ∧ c.p.val.take w = p.val ∧ c.q.val.take w = q.val ∧
      VG.Spec.Rsa.privatePrecompute (VG.Spec.Rsa.i2osp (wordsNat n.val) (octetLen (wordsNat n.val)))
          (VG.Spec.Rsa.i2osp (wordsNat p.val) (8 * w)) (VG.Spec.Rsa.i2osp (wordsNat q.val) (8 * w)) =
        some ((c.pre.val.take (6 * w)).map (·.bv)) ⦄ := by
  unfold low.x86_64.rsa_ifma.IfmaCrt.precompute
  have h64 : (64#usize : Usize).val = 64 := rfl
  have h32 : (32#usize : Usize).val = 32 := rfl
  step with from_words_spec 64#usize n (by rw [h64]; omega) as ⟨r, x, hr, hxu, hxv, hxc⟩
  subst hr
  simp only [core.result.Result.ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
  step with from_words_spec 32#usize p (by rw [h32]; omega) as ⟨r1, y, hr1, hyu, hyv, hyc⟩
  subst hr1
  step with from_words_spec 32#usize q (by rw [h32]; omega) as ⟨r2, z, hr2, hzu, hzv, hzc⟩
  subst hr2
  step with is_even_spec x (by rw [h64]; omega) hxc as ⟨b, hb⟩
  split
  · simp
  rename_i hbe
  have hNo : wordsNat n.val % 2 = 1 := by
    have : b = false := by simpa using hbe
    rw [hb, hxv] at this; simpa using this
  unfold low.posint.PosInt.as_words
  step*
  have hs : s.val = n.val := by rw [← hxv]; simp [lowWords, s_post]
  have hpl : p.len.val = w := by rw [Slice.len_val]; exact hpw
  have htop : 2 ^ (64 * (2 * w - 1)) ≤ wordsNat n.val := by
    have ht := wordsNat_top n.val (2 * w - 1) (by simp only [Slice.length] at hn; omega)
    have hi2v : n.val[2 * w - 1]! = i2 := by
      have hlt : i1.val < s.val.length := by
        have : s.val.length = 2 * w := by rw [hs]; exact hn
        omega
      rw [i2_post, ← getElem!_pos s.val i1.val hlt, hs, i1_post, i_post, hpl]
    have h1 : 1 ≤ i2.val := by
      rename_i hi20
      have : i2.val ≠ 0 := fun h0 => hi20 (UScalar.eq_of_val_eq (by simpa using h0))
      omega
    rw [ht, hi2v]
    calc 2 ^ (64 * (2 * w - 1)) = 2 ^ (64 * (2 * w - 1)) * 1 := (mul_one _).symm
      _ ≤ 2 ^ (64 * (2 * w - 1)) * i2.val := Nat.mul_le_mul_left _ h1
      _ ≤ _ := Nat.le_add_left _ _
  step with posint_mul_spec 64#usize y z (by rw [h32, h64]) (by rw [hyu, h32]; omega)
    (by rw [hzu, h32]; omega) as ⟨pq, hpqu, hpqv⟩
  step with equals_spec pq x (by rw [hpqu, h64]; omega) (by rw [hxu, h64]; omega) as ⟨b1, hb1⟩
  simp only [low.ct.into_public, bind_ok]
  split
  swap
  · simp
  rename_i hb1t
  rw [hb1, decide_eq_true_eq, hpqv, hyv, hzv, hxv] at hb1t
  have hodd2 : Odd (wordsNat p.val * wordsNat q.val) := by rw [hb1t]; exact Nat.odd_iff.mpr hNo
  obtain ⟨hPo, hQo⟩ := Nat.odd_mul.mp hodd2
  rw [Nat.odd_iff] at hPo hQo
  step*
  case h =>
    show i.val ≤ (index_mut_back3 s9).val.length
    rw [s8_post2, List.length_setSlice!]
    have h1 : pre_n.val.length = i4.val := pre_n_post
    omega
  case h =>
    rw [s10_post1]
    show (index_mut_back3 s9).val.length - i.val = nm.val.length
    rw [s8_post2, List.length_setSlice!]
    have h1 : pre_n.val.length = i4.val := pre_n_post
    have h2 : nm.val.length = 2 * w := hnm
    omega
  case h =>
    show p.len.val ≤ pre_p.val.length
    have h1 : pre_p.val.length = s7.val.length - i4.val := pre_n_post1
    have h2 : s7.val.length = i3.val := s7_post1
    omega
  step with montifier_spec y (by rw [h32]; omega) (by rw [hyv]; exact hPo) as ⟨pi, hpiu, hpiv⟩
  step*
  case h =>
    show pi.used.val ≤ pi.words.to_slice.val.length
    have h1 : pi.words.to_slice.val.length = 32 := by simp
    rw [hpiu, h1]
    omega
  case h =>
    show p.len.val ≤ (index_mut_back5 s14).val.length
    rw [s12_post2, List.length_setSlice!]
    have h1 : pre_p.val.length = s7.val.length - i4.val := pre_n_post1
    have h2 : s7.val.length = i3.val := s7_post1
    omega
  step with montifier_spec z (by rw [h32]; omega) (by rw [hzv]; exact hQo) as ⟨pi1, hpi1u, hpi1v⟩
  step*
  case h =>
    show pi1.used.val ≤ pi1.words.to_slice.val.length
    have h1 : pi1.words.to_slice.val.length = 32 := by simp
    rw [hpi1u, h1]
    omega
  case h =>
    show s15.val.length = s16.val.length
    rw [s15_post, List.length_drop, s12_post2, List.length_setSlice!]
    have h1 : pre_p.val.length = s7.val.length - i4.val := pre_n_post1
    have h2 : s7.val.length = i3.val := s7_post1
    have h3 : s16.val.length = pi1.used.val := s16_post1
    rw [h3, hpi1u]
    omega
  intro c hc
  cases hc
  -- The values each write leaves, from zeros.
  have hs7v : s7.val = List.replicate (6 * w) 0#u64 := by
    have h192 : (192#usize : Usize).val = 192 := rfl
    rw [s7_post, i3_post, hpl, List.slice, Array.repeat_val, List.drop_zero, List.take_replicate, h192]
    congr 1
    omega
  have hpn : pre_n.val = List.replicate (2 * w) 0#u64 ++ List.replicate (2 * w) 0#u64 := by
    rw [pre_n_post2, hs7v, i4_post, hpl, List.take_replicate, ← List.replicate_add]; congr 1; omega
  have hpp : pre_p.val = List.replicate w 0#u64 ++ List.replicate w 0#u64 := by
    rw [pre_n_post3, hs7v, i4_post, hpl, List.drop_replicate, ← List.replicate_add]; congr 1; omega
  have hb3 : (index_mut_back3 s9).val = n.val ++ List.replicate (2 * w) 0#u64 := by
    have := setSlice!_append [] (List.replicate (2 * w) 0#u64) (List.replicate (2 * w) 0#u64) n.val
      (by simp only [List.length_replicate]; exact hn)
    rw [s8_post2, s9_post, hs, hpn]
    simpa using this
  have hb4 : (index_mut_back4 s11).val = n.val ++ nm.val := by
    rw [s10_post2, hb3, s11_post, i_post, hpl,
      setSlice!_end _ _ _ (by simp only [List.length_append, List.length_replicate]; rw [show nm.val.length = 2 * w from hnm, show n.val.length = 2 * w from hn]),
      List.take_left' hn]
  have hs13v : s13.val = lowWords pi y.used := by simp [lowWords, s13_post, hpiu]
  have hs16v : s16.val = lowWords pi1 z.used := by simp [lowWords, s16_post, hpi1u]
  have hs13l : s13.val.length = w := by
    have : s13.length = pi.used.val := s13_post1
    rw [hpiu, hyu, hpw] at this; exact this
  have hs16l : s16.val.length = w := by
    have : s16.length = pi1.used.val := s16_post1
    rw [hpi1u, hzu, hqw] at this; exact this
  have hb5 : (index_mut_back5 s14).val = s13.val ++ List.replicate w 0#u64 := by
    have := setSlice!_append [] (List.replicate w 0#u64) (List.replicate w 0#u64) s13.val
      (by simp only [List.length_replicate]; exact hs13l)
    rw [s12_post2, s14_post, hpp]
    simpa using this
  have hb6 : (index_mut_back6 s17).val = s13.val ++ s16.val := by
    rw [s15_post2, hb5, s17_post, hpl,
      setSlice!_end _ _ _ (by simp only [List.length_append, List.length_replicate]; rw [hs13l, hs16l]),
      List.take_left' hs13l]
  obtain ⟨hsplit, -⟩ := pre_n_post4 (index_mut_back4 s11) (index_mut_back6 s17)
    (by
      show (index_mut_back4 s11).val.length = _
      rw [hb4, i4_post, hpl, List.length_append, show n.val.length = 2 * w from hn,
        show nm.val.length = 2 * w from hnm]
      omega)
    (by
      show (index_mut_back6 s17).val.length = _
      rw [hb6, List.length_append, hs13l, hs16l]
      have h1 : s7.val.length = i3.val := s7_post1
      omega)
  have hpre : (index_mut_back2 (split_at_mut_back (index_mut_back4 s11, index_mut_back6 s17))).val.take (6 * w) =
      n.val ++ nm.val ++ s13.val ++ s16.val := by
    have hl : (split_at_mut_back (index_mut_back4 s11, index_mut_back6 s17)).val.length = 6 * w := by
      rw [hsplit, List.length_append, hb4, hb6, List.length_append, List.length_append, hs13l, hs16l,
        show n.val.length = 2 * w from hn, show nm.val.length = 2 * w from hnm]
      omega
    have h192 : (Array.repeat 192#usize 0#u64).val.length = 192 := (Array.repeat 192#usize 0#u64).property
    have := take_setSlice! (Array.repeat 192#usize 0#u64).val
      (split_at_mut_back (index_mut_back4 s11, index_mut_back6 s17)).val 0 (by rw [h192, hl]; omega)
    rw [List.take_zero, List.nil_append, zero_add, hl] at this
    rw [s7_post2, this, hsplit, hb4, hb6]
    simp only [List.append_assoc]
  have hzero : ∀ (l : List U64) (k : Nat), l.length = k → k ≤ 32 →
      ((Array.repeat 32#usize 0#u64).val.setSlice! 0 l).take k = l := fun l k hl hk => by
    have := take_setSlice! (Array.repeat 32#usize 0#u64).val l 0 (by simp; omega)
    rwa [List.take_zero, List.nil_append, zero_add, hl] at this
  have hs2v : s2.val = p.val := by rw [← hyv]; simp [lowWords, s2_post]
  have hs5v : s5.val = q.val := by rw [← hzv]; simp [lowWords, s5_post]
  have hP : wordsNat p.val < 2 ^ (64 * w) := by have := wordsNat_lt' p.val; rwa [show p.val.length = w from hpw] at this
  have hQ : wordsNat q.val < 2 ^ (64 * w) := by have := wordsNat_lt' q.val; rwa [show q.val.length = w from hqw] at this
  have hvg := private_precompute_eq n.val nm.val s13.val s16.val (wordsNat p.val) (wordsNat q.val) w hw16 hw32
    hn hnm hs13l hs16l hNo htop hb1t hP hQ hnmv
    (by rw [hs13v, hpiv, hyv, hyu, hpw])
    (by rw [hs16v, hpi1v, hzv, hzu, hqw])
  refine ⟨hpl, ?_, ?_, ?_, ?_⟩
  · rw [show 2 * w = min (2 * w) (6 * w) by omega, ← List.take_take, hpre, List.append_assoc,
      List.append_assoc, List.take_left' hn]
  · rw [s1_post2, s3_post, hs2v]; exact hzero _ _ hpw (by omega)
  · rw [s4_post2, s6_post, hs5v]; exact hzero _ _ hqw (by omega)
  · rw [hpre]; exact hvg

/-- What `IfmaCrt::new` holds when it sets pyca/verified-garbage's CRT up
for a modulus `n` and primes `p` and `q`: a CPU whose AVX-512 check passes;
the primes' width `w`, 16, 24, or 32 words and half the modulus's; the
modulus's and primes' words; and `VG.Spec.Rsa.privatePrecompute`'s words. -/
def IfmaCrtSet (n p q : Slice U64) (c : low.x86_64.rsa_ifma.IfmaCrt) : Prop :=
  (∃ t, low.x86_64.cpu.HaveAvx512ForRsa.check = ok (some t)) ∧
    (c.w.val = 16 ∨ c.w.val = 24 ∨ c.w.val = 32) ∧ c.w.val = p.length ∧ n.length = 2 * c.w.val ∧
    c.pre.val.take (2 * c.w.val) = n.val ∧ c.p.val.take c.w.val = p.val ∧ c.q.val.take c.w.val = q.val ∧
    VG.Spec.Rsa.privatePrecompute (VG.Spec.Rsa.i2osp (wordsNat n.val) (octetLen (wordsNat n.val)))
        (VG.Spec.Rsa.i2osp (wordsNat p.val) (8 * c.w.val)) (VG.Spec.Rsa.i2osp (wordsNat q.val) (8 * c.w.val)) =
      some ((c.pre.val.take (6 * c.w.val)).map (·.bv))

/-- `IfmaCrt::try_new` returns VG's CRT values, as `IfmaCrtSet` says, or
none: on a CPU whose AVX-512 check fails, at a width other than 16, 24 with
AVX512_FP16, or 32 words, or for inputs `precompute` refuses. -/
theorem try_new_spec (hifma : IfmaCheckReturns)
    (hfp16 : ∀ t, ∃ b, low.x86_64.cpu.HaveAvx512ForRsa.fp16 t = ok b) (n nm p q : Slice U64)
    (hnmv : wordsNat nm.val = 2 ^ (128 * n.length) % wordsNat n.val) :
    low.x86_64.rsa_ifma.IfmaCrt.try_new n nm p q ⦃ r => ∀ c, r = some c → IfmaCrtSet n p q c ⦄ := by
  obtain ⟨o, ho⟩ := hifma
  unfold low.x86_64.rsa_ifma.IfmaCrt.try_new
  simp only [ho, bind_ok]
  cases o with
  | none =>
    simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual, WP.spec_ok]
  | some t =>
  simp only [core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
  refine WP.spec_bind (Pₘ := fun b : Bool => b = true → p.length = 16 ∨ p.length = 32) ?_ ?_
  · split <;> simp_all [WP.spec_ok]
  intro b hb
  refine WP.spec_bind (Pₘ := fun sized : Bool => sized = true → p.length = 16 ∨ p.length = 24 ∨ p.length = 32)
    ?_ ?_
  · split
    · rename_i hbt
      simp only [WP.spec_ok]
      intro _
      rcases hb hbt with h | h <;> omega
    · split
      · rename_i h24
        obtain ⟨b', hb'⟩ := hfp16 t
        rw [hb', WP.spec_ok]
        intro _
        have : (Slice.len p).val = 24 := by rw [h24]; rfl
        rw [Slice.len_val] at this
        omega
      · simp [WP.spec_ok]
  intro sized hsized
  split
  swap
  · simp [WP.spec_ok]
  rename_i hst
  have hw := hsized hst
  split
  · simp [WP.spec_ok]
  rename_i hqw
  step as ⟨i2, hi2⟩
  case hmax =>
    have : (Slice.len p).val ≤ 32 := by rw [Slice.len_val]; omega
    scalar_tac
  split
  · simp [WP.spec_ok]
  rename_i hnw
  split
  · simp [WP.spec_ok]
  rename_i hnmw
  simp only [bne_iff_ne, ne_eq, not_not] at hqw hnw hnmw
  have hpl : (Slice.len p).val = p.length := Slice.len_val p
  have hql : q.length = p.length := by rw [← Slice.len_val q, hqw, hpl]
  have hnl : n.length = 2 * p.length := by rw [← Slice.len_val n, hnw, hi2, hpl]
  have hnml : nm.length = 2 * p.length := by rw [← Slice.len_val nm, hnmw, hi2, hpl]
  step with precompute_spec n nm p q p.length (by omega) (by omega) rfl hql hnl hnml (by rw [hnmv, hnl])
    as ⟨r, hr⟩
  rename_i c hc
  obtain ⟨hcw, hpre, hp, hq, hvg⟩ := hr c hc
  unfold IfmaCrtSet
  rw [hcw]
  exact ⟨⟨t, ho⟩, by omega, rfl, hnl, hpre, hp, hq, hvg⟩

/-- `IfmaCrt::new` sets pyca/verified-garbage's CRT up, as `IfmaCrtSet`
says, or leaves it off, `w = 0`. -/
theorem ifma_crt_new_spec (hifma : IfmaCheckReturns)
    (hfp16 : ∀ t, ∃ b, low.x86_64.cpu.HaveAvx512ForRsa.fp16 t = ok b) (n nm p q : Slice U64)
    (hnmv : wordsNat nm.val = 2 ^ (128 * n.length) % wordsNat n.val) :
    low.x86_64.rsa_ifma.IfmaCrt.new n nm p q ⦃ r => r.w = 0#usize ∨ IfmaCrtSet n p q r ⦄ := by
  unfold low.x86_64.rsa_ifma.IfmaCrt.new
  refine WP.spec_bind (try_new_spec hifma hfp16 n nm p q hnmv) ?_
  intro o ho
  cases o with
  | none => simp [core.option.Option.unwrap_or, WP.spec_ok]
  | some c =>
    simp only [core.option.Option.unwrap_or, WP.spec_ok]
    exact Or.inr (ho c rfl)

/-! ## The rest of `RsaPrivateKey::new` -/

theorem secret_from {N : Usize} (pi : low.posint.PosInt N) :
    low.posint.SecretPosInt.Insts.CoreConvertFromPosInt.from pi = ok pi := by
  simp [low.posint.SecretPosInt.Insts.CoreConvertFromPosInt.from, low.ct.into_secret]

theorem secret_deref {N : Usize} (pi : low.posint.SecretPosInt N) :
    low.posint.SecretPosInt.Insts.CoreOpsDerefDerefPosInt.deref pi = ok pi := rfl

/-- A clean value fits the words its bit length needs. -/
theorem fits_size {N : Usize} (p : low.posint.PosInt N) (w : Nat)
    (hw : (wordsNat (lowWords p p.used)).size ≤ 64 * w) :
    wordsNat (lowWords p p.used) < 2 ^ (64 * w) :=
  lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) hw)

/-- An odd value of at least two is above the power of two its top word
starts at, at the width its bit length needs. -/
theorem top_word_lt (X w : Nat) (hw : w = (X.size + 64 - 1) / 64) (hodd : X % 2 = 1) (h2 : 2 ≤ X) :
    2 ^ (64 * (w - 1)) < X := by
  have hs : 1 ≤ X.size := Nat.size_pos.mpr (by omega)
  have hle : 2 ^ (64 * (w - 1)) ≤ X := Nat.lt_size.mp (by omega)
  rcases Nat.lt_or_eq_of_le hle with h | h
  · exact h
  · exfalso
    rcases Nat.eq_zero_or_pos (64 * (w - 1)) with h0 | h0
    · rw [h0] at h; omega
    · rw [← Nat.succ_pred_eq_of_pos h0, Nat.pow_succ] at h; omega

/-- A Montgomery form of `C mod M` is `C·R mod M`. -/
theorem mont_pow_one_eq {M R C : Nat} {a : List U64} (h : MontPow M R (C % M) 1 a) :
    wordsNat a = C * R % M := by
  obtain ⟨hlt, hmod⟩ := h
  rw [pow_one] at hmod
  unfold Nat.ModEq at hmod
  rw [← Nat.mod_eq_of_lt hlt, hmod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]

/-- The Montgomery product of `qInv`'s Montgomery form and `q mod p` is one
just when `qInv` inverts `q` modulo `p`. -/
theorem iqmp_inverse {P Q IQ k a : Nat} (hP : 1 < P) (hodd : P % 2 = 1)
    (ha : a = IQ * 2 ^ k % P) (h : 1 * 2 ^ k % P = a * (Q % P) % P) : IQ * Q % P = 1 := by
  have h1 : 1 * 2 ^ k ≡ IQ * Q * 2 ^ k [MOD P] := by
    show 1 * 2 ^ k % P = IQ * Q * 2 ^ k % P
    rw [h, ha, ← Nat.mul_mod, Nat.mul_right_comm]
  have := mont_cancel (coprime_two_pow_odd hodd k) h1
  unfold Nat.ModEq at this
  rw [Nat.mod_eq_of_lt hP] at this
  exact this.symm

end PrivKey

open PrivKey

/-- The width, in words, a private key works at: its wider prime's. -/
def keyWords (P Q : Nat) : Nat := max ((P.size + 63) / 64) ((Q.size + 63) / 64)

/-- The key's width is its primes' wider, at most 64 words for primes of at
most 4096 bits. -/
theorem keyWords_bounds (P Q pw qw : Nat) (hpw : pw = (P.size + 64 - 1) / 64) (hqw : qw = (Q.size + 64 - 1) / 64)
    (hP : P.size ≤ 4096) (hQ : Q.size ≤ 4096) :
    pw ≤ keyWords P Q ∧ qw ≤ keyWords P Q ∧ keyWords P Q ≤ 64 ∧
      (P.size < Q.size → pw ≤ qw ∧ qw = keyWords P Q) ∧ (¬ P.size < Q.size → qw ≤ pw ∧ pw = keyWords P Q) := by
  unfold keyWords
  refine ⟨?_, ?_, ?_, fun h => ⟨?_, ?_⟩, fun h => ⟨?_, ?_⟩⟩ <;> omega

/-- RFC 8017's relations between a private key's components, which
`RsaPrivateKey::new` checks: `n = p·q`; `dP` is `d mod (p - 1)` and inverts
`e` modulo `p - 1`, and `dQ` the same for `q`; and `qInv` is below `p` and
inverts `q` modulo `p`. -/
def CrtRelations (N P Q D DP DQ QINV E : Nat) : Prop :=
  N = P * Q ∧ DP = D % (P - 1) ∧ DP * E % (P - 1) = 1 ∧ DQ = D % (Q - 1) ∧ DQ * E % (Q - 1) = 1 ∧
    QINV < P ∧ QINV * Q % P = 1

/-- What `RsaPrivateKey::new` returns for its components: a key that meets
`PrivKeyInv`, as the private operation needs, holds them, and they meet
`CrtRelations`. -/
def PrivKeyLoaded (p q dp dq iqmp : low.posint.PosInt 64#usize) (d n : RsaInt) (e : U64)
    (key : mid.rsa_priv.RsaPrivateKey) : Prop :=
  PrivKeyInv key ∧ key.public.n = n ∧ key.public.e = e ∧
    key.p.used.val = keyWords (wordsNat (lowWords p p.used)) (wordsNat (lowWords q q.used)) ∧
    wordsNat (lowWords key.p key.p.used) = wordsNat (lowWords p p.used) ∧
    wordsNat (lowWords key.q key.p.used) = wordsNat (lowWords q q.used) ∧
    wordsNat (lowWords key.d key.d.used) = wordsNat (lowWords d d.used) ∧
    wordsNat (lowWords key.dp key.dp.used) = wordsNat (lowWords dp dp.used) ∧
    wordsNat (lowWords key.dq key.dq.used) = wordsNat (lowWords dq dq.used) ∧
    wordsNat (lowWords key.iqmp key.p.used) = wordsNat (lowWords iqmp iqmp.used) ∧
    CrtRelations (wordsNat (lowWords n n.used)) (wordsNat (lowWords p p.used)) (wordsNat (lowWords q q.used))
      (wordsNat (lowWords d d.used)) (wordsNat (lowWords dp dp.used)) (wordsNat (lowWords dq dq.used))
      (wordsNat (lowWords iqmp iqmp.used)) e.val

/-- `RsaPrivateKey::new` refuses components it cannot use, without fault, and
otherwise returns a key it loaded from them. -/
theorem rsa_private_key_new_spec (hrun : Runs) (h : low.entry.Entry.assert_held = ok ())
    (hifma : IfmaCheckReturns) (hfp16 : ∀ t, ∃ b, low.x86_64.cpu.HaveAvx512ForRsa.fp16 t = ok b)
    (p q dp dq iqmp : low.posint.PosInt 64#usize) (d n : RsaInt) (e : U64)
    (hpu : p.used.val ≤ 64) (hqu : q.used.val ≤ 64) (hdpu : dp.used.val ≤ 64) (hdqu : dq.used.val ≤ 64)
    (hiu : iqmp.used.val ≤ 64) (hdu : d.used.val ≤ 128) (hnu : n.used.val ≤ 128)
    (hpc : Clean p) (hqc : Clean q) (hdpc : Clean dp) (hdqc : Clean dq) (hic : Clean iqmp)
    (htight : n.used.val = 0 ∨ 2 ^ (64 * (n.used.val - 1)) ≤ wordsNat (lowWords n n.used))
    (hP : MontProducts (keyWords (wordsNat (lowWords p p.used)) (wordsNat (lowWords q q.used)))) :
    mid.rsa_priv.RsaPrivateKey.new p q d dp dq iqmp n e ⦃ r => match r with
      | .Ok key => PrivKeyLoaded p q dp dq iqmp d n e key
      | .Err _ => True ⦄ := by
  unfold mid.rsa_priv.RsaPrivateKey.new
  set P := wordsNat (lowWords p p.used) with hPdef
  set Q := wordsNat (lowWords q q.used) with hQdef
  have h64 : (64#usize : Usize).val = 64 := rfl
  have h128 : (128#usize : Usize).val = 128 := rfl
  step with len_bits_spec n (by rw [h128]; exact hnu) as ⟨i, hi⟩
  split
  · simp [error.Error.Insts.CoreConvertFromKeyFormatError.from,
      WP.spec_ok]
  rename_i hnbits
  step with len_bits_spec p (by rw [h64]; exact hpu) as ⟨i1, hi1⟩
  simp only [low.ct.into_public, bind_ok]
  step with len_bits_spec q (by rw [h64]; exact hqu) as ⟨i2, hi2⟩
  try simp only [← hPdef] at hi1
  try simp only [← hQdef] at hi2
  have e8 : (8#usize : Usize).val = 8 := rfl
  have e1024 : (1024#usize : Usize).val = 1024 := rfl
  have e4096 : (4096#usize : Usize).val = 4096 := rfl
  step with div_ceil_spec i1 8#usize (by decide) as ⟨plen, hplen⟩
  step with is_even_spec p (by rw [h64]; omega) hpc as ⟨b, hb⟩
  step with is_even_spec q (by rw [h64]; omega) hqc as ⟨b1, hb1⟩
  have herr : ∀ k, (do
      let e1 ← error.Error.Insts.CoreConvertFromKeyFormatError.from k
      ok (core.result.Result.Err e1) : Result (core.result.Result mid.rsa_priv.RsaPrivateKey error.Error)) ⦃ r =>
        match r with
        | .Ok key => PrivKeyLoaded p q dp dq iqmp d n e key
        | .Err _ => True ⦄ := by
    intro k; simp [error.Error.Insts.CoreConvertFromKeyFormatError.from, WP.spec_ok]
  split
  · exact herr _
  rename_i hbb
  have hPo : P % 2 = 1 := by
    have : b = false := by simp_all
    rw [hb] at this; simpa using this
  have hQo : Q % 2 = 1 := by
    have : b1 = false := by simp_all
    rw [hb1] at this; simpa using this
  split
  · exact herr _
  rename_i hq2
  have hq2' : 2 ≤ Q.size := by
    rw [← hi2]; have : ¬ i2.val < 2 := fun h' => hq2 (by scalar_tac); omega
  simp only [mid.rsa_priv.MIN_PRIVATE_MODULUS_BYTES, mid.rsa_priv.MAX_PRIVATE_MODULUS_BYTES,
    mid.rsa_priv.MIN_PRIVATE_MODULUS_BITS, mid.rsa_priv.MAX_PRIVATE_MODULUS_BITS]
  step as ⟨i3, hi3⟩
  step as ⟨i4, hi4⟩
  simp only [core.ops.range.RangeInclusive.new, bind_ok, contains_usize]
  split
  swap
  · exact herr _
  rename_i hlen
  simp only [decide_eq_true_eq] at hlen
  have hPs1 : 1017 ≤ P.size := by
    have := hlen.1; simp only [hi3, hplen, hi1] at this; omega
  have hPs2 : P.size ≤ 4096 := by
    have := hlen.2; simp only [hi4, hplen, hi1] at this; omega
  have hQs2 : Q.size ≤ 4096 := by
    have := Nat.size_le.mpr (lt_of_lt_of_le (wordsNat_lt' (lowWords q q.used))
      (Nat.pow_le_pow_right (by norm_num) (show 64 * (lowWords q q.used).length ≤ 4096 by
        rw [lowWords_length q (by rw [h64]; exact hqu)]; omega)))
    exact this
  step with div_ceil_spec i1 64#usize (by decide) as ⟨pw, hpw⟩
  step with div_ceil_spec i2 64#usize (by decide) as ⟨qw, hqw⟩
  simp only [hi1, hi2] at hpw hqw
  have hpwr : 16 ≤ pw.val ∧ pw.val ≤ 64 := by omega
  have hqwr : 1 ≤ qw.val ∧ qw.val ≤ 64 := by omega
  have hPfit : P < 2 ^ (64 * pw.val) := fits_size p pw.val (by show P.size ≤ _; omega)
  have hQfit : Q < 2 ^ (64 * qw.val) := fits_size q qw.val (by show Q.size ≤ _; omega)
  step with fit_spec p pw (by rw [h64]; omega) (by rw [h64]; exact hpu) hpc as ⟨b4, p1, hp1u, hp1c, hp1v, hb4⟩
  step with fit_spec q qw (by rw [h64]; omega) (by rw [h64]; exact hqu) hqc as ⟨b5, q1, hq1u, hq1c, hq1v, hb5⟩
  step with fit_spec dp pw (by rw [h64]; omega) (by rw [h64]; exact hdpu) hdpc
    as ⟨b6, dp1, hdp1u, hdp1c, hdp1v, hb6⟩
  step with fit_spec dq qw (by rw [h64]; omega) (by rw [h64]; exact hdqu) hdqc
    as ⟨b7, dq1, hdq1u, hdq1c, hdq1v, hb7⟩
  step with fit_spec iqmp pw (by rw [h64]; omega) (by rw [h64]; exact hiu) hic
    as ⟨b8, iqmp1, hi1u, hi1c, hi1v, hb8⟩
  rw [← hPdef, Nat.mod_eq_of_lt hPfit] at hp1v
  rw [← hQdef, Nat.mod_eq_of_lt hQfit] at hq1v
  step with rsa_public_key_new_spec hrun h n e hnu htight as ⟨r, hr⟩
  cases r with
  | Err err =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, WP.spec_ok]
  | Ok val =>
  obtain ⟨hvn, hve, hpub, hvnu⟩ := hr
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, secret_from, secret_deref]
  have hP2 : 2 ≤ P := Nat.lt_size.mp (show 1 < P.size by omega)
  have hQ2 : 2 ≤ Q := Nat.lt_size.mp (show 1 < Q.size by omega)
  step with word_spec 64#usize e (by rw [h64]; omega) as ⟨e1, he1u, he1w⟩
  have he1v : wordsNat (lowWords e1 e1.used) = e.val := by
    rw [he1u]; exact wordsNat_first e1 e 1 le_rfl he1w
  step with exponents_agree_spec p1 dp1 e1 d (by rw [hp1u]; omega) (by rw [hp1u]; omega)
    (by rw [hp1u, hp1v]; exact top_word_lt P pw.val hpw hPo hP2) (by rw [hp1u, hp1v]; omega) hdu
    (by rw [hdp1u]; omega) (by rw [he1u]; omega) as ⟨b9, hb9⟩
  step with exponents_agree_spec q1 dq1 e1 d (by rw [hq1u]; omega) (by rw [hq1u]; omega)
    (by rw [hq1u, hq1v]; exact top_word_lt Q qw.val hqw hQo hQ2) (by rw [hq1u, hq1v]; omega) hdu
    (by rw [hdq1u]; omega) (by rw [he1u]; omega) as ⟨b10, hb10⟩
  obtain ⟨hKp, hKq, hK64, hKlt, hKge⟩ := keyWords_bounds P Q pw.val qw.val hpw hqw hPs2 hQs2
  -- The narrower prime takes the wider one's width, which its clean words
  -- above its own leave its value at.
  refine WP.spec_bind (Pₘ := fun r : low.posint.PosInt 64#usize × low.posint.PosInt 64#usize =>
    r.1.used.val = keyWords P Q ∧ r.2.used = r.1.used ∧
      wordsNat (lowWords r.1 r.1.used) = P ∧ wordsNat (lowWords r.2 r.1.used) = Q) ?_ ?_
  · split
    · rename_i hlt
      have hlt' : P.size < Q.size := by rw [← hi1, ← hi2]; exact hlt
      simp only [low.posint.SecretPosInt.Insts.CoreOpsDerefDerefMutPosInt.deref_mut, low.posint.PosInt.expand,
        bind_ok]
      apply (WP.spec_ok _).mpr
      refine ⟨?_, rfl, ?_, ?_⟩
      · show q1.used.val = keyWords P Q
        rw [hq1u]; exact (hKlt hlt').2
      · show wordsNat (lowWords p1 q1.used.val) = P
        rw [clean_lowWords hp1c (by rw [hp1u, h64]; omega) (by rw [hp1u, hq1u]; exact (hKlt hlt').1), hp1u, hp1v]
      · show wordsNat (lowWords q1 q1.used.val) = Q
        rw [hq1u, hq1v]
    · rename_i hlt
      have hlt' : ¬ P.size < Q.size := by rw [← hi1, ← hi2]; exact hlt
      simp only [low.posint.SecretPosInt.Insts.CoreOpsDerefDerefMutPosInt.deref_mut, low.posint.PosInt.expand,
        bind_ok]
      apply (WP.spec_ok _).mpr
      refine ⟨?_, rfl, ?_, ?_⟩
      · show p1.used.val = keyWords P Q
        rw [hp1u]; exact (hKge hlt').2
      · show wordsNat (lowWords p1 p1.used.val) = P
        rw [hp1u, hp1v]
      · show wordsNat (lowWords q1 p1.used.val) = Q
        rw [clean_lowWords hq1c (by rw [hq1u, h64]; omega) (by rw [hq1u, hp1u]; exact (hKge hlt').1), hq1u, hq1v]
  rintro ⟨p3, q3⟩ ⟨hp3u, hq3u, hp3v, hq3v⟩
  simp only at hp3u hq3u hp3v hq3v ⊢
  have hk64 : p3.used.val ≤ (64#usize : Usize).val := by rw [hp3u, h64]; exact hK64
  have hq3u' : q3.used.val = p3.used.val := by rw [hq3u]
  have hq3k : q3.used.val ≤ (64#usize : Usize).val := by rw [hq3u']; exact hk64
  have hP' : MontProducts p3.used.val := by rw [hp3u]; exact hP
  step with montifier_spec p3 hk64 (by rw [hp3v]; exact hPo) as ⟨pm, hpmu, hpmv⟩
  step with montifier_spec q3 hq3k (by rw [hq3u, hq3v]; exact hQo) as ⟨qm, hqmu, hqmv⟩
  rw [hq3u, hq3v] at hqmv
  step with widen_spec 128#usize iqmp1 (by rw [h64, h128]; omega) (by rw [hi1u, h64]; omega)
    as ⟨iw, hiwu, hiww⟩
  have hiwv : wordsNat (lowWords iw iw.used) = wordsNat (lowWords iqmp1 pw) := by
    have hl : (lowWords iqmp1 iqmp1.used).length = iqmp1.used.val :=
      lowWords_length _ (by rw [hi1u, h64]; omega)
    show wordsNat (iw.words.val.take iw.used.val) = _
    rw [hiww, hiwu, List.take_left' hl, hi1u]
  have hIQ1lt : wordsNat (lowWords iqmp1 pw) < 2 ^ (64 * pw.val) := by
    rw [hi1v]; exact Nat.mod_lt _ (by positivity)
  have hRK : 2 ^ (64 * pw.val) ≤ 2 ^ (64 * p3.used.val) :=
    Nat.pow_le_pow_right (by norm_num) (by rw [hp3u]; omega)
  step with posint_reduce_spec iw p3 pm (by rw [h64, h128]; omega) hP' (by rw [hp3u]; omega) hk64
    (by rw [hp3u]; omega) (by rw [hiwu, hi1u, h128]; omega) (by rw [hiwu, hi1u]; omega)
    (by rw [hp3v]; exact hPo) (by rw [hp3v]; omega) hpmv
    (by
      rw [hiwv, hp3v]
      calc _ < 2 ^ (64 * pw.val) := hIQ1lt
        _ ≤ 2 ^ (64 * p3.used.val) := hRK
        _ ≤ 2 ^ (64 * p3.used.val) * P := Nat.le_mul_of_pos_right _ (by omega))
    as ⟨ir, hiru, hirv⟩
  rw [hiwv, hp3v] at hirv
  step with to_montgomery_spec ir pm p3 hP' (by rw [hp3u]; omega) (by rw [hp3u]; omega) hk64
    (by rw [hp3v]; exact hPo) (by rw [hirv, hp3v]; exact Nat.mod_lt _ (by omega)) hpmv as ⟨im, himu, himv⟩
  step with mont_neg_inverse_spec p3 (by rw [hp3u]; omega) hk64 (by rw [hp3v]; exact hPo) as ⟨p0, hp0⟩
  step with mont_neg_inverse_spec q3 (by rw [hq3u']; rw [hp3u]; omega) hq3k (by rw [hq3u, hq3v]; exact hQo)
    as ⟨q0, hq0⟩
  rw [hq3u, hq3v] at hq0
  step with posint_mul_spec 128#usize p3 q3 (by rw [h64, h128]) hk64 hq3k as ⟨pq, hpqu, hpqv⟩
  rw [hp3v, hq3u, hq3v] at hpqv
  step with widen_spec 128#usize q3 (by rw [h64, h128]; omega) hq3k as ⟨qwide, hqwu, hqww⟩
  have hqwidev : wordsNat (lowWords qwide qwide.used) = Q := by
    have hl : (lowWords q3 q3.used).length = q3.used.val := lowWords_length _ hq3k
    show wordsNat (qwide.words.val.take qwide.used.val) = _
    rw [hqww, hqwu, List.take_left' hl, hq3u, hq3v]
  step with posint_reduce_spec qwide p3 pm (by rw [h64, h128]; omega) hP' (by rw [hp3u]; omega) hk64
    (by rw [hp3u]; omega) (by rw [hqwu, hq3u', h128]; omega) (by rw [hqwu, hq3u', hp3u]; omega)
    (by rw [hp3v]; exact hPo) (by rw [hp3v]; omega) hpmv
    (by
      rw [hqwidev, hp3v]
      calc _ < 2 ^ (64 * qw.val) := hQfit
        _ ≤ 2 ^ (64 * p3.used.val) := Nat.pow_le_pow_right (by norm_num) (by rw [hp3u]; omega)
        _ ≤ 2 ^ (64 * p3.used.val) * P := Nat.le_mul_of_pos_right _ (by omega))
    as ⟨qp, hqpu, hqpv⟩
  rw [hqwidev, hp3v] at hqpv
  step with equals_spec pq val.n (by rw [hpqu, h128]; omega) (by rw [hvn, h128]; exact hnu) as ⟨b11, hb11⟩
  step with less_than_spec iqmp1 p3 (by rw [hi1u, h64]; omega) hk64 as ⟨b12, hb12⟩
  step with posint_mont_mul_spec im qp p3 p0 hP' hk64
    (mont_args_of im qp p3 p0 hk64 (by rw [hp3u]; omega) (by rw [hp3u]; omega) (by rw [hp3v]; exact hPo) hp0
      himv.1 (by rw [hqpv, hp3v]; exact Nat.mod_lt _ (by omega))) as ⟨pi14, h14u, h14v⟩
  step with fixed_one_spec p3 (by rw [hp3u]; omega) hk64 as ⟨one, honeu, honev⟩
  step with equals_spec pi14 one (by rw [h14u]; exact hk64) (by rw [honeu]; exact hk64) as ⟨b13, hb13⟩
  split
  swap
  · exact herr _
  rename_i hall
  simp only [Bool.and_eq_true, and_assoc] at hall
  obtain ⟨-, -, hb6t, hb7t, hb8t, hb9t, hb10t, hb11t, hb12t, hb13t⟩ := hall
  have hDP1 : wordsNat (lowWords dp1 dp1.used) = wordsNat (lowWords dp dp.used) := by
    rw [hdp1u, hdp1v]; exact Nat.mod_eq_of_lt (hb6.mp hb6t)
  have hDQ1 : wordsNat (lowWords dq1 dq1.used) = wordsNat (lowWords dq dq.used) := by
    rw [hdq1u, hdq1v]; exact Nat.mod_eq_of_lt (hb7.mp hb7t)
  have hIQ1 : wordsNat (lowWords iqmp1 pw) = wordsNat (lowWords iqmp iqmp.used) := by
    rw [hi1v]; exact Nat.mod_eq_of_lt (hb8.mp hb8t)
  have hIQK : wordsNat (lowWords iqmp1 p3.used) = wordsNat (lowWords iqmp iqmp.used) := by
    rw [clean_lowWords hi1c (by rw [hi1u, h64]; omega) (by rw [hi1u, hp3u]; omega), hi1u, hIQ1]
  obtain ⟨h9a, h9b⟩ := hb9.mp hb9t
  simp only [hp1u, hp1v, hDP1, he1v] at h9a h9b
  obtain ⟨h10a, h10b⟩ := hb10.mp hb10t
  simp only [hq1u, hq1v, hDQ1, he1v] at h10a h10b
  rw [hb11, decide_eq_true_eq, hpqv, hvn] at hb11t
  rw [hb12, decide_eq_true_eq, hi1u, hIQ1, hp3v] at hb12t
  rw [hb13, decide_eq_true_eq, h14u, honeu, honev] at hb13t
  rw [hp3v, hirv, hIQ1] at himv
  have himv' := mont_pow_one_eq himv
  have h14 := h14v.2.2
  rw [lowWords_length p3 hk64, hb13t, hp3v, hqpv] at h14
  have hinv := iqmp_inverse (by omega) hPo himv' h14
  unfold low.posint.PosInt.as_words mid.rsa_pub.RsaPublicKey.montifier_words low.posint.PosInt.as_words_with_len_of
  have hvnk : val.n.used.val ≤ 128 := by rw [hvn]; exact hnu
  step as ⟨s, hs, hsl⟩
  step as ⟨s1, hs1, hs1l⟩
  step as ⟨s2, hs2, hs2l⟩
  step as ⟨s3, hs3, hs3l⟩
  have hsv : s.val = lowWords val.n val.n.used := by simp [lowWords, hs]
  have hs1v : s1.val = lowWords val.montifier val.n.used := by simp [lowWords, hs1]
  have hs2v : s2.val = lowWords p3 p3.used := by simp [lowWords, hs2]
  have hs3v : s3.val = lowWords q3 p3.used := by simp [lowWords, hs3, hq3u]
  have hnmv : wordsNat s1.val = 2 ^ (128 * s.length) % wordsNat s.val := by
    obtain ⟨-, -, -, -, hm, -⟩ := hpub
    rw [hs1v, hsv, hsl]; exact hm
  step with ifma_crt_new_spec hifma hfp16 s s1 s2 s3 hnmv as ⟨ic, hic⟩
  dsimp only [PrivKeyLoaded, PrivKeyInv]
  refine ⟨⟨hpub, hq3u, hk64, by rw [hp3u]; omega, by rw [hp3v]; exact hPo, by rw [hq3v]; exact hQo,
    by rw [hp3v]; omega, by rw [hq3v]; omega, by rw [hvn, hp3v, hq3v]; exact hb11t.symm, hp0,
    by rw [hq3v]; exact hq0, by rw [hpmv, hp3v], by rw [hq3v]; exact hqmv, by rw [hdp1u]; omega, by rw [hdq1u]; omega,
    by rw [hIQK, hp3v]; exact hb12t, by rw [himv', hIQK, hp3v], ?_⟩,
    hvn, hve, hp3u, hp3v, hq3v, rfl, hDP1, hDQ1, hIQK,
    hb11t.symm, h9a.symm, by rw [← h9a]; exact h9b, h10a.symm, by rw [← h10a]; exact h10b, hb12t, hinv⟩
  -- pyca/verified-garbage's CRT values, where `IfmaCrt::new` set them up.
  dsimp only [IfmaCrtInv]
  rcases hic with hw0 | ⟨hck, hw3, hwp, hnw, hpre, hpp, hqq, hvg⟩
  · exact Or.inl hw0
  rw [hsv, hs2v, hs3v] at hvg
  refine Or.inr ⟨UScalar.eq_of_val_eq (by rw [hwp, hs2l]), hck, hw3, by rw [← hsl, hnw], by rw [hpre, hsv],
    by rw [hpp, hs2v], by rw [hqq, hs3v], ?_, ?_, hvg⟩
  · exact clean_lowWords hdp1c (by rw [hdp1u, h64]; omega) (by rw [hdp1u, hp3u]; omega)
  · exact clean_lowWords hdq1c (by rw [hdq1u, h64]; omega) (by rw [hdq1u, hp3u]; omega)

end rind.x86_64
