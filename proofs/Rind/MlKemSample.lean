import Rind.Sha3
import Rind.SymCrypt.MlKem

/-!
# FIPS 203's `SampleNTT` over SHAKE128's bytes

`SampleNTT(B)` (Algorithm 7) reads `XOF(B)` three bytes at a time through
SymCrypt's incremental sponge. `xof_read` shows that the `k`th three bytes
it reads are bytes `3k` to `3k + 3` of `SHAKE128(B)`, which `xofByte`
gives one at a time, and `sampleNTT_eq` that `SampleNTT(B)` is the first 256
of `accepted`, the 12-bit candidates below `q` those bytes hold, once the
first `3t` bytes hold 256 of them (`Halts`). Without that, FIPS 203's loop
never finishes, and no proof shows that it finishes on every input: that
would take checking all 2^272 of them, or a property of SHAKE128 no one has
proven. `sampled` names those 256 candidates without the `t`, and
`sampleNTT_sampled` restates `sampleNTT_eq` over it.
-/

namespace rind.spec.mlkem

open Spec Spec.SHA3 Spec.MLKEM rind.spec
open scoped Spec.Notations

/-! ## The candidates -/

/-- The 12-bit candidates `d₁` and `d₂` of three bytes, as `SampleNTT` reads
them, that are below `q`. -/
def keep (b0 b1 b2 : Byte) : List ℕ :=
  (if b0.val + 256 * (b1.val % 16) < q then [b0.val + 256 * (b1.val % 16)] else []) ++
    (if b1.val / 16 + 16 * b2.val < q then [b1.val / 16 + 16 * b2.val] else [])

/-- The candidates below `q` of each three bytes of `bytes`, in order, a
trailing one or two bytes ignored. -/
def accepted : List Byte → List ℕ
  | b0 :: b1 :: b2 :: rest => keep b0 b1 b2 ++ accepted rest
  | _ => []

theorem accepted_append (a c : List Byte) (ha : a.length % 3 = 0) :
    accepted (a ++ c) = accepted a ++ accepted c := by
  match a, ha with
  | [], _ => simp [accepted]
  | b0 :: b1 :: b2 :: rest, ha =>
    simp only [List.cons_append, accepted, List.append_assoc]
    rw [accepted_append rest c (by simp at ha; omega)]
  | [_], ha => simp at ha
  | [_, _], ha => simp at ha

/-- The candidates of a prefix are a prefix of the candidates. -/
theorem accepted_prefix (a c : List Byte) : accepted a <+: accepted (a ++ c) := by
  match a with
  | [] => simp [accepted]
  | [_] => simp [accepted]
  | [_, _] => simp [accepted]
  | b0 :: b1 :: b2 :: rest =>
    simp only [List.cons_append, accepted]
    exact (List.prefix_append_right_inj _).2 (accepted_prefix rest c)

theorem keep_lt (b0 b1 b2 : Byte) : ∀ x ∈ keep b0 b1 b2, x < 3329 := by
  intro x hx
  simp only [keep, List.mem_append] at hx
  rcases hx with hx | hx <;> split_ifs at hx with h <;> simp_all

theorem accepted_lt : ∀ (l : List Byte), ∀ x ∈ accepted l, x < 3329
  | b0 :: b1 :: b2 :: rest => by
    intro x hx
    simp only [accepted, List.mem_append] at hx
    exact hx.elim (keep_lt b0 b1 b2 x) (accepted_lt rest x)
  | [] | [_] | [_, _] => by simp [accepted]

/-! ## SHAKE128's output, byte by byte -/

/-- The state of SHAKE128 on `M` once absorbed. -/
abbrev absorbed (M : List Byte) : List Byte :=
  absorb 168 (List.replicate 200 0) (keccakPad 168 shakePad M)

/-- Byte `i` of `SHAKE128(M)`. -/
def xofByte (M : List Byte) (i : ℕ) : Byte := (keccakF^[i / 168] (absorbed M))[i % 168]!

theorem shake128_map (M : List Byte) (n : ℕ) : shake128 M n = (List.range n).map (xofByte M) := rfl

theorem shake128_add (M : List Byte) (n c : ℕ) :
    shake128 M (n + c) = shake128 M n ++ (List.range c).map (fun i => xofByte M (n + i)) := by
  rw [shake128_map, shake128_map, List.range_add, List.map_append, List.map_map]
  rfl

/-- `SHAKE128(M)`'s first `3t` bytes are its first `3s`, then more. -/
theorem shake128_prefix (M : List Byte) {n n' : ℕ} (h : n ≤ n') : shake128 M n <+: shake128 M n' := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [shake128_add]
  exact List.prefix_append _ _

/-- The candidates of SHAKE128's first `n` bytes. -/
abbrev acc (M : List Byte) (n : ℕ) : List ℕ := accepted (shake128 M n)

theorem acc_prefix (M : List Byte) {n n' : ℕ} (h : n ≤ n') : acc M n <+: acc M n' := by
  obtain ⟨c, hc⟩ := shake128_prefix M h
  rw [acc, acc, ← hc]
  exact accepted_prefix _ _

theorem acc_getElem! (M : List Byte) {n n' : ℕ} (h : n ≤ n') (p : ℕ) (hp : p < (acc M n).length) :
    (acc M n')[p]! = (acc M n)[p]! := by
  obtain ⟨c, hc⟩ := acc_prefix M h
  rw [← hc, getElem!_pos _ p (by simp; omega), getElem!_pos _ p hp, List.getElem_append_left hp]

/-- Any two prefixes of the candidates agree where both reach. -/
theorem acc_agree (M : List Byte) (n n' p : ℕ) (h : p < (acc M n).length) (h' : p < (acc M n').length) :
    (acc M n)[p]! = (acc M n')[p]! := by
  rcases le_total n n' with hle | hle
  · exact (acc_getElem! M hle p h).symm
  · exact acc_getElem! M hle p h'

theorem acc_length_mono (M : List Byte) {n n' : ℕ} (h : n ≤ n') : (acc M n).length ≤ (acc M n').length :=
  (acc_prefix M h).length_le

/-- Three more bytes add their candidates. -/
theorem acc_succ (M : List Byte) (t : ℕ) :
    acc M (3 * (t + 1)) = acc M (3 * t) ++ keep (xofByte M (3 * t)) (xofByte M (3 * t + 1)) (xofByte M (3 * t + 2)) := by
  rw [acc, show 3 * (t + 1) = 3 * t + 3 by ring, shake128_add, accepted_append _ _ (by simp [shake128_map])]
  simp [List.range_succ, accepted]

/-- `SampleNTT`'s loop on `M` finishes: SHAKE128's first `3t` bytes hold 256
candidates below `q`, for some `t`. -/
def Halts (M : List Byte) : Prop := ∃ t, 256 ≤ (acc M (3 * t)).length

/-! ## SymCrypt's incremental sponge -/

section Incremental

open Incremental

variable (f : Vector Bool b → Vector Bool b) (r : ℕ) (hr : 0 < r ∧ r < b)

/-- Bit `j` of the sponge's output from `S0`, its state once absorbed. -/
def outBit (S0 : Vector Bool b) (j : ℕ) : Bool :=
  (f^[j / r] S0)[j % r]'(by have := Nat.mod_lt j hr.1; omega)

/-- An incremental sponge state, absorbed into `S0`, that has permuted `m`
times since, keeping each block it squeezed. -/
def Squeezed (S0 : Vector Bool b) (s : sponge.state r) : Prop :=
  ∃ m, s.S = f^[m] S0 ∧ s.Z.size = m * r ∧ ∀ j (h : j < s.Z.size), s.Z[j] = outBit f r hr S0 j

theorem squeezed_squeeze_r (S0 : Vector Bool b) (s : sponge.state r) (hs : Squeezed f r hr S0 s) :
    Squeezed f r hr S0 (sponge.squeeze_r f r hr s) ∧ (sponge.squeeze_r f r hr s).x = s.x := by
  obtain ⟨m, hS, hZ, hbits⟩ := hs
  refine ⟨⟨m + 1, ?_, ?_, ?_⟩, rfl⟩
  · simp [sponge.squeeze_r, SPONGE.squeeze_step, hS, Function.iterate_succ_apply']
  · simp [sponge.squeeze_r, SPONGE.squeeze_step, hZ, Nat.succ_mul]
  · intro j hj
    simp only [sponge.squeeze_r, SPONGE.squeeze_step, Array.size_append, Vector.size_toArray] at hj ⊢
    rw [Array.getElem_append]
    split
    · rename_i hjZ
      exact hbits j hjZ
    · rename_i hjZ
      rw [Vector.getElem_toArray, getElem_Trunc _ _ _ (by omega), outBit]
      simp only [hS]
      have hq : j / r = m := Nat.div_eq_of_lt_le (by rw [← hZ]; omega) (by rw [Nat.succ_mul, ← hZ]; omega)
      have hm : j % r = j - s.Z.size := by
        rw [hZ, Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]
      simp only [hq, hm]

/-- Squeezing `d` bits returns the output's next `d`. -/
theorem squeeze1_spec (S0 : Vector Bool b) (s : sponge.state r) (d : ℕ) (hs : Squeezed f r hr S0 s) :
    Squeezed f r hr S0 (sponge.squeeze1 f r hr s d).1 ∧ (sponge.squeeze1 f r hr s d).1.x = s.x + d ∧
      ∀ i (hi : i < d), (sponge.squeeze1 f r hr s d).2[i] = outBit f r hr S0 (s.x + i) := by
  rw [sponge.squeeze1]
  split
  · obtain ⟨hs', hx⟩ := squeezed_squeeze_r f r hr S0 s hs
    have := squeeze1_spec S0 (sponge.squeeze_r f r hr s) d hs'
    rw [hx] at this
    exact this
  · rename_i hd
    obtain ⟨m, hS, hZ, hbits⟩ := hs
    refine ⟨⟨m, hS, hZ, hbits⟩, rfl, fun i hi => ?_⟩
    simp only [Vector.getElem_cast, Vector.getElem_mk, Array.getElem_extract]
    rw [Array.getElem_append]
    split
    · rename_i hjZ
      exact hbits _ hjZ
    · rename_i hjZ
      rw [Vector.getElem_toArray, getElem_Trunc _ _ _ (by omega), outBit]
      simp only [hS]
      have hq : (s.x + i) / r = m :=
        Nat.div_eq_of_lt_le (by rw [← hZ]; omega) (by rw [Nat.succ_mul, ← hZ]; omega)
      have hm : (s.x + i) % r = s.x + i - s.Z.size := by
        rw [hZ, Nat.mod_eq_sub_mul_div, hq, Nat.mul_comm]
      simp only [hq, hm]
termination_by s.x + d - (s.Z.size + r)
decreasing_by
  simp only [sponge.squeeze_r, SPONGE.squeeze_step, Array.size_append, Vector.size_toArray]
  omega

end Incremental

/-- An incremental SHAKE128 context of `M` that has read its first `n` bytes. -/
def XofRead (M : List Byte) (s : Incremental.sponge.state (b - 256)) (n : ℕ) : Prop :=
  Squeezed KECCAK_f (b - 256) (by decide) (bitsOf (absorbed M)) s ∧ s.x = 8 * n

/-- Bit `u` of byte `k` of the output is bit `8k + u` of the sponge's. -/
theorem outBit_bitsOf (M : List Byte) (k u : ℕ) (hu : u < 8) :
    outBit KECCAK_f (b - 256) (by decide) (bitsOf (absorbed M)) (8 * k + u) =
      (xofByte M k).toNat.testBit u := by
  unfold outBit xofByte
  rw [← bitsOf_iterate_keccakF]
  simp only [bitsOf, Vector.getElem_ofFn]
  have h1 : (8 * k + u) / (b - 256) = k / 168 := by simp only [b]; omega
  have h2 : (8 * k + u) % (b - 256) / 8 = k % 168 := by simp only [b]; omega
  have h3 : (8 * k + u) % (b - 256) % 8 = u := by simp only [b]; omega
  simp only [h1, h2, h3]

/-- `XOF.Init` then `XOF.Absorb` of `M` has read nothing. -/
theorem xof_absorb (M : List Byte) : XofRead M (XOF.Absorb XOF.Init (toB M)) 0 := by
  refine ⟨⟨0, ?_, by rfl, fun j hj => by simp [XOF.Absorb, XOF.Init, SHAKE128.absorb, SHAKE128.init,
    Incremental.sponge.absorb1, Incremental.sponge.init] at hj⟩, rfl⟩
  simp only [Function.iterate_zero, id, XOF.Absorb, XOF.Init, SHAKE128.absorb, SHAKE128.init,
    Incremental.sponge.absorb1]
  have hpl := padLen_eq 168 M.length 4 (by omega) (by omega)
  exact (bitsOf_absorb 168 (by omega) (keccakPad 168 shakePad M) _
    (by rw [length_keccakPad 168 (by omega), ← hpl])
    (fun i hi => getElem_padded 168 4 (by omega) shakePad xofSuffix (by omega) shakePad_testBit M i hi)
    (padLen_dvd _ _)).symm

/-- `XOF.Absorb` depends only on its input's bytes. -/
theorem xof_absorb_congr {n n' : ℕ} (B : 𝔹 n) (C : 𝔹 n') (h : B.toList = C.toList) :
    XOF.Absorb XOF.Init B = XOF.Absorb XOF.Init C := by
  have hn : n = n' := by rw [← B.length_toList, ← C.length_toList, h]
  subst hn
  rw [Vector.toList_inj.mp h]

/-- `XOF.Squeeze` of three bytes reads the next three. -/
theorem xof_read (M : List Byte) (s : Incremental.sponge.state (b - 256)) (n : ℕ) (hs : XofRead M s n) :
    XofRead M (XOF.Squeeze s 3).1 (n + 3) ∧ ∀ t (ht : t < 3), (XOF.Squeeze s 3).2[t] = xofByte M (n + t) := by
  obtain ⟨hsq, hx⟩ := hs
  obtain ⟨h1, h2, h3⟩ := squeeze1_spec KECCAK_f (b - 256) (by decide) _ s (8 * 3) hsq
  refine ⟨⟨h1, by simp only [XOF.Squeeze, SHAKE128.squeeze]; rw [h2, hx]; ring⟩, fun t ht => ?_⟩
  apply Byte.ext_testBit
  intro u hu
  simp only [XOF.Squeeze, SHAKE128.squeeze]
  rw [bitsToBytes_testBit _ _ ht _ hu, h3 _ (by omega), hx,
    show 8 * n + (8 * t + u) = 8 * (n + t) + u by ring, outBit_bitsOf M _ _ hu]

/-! ## `SampleNTT` -/

/-- A loop in `Id` that keeps `I`, ends in `P`, and takes no more than `N`
iterations from the `t`th. -/
theorem loop_id {σ : Type} (body : Unit → σ → Id (ForInStep σ)) (I : ℕ → σ → Prop) (P : σ → Prop) (N : ℕ)
    (hstep : ∀ t s, I t s → match (body () s).run with
      | .done s' => P s'
      | .yield s' => t < N ∧ I (t + 1) s') :
    ∀ t s, I t s → P (forIn (m := Id) Lean.Loop.mk s body).run := by
  intro t
  induction hk : N - t generalizing t with
  | zero =>
    intro s hs
    have h := hstep t s hs
    rw [show (forIn Lean.Loop.mk s body : Id σ) = Lean.Loop.forIn Lean.Loop.mk s body from rfl,
      Lean.Loop.forIn_eq_of_monadTail]
    revert h
    generalize body () s = x
    cases x with
    | done s' => intro h; exact h
    | yield s' => intro h; exact absurd h.1 (by omega)
  | succ k ih =>
    intro s hs
    have h := hstep t s hs
    rw [show (forIn Lean.Loop.mk s body : Id σ) = Lean.Loop.forIn Lean.Loop.mk s body from rfl,
      Lean.Loop.forIn_eq_of_monadTail]
    revert h
    generalize body () s = x
    cases x with
    | done s' => intro h; exact h
    | yield s' => intro h; exact ih (t + 1) (by omega) s' h.2

/-- `SampleNTT`'s loop state after `t` iterations: the context has read `3t`
bytes, and `â` holds the first `j` candidates they hold, up to 256. -/
def SampleInv (M : List Byte) (t : ℕ) (s : Spec.SHA3.Incremental.sponge.state (Spec.SHA3.b - 256) × Polynomial × ℕ) : Prop :=
  XofRead M s.1 (3 * t) ∧ s.2.2 = min 256 (acc M (3 * t)).length ∧
    ∀ p (hp : p < s.2.2) (h : p < 256), s.2.1[p] = ((acc M (3 * t))[p]! : Zq)

theorem getElem!_append_left' (A K : List ℕ) (p : ℕ) (hp : p < A.length) : (A ++ K)[p]! = A[p]! := by
  rw [getElem!_pos _ p (by simp; omega), getElem!_pos _ p hp, List.getElem_append_left hp]

theorem getElem!_append_length (A K : List ℕ) (i : ℕ) : (A ++ K)[A.length + i]! = K[i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_append_right]

/-- `SampleNTT(B)` is the first 256 candidates below `q` of `SHAKE128(B)`,
given `3T` of its bytes that hold them. -/
theorem sampleNTT_eq (B : 𝔹 34) (T : ℕ) (hT : 256 ≤ (acc B.toList (3 * T)).length) (p : ℕ) (hp : p < 256) :
    (SampleNTT B)[p] = ((acc B.toList (3 * T))[p]! : Zq) := by
  unfold SampleNTT
  simp only [Id.run]
  show (forIn (m := Id) Lean.Loop.mk (XOF.Absorb XOF.Init B, Polynomial.zero, 0) _).run.2.1[p] = _
  refine loop_id (σ := Spec.SHA3.Incremental.sponge.state (Spec.SHA3.b - 256) × Polynomial × ℕ) _
    (SampleInv B.toList) (fun s => ∀ p (hp : p < 256), s.2.1[p] = (((acc B.toList (3 * T))[p]! : ℕ) : Zq))
    T ?_ 0 _ ?_ p hp
  · rintro t ⟨ctx, a, j⟩ ⟨hx, hj, ha⟩
    simp only at hj ha ⊢
    obtain ⟨hx', hC⟩ := xof_read _ ctx _ hx
    have hC0 := hC 0 (by decide)
    have hC1 := hC 1 (by decide)
    have hC2 := hC 2 (by decide)
    simp only [Nat.add_zero] at hC0
    have hsucc := acc_succ B.toList t
    have htT : j < 256 → t < T := by
      intro hj'
      by_contra hc
      have := (acc_prefix B.toList (show 3 * T ≤ 3 * t by omega)).length_le
      omega
    have hx'' : XofRead B.toList (XOF.Squeeze ctx 3).1 (3 * (t + 1)) := by
      rw [show 3 * (t + 1) = 3 * t + 3 by ring]; exact hx'
    simp only [hC0, hC1, hC2]
    split_ifs with h0 h1 h2 h3
    · have hl : (acc B.toList (3 * t)).length = j := by omega
      refine ⟨htT h0, hx'', ?_, ?_⟩
      · rw [hsucc]; simp [keep, h1, h2.1]; omega
      · intro p hp hp256
        dsimp only at hp ⊢
        rw [hsucc, Vector.getElem_set, Vector.getElem_set]
        split_ifs with e1 e2
        · subst e1
          rw [← hl, getElem!_append_length]
          simp [keep, h1, h2.1]
        · subst e2
          rw [← hl, ← Nat.add_zero (acc B.toList (3 * t)).length, getElem!_append_length]
          simp [keep, h1]
        · rw [getElem!_append_left' _ _ _ (by omega)]
          exact ha p (by omega) hp256
    · have hl : (acc B.toList (3 * t)).length = j := by omega
      refine ⟨htT h0, hx'', ?_, ?_⟩
      · rw [hsucc]
        by_cases h4 : (xofByte B.toList (3 * t + 1)).val / 16 + 16 * (xofByte B.toList (3 * t + 2)).val < q
        · simp [keep, h1, h4]; omega
        · simp [keep, h1, h4]; omega
      · intro p hp hp256
        dsimp only at hp ⊢
        rw [hsucc, Vector.getElem_set]
        split_ifs with e1
        · subst e1
          rw [← hl, ← Nat.add_zero (acc B.toList (3 * t)).length, getElem!_append_length]
          simp [keep, h1]
        · rw [getElem!_append_left' _ _ _ (by omega)]
          exact ha p (by omega) hp256
    · have hl : (acc B.toList (3 * t)).length = j := by omega
      refine ⟨htT h0, hx'', ?_, ?_⟩
      · rw [hsucc]; simp [keep, h1, h3.1]; omega
      · intro p hp hp256
        dsimp only at hp ⊢
        rw [hsucc, Vector.getElem_set]
        split_ifs with e1
        · subst e1
          rw [← hl, ← Nat.add_zero (acc B.toList (3 * t)).length, getElem!_append_length]
          simp [keep, h1, h3.1]
        · rw [getElem!_append_left' _ _ _ (by omega)]
          exact ha p (by omega) hp256
    · have hl : (acc B.toList (3 * t)).length = j := by omega
      have h4 : ¬ (xofByte B.toList (3 * t + 1)).val / 16 + 16 * (xofByte B.toList (3 * t + 2)).val < q := fun h => h3 ⟨h, h0⟩
      refine ⟨htT h0, hx'', ?_, ?_⟩
      · rw [hsucc]; simp [keep, h1, h4]; omega
      · intro p hp hp256
        dsimp only at hp ⊢
        rw [hsucc, getElem!_append_left' _ _ _ (by omega)]
        exact ha p hp hp256
    · intro p hp
      have hl : 256 ≤ (acc B.toList (3 * t)).length := by omega
      rw [ha p (by omega) hp, acc_agree _ (3 * t) (3 * T) p (by omega) (by omega)]
  · refine ⟨?_, ?_, fun p hp => absurd hp (by simp)⟩
    · show XofRead B.toList (XOF.Absorb XOF.Init B) (3 * 0)
      rw [xof_absorb_congr B (toB B.toList) (by simp [toB])]
      exact xof_absorb B.toList
    · show 0 = min 256 (acc B.toList (3 * 0)).length
      simp [shake128_map, accepted]

open Classical in
/-- SHAKE128's first 256 candidates below `q` on `M`, where `SampleNTT` on
`M` finishes. -/
noncomputable def sampled (M : List Byte) : List ℕ :=
  if h : Halts M then (acc M (3 * Classical.choose h)).take 256 else []

theorem take_getElem! (l : List ℕ) (n k : ℕ) (h : k < n) : (l.take n)[k]! = l[k]! := by
  simp [List.getElem!_eq_getElem?_getD, h]

theorem sampled_getElem! (M : List Byte) (T : ℕ) (hT : 256 ≤ (acc M (3 * T)).length) (p : ℕ) (hp : p < 256) :
    (sampled M)[p]! = (acc M (3 * T))[p]! := by
  have hH : Halts M := ⟨T, hT⟩
  have := Classical.choose_spec hH
  unfold sampled
  rw [dite_eq_left hH, take_getElem! _ _ _ hp]
  exact acc_agree M _ _ p (by omega) (by omega)

/-- `SampleNTT(B)` is the first 256 candidates below `q` of `SHAKE128(B)`. -/
theorem sampleNTT_sampled (B : 𝔹 34) (hH : Halts B.toList) (p : ℕ) (hp : p < 256) :
    (SampleNTT B)[p] = ((sampled B.toList)[p]! : Zq) := by
  obtain ⟨T, hT⟩ := hH
  rw [sampleNTT_eq B T hT p hp, sampled_getElem! _ T hT p hp]

theorem sampled_lt (M : List Byte) (p : ℕ) (hp : p < 256) (hH : Halts M) : (sampled M)[p]! < 3329 := by
  obtain ⟨T, hT⟩ := hH
  rw [sampled_getElem! M T hT p hp, getElem!_pos _ p (by omega)]
  exact accepted_lt _ _ (List.getElem_mem _)

end rind.spec.mlkem
