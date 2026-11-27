import Rind.X86_64.RsaExp
import Rind.X86_64.RsaIfma
open Aeneas Aeneas.Std Result rind.spec rind.spec.rsa

/-!
# RSA's private operation on x86_64

`RsaPrivateKey::private_op` is RFC 8017's RSASP1 in its CRT form: two
exponentiations modulo the primes, by `PosInt::mod_exp_pair`, recombined by
Garner's formula, then checked by the public operation. This proves it for a
key meeting `PrivKeyInv`, with primes of 16 or 32 words, on a CPU with BMI2
and ADX, where `mont_exp` runs rind's Montgomery products, and where neither
pyca/verified-garbage's IFMA CRT nor aws-lc's dual RSAZ runs. That
`RsaPrivateKey::new` establishes `PrivKeyInv`, and the IFMA CRT's path, are
left to proofs to come.
-/

namespace rind.x86_64

/-- `fixed_one` is one at `n`'s width. -/
theorem fixed_one_spec {N : Usize} (n : low.posint.PosInt N) (hk : 1 ≤ n.used.val)
    (hkN : n.used.val ≤ N.val) :
    low.posint.PosInt.fixed_one n ⦃ r => r.used = n.used ∧ wordsNat (lowWords r n.used) = 1 ⦄ := by
  unfold low.posint.PosInt.fixed_one low.posint.PosInt.one low.posint.PosInt.zero
    low.posint.PosInt.expand
  step*
  subst x_post
  have hv : ((Array.repeat N 0#u64).set 0#usize 1#u64).val = (List.replicate N.val 0#u64).set 0 1#u64 := by
    simp [Array.repeat_val]
  obtain ⟨j, hj⟩ : ∃ j, N.val = j + 1 := ⟨N.val - 1, by omega⟩
  obtain ⟨i, hi⟩ : ∃ i, n.used.val = i + 1 := ⟨n.used.val - 1, by omega⟩
  simp only [lowWords, hv, hj, hi, List.replicate_succ, List.set_cons_zero, List.take_succ_cons,
    wordsNat_cons, List.take_replicate, wordsNat_replicate_zero]
  simp

/-- `PosInt::mont_mul`, a Montgomery product at `n`'s width. -/
theorem posint_mont_mul_spec {N : Usize} (self v n : low.posint.PosInt N) (n0 : U64)
    (hP : MontProducts n.used.val) (hk : n.used.val ≤ N.val)
    (hargs : MontArgs (lowWords self n.used) (lowWords v n.used) (lowWords n n.used) n0) :
    low.posint.PosInt.mont_mul self v n n0 ⦃ r => r.used = n.used ∧
      MontResult (lowWords self n.used) (lowWords v n.used) (lowWords n n.used) (lowWords r n.used) ⦄ := by
  unfold low.posint.PosInt.mont_mul low.posint.PosInt.zero
  simp only [bind_ok]
  apply WP.spec_mono (mont_mul_into_spec self v _ n n0 hP hk hargs)
  rintro r ⟨h1, h2, -⟩
  exact ⟨h1, h2⟩

/-- `to_montgomery` takes `self`, below `n`, into the Montgomery domain, given
`montifier`, which is `R² mod n`. -/
theorem to_montgomery_spec {N : Usize} (self montifier n : low.posint.PosInt N)
    (hP : MontProducts n.used.val) (hk2 : 2 ≤ n.used.val) (hk32 : n.used.val < 2 ^ 32)
    (hk : n.used.val ≤ N.val)
    (hodd : wordsNat (lowWords n n.used) % 2 = 1)
    (hx : wordsNat (lowWords self n.used) < wordsNat (lowWords n n.used))
    (hmont : wordsNat (lowWords montifier n.used) = 2 ^ (128 * n.used.val) % wordsNat (lowWords n n.used)) :
    low.posint.PosInt.to_montgomery self montifier n ⦃ r => r.used = n.used ∧
      MontPow (wordsNat (lowWords n n.used)) (2 ^ (64 * n.used.val)) (wordsNat (lowWords self n.used)) 1
        (lowWords r n.used) ⦄ := by
  unfold low.posint.PosInt.to_montgomery
  step with mont_neg_inverse_spec n (by omega) hk hodd as ⟨i, hi⟩
  have hM0 : 0 < wordsNat (lowWords n n.used) := by omega
  step with posint_mont_mul_spec self montifier n i hP hk
    (mont_args_of self montifier n i hk hk2 hk32 hodd hi hx (by rw [hmont]; exact Nat.mod_lt _ hM0))
    as ⟨r, hru, hr⟩
  refine ⟨hru, hr.2.1, ?_⟩
  apply mont_cancel (coprime_two_pow_odd hodd (64 * n.used.val))
  have h2 := hr.2.2
  rw [lowWords_length n hk] at h2
  have hRR : 2 ^ (128 * n.used.val) = 2 ^ (64 * n.used.val) * 2 ^ (64 * n.used.val) := by
    rw [← pow_add]; ring_nf
  unfold Nat.ModEq
  rw [h2, hmont, Nat.mul_mod_mod, hRR, pow_one, mul_assoc]

/-- `from_montgomery` takes what stands for `C^t` in the Montgomery domain out
of it: `C^t mod n`. -/
theorem from_montgomery_spec {N : Usize} (self n : low.posint.PosInt N)
    (hP : MontProducts n.used.val) (hk2 : 2 ≤ n.used.val) (hk32 : n.used.val < 2 ^ 32)
    (hk : n.used.val ≤ N.val)
    (hodd : wordsNat (lowWords n n.used) % 2 = 1) (hM1 : 1 < wordsNat (lowWords n n.used))
    (C t : Nat)
    (hx : MontPow (wordsNat (lowWords n n.used)) (2 ^ (64 * n.used.val)) C t (lowWords self n.used)) :
    low.posint.PosInt.from_montgomery self n ⦃ r => r.used = n.used ∧
      wordsNat (lowWords r n.used) = C ^ t % wordsNat (lowWords n n.used) ⦄ := by
  unfold low.posint.PosInt.from_montgomery
  step with fixed_one_spec n (by omega) hk as ⟨one, hou, hov⟩
  step with mont_neg_inverse_spec n (by omega) hk hodd as ⟨i, hi⟩
  step with posint_mont_mul_spec self one n i hP hk
    (mont_args_of self one n i hk hk2 hk32 hodd hi hx.1 (by rw [hov]; exact hM1)) as ⟨r, hru, hr⟩
  refine ⟨hru, ?_⟩
  have h2 := hr.2.2
  rw [lowWords_length n hk, hov, mul_one] at h2
  have hc : wordsNat (lowWords r n.used) ≡ C ^ t [MOD wordsNat (lowWords n n.used)] :=
    mont_cancel (coprime_two_pow_odd hodd (64 * n.used.val)) (h2.trans hx.2)
  rw [← Nat.mod_eq_of_lt hr.2.1]
  exact hc

/-- With BMI2 and ADX, aws-lc's RSAZ does not run. -/
theorem rsaz_none_spec {N : Usize} (t : low.x86_64.cpu.HaveBmi2Adx)
    (hadx : low.x86_64.cpu.HaveBmi2Adx.check = ok (some t)) (e n : low.posint.PosInt N) :
    low.posint.PosInt.rsaz e n ⦃ r => r = none ⦄ := by
  unfold low.posint.PosInt.rsaz low.x86_64.rsaz.Rsaz.check
  simp [hadx, core.option.Option.is_some, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
    core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

/-- `mod_exp` at 16 and 32 words with BMI2 and ADX: `self^e mod n`, for `self`
below `n`, given `n`'s montifier, `R² mod n`, and `n0`, `-n⁻¹ mod 2^64`. -/
theorem mod_exp_spec {N : Usize} (havx : ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t)
    (t : low.x86_64.cpu.HaveBmi2Adx) (hadx : low.x86_64.cpu.HaveBmi2Adx.check = ok (some t))
    (self e n montifier : low.posint.PosInt N) (n0 : U64)
    (hP : MontProducts n.used.val) (hk : n.used.val = 16 ∨ n.used.val = 32) (hN : n.used.val ≤ N.val)
    (he : e.used.val ≤ N.val) (hel : 64 * e.used.val ≤ Usize.max)
    (hodd : wordsNat (lowWords n n.used) % 2 = 1) (hM1 : 1 < wordsNat (lowWords n n.used))
    (hn0 : (wordsNat (lowWords n n.used) * n0.val + 1) % 2 ^ 64 = 0)
    (hmont : wordsNat (lowWords montifier n.used) = 2 ^ (128 * n.used.val) % wordsNat (lowWords n n.used))
    (hx : wordsNat (lowWords self n.used) < wordsNat (lowWords n n.used)) :
    low.posint.PosInt.mod_exp self e n montifier n0 ⦃ r => r.used = n.used ∧
      wordsNat (lowWords r n.used) =
        wordsNat (lowWords self n.used) ^ wordsNat (lowWords e e.used) % wordsNat (lowWords n n.used) ⦄ := by
  have hk2 : 2 ≤ n.used.val := by omega
  have hM0 : 0 < wordsNat (lowWords n n.used) := by omega
  have hR : Nat.Coprime (2 ^ (64 * n.used.val)) (wordsNat (lowWords n n.used)) :=
    coprime_two_pow_odd hodd _
  unfold low.posint.PosInt.mod_exp
  step with rsaz_none_spec t hadx e n as ⟨o, ho⟩
  subst ho
  simp only
  step with fixed_one_spec n (by omega) hN as ⟨one, hou, hov⟩
  step with posint_mont_mul_spec one montifier n n0 hP hN
    (mont_args_of one montifier n n0 hN hk2 (by omega) hodd hn0 (by rw [hov]; exact hM1)
      (by rw [hmont]; exact Nat.mod_lt _ hM0)) as ⟨om, homu, hom⟩
  have homp : MontPow (wordsNat (lowWords n n.used)) (2 ^ (64 * n.used.val))
      (wordsNat (lowWords self n.used)) 0 (lowWords om n.used) := by
    refine ⟨hom.2.1, ?_⟩
    apply mont_cancel hR
    have h2 := hom.2.2
    rw [lowWords_length n hN, hov, one_mul, hmont, Nat.mod_mod] at h2
    have hRR : 2 ^ (128 * n.used.val) = 2 ^ (64 * n.used.val) * 2 ^ (64 * n.used.val) := by
      rw [← pow_add]; ring_nf
    unfold Nat.ModEq
    rw [h2, hRR, pow_zero, one_mul]
  step with to_montgomery_spec self montifier n hP hk2 (by omega) hN hodd hx hmont as ⟨sm, hsmu, hsm⟩
  step with posint_mont_exp_spec havx t hadx sm om e n n0 (wordsNat (lowWords self n.used)) hP hk hN he hel
    hodd hn0 hsm homp as ⟨pe, hpeu, hpe⟩
  step with from_montgomery_spec pe n hP hk2 (by omega) hN hodd hM1 _ _ hpe as ⟨r, hru, hr⟩
  exact ⟨hru, hr⟩

/-- aws-lc's dual RSAZ, which no proof covers, does not run at `k` words: it
takes only 24 and 32, and the CPU check for it returns, or the CPU lacks it. -/
def NoRsazPair (k : Nat) : Prop :=
  (k ≠ 24 ∧ k ≠ 32 ∧ IfmaCheckReturns) ∨ low.x86_64.cpu.HaveAvx512ForRsa.check = ok none

theorem rsaz_pair_none_spec {N : Usize} (x y : low.posint.ModExp N) (h : NoRsazPair x.n.used.val) :
    low.posint.PosInt.rsaz_pair x y ⦃ r => r = none ⦄ := by
  unfold low.posint.PosInt.rsaz_pair
  split
  · simp
  split
  · simp
  split
  · simp
  unfold low.x86_64.rsaz_avx512.RsazAvx512.check
  rcases h with ⟨h24, h32, o, ho⟩ | h
  · rw [ho]
    cases o with
    | none =>
      simp [core.option.Option.Insts.CoreOpsTry_traitTry.branch,
        core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
    | some tok =>
      simp only [bind_ok, core.option.Option.Insts.CoreOpsTry_traitTry.branch]
      simp [core.bool.Bool.then_some]
  · simp [h, core.option.Option.Insts.CoreOpsTry_traitTry.branch,
      core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]

/-- What `mod_exp` takes, as `x` holds it: a modulus of 16 or 32 words, odd and
above one, whose Montgomery products return their results, its montifier,
`R² mod n`, and `n0`, `-n⁻¹ mod 2^64`, an exponent no wider than `N`, and a
base below the modulus. -/
def ModExpArgs {N : Usize} (x : low.posint.ModExp N) : Prop :=
  MontProducts x.n.used.val ∧ (x.n.used.val = 16 ∨ x.n.used.val = 32) ∧ x.n.used.val ≤ N.val ∧
    x.e.used.val ≤ N.val ∧ 64 * x.e.used.val ≤ Usize.max ∧
    wordsNat (lowWords x.n x.n.used) % 2 = 1 ∧ 1 < wordsNat (lowWords x.n x.n.used) ∧
    (wordsNat (lowWords x.n x.n.used) * x.n_0.val + 1) % 2 ^ 64 = 0 ∧
    wordsNat (lowWords x.n_montifier x.n.used) =
      2 ^ (128 * x.n.used.val) % wordsNat (lowWords x.n x.n.used) ∧
    wordsNat (lowWords x.base x.n.used) < wordsNat (lowWords x.n x.n.used)

/-- What `mod_exp` returns for `x`: `base^e mod n`, at `n`'s width. -/
def ModExpResult {N : Usize} (x : low.posint.ModExp N) (r : low.posint.PosInt N) : Prop :=
  r.used = x.n.used ∧ wordsNat (lowWords r x.n.used) =
    wordsNat (lowWords x.base x.n.used) ^ wordsNat (lowWords x.e x.e.used) % wordsNat (lowWords x.n x.n.used)

/-- `mod_exp_pair` at 16 and 32 words with BMI2 and ADX, where the dual RSAZ
does not run: each base to its exponent, modulo its modulus. -/
theorem mod_exp_pair_spec {N : Usize} (havx : ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t)
    (t : low.x86_64.cpu.HaveBmi2Adx) (hadx : low.x86_64.cpu.HaveBmi2Adx.check = ok (some t))
    (x y : low.posint.ModExp N) (hx : ModExpArgs x) (hy : ModExpArgs y)
    (hpair : NoRsazPair x.n.used.val) :
    low.posint.PosInt.mod_exp_pair x y ⦃ r => ModExpResult x r.1 ∧ ModExpResult y r.2 ⦄ := by
  unfold low.posint.PosInt.mod_exp_pair
  step with rsaz_pair_none_spec x y hpair as ⟨o, ho⟩
  subst ho
  simp only
  obtain ⟨hP, hk, hN, he, hel, hodd, hM1, hn0, hmont, hb⟩ := hx
  step with mod_exp_spec havx t hadx x.base x.e x.n x.n_montifier x.n_0 hP hk hN he hel hodd hM1 hn0
    hmont hb as ⟨r1, h1u, h1v⟩
  obtain ⟨hP', hk', hN', he', hel', hodd', hM1', hn0', hmont', hb'⟩ := hy
  step with mod_exp_spec havx t hadx y.base y.e y.n y.n_montifier y.n_0 hP' hk' hN' he' hel' hodd' hM1'
    hn0' hmont' hb' as ⟨r2, h2u, h2v⟩
  exact ⟨⟨h1u, h1v⟩, ⟨h2u, h2v⟩⟩

/-- `mont_redc` at `n`'s width `k`: `self·R⁻¹ mod n`, for `self` below `R·n`,
where `R = 2^(64k)`. -/
theorem mont_redc_spec {N M : Usize} (self : low.posint.PosInt N) (n : low.posint.PosInt M)
    (hk : n.used.val ≤ M.val) (hk61 : n.used.val < 2 ^ 61) (hsu : self.used.val ≤ N.val)
    (hs61 : self.used.val < 2 ^ 61) (hodd : wordsNat (lowWords n n.used) % 2 = 1)
    (hX : wordsNat (lowWords self self.used) < 2 ^ (64 * n.used.val) * wordsNat (lowWords n n.used)) :
    low.posint.PosInt.mont_redc self n ⦃ r => r.used = n.used ∧
      ∀ i, 2 ^ (64 * n.used.val) * i % wordsNat (lowWords n n.used) = 1 % wordsNat (lowWords n n.used) →
        wordsNat (lowWords r n.used) = i * wordsNat (lowWords self self.used) % wordsNat (lowWords n n.used) ⦄ := by
  unfold low.posint.PosInt.mont_redc low.posint.PosInt.as_mut_words low.posint.PosInt.as_words
    low.posint.PosInt.zero
  step*
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step as ⟨s1, hs1v, hs1l⟩
  step as ⟨s2, hs2v, hs2l⟩
  have hs1 : s1.val = lowWords self self.used := by simp [hs1v, lowWords]
  have hs2 : s2.val = lowWords n n.used := by simp [hs2v, lowWords]
  have hcv : (UScalar.cast UScalarTy.U64 s2.len).val = n.used.val := by
    simp only [UScalar.cast_val_eq, Slice.len_val, UScalarTy.numBits]
    rw [hs2l]; apply Nat.mod_eq_of_lt; scalar_tac
  simp only [lift, bind_ok]
  step with bignum_montredc_spec s s1 s2 (UScalar.cast UScalarTy.U64 s2.len) (by rw [hs2l, x_post1])
    (by rw [hcv]; omega) (by rw [hs1l]; omega) as ⟨s3, hs3l, hs3⟩
  intro i hi
  obtain ⟨h1, -⟩ := mont_into_post ({ n with words := Array.repeat M 0#u64 } : low.posint.PosInt M) n back
    x_post2 hk s3 (by rw [hs3l, x_post1])
  have hMR : wordsNat (lowWords n n.used) < 2 ^ (64 * n.used.val) := by
    have := wordsNat_lt' (lowWords n n.used); rwa [lowWords_length n hk] at this
  have hXR : wordsNat (lowWords self self.used) < 2 ^ (64 * (n.used.val + n.used.val)) := by
    rw [mul_add, pow_add]
    exact lt_of_lt_of_le hX (Nat.mul_le_mul_left _ hMR.le)
  rw [hcv, x_post1, hs1, hs2] at hs3
  rw [h1, hs3 hodd (by rw [Nat.mod_eq_of_lt hXR]; exact hX.le) i hi, Nat.mod_eq_of_lt hXR]

/-- `reduce` at `n`'s width `k`: `self mod n`, for `self` below `R·n`, where
`R = 2^(64k)`, given `n`'s montifier, `R² mod n`. -/
theorem posint_reduce_spec {N M : Usize} (self : low.posint.PosInt N) (n montifier : low.posint.PosInt M)
    (hMN : M.val < N.val) (hP : MontProducts n.used.val) (hk2 : 2 ≤ n.used.val) (hk : n.used.val ≤ M.val)
    (hk32 : n.used.val < 2 ^ 32) (hsu : self.used.val ≤ N.val) (hs61 : self.used.val < 2 ^ 61)
    (hodd : wordsNat (lowWords n n.used) % 2 = 1) (hM1 : 1 < wordsNat (lowWords n n.used))
    (hmont : wordsNat (lowWords montifier n.used) = 2 ^ (128 * n.used.val) % wordsNat (lowWords n n.used))
    (hX : wordsNat (lowWords self self.used) < 2 ^ (64 * n.used.val) * wordsNat (lowWords n n.used)) :
    low.posint.PosInt.reduce self n montifier ⦃ r => r.used = n.used ∧
      wordsNat (lowWords r n.used) = wordsNat (lowWords self self.used) % wordsNat (lowWords n n.used) ⦄ := by
  unfold low.posint.PosInt.reduce
  step
  step with mont_redc_spec self n hk (by omega) hsu hs61 hodd hX as ⟨r1, hr1u, hr1⟩
  obtain ⟨i, -, hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime (coprime_two_pow_odd hodd (64 * n.used.val)) hM1
  have hr1v := hr1 i (by rw [hi, Nat.mod_eq_of_lt hM1])
  have hM0 : 0 < wordsNat (lowWords n n.used) := by omega
  step with to_montgomery_spec r1 montifier n hP hk2 hk32 hk hodd (by rw [hr1v]; exact Nat.mod_lt _ hM0) hmont
    as ⟨r, hru, hr⟩
  refine ⟨hru, ?_⟩
  have hc : wordsNat (lowWords r n.used) ≡ wordsNat (lowWords self self.used) [MOD wordsNat (lowWords n n.used)] := by
    refine hr.2.trans ?_
    rw [pow_one, hr1v]
    unfold Nat.ModEq
    rw [Nat.mod_mul_mod, show i * wordsNat (lowWords self self.used) * 2 ^ (64 * n.used.val) =
      wordsNat (lowWords self self.used) * (2 ^ (64 * n.used.val) * i) by ring, Nat.mul_mod, hi, mul_one,
      Nat.mod_mod]
  rw [← Nat.mod_eq_of_lt hr.1]
  exact hc

/-- `widen` copies `self`'s words below its width into a wider integer, zero
above. -/
theorem widen_spec {N : Usize} (M : Usize) (self : low.posint.PosInt N) (hNM : N.val ≤ M.val)
    (hsu : self.used.val ≤ N.val) :
    low.posint.PosInt.widen M self ⦃ r => r.used = self.used ∧
      r.words.val = lowWords self self.used ++ List.replicate (M.val - self.used.val) 0#u64 ⦄ := by
  unfold low.posint.PosInt.widen low.posint.PosInt.zero low.posint.PosInt.as_words
  step*
  have hs1 : s1.val = lowWords self self.used := by simp [s1_post, lowWords]
  have hl : (lowWords self self.used).length = self.used.val := by
    rw [← hs1]; exact s1_post1
  rw [s_post2, s2_post, hs1, Array.repeat_val]
  simp only [List.setSlice!, List.take_zero, List.nil_append, List.length_replicate, Nat.sub_zero, hl,
    Nat.min_eq_left (show self.used.val ≤ M.val by omega), Nat.zero_add, List.drop_replicate]
  rw [List.take_of_length_le (by omega)]

/-- `sub_mod`: `self - b mod p`, for `self` and `b` below `p`, as wide. -/
theorem sub_mod_spec {N : Usize} (self b p : low.posint.PosInt N) (hk : p.used.val ≤ N.val)
    (hsu : self.used = p.used) (hbu : b.used = p.used)
    (ha : wordsNat (lowWords self p.used) < wordsNat (lowWords p p.used))
    (hb : wordsNat (lowWords b p.used) < wordsNat (lowWords p p.used)) :
    low.posint.PosInt.sub_mod self b p ⦃ r => r.used = p.used ∧
      (wordsNat (lowWords r p.used) : Int) =
        ((wordsNat (lowWords self p.used) : Int) - wordsNat (lowWords b p.used)) %
          wordsNat (lowWords p p.used) ⦄ := by
  unfold low.posint.PosInt.sub_mod low.posint.PosInt.as_mut_words low.posint.PosInt.as_words
    low.posint.PosInt.zero
  step*
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step as ⟨s1, hs1v, hs1l⟩
  step as ⟨s2, hs2v, hs2l⟩
  step as ⟨s3, hs3v, hs3l⟩
  have hs1 : s1.val = lowWords self p.used := by simp [hs1v, lowWords, hsu]
  have hs2 : s2.val = lowWords b p.used := by simp [hs2v, lowWords, hbu]
  have hs3 : s3.val = lowWords p p.used := by simp [hs3v, lowWords]
  step with bignum_modsub_spec s s1 s2 s3 (by rw [hs1l, x_post1, hsu]) (by rw [hs2l, x_post1, hbu])
    (by rw [hs3l, x_post1]) (by rw [hs1, hs3]; exact ha) (by rw [hs2, hs3]; exact hb) as ⟨s4, hs4l, hs4⟩
  obtain ⟨h1, -⟩ := mont_into_post ({ p with words := Array.repeat N 0#u64 } : low.posint.PosInt N) p back
    x_post2 hk s4 (by rw [hs4l, x_post1])
  rw [h1, hs4, hs1, hs2, hs3]

/-- `PosInt::mul`: `a·b`, as wide as both together. -/
theorem posint_mul_spec {N : Usize} (M : Usize) (a b : low.posint.PosInt N) (hNM : N.val + N.val ≤ M.val)
    (hau : a.used.val ≤ N.val) (hbu : b.used.val ≤ N.val) :
    low.posint.PosInt.mul M a b ⦃ r => r.used.val = a.used.val + b.used.val ∧
      wordsNat (lowWords r r.used) = wordsNat (lowWords a a.used) * wordsNat (lowWords b b.used) ⦄ := by
  unfold low.posint.PosInt.mul low.posint.PosInt.as_mut_words low.posint.PosInt.as_words
    low.posint.PosInt.zero
  step*
  obtain ⟨s, back⟩ := x
  dsimp only at *
  step as ⟨s1, hs1v, hs1l⟩
  step as ⟨s2, hs2v, hs2l⟩
  have hs1 : s1.val = lowWords a a.used := by simp [hs1v, lowWords]
  have hs2 : s2.val = lowWords b b.used := by simp [hs2v, lowWords]
  step with bignum_mul_spec s s1 s2 (by rw [hs1l, hs2l, x_post1, i1_post]) as ⟨s3, hs3l, hs3⟩
  refine ⟨i1_post, ?_⟩
  obtain ⟨h1, -⟩ := mont_into_post ({ words := Array.repeat M 0#u64, used := i1 } : low.posint.PosInt M)
    ({ words := Array.repeat M 0#u64, used := i1 } : low.posint.PosInt M) back x_post2
      (by show i1.val ≤ M.val; scalar_tac) s3
    (by rw [hs3l, x_post1])
  have ha := wordsNat_lt' (lowWords a a.used)
  have hb := wordsNat_lt' (lowWords b b.used)
  rw [lowWords_length a hau] at ha
  rw [lowWords_length b hbu] at hb
  have hab : wordsNat (lowWords a a.used) * wordsNat (lowWords b b.used) < 2 ^ (64 * s.length) := by
    rw [x_post1, i1_post, mul_add, pow_add]
    exact Nat.mul_lt_mul'' ha hb
  rw [h1, hs3, hs1, hs2, Nat.mod_eq_of_lt hab]

/-- `PosInt::add`: `self + b`, over all of its `N` words, whatever its width. -/
theorem posint_add_spec {N : Usize} (self b : low.posint.PosInt N) (hsu : self.used.val ≤ N.val)
    (hbu : b.used.val ≤ N.val)
    (hlt : wordsNat (lowWords self self.used) + wordsNat (lowWords b b.used) < 2 ^ (64 * N.val)) :
    low.posint.PosInt.add self b ⦃ r =>
      wordsNat r.words.val = wordsNat (lowWords self self.used) + wordsNat (lowWords b b.used) ⦄ := by
  unfold low.posint.PosInt.add low.posint.PosInt.as_words low.posint.PosInt.zero
  step*
  have hsl : s.val.length = N.val := by rw [s_post]; simp
  have hs3l : s3.val.length = N.val := by
    have : s3.length = s.length := __post; simp only [Slice.length] at this; omega
  have hs1 : s1.val = lowWords self self.used := by simp [s1_post, lowWords]
  have hs2 : s2.val = lowWords b b.used := by simp [s2_post, lowWords]
  rw [to_slice_mut_back_post, Array.from_slice_val _ _ hs3l, __post1, hs1, hs2]
  have : s.length = N.val := hsl
  rw [this, Nat.mod_eq_of_lt hlt]

/-- Garner's `h`, as the CRT computes it: `(s₁ - s₂ mod p)·qInv mod p`, by a
Montgomery product whose result is `h`, is RFC 8017's `(s₁ - s₂)·qInv mod p`. -/
theorem garner_h {P s1 s2 qInv d h : Nat} (hP : 0 < P)
    (hd : (d : Int) = ((s1 : Int) - ((s2 % P : Nat) : Int)) % P)
    (hh : h ≡ d * qInv [MOD P]) (hhP : h < P) :
    h = ((((s1 : Int) - s2) * qInv) % (P : Int)).toNat := by
  have hP' : (0 : Int) < P := by exact_mod_cast hP
  have h1 : (h : Int) = ((d : Int) * qInv) % P := by
    have := Nat.mod_eq_of_lt hhP
    rw [← this, hh]; push_cast; rfl
  have hd' : (d : Int) ≡ (s1 : Int) - s2 [ZMOD P] := by
    rw [hd]
    refine (Int.mod_modEq _ _).trans (Int.ModEq.sub_left _ ?_)
    push_cast
    exact Int.mod_modEq _ _
  have h2 : (((s1 : Int) - s2) * qInv) % P = (h : Int) := by
    rw [h1]; exact (hd'.mul_right _).symm
  rw [h2, Int.toNat_natCast]

/-- What `RsaPrivateKey::new` establishes about a key, as its private
operation by rind's exponentiations needs: its public key meets `PubKeyInv`
with the modulus `n = p·q`; the factors `p` and `q`, which it does not require
to be prime, are odd, above one, and as wide, `k` words; their montifiers are
`R² mod p` and `R² mod q`, for `R = 2^(64k)`; `p0` and `q0` are `-p⁻¹` and
`-q⁻¹ mod 2^64`; `dp` and `dq` fit their arrays; `iqmp` is below `p`; and
`iqmp_mont` is `iqmp·R mod p`. -/
def PrivKeyInv (key : mid.rsa_priv.RsaPrivateKey) : Prop :=
  PubKeyInv key.public ∧ key.q.used = key.p.used ∧ key.p.used.val ≤ 64 ∧ 2 ≤ key.p.used.val ∧
    wordsNat (lowWords key.p key.p.used) % 2 = 1 ∧ wordsNat (lowWords key.q key.p.used) % 2 = 1 ∧
    1 < wordsNat (lowWords key.p key.p.used) ∧ 1 < wordsNat (lowWords key.q key.p.used) ∧
    wordsNat (lowWords key.public.n key.public.n.used) =
      wordsNat (lowWords key.p key.p.used) * wordsNat (lowWords key.q key.p.used) ∧
    (wordsNat (lowWords key.p key.p.used) * key.p0.val + 1) % 2 ^ 64 = 0 ∧
    (wordsNat (lowWords key.q key.p.used) * key.q0.val + 1) % 2 ^ 64 = 0 ∧
    wordsNat (lowWords key.p_montifier key.p.used) =
      2 ^ (128 * key.p.used.val) % wordsNat (lowWords key.p key.p.used) ∧
    wordsNat (lowWords key.q_montifier key.p.used) =
      2 ^ (128 * key.p.used.val) % wordsNat (lowWords key.q key.p.used) ∧
    key.dp.used.val ≤ 64 ∧ key.dq.used.val ≤ 64 ∧
    wordsNat (lowWords key.iqmp key.p.used) < wordsNat (lowWords key.p key.p.used) ∧
    wordsNat (lowWords key.iqmp_mont key.p.used) =
      wordsNat (lowWords key.iqmp key.p.used) * 2 ^ (64 * key.p.used.val) %
        wordsNat (lowWords key.p key.p.used)

/-- RFC 8017's RSASP1, second form, of `c` with `key`'s components. -/
def keyRsasp1 (key : mid.rsa_priv.RsaPrivateKey) (c : Nat) : Nat :=
  rsasp1Crt (wordsNat (lowWords key.p key.p.used)) (wordsNat (lowWords key.q key.p.used))
    (wordsNat (lowWords key.dp key.dp.used)) (wordsNat (lowWords key.dq key.dq.used))
    (wordsNat (lowWords key.iqmp key.p.used)) c

/-- The CRT, by rind's exponentiations at 16 and 32 words with BMI2 and ADX,
where the dual RSAZ does not run: RSASP1 of `c`, below `n`, at `n`'s width,
zero above. -/
theorem crt_spec (havx : ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t)
    (t : low.x86_64.cpu.HaveBmi2Adx) (hadx : low.x86_64.cpu.HaveBmi2Adx.check = ok (some t))
    (key : mid.rsa_priv.RsaPrivateKey) (hinv : PrivKeyInv key) (hP : MontProducts key.p.used.val)
    (hk : key.p.used.val = 16 ∨ key.p.used.val = 32) (hpair : NoRsazPair key.p.used.val)
    (c : RsaInt) (hcu : c.used.val ≤ 128)
    (hc : wordsNat (lowWords c c.used) < wordsNat (lowWords key.public.n key.public.n.used)) :
    mid.rsa_priv.RsaPrivateKey.crt key c ⦃ m => m.used = key.public.n.used ∧
      wordsNat (lowWords m m.used) = keyRsasp1 key (wordsNat (lowWords c c.used)) ∧
      wordsNat (lowWords m m.used) < wordsNat (lowWords key.public.n key.public.n.used) ∧
      wordsNat (m.words.val.drop m.used.val) = 0 ⦄ := by
  obtain ⟨hpub, hqk, hk64, hk2, hpo, hqo, hp1, hq1, hn, hp0, hq0, hpm, hqm, hdp, hdq, hqi, hqim⟩ := hinv
  obtain ⟨hnk2, hnk, -⟩ := hpub
  have hk64' : key.p.used.val ≤ (64#usize : Usize).val := hk64
  have h128 : (128#usize : Usize).val = 128 := rfl
  have hRk : ∀ {N : Usize} (x : low.posint.PosInt N), key.p.used.val ≤ N.val →
      wordsNat (lowWords x key.p.used) < 2 ^ (64 * key.p.used.val) := fun x h => by
    have := wordsNat_lt' (lowWords x key.p.used); rwa [lowWords_length x h] at this
  have hQR := hRk key.q hk64'
  have hPR := hRk key.p hk64'
  have hP0 : 0 < wordsNat (lowWords key.p key.p.used) := by omega
  have hQ0 : 0 < wordsNat (lowWords key.q key.p.used) := by omega
  have hcP : wordsNat (lowWords c c.used) <
      2 ^ (64 * key.p.used.val) * wordsNat (lowWords key.p key.p.used) := by
    rw [hn] at hc
    calc _ < _ := hc
      _ ≤ wordsNat (lowWords key.p key.p.used) * 2 ^ (64 * key.p.used.val) := Nat.mul_le_mul_left _ hQR.le
      _ = _ := mul_comm _ _
  have hcQ : wordsNat (lowWords c c.used) <
      2 ^ (64 * key.p.used.val) * wordsNat (lowWords key.q key.p.used) := by
    rw [hn] at hc
    exact lt_of_lt_of_le hc (Nat.mul_le_mul_right _ hPR.le)
  have hc61 : c.used.val < 2 ^ 61 := by omega
  unfold mid.rsa_priv.RsaPrivateKey.crt low.posint.SecretPosInt.Insts.CoreOpsDerefDerefPosInt.deref
  simp only [bind_ok]
  step with posint_reduce_spec c key.p key.p_montifier (by decide) hP hk2 hk64' (by omega) hcu hc61 hpo hp1
    hpm hcP as ⟨cmp, hcmpu, hcmp⟩
  have hqk' : key.q.used.val = key.p.used.val := by rw [hqk]
  have hPq : MontProducts key.q.used.val := by rw [hqk']; exact hP
  have hkq : key.q.used.val = 16 ∨ key.q.used.val = 32 := by rw [hqk']; exact hk
  rw [← hqk] at hqo hq1 hqm hQ0 hQR hcQ hq0
  step with posint_reduce_spec c key.q key.q_montifier (by decide) hPq (by omega) (by omega) (by omega) hcu hc61
    hqo hq1 hqm hcQ as ⟨cmq, hcmqu, hcmq⟩
  have hdp' : 64 * key.dp.used.val ≤ Usize.max := by scalar_tac
  have hdq' : 64 * key.dq.used.val ≤ Usize.max := by scalar_tac
  have hxa : ModExpArgs (low.posint.ModExp.mk cmp key.dp key.p key.p_montifier key.p0) :=
    ⟨hP, hk, hk64', hdp, hdp', hpo, hp1, hp0, hpm, by
      show wordsNat (lowWords cmp key.p.used) < _; rw [hcmp]; exact Nat.mod_lt _ hP0⟩
  have hya : ModExpArgs (low.posint.ModExp.mk cmq key.dq key.q key.q_montifier key.q0) :=
    ⟨hPq, hkq, by rw [hqk']; exact hk64', hdq, hdq', hqo, hq1, hq0, hqm, by
      show wordsNat (lowWords cmq key.q.used) < _; rw [hcmq]; exact Nat.mod_lt _ hQ0⟩
  step with mod_exp_pair_spec havx t hadx _ _ hxa hya hpair as ⟨m_1, m_2, hm1, hm2⟩
  obtain ⟨hm1u, hm1⟩ := hm1
  obtain ⟨hm2u, hm2⟩ := hm2
  simp only at hm1u hm1 hm2u hm2
  rw [hcmp, ← Nat.pow_mod] at hm1
  rw [hcmq, ← Nat.pow_mod] at hm2
  have hm2q : m_2.used.val ≤ 64 := by rw [hm2u, hqk']; exact hk64
  step with widen_spec 128#usize m_2 (by decide) hm2q as ⟨w2, hw2u, hw2⟩
  have hw2l : lowWords w2 w2.used = lowWords m_2 m_2.used := by
    have hl := lowWords_length m_2 hm2q
    have hw : lowWords w2 w2.used = List.take w2.used.val w2.words.val := rfl
    rw [hw, hw2, hw2u, List.take_append_of_le_length hl.symm.le, List.take_of_length_le hl.le]
  have hw2v : wordsNat (lowWords w2 w2.used) =
      wordsNat (lowWords c c.used) ^ wordsNat (lowWords key.dq key.dq.used) %
        wordsNat (lowWords key.q key.q.used) := by rw [hw2l, hm2u]; exact hm2
  have hm2Q : wordsNat (lowWords w2 w2.used) < wordsNat (lowWords key.q key.q.used) := by
    rw [hw2v]; exact Nat.mod_lt _ hQ0
  have hw2u' : w2.used.val ≤ 64 := by rw [hw2u]; exact hm2q
  step with posint_reduce_spec w2 key.p key.p_montifier (by decide) hP hk2 hk64' (by omega) (by omega) (by omega)
    hpo hp1 hpm (by
      calc _ < wordsNat (lowWords key.q key.q.used) := hm2Q
        _ < 2 ^ (64 * key.p.used.val) := by rw [← hqk']; exact hQR
        _ ≤ _ := Nat.le_mul_of_pos_right _ hP0) as ⟨m2p, hm2pu, hm2p⟩
  have hm1P : wordsNat (lowWords m_1 key.p.used) < wordsNat (lowWords key.p key.p.used) := by
    rw [hm1]; exact Nat.mod_lt _ hP0
  have hm2pP : wordsNat (lowWords m2p key.p.used) < wordsNat (lowWords key.p key.p.used) := by
    rw [hm2p]; exact Nat.mod_lt _ hP0
  step with sub_mod_spec m_1 m2p key.p hk64' hm1u hm2pu hm1P hm2pP as ⟨d, hdu, hd⟩
  have hdP : wordsNat (lowWords d key.p.used) < wordsNat (lowWords key.p key.p.used) := by
    have hP' : (0 : Int) < wordsNat (lowWords key.p key.p.used) := by exact_mod_cast hP0
    have := Int.emod_lt_of_pos ((wordsNat (lowWords m_1 key.p.used) : Int) -
      wordsNat (lowWords m2p key.p.used)) hP'
    rw [← hd] at this; exact_mod_cast this
  have hqimP : wordsNat (lowWords key.iqmp_mont key.p.used) < wordsNat (lowWords key.p key.p.used) := by
    rw [hqim]; exact Nat.mod_lt _ hP0
  step with posint_mont_mul_spec d key.iqmp_mont key.p key.p0 hP hk64'
    (mont_args_of d key.iqmp_mont key.p key.p0 hk64' hk2 (by omega) hpo hp0 hdP hqimP) as ⟨h, hhu, hh⟩
  have hhu' : h.used.val ≤ 64 := by rw [hhu]; exact hk64
  have hqu' : key.q.used.val ≤ (64#usize : Usize).val := by rw [hqk']; exact hk64
  step with posint_mul_spec 128#usize key.q h (by decide) hqu' hhu' as ⟨pi8, hpi8u, hpi8⟩
  have hH : wordsNat (lowWords h h.used) < wordsNat (lowWords key.p key.p.used) := by
    rw [hhu]; exact hh.2.1
  have hNv : wordsNat (lowWords key.public.n key.public.n.used) < 2 ^ (64 * key.public.n.used.val) := by
    have := wordsNat_lt' (lowWords key.public.n key.public.n.used)
    rwa [lowWords_length _ hnk] at this
  have hV : wordsNat (lowWords w2 w2.used) + wordsNat (lowWords pi8 pi8.used) <
      wordsNat (lowWords key.public.n key.public.n.used) := by
    have hQq : wordsNat (lowWords key.q key.q.used) = wordsNat (lowWords key.q key.p.used) := by rw [hqk]
    rw [hpi8, hn, hQq]
    rw [hQq] at hm2Q
    have h1 : wordsNat (lowWords h h.used) + 1 ≤ wordsNat (lowWords key.p key.p.used) := hH
    calc _ < wordsNat (lowWords key.q key.p.used) + wordsNat (lowWords key.q key.p.used) *
            wordsNat (lowWords h h.used) := Nat.add_lt_add_right hm2Q _
      _ = wordsNat (lowWords key.q key.p.used) * (wordsNat (lowWords h h.used) + 1) := by ring
      _ ≤ wordsNat (lowWords key.q key.p.used) * wordsNat (lowWords key.p key.p.used) :=
          Nat.mul_le_mul_left _ h1
      _ = _ := mul_comm _ _
  have hV' : wordsNat (lowWords w2 w2.used) + wordsNat (lowWords pi8 pi8.used) <
      2 ^ (64 * key.public.n.used.val) := lt_trans hV hNv
  step with posint_add_spec w2 pi8 (by omega) (by omega) (lt_of_lt_of_le hV'
    (Nat.pow_le_pow_right (by norm_num) (by omega))) as ⟨m, hm⟩
  unfold low.posint.PosInt.expand
  simp only [WP.spec_ok]
  have htake : wordsNat (lowWords ({ m with used := key.public.n.used } : RsaInt) key.public.n.used) =
      wordsNat (lowWords w2 w2.used) + wordsNat (lowWords pi8 pi8.used) := by
    show wordsNat (List.take _ m.words.val) = _
    rw [wordsNat_take_mod, hm, Nat.mod_eq_of_lt hV']
  refine ⟨trivial, htake.trans ?_, by rw [htake]; exact hV, ?_⟩
  · have hQq : wordsNat (lowWords key.q key.q.used) = wordsNat (lowWords key.q key.p.used) := by rw [hqk]
    have hHv : wordsNat (lowWords h h.used) =
        ((((wordsNat (lowWords c c.used) ^ wordsNat (lowWords key.dp key.dp.used) %
            wordsNat (lowWords key.p key.p.used) : Nat) : Int) -
          (wordsNat (lowWords c c.used) ^ wordsNat (lowWords key.dq key.dq.used) %
            wordsNat (lowWords key.q key.p.used) : Nat)) * wordsNat (lowWords key.iqmp key.p.used) %
          (wordsNat (lowWords key.p key.p.used) : Int)).toNat := by
      apply garner_h hP0 (d := wordsNat (lowWords d key.p.used))
      · rw [hd, hm1, hm2p, hw2v, hQq]
      · have h2 := hh.2.2
        rw [lowWords_length _ hk64', hqim] at h2
        rw [hhu]
        apply mont_cancel (coprime_two_pow_odd hpo (64 * key.p.used.val))
        unfold Nat.ModEq
        rw [h2, Nat.mul_mod_mod, ← mul_assoc]
      · exact hH
    rw [hw2v, hpi8, hHv, hQq]
    rfl
  · have hsplit := wordsNat_take_drop m.words.val key.public.n.used.val
    have ht : wordsNat (List.take key.public.n.used.val m.words.val) =
        wordsNat (lowWords w2 w2.used) + wordsNat (lowWords pi8 pi8.used) := htake
    rw [hm, ht] at hsplit
    have hpos : 0 < 2 ^ (64 * (List.take key.public.n.used.val m.words.val).length) := by positivity
    have h0 : 2 ^ (64 * (List.take key.public.n.used.val m.words.val).length) *
        wordsNat (List.drop key.public.n.used.val m.words.val) = 0 := by omega
    rcases Nat.mul_eq_zero.mp h0 with h0 | h0
    · omega
    · exact h0

theorem equals_spec (x y : RsaInt) (hx : x.used.val ≤ 128) (hy : y.used.val ≤ 128) :
    low.posint.PosInt.equals x y ⦃ b =>
      b = decide (wordsNat (lowWords x x.used) = wordsNat (lowWords y y.used)) ⦄ := by
  unfold low.posint.PosInt.equals low.posint.PosInt.as_words
  step*
  have hs : s.val = lowWords x x.used := by simp [lowWords, s_post]
  have hs1 : s1.val = lowWords y y.used := by simp [lowWords, s1_post]
  rw [b_post, hs, hs1]

/-- What `private_op` returns for `c`: refusing with `WrongLength` a `c` not
below `n`, and otherwise RSASP1 of `c`, at `n`'s width, which raised to `e`
modulo `n` is `c`, or refusing with `Fault` where it is not. -/
def PrivateOpResult (key : mid.rsa_priv.RsaPrivateKey) (c : RsaInt) :
    core.result.Result RsaInt error.Error → Prop
  | .Ok s => wordsNat (lowWords c c.used) < wordsNat (lowWords key.public.n key.public.n.used) ∧
      s.used = key.public.n.used ∧
      wordsNat (lowWords s s.used) = keyRsasp1 key (wordsNat (lowWords c c.used)) ∧
      keyRsasp1 key (wordsNat (lowWords c c.used)) ^ key.public.e.val %
        wordsNat (lowWords key.public.n key.public.n.used) = wordsNat (lowWords c c.used)
  | .Err e => (e = .WrongLength ∧
        wordsNat (lowWords key.public.n key.public.n.used) ≤ wordsNat (lowWords c c.used)) ∨
      (e = .Fault ∧ wordsNat (lowWords c c.used) < wordsNat (lowWords key.public.n key.public.n.used) ∧
        keyRsasp1 key (wordsNat (lowWords c c.used)) ^ key.public.e.val %
          wordsNat (lowWords key.public.n key.public.n.used) ≠ wordsNat (lowWords c c.used))

/-- RSASP1 by the CRT, checked, on x86_64 with BMI2 and ADX for primes of 16
and 32 words, where neither pyca/verified-garbage's IFMA CRT nor the dual RSAZ
runs: `private_op` refuses with `WrongLength` a `c` not below `n`, and
otherwise returns RSASP1 of `c`, `s` with `s^e mod n = c`, or refuses with
`Fault` where `s^e mod n ≠ c`. A valid key rules that out and a fault does
not: two primes, dP and dQ inverting e modulo p - 1 and q - 1, and qInv
inverting q modulo p. `PrivKeyInv` states none of those relations. `new`
checks all but primality, so a key it accepts with composite factors can
still refuse some `c`. -/
theorem private_op_spec (havx : ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t)
    (t : low.x86_64.cpu.HaveBmi2Adx) (hadx : low.x86_64.cpu.HaveBmi2Adx.check = ok (some t))
    (hifma : IfmaCheckReturns) (key : mid.rsa_priv.RsaPrivateKey) (hinv : PrivKeyInv key)
    (hP : MontProducts key.p.used.val) (hPn : MontProducts key.public.n.used.val)
    (hk : key.p.used.val = 16 ∨ key.p.used.val = 32) (hpair : NoRsazPair key.p.used.val)
    (hw : key.ifma.w = 0#usize) (c : RsaInt) (hcu : c.used.val ≤ 128) :
    mid.rsa_priv.RsaPrivateKey.private_op key c ⦃ r => PrivateOpResult key c r ⦄ := by
  have hpub := hinv.1
  obtain ⟨hnk2, hnk, -⟩ := hpub
  unfold mid.rsa_priv.RsaPrivateKey.private_op
  step with less_than_spec c key.public.n hcu hnk as ⟨b, hb⟩
  split
  · rename_i hlt
    have hlt : wordsNat (lowWords c c.used) < wordsNat (lowWords key.public.n key.public.n.used) := by
      simpa [hb] using hlt
    unfold low.x86_64.rsa_ifma.IfmaCrt.runs
    simp only [hw, bne_self_eq_false, bind_ok, Bool.false_eq_true, ↓reduceIte]
    step with crt_spec havx t hadx key hinv hP hk hpair c hcu hlt as ⟨m, hmu, hmv, hmN, hmz⟩
    step with clone_spec as ⟨pi, hpi⟩
    subst hpi
    step with public_op_spec key.public hinv.1 hPn hifma pi (by rw [hmu]; exact hnk) hmz as ⟨r, hr⟩
    split
    · rename_i c2
      obtain ⟨-, hc2u, hc2v⟩ := hr
      step with equals_spec c2 c (by rw [hc2u]; exact hnk) hcu as ⟨b2, hb2⟩
      unfold low.ct.into_public
      simp only [bind_ok]
      have hc2 : wordsNat (lowWords c2 c2.used) = keyRsasp1 key (wordsNat (lowWords c c.used)) ^
          key.public.e.val % wordsNat (lowWords key.public.n key.public.n.used) := by
        rw [hc2u, hc2v, ← hmv, hmu]
      split
      · rename_i heq
        rw [hb2, decide_eq_true_iff, hc2] at heq
        simp only [WP.spec_ok]
        exact ⟨hlt, hmu, hmv, heq⟩
      · rename_i hne
        rw [hb2, decide_eq_true_iff, hc2] at hne
        simp only [WP.spec_ok]
        exact Or.inr ⟨rfl, hlt, hne⟩
    · exfalso
      omega
  · rename_i hge
    have hge : wordsNat (lowWords key.public.n key.public.n.used) ≤ wordsNat (lowWords c c.used) := by
      simpa [hb] using hge
    simp only [WP.spec_ok]
    exact Or.inl ⟨rfl, hge⟩

/-- `private_op_spec` for RSA-2048, primes of 16 words and a modulus of 32,
with BMI2 and ADX: the Montgomery products at both widths are s2n-bignum's,
and the dual RSAZ never takes 16 words. -/
theorem private_op_rsa2048_spec (havx : ∃ t, low.x86_64.cpu.HaveAvx2.check = ok t)
    (t : low.x86_64.cpu.HaveBmi2Adx) (hadx : low.x86_64.cpu.HaveBmi2Adx.check = ok (some t))
    (hifma : IfmaCheckReturns) (key : mid.rsa_priv.RsaPrivateKey) (hinv : PrivKeyInv key)
    (hk : key.p.used.val = 16) (hn : key.public.n.used.val = 32) (hw : key.ifma.w = 0#usize)
    (c : RsaInt) (hcu : c.used.val ≤ 128) :
    mid.rsa_priv.RsaPrivateKey.private_op key c ⦃ r => PrivateOpResult key c r ⦄ :=
  private_op_spec havx t hadx hifma key hinv (karatsuba_products (some t) hadx rfl (Or.inl hk))
    (karatsuba_products (some t) hadx rfl (Or.inr hn)) (Or.inl hk) (Or.inl ⟨by omega, by omega, hifma⟩)
    hw c hcu

end rind.x86_64
