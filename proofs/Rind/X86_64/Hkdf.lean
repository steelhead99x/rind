import Rind.X86_64.Kdf.Funs
import Rind.X86_64.HmacApi
import Rind.X86_64.ChaCha20
open Aeneas Aeneas.Std Result rind.spec

/-!
# HKDF's API, `high::hkdf`

`Salt::extract` is RFC 5869's HKDF-Extract and `Okm::fill` its HKDF-Expand,
over HMAC with any of `high::hmac`'s hashes, down to `Rind.X86_64.HmacApi`.
`Salt`, `Prk`, and `Okm` are translated in the second Aeneas pass, and
`Prk::expand_into`'s loop is modelled in `Rind.X86_64.HkdfExpand`.
`admin/prove` writes the aarch64 proof from this file by renaming the target.
-/

namespace rind.x86_64.kdf

/-! ## Output of whole blocks

HKDF-Expand and PBKDF2 both write the first `L` bytes of `T(1) | T(2) | ...`
one `n`-byte block at a time. -/

theorem bv_append (x y : List U8) : bv (x ++ y) = bv x ++ bv y := List.map_append

theorem bv_take (x : List U8) (n : Nat) : bv (x.take n) = (bv x).take n := List.map_take ..

theorem bv_length (x : List U8) : (bv x).length = x.length := List.length_map ..

/-- `T(1) | ... | T(j)`. -/
def blocksOut (T : Nat → List Byte) (j : Nat) : List Byte :=
  (List.range j).flatMap fun i => T (i + 1)

section
variable (T : Nat → List Byte) (n : Nat) (hT : ∀ i, (T (i + 1)).length = n)

theorem blocksOut_succ (j : Nat) : blocksOut T (j + 1) = blocksOut T j ++ T (j + 1) := by
  simp [blocksOut, List.range_succ, List.flatMap_append]

include hT in
theorem blocksOut_length (j : Nat) : (blocksOut T j).length = j * n := by
  induction j with
  | zero => simp [blocksOut]
  | succ j ih => rw [blocksOut_succ, List.length_append, ih, hT]; ring

include hT in
theorem blocksOut_take (L j d : Nat) (hj : L ≤ j * n) :
    (blocksOut T (j + d)).take L = (blocksOut T j).take L := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, blocksOut_succ, List.take_append_of_le_length
      (by rw [blocksOut_length T n hT]; nlinarith), ih]

theorem ceilDiv_ge (L : Nat) (hn : 0 < n) : L ≤ (L + n - 1) / n * n := by
  have h1 := Nat.div_add_mod (L + n - 1) n
  have h2 := Nat.mod_lt (L + n - 1) hn
  rw [Nat.mul_comm] at h1
  omega

theorem ceilDiv_le (L j : Nat) (hn : 0 < n) (h : L ≤ j * n) : (L + n - 1) / n ≤ j := by
  have : (L + n - 1) / n < j + 1 := by
    rw [Nat.div_lt_iff_lt_mul hn, Nat.add_mul, one_mul]
    omega
  omega

include hT in
/-- Once `j` blocks cover the output, it is the first `L` bytes of `ceil(L / n)` blocks. -/
theorem prefix_done (hn : 0 < n) (out : List Byte) (j : Nat) (hL : out.length ≤ j * n)
    (hpre : out.take (j * n) = (blocksOut T j).take out.length) :
    out = (blocksOut T ((out.length + n - 1) / n)).take out.length := by
  have hK := ceilDiv_le n out.length j hn hL
  calc out = out.take (j * n) := (List.take_of_length_le hL).symm
    _ = (blocksOut T j).take out.length := hpre
    _ = _ := by
      rw [show j = (out.length + n - 1) / n + (j - (out.length + n - 1) / n) by omega,
        blocksOut_take T n hT _ _ _ (ceilDiv_ge n _ hn)]

include hT in
/-- Writing block `c' + 1`, cut to what is left of the output, at its offset. -/
theorem prefix_step (out blk : List U8) (c' : Nat) (hoff : c' * n < out.length)
    (hbl : blk.length = n) (hblk : bv blk = T (c' + 1))
    (hpre : (bv out).take (c' * n) = (blocksOut T c').take out.length) :
    (bv (out.setSlice! (c' * n) (blk.take (min n (out.length - c' * n))))).take ((c' + 1) * n) =
      (blocksOut T (c' + 1)).take out.length := by
  have hOl := blocksOut_length T n hT c'
  rw [← bv_take, blocksOut_succ, List.take_append, hOl,
    List.take_of_length_le (l := blocksOut T c') (by rw [hOl]; omega)]
  have hs'l : (blk.take (min n (out.length - c' * n))).length = min n (out.length - c' * n) := by
    simp only [List.length_take, hbl]; omega
  have h1 := take_setSlice! out (blk.take (min n (out.length - c' * n))) (c' * n)
    (by rw [hs'l]; omega)
  rw [hs'l] at h1
  have hsetl : (out.setSlice! (c' * n) (blk.take (min n (out.length - c' * n)))).length =
      out.length := by
    simp [List.length_setSlice!]
  have htake : (out.setSlice! (c' * n) (blk.take (min n (out.length - c' * n)))).take
      ((c' + 1) * n) = out.take (c' * n) ++ blk.take (min n (out.length - c' * n)) := by
    rw [← h1]
    by_cases hcase : n ≤ out.length - c' * n
    · rw [show c' * n + min n (out.length - c' * n) = (c' + 1) * n by
        rw [Nat.add_mul, one_mul]; omega]
    · have e1 : (out.setSlice! (c' * n) (blk.take (min n (out.length - c' * n)))).take
          ((c' + 1) * n) = out.setSlice! (c' * n) (blk.take (min n (out.length - c' * n))) :=
        List.take_of_length_le (by rw [hsetl, Nat.add_mul, one_mul]; omega)
      have e2 : (out.setSlice! (c' * n) (blk.take (min n (out.length - c' * n)))).take
          (c' * n + min n (out.length - c' * n)) =
          out.setSlice! (c' * n) (blk.take (min n (out.length - c' * n))) :=
        List.take_of_length_le (by rw [hsetl]; omega)
      rw [e1, e2]
  rw [htake, bv_append, bv_take, hpre, List.take_of_length_le (by rw [hOl]; omega),
    bv_take, hblk]
  congr 1
  rw [← List.take_take, List.take_of_length_le (l := List.take _ _)
    (by simp only [List.length_take, hT]; omega)]

end

/-! ## HKDF-Expand's blocks -/

section
variable (prf : List Byte → List Byte → List Byte) (prk info : List Byte)

/-- HKDF-Expand's `T(i)`. -/
def hkdfT : Nat → List Byte
  | 0 => []
  | i + 1 => prf prk (hkdfT i ++ info ++ [BitVec.ofNat 8 (i + 1)])

theorem hkdf_fold (j : Nat) :
    (List.range j).foldl (fun (acc : List Byte × List Byte) i =>
      let t := prf prk (acc.1 ++ info ++ [BitVec.ofNat 8 (i + 1)])
      (t, acc.2 ++ t)) ([], []) = (hkdfT prf prk info j, blocksOut (hkdfT prf prk info) j) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [List.range_succ, List.foldl_append, ih, blocksOut_succ]
    rfl

theorem hkdfExpand_eq (n L : Nat) :
    hkdfExpand prf n prk info L = (blocksOut (hkdfT prf prk info) ((L + n - 1) / n)).take L := by
  simp only [hkdfExpand, hkdf_fold]

end

/-! ## `Prk::expand_into` -/

/-- `info`'s parts, joined. -/
def infoBytes (info : Slice (Slice U8)) : List U8 := info.val.flatMap (·.val)

theorem stream_updates_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (key : List Byte)
    (parts : List (Slice U8)) (p : List U8) (s : high.hmac.Streaming)
    (hs : StreamOf a key p s)
    (hm : hmacBlock a + p.length + (parts.flatMap (·.val)).length ≤ maxInput) :
    parts.foldlM high.hmac.Streaming.update s ⦃ s' =>
      StreamOf a key (p ++ parts.flatMap (·.val)) s' ⦄ := by
  induction parts generalizing p s with
  | nil =>
    simp only [List.foldlM_nil, List.flatMap_nil, List.append_nil]
    exact (WP.spec_ok s).mpr hs
  | cons x parts ih =>
    simp only [List.foldlM_cons, List.flatMap_cons, List.length_append] at hm ⊢
    apply WP.spec_bind (stream_update_spec a hr key p s hs x (by simp only [Slice.length]; omega))
    intro s' hs'
    have := ih (p ++ x.val) s' hs' (by simp only [List.length_append]; omega)
    simpa using this

theorem counterSlice_val (c : Nat) : (counterSlice c).val = [⟨BitVec.ofNat 8 c⟩] := by
  simp [counterSlice]

theorem expand_into_loop_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (prk : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput) :
    ∀ (m c : Nat) (block : Option high.digest.Digest) (out : Slice U8),
      out.length - (c - 1) * tagLen a = m → 1 ≤ c →
      (match block with
        | none => c = 1
        | some t => outLen t.algorithm = tagLen a ∧
            digestBytes t = hkdfT (hmacOf a) prk (bv (infoBytes info)) (c - 1)) →
      out.length ≤ 255 * tagLen a →
      (bv out.val).take ((c - 1) * tagLen a) =
        (blocksOut (hkdfT (hmacOf a) prk (bv (infoBytes info))) (c - 1)).take out.length →
      high.hkdf.Prk.expand_into_loop k info (tagLen a) block c ((c - 1) * tagLen a) out ⦃ r =>
        r.length = out.length ∧
          bv r.val = (blocksOut (hkdfT (hmacOf a) prk (bv (infoBytes info)))
            ((out.length + tagLen a - 1) / tagLen a)).take out.length ⦄ := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c block out hm hc hb hL hpre
  have hn := tagLen_pos a
  have hlen : ∀ x, (hmacOf a prk x).length = tagLen a := fun x => hmacOf_length a prk x hr
  have hTlen : ∀ i, (hkdfT (hmacOf a) prk (bv (infoBytes info)) (i + 1)).length = tagLen a :=
    fun i => hlen _
  rw [high.hkdf.Prk.expand_into_loop]
  split
  · rename_i hcond
    obtain ⟨hoff, hc255, -⟩ := hcond
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hb hpre hoff hm ⊢
    apply WP.spec_bind (key_start_spec a hr prk k hk)
    intro ctx hctx
    apply WP.spec_bind (Pₘ := fun ctx => ∃ p : List U8,
      bv p = hkdfT (hmacOf a) prk (bv (infoBytes info)) c' ∧ p.length ≤ tagLen a ∧
        StreamOf a prk p ctx)
    · cases block with
      | none =>
        simp only at hb
        obtain rfl : c' = 0 := by omega
        simp only [WP.spec_ok]
        exact ⟨[], rfl, by simp, hctx⟩
      | some t =>
        obtain ⟨htl, htb⟩ := hb
        simp only
        step with digest_as_ref_spec t as ⟨s, hsl, hsb⟩
        apply WP.spec_mono (stream_update_spec a hr prk [] ctx hctx s (by
          have := tagLen_le a
          simp only [List.length_nil, Slice.length] at hsl ⊢; omega))
        intro ctx' hctx'
        refine ⟨s.val, by rw [hsb, htb], ?_, by simpa using hctx'⟩
        simp only [Slice.length] at hsl; omega
    · rintro ctx1 ⟨p, hpb, hpl, hctx1⟩
      apply WP.spec_bind (stream_updates_spec a hr prk info.val p ctx1 hctx1 (by
        show hmacBlock a + p.length + (infoBytes info).length ≤ maxInput
        omega))
      intro ctx2 hctx2
      apply WP.spec_bind (stream_update_spec a hr prk _ ctx2 hctx2 (counterSlice (c' + 1)) (by
        show hmacBlock a + (p ++ infoBytes info).length + (counterSlice (c' + 1)).val.length ≤ maxInput
        simp only [List.length_append, counterSlice_val, List.length_singleton]
        omega))
      intro ctx3 hctx3
      apply WP.spec_bind (stream_finish_spec a hr prk _ ctx3 hctx3 (by
        show hmacBlock a + (p ++ infoBytes info ++ (counterSlice (c' + 1)).val).length ≤ maxInput
        simp only [List.length_append, counterSlice_val, List.length_singleton]
        omega))
      rintro tag ⟨htl, htb⟩
      step with digest_as_ref_spec tag as ⟨s, hsl, hsb⟩
      have hT : bv s.val = hkdfT (hmacOf a) prk (bv (infoBytes info)) (c' + 1) := by
        rw [hsb, htb, hkdfT, ← hpb]
        simp only [bv_append, counterSlice_val]
        rfl
      have hsl' : s.val.length = tagLen a := by
        have : s.length = tagLen a := by rw [hsl, htl]
        simpa only [Slice.length] using this
      split
      · rename_i hle
        rw [show c' * tagLen a + tagLen a = (c' + 1 + 1 - 1) * tagLen a by
          simp only [Nat.add_sub_cancel]; ring]
        have hlen' := Slice.setSlice!_length out (c' * tagLen a)
          (s.val.take (min (tagLen a) (out.length - c' * tagLen a)))
        apply WP.spec_mono (ih _ (by rw [hlen', Nat.add_sub_cancel, Nat.add_mul, one_mul]; omega)
          (c' + 1 + 1) (some tag)
          (out.setSlice! (c' * tagLen a) (s.val.take (min (tagLen a) (out.length - c' * tagLen a))))
          rfl (by omega) ⟨htl, by rw [Nat.add_sub_cancel, ← hT, hsb]⟩ (by rw [hlen']; exact hL) ?_)
        · rintro r ⟨hrl, hrv⟩
          rw [hlen'] at hrl hrv
          exact ⟨hrl, hrv⟩
        · rw [hlen', Nat.add_sub_cancel, Slice.setSlice!_val]
          exact prefix_step _ _ hTlen out.val s.val c' hoff hsl' hT hpre
      · rename_i hgt
        exfalso
        apply hgt
        simp only [Slice.length] at hsl' ⊢
        omega
  · rename_i hcond
    simp only [WP.spec_ok]
    refine ⟨by simp, ?_⟩
    have hdone : out.length ≤ (c - 1) * tagLen a := by
      by_contra h
      apply hcond
      refine ⟨by omega, ?_, hn⟩
      by_contra h'
      have : 255 * tagLen a ≤ (c - 1) * tagLen a := Nat.mul_le_mul_right _ (by omega)
      omega
    exact prefix_done _ _ hTlen hn (bv out.val) (c - 1) (by rw [bv_length]; exact hdone)
      (by rw [bv_length]; exact hpre) |>.trans (by rw [bv_length])

/-- `Prk::expand_into` fills `out` with HKDF-Expand's output. -/
theorem expand_into_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (prk : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput) (out : Slice U8)
    (hL : out.length ≤ 255 * tagLen a) :
    high.hkdf.Prk.expand_into k info out ⦃ r => r.length = out.length ∧
      bv r.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) out.length ⦄ := by
  obtain ⟨n, hn, hnv⟩ := tagLen_eq a
  have hloop := expand_into_loop_spec a hr prk k hk info hinfo _ 1 none out rfl le_rfl rfl hL
    (by simp [blocksOut])
  obtain ⟨⟨e, he⟩, -⟩ := hr
  simp only [Nat.sub_self, Nat.zero_mul] at hloop
  unfold high.hkdf.Prk.expand_into
  have h0 : ¬ (tagLen a = 0) := by have := tagLen_pos a; omega
  rw [he, bind_ok, key_algorithm_eq hk, bind_ok, hn, bind_ok, hnv]
  simp only [h0, ↓reduceIte]
  apply WP.spec_mono hloop
  rintro r ⟨h1, h2⟩
  exact ⟨h1, by rw [h2, hkdfExpand_eq]⟩

/-- `Okm::fill` fills `out` with HKDF-Expand's output when `out` is the
length asked for and at most 255 blocks, and refuses it otherwise. -/
theorem okm_fill_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (prk : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput) (len : Usize)
    (out : Slice U8) :
    high.hkdf.Okm0Usize.fill { prk := k, info, len } out ⦃ r =>
      if out.length = len.val ∧ out.length ≤ 255 * tagLen a then
        r.1 = .Ok () ∧ r.2.length = out.length ∧
          bv r.2.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) out.length
      else r = (.Err .WrongLength, out) ⦄ := by
  obtain ⟨n, hn, hnv⟩ := tagLen_eq a
  have hn64 : tagLen a ≤ 64 := by cases a <;> decide
  unfold high.hkdf.Okm0Usize.fill
  simp only [key_algorithm_eq hk, hn, bind_ok]
  split
  · rename_i hne
    simp only [WP.spec_ok]
    split
    · rename_i hc
      exfalso
      obtain ⟨h, -⟩ := hc
      simp only [bne_iff_ne, ne_eq] at hne
      apply hne
      apply UScalar.eq_of_val_eq
      rw [Slice.len_val, h]
    · trivial
  · rename_i heq
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at heq
    have hlen : out.length = len.val := by rw [← heq, Slice.len_val]
    step as ⟨i3, hi3⟩
    split
    · rename_i hgt
      simp only [WP.spec_ok]
      split
      · rename_i hc
        exfalso
        obtain ⟨-, h⟩ := hc
        simp only [GT.gt, UScalar.lt_equiv, Slice.len_val] at hgt
        omega
      · trivial
    · rename_i hle
      simp only [GT.gt, UScalar.lt_equiv, Slice.len_val, not_lt] at hle
      apply WP.spec_bind (expand_into_spec a hr prk k hk info hinfo out (by omega))
      rintro r ⟨h1, h2⟩
      simp only [WP.spec_ok]
      split
      · exact ⟨trivial, h1, h2⟩
      · rename_i hc
        exact absurd ⟨hlen, by omega⟩ hc

/-- `Salt::new` keys HMAC with the salt. -/
theorem salt_new_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (salt : Slice U8)
    (hs : salt.length ≤ maxInput) :
    high.hkdf.Salt.new a salt ⦃ k => KeyOf a (bv salt.val) k ⦄ := by
  unfold high.hkdf.Salt.new
  apply WP.spec_bind (key_new_spec a hr salt hs)
  intro k hk
  simpa using hk

/-- `Salt::extract` is HKDF-Extract: the PRK is HMAC of the secret under the salt. -/
theorem salt_extract_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (salt : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a salt k) (secret : Slice U8)
    (hm : hmacBlock a + secret.length ≤ maxInput) :
    high.hkdf.Salt.extract k secret ⦃ prk =>
      KeyOf a (hkdfExtract (hmacOf a) salt (bv secret.val)) prk ⦄ := by
  have hsign := sign_spec a hr salt k hk secret hm
  have hnew := key_new_spec a hr
  obtain ⟨⟨e, he⟩, -⟩ := hr
  unfold high.hkdf.Salt.extract
  rw [he, bind_ok]
  apply WP.spec_bind hsign
  rintro d ⟨hdl, hdb⟩
  rw [key_algorithm_eq hk, bind_ok]
  unfold high.hmac.Tag.Insts.CoreConvertAsRefSliceU8.as_ref
  step with digest_as_ref_spec d as ⟨s, hsl, hsb⟩
  apply WP.spec_bind (hnew s (by
    have h64 : tagLen a ≤ 64 := by cases a <;> decide
    rw [hsl, hdl]; unfold maxInput; scalar_tac))
  intro prk hprk
  simp only [WP.spec_ok]
  rw [hsb, hdb] at hprk
  exact hprk

/-- HKDF in rind's calls: `Salt::new(a, salt).extract(ikm).expand(info, len).fill(out)`
fills `out` with RFC 5869's HKDF-Expand of HKDF-Extract's PRK, for any `len`
that is `out`'s length and at most 255 blocks. -/
theorem hkdf_fill (a : high.hmac.Algorithm) (hr : RunsHmac a) (inst : high.hkdf.KeyType Usize)
    (salt ikm : Slice U8) (info : Slice (Slice U8)) (len : Usize) (out : Slice U8)
    (hs : salt.length ≤ maxInput) (hm : hmacBlock a + ikm.length ≤ maxInput)
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput)
    (hlen : out.length = len.val) (hL : out.length ≤ 255 * tagLen a) :
    (do
      let s ← high.hkdf.Salt.new a salt
      let prk ← high.hkdf.Salt.extract s ikm
      let okm ← high.hkdf.Prk.expand inst prk info len
      high.hkdf.Okm0Usize.fill okm out) ⦃ r =>
      r.1 = .Ok () ∧ bv r.2.val = hkdfExpand (hmacOf a) (tagLen a)
        (hkdfExtract (hmacOf a) (bv salt.val) (bv ikm.val)) (bv (infoBytes info)) out.length ⦄ := by
  apply WP.spec_bind (salt_new_spec a hr salt hs)
  intro s hsk
  apply WP.spec_bind (salt_extract_spec a hr _ s hsk ikm hm)
  intro prk hprk
  simp only [high.hkdf.Prk.expand, bind_ok]
  apply WP.spec_mono (okm_fill_spec a hr _ prk hprk info hinfo len out)
  intro r hr'
  split at hr'
  · exact ⟨hr'.1, hr'.2.2⟩
  · rename_i hc
    exact absurd (And.intro hlen hL) hc

/-! ## The conversions from `Okm`

Each `From<Okm<..>>` fills a zeroed 64-byte buffer's first `len` bytes with
`Prk::expand_into`, then makes its key of them. Its `len` is the length the
key takes, so the buffer's `..len` is that many bytes. -/

/-- `high::hmac::Key`'s conversion from `Okm` keys HMAC under `a` with the
`tag_len` bytes of HKDF-Expand. -/
theorem hmac_key_from_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (prk : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput) :
    high.hmac.Key.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
      { prk := k, info := info, len := a } ⦃ key =>
      KeyOf a (hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (tagLen a)) key ⦄ := by
  obtain ⟨m, hm, hmv⟩ := tagLen_eq a
  have h64 : tagLen a ≤ 64 := by cases a <;> decide
  have hpos := tagLen_pos a
  unfold high.hmac.Key.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
  simp only [hm, bind_ok]
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice (Array.repeat 64#usize 0#u8)
    { «end» := m } (by scalar_tac))
  rintro ⟨bytes, back⟩ ⟨hb1, hb2, -⟩
  have hblen : bytes.length = tagLen a := by rw [← hmv]; exact hb2
  apply WP.spec_bind (expand_into_spec a hr prk k hk info hinfo bytes (by rw [hblen]; omega))
  rintro bytes1 ⟨hl1, hl2⟩
  have hbv : bv bytes1.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (tagLen a) := by
    rw [hl2, hblen]
  apply WP.spec_mono (key_new_spec a hr bytes1 (by rw [hl1, hblen]; omega))
  intro key' hkey
  rw [hbv] at hkey
  exact hkey

/-- The header-protection key that `HeaderProtectionKey::new` gives ChaCha20 for
32 bytes holds them, as `chacha20_new` states: the translation's wrapper refuses
nothing that `new` accepts, and panics where `new` refuses. -/
theorem header_new_spec (key : Slice U8) (hk : key.length = 32) :
    aead.quic.HeaderProtectionKey.new rind.x86_64.aead.quic.CHACHA20 key ⦃ r =>
      ∃ c : mid.chacha20.ChaCha20, r = .Ok (.ChaCha20 c) ∧ c.key.val = key.val ⦄ := by
  unfold aead.quic.HeaderProtectionKey.new
  apply WP.spec_bind (rind.x86_64.chacha20_new key)
  intro r hr
  rw [if_pos hk] at hr
  obtain ⟨c, rfl, hc⟩ := hr
  exact (WP.spec_ok _).mpr ⟨c, rfl, hc⟩

/-- `aead::quic::HeaderProtectionKey`'s conversion from `Okm` keys ChaCha20 with
the 32 bytes of HKDF-Expand. -/
theorem header_key_from_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (prk : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput) :
    aead.quic.HeaderProtectionKey.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
      { prk := k, info := info, len := rind.x86_64.aead.quic.CHACHA20 } ⦃ key =>
      ∃ c : mid.chacha20.ChaCha20, key = .ChaCha20 c ∧
        bv c.key.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) 32 ⦄ := by
  have hpos := tagLen_pos a
  unfold aead.quic.HeaderProtectionKey.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
  unfold aead.quic.Algorithm.key_len
  have hk32 : (rind.x86_64.aead.quic.Algorithm.key_len rind.x86_64.aead.quic.CHACHA20).val = 32 := rfl
  simp only [bind_ok]
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice (Array.repeat 64#usize 0#u8)
    { «end» := rind.x86_64.aead.quic.Algorithm.key_len rind.x86_64.aead.quic.CHACHA20 }
    (by scalar_tac))
  rintro ⟨bytes, back⟩ ⟨hb1, hb2, -⟩
  have hblen : bytes.length = 32 := by rw [hb2]; exact hk32
  apply WP.spec_bind (expand_into_spec a hr prk k hk info hinfo bytes (by rw [hblen]; omega))
  rintro bytes1 ⟨hl1, hl2⟩
  have hbv : bv bytes1.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) 32 := by
    rw [hl2, hblen]
  apply WP.spec_bind (header_new_spec bytes1 (by rw [hl1, hblen]))
  rintro r ⟨c, rfl, hc⟩
  unfold core.result.Result.expect
  exact (WP.spec_ok _).mpr ⟨c, rfl, by rw [hc]; exact hbv⟩

/-- `high::hkdf::Prk`'s conversion from `Okm` keys the PRK, which is HMAC's key,
under `a` with the `tag_len` bytes of HKDF-Expand. -/
theorem prk_from_spec (a : high.hmac.Algorithm) (hr : RunsHmac a) (prk : List Byte)
    (k : high.hmac.Key) (hk : KeyOf a prk k) (info : Slice (Slice U8))
    (hinfo : hmacBlock a + tagLen a + (infoBytes info).length + 1 ≤ maxInput) :
    high.hkdf.Prk.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
      { prk := k, info := info, len := a } ⦃ key =>
      KeyOf a (hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (tagLen a)) key ⦄ := by
  obtain ⟨m, hm, hmv⟩ := tagLen_eq a
  have h64 : tagLen a ≤ 64 := by cases a <;> decide
  have hpos := tagLen_pos a
  unfold high.hkdf.Prk.Insts.CoreConvertFromOkm0SharedStaticAlgorithm.from
  simp only [hm, bind_ok]
  apply WP.spec_bind (Array.index_mut_SliceIndexRangeToUsizeSlice (Array.repeat 64#usize 0#u8)
    { «end» := m } (by scalar_tac))
  rintro ⟨bytes, back⟩ ⟨hb1, hb2, -⟩
  have hblen : bytes.length = tagLen a := by rw [← hmv]; exact hb2
  apply WP.spec_bind (expand_into_spec a hr prk k hk info hinfo bytes (by rw [hblen]; omega))
  rintro bytes1 ⟨hl1, hl2⟩
  have hbv : bv bytes1.val = hkdfExpand (hmacOf a) (tagLen a) prk (bv (infoBytes info)) (tagLen a) := by
    rw [hl2, hblen]
  apply WP.spec_bind (key_new_spec a hr bytes1 (by rw [hl1, hblen]; omega))
  intro key' hkey
  rw [hbv] at hkey
  exact (WP.spec_ok _).mpr hkey

end rind.x86_64.kdf
