import Rind.Armv7.X25519Bytes
import Rind.Armv7.Dalek
open Aeneas Aeneas.Std Result rind.spec

/-!
# X25519's dispatch on armv7

`low::arm::curve25519` runs X25519's shared secret on BoringSSL's NEON ladder
where the CPU has NEON, which no proof covers, and on curve25519-dalek
otherwise; the public key runs on dalek on every CPU. This states what each
returns where both run dalek, in the terms `Rind.Armv7.X25519`, x86_64's
proof with the target renamed, reads them in: `DalekCpu o`, that the NEON
check returned `o` and that it is `none`, takes the place of x86_64's IFMA
check, and `cpuX25519 o` is dalek's X25519 as BAIF's theorems, which
`Rind.Armv7.Dalek` restates, state it. Those theorems therefore hold on a CPU
without NEON, the public key's included.
-/

namespace rind.armv7

variable {o : Option low.arm.cpu.HaveNeon}

/-- rind runs on this CPU: its entry guards' checks pass. Neither reads an input. -/
def Runs : Prop :=
  (∃ e, low.entry.Entry.new_secret = ok e) ∧ ∃ e, low.entry.Entry.new_public = ok e

/-- The NEON check returned `o`, and the CPU lacks NEON, so X25519 runs
curve25519-dalek for its shared secret as for its public key. The check reads
no input. -/
def DalekCpu (o : Option low.arm.cpu.HaveNeon) : Prop :=
  low.arm.cpu.HaveNeon.check = ok o ∧ o = none

/-- RFC 7748's X25519, as the CPUs `DalekCpu` admits compute it: BAIF's spec
of dalek's. -/
def cpuX25519 (_ : Option low.arm.cpu.HaveNeon) : Nat → Nat → Nat := dalekX25519

@[step]
theorem new_secret_spec (h : Runs) : low.entry.Entry.new_secret ⦃ _ => True ⦄ := by
  obtain ⟨⟨e, he⟩, -⟩ := h
  simp [he]

@[step]
theorem new_public_spec (h : Runs) : low.entry.Entry.new_public ⦃ _ => True ⦄ := by
  obtain ⟨-, ⟨e, he⟩⟩ := h
  simp [he]

/-- `to_bytes` is `mid::util::u64x4_to_little_endian`, whose code it copies. -/
theorem to_bytes_eq (w : Std.Array U64 4#usize) :
    low.portable.curve25519.to_bytes w = mid.util.u64x4_to_little_endian w := by
  unfold low.portable.curve25519.to_bytes mid.util.u64x4_to_little_endian
    low.portable.curve25519.to_bytes_loop mid.util.u64x4_to_little_endian_loop
    low.portable.curve25519.to_bytes_loop.body mid.util.u64x4_to_little_endian_loop.body
  rfl

/-- `from_bytes` is `mid::util::little_endian_to_u64x4`, whose code it copies. -/
theorem from_bytes_eq (b : Std.Array U8 32#usize) :
    low.portable.curve25519.from_bytes b = mid.util.little_endian_to_u64x4 b := by
  unfold low.portable.curve25519.from_bytes mid.util.little_endian_to_u64x4
    low.portable.curve25519.from_bytes_loop mid.util.little_endian_to_u64x4_loop
    low.portable.curve25519.from_bytes_loop.body mid.util.little_endian_to_u64x4_loop.body
  rfl

@[step]
theorem portable_to_bytes_spec (w : Std.Array U64 4#usize) :
    low.portable.curve25519.to_bytes w ⦃ b => leNat b.val = wordsNat w.val ⦄ := by
  rw [to_bytes_eq]
  exact u64x4_to_le_spec w

@[step]
theorem portable_from_bytes_spec (b : Std.Array U8 32#usize) :
    low.portable.curve25519.from_bytes b ⦃ w => wordsNat w.val = leNat b.val ⦄ := by
  rw [from_bytes_eq]
  exact le_to_u64x4_spec b

/-- dalek's ladder, on the 32 little-endian bytes of the words. -/
theorem portable_x25519_spec (res scalar point : Std.Array U64 4#usize) :
    low.portable.curve25519.curve25519_x25519 res scalar point ⦃ r =>
      wordsNat r.val = dalekX25519 (wordsNat scalar.val) (wordsNat point.val) ⦄ := by
  unfold low.portable.curve25519.curve25519_x25519
  step as ⟨u, hu⟩
  step as ⟨k, hk⟩
  step as ⟨m, hm⟩
  step as ⟨r, hr⟩
  rw [hr, ← hk, ← hu]
  exact dalekX25519_eq k u m hm

/-- The base point's multiple, which runs on dalek on every CPU. -/
@[step]
theorem curve25519_x25519base_spec (_hi : DalekCpu o) (res scalar : Std.Array U64 4#usize) :
    low.portable.curve25519.curve25519_x25519base res scalar ⦃ r =>
      wordsNat r.val = cpuX25519 o (wordsNat scalar.val) 9 ⦄ := by
  unfold low.portable.curve25519.curve25519_x25519base
  step as ⟨k, hk⟩
  step as ⟨m, hm⟩
  step as ⟨r, hr⟩
  rw [hr, cpuX25519, ← hk]
  exact dalekX25519_base_eq k m hm

/-- The dispatch runs dalek on a CPU without NEON. -/
@[step]
theorem curve25519_x25519_spec (hi : DalekCpu o) (res scalar point : Std.Array U64 4#usize) :
    low.arm.curve25519.curve25519_x25519 res scalar point ⦃ r =>
      wordsNat r.val = cpuX25519 o (wordsNat scalar.val) (wordsNat point.val) ⦄ := by
  obtain ⟨hc, rfl⟩ := hi
  unfold low.arm.curve25519.curve25519_x25519
  simp only [hc, bind_ok]
  exact portable_x25519_spec res scalar point

/-- The bitwise-or of a difference into an accumulator is zero exactly when
both are. -/
theorem or_xor_eq_zero (d a b : U64) : (d ||| (a ^^^ b)) = 0#u64 ↔ d = 0#u64 ∧ a = b := by
  have key : ∀ u v : U64, u = v ↔ u.val = v.val := fun u v => ⟨fun h => h ▸ rfl, UScalar.eq_of_val_eq⟩
  rw [key, key d, key a b, UScalar.val_or, UScalar.val_xor]
  simp [Nat.or_eq_zero_iff, Nat.xor_eq_zero_iff]

/-- Equal numbers of equally many words are the same words. -/
theorem wordsNat_inj (x y : List U64) (hl : x.length = y.length) : wordsNat x = wordsNat y ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have hm : x.map (·.val) = y.map (·.val) :=
    Nat.ofDigits_inj_of_len_eq (b := 2 ^ 64) (by norm_num) (by simp [hl])
      (fun l hl => by obtain ⟨u, -, rfl⟩ := List.mem_map.mp hl; exact u.hBounds)
      (fun l hl => by obtain ⟨u, -, rfl⟩ := List.mem_map.mp hl; exact u.hBounds) h
  exact List.map_injective_iff.mpr (fun a b hab => UScalar.eq_of_val_eq hab) hm

theorem bignum_eq_loop_spec (x y : Slice U64) (hl : x.length = y.length)
    (iter : core.ops.range.Range Std.Usize) (diff : U64)
    (he : iter.end.val = x.length) (hs : iter.start.val ≤ x.length)
    (hd : diff = 0#u64 ↔ ∀ j < iter.start.val, x.val[j]? = y.val[j]?) :
    low.portable.bignum_eq.bignum_eq_loop iter x y diff ⦃ d =>
      d = 0#u64 ↔ ∀ j < x.length, x.val[j]? = y.val[j]? ⦄ := by
  unfold low.portable.bignum_eq.bignum_eq_loop
  apply loop.spec_decr_nat (fun p => x.length - p.1.start.val)
    (fun p => p.1.end.val = x.length ∧ p.1.start.val ≤ x.length ∧
      (p.2 = 0#u64 ↔ ∀ j < p.1.start.val, x.val[j]? = y.val[j]?))
  · rintro ⟨rg, d⟩ ⟨he, hs, hd⟩
    simp only at he hs hd ⊢
    unfold low.portable.bignum_eq.bignum_eq_loop.body
    step as ⟨o, rg', ho, he'⟩
    split_ifs at ho with hlt
    · obtain ⟨rfl, hst⟩ := ho
      have hx : rg.start.val < x.val.length := by simp only [Slice.length] at he; omega
      have hy : rg.start.val < y.val.length := by simp only [Slice.length] at he hl; omega
      simp only [core.slice.Slice.get, core.slice.index.Usize.get, core.option.OptionShared0T.copied,
        core.option.Option.unwrap_or, bind_ok, lift, Slice.getElem?_Usize_eq, List.getElem?_eq_getElem hx,
        List.getElem?_eq_getElem hy, WP.spec_ok]
      refine ⟨by rw [he']; exact he, by omega, ?_, by omega⟩
      rw [hst, or_xor_eq_zero, hd]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · exact h1 j hj
        · rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy, h2]
      · intro h
        refine ⟨fun j hj => h j (by omega), ?_⟩
        have := h rg.start.val (by omega)
        rw [List.getElem?_eq_getElem hx, List.getElem?_eq_getElem hy] at this
        exact Option.some.inj this
    · obtain ⟨rfl, hst⟩ := ho
      simp only [WP.spec_ok]
      have : rg.start.val = x.length := by omega
      rw [← this]
      exact hd
  · exact ⟨he, hs, hd⟩

/-- `bignum_eq`, on words of equal length, as `Rind.Armv7.X25519` calls it. -/
@[step]
theorem bignum_eq_spec (x y : Slice U64) (hl : x.length = y.length) :
    low.portable.bignum_eq.bignum_eq x y ⦃ b => b = decide (wordsNat x.val = wordsNat y.val) ⦄ := by
  unfold low.portable.bignum_eq.bignum_eq
  simp only [lift, bind_ok, core.cmp.impls.OrdUsize.max]
  have hxy : x.len = y.len := UScalar.eq_of_val_eq (by simpa [Slice.len, Slice.length] using hl)
  simp only [hxy, lt_self_iff_false, ↓reduceIte]
  step with bignum_eq_loop_spec x y hl { start := 0#usize, «end» := y.len } 0#u64
    (by simpa [Slice.len, Slice.length] using hl.symm) (by simp) (by simp) as ⟨d, hd⟩
  simp only [core.hint.black_box, bind_ok, WP.spec_ok]
  rw [decide_eq_decide, hd, wordsNat_inj x.val y.val hl]
  constructor
  · intro h
    apply List.ext_getElem?
    intro j
    by_cases hj : j < x.length
    · exact h j hj
    · rw [List.getElem?_eq_none (by simp only [Slice.length] at hj; omega),
        List.getElem?_eq_none (by simp only [Slice.length] at hj hl; omega)]
  · rintro h j -
    rw [h]

end rind.armv7
