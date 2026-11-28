module

public import VerifiedGarbage.Impl.Scrub.X86_64
public import VerifiedGarbage.Proof.Framework.CodeOnce
public import VerifiedGarbage.TCB.X86_64.Residue
public import VerifiedGarbage.Proof.Framework.X86_64.Depth
public import VerifiedGarbage.Proof.Framework.X86_64.ResidueKeep
public import VerifiedGarbage.Proof.Framework.X86_64.Mxcsr
public import VerifiedGarbage.TCB.Registration
public import VerifiedGarbage.Proof.Framework.X86_64.ScrubPaths
import VerifiedGarbage.Proof.Framework.X86_64.Reduce
import VerifiedGarbage.Proof.Framework.Mem
import VerifiedGarbage.Proof.Framework.X86_64.Inline
import VerifiedGarbage.Proof.Framework.X86_64.Call
import VerifiedGarbage.Proof.Framework.X86_64.Frame
import VerifiedGarbage.Proof.Framework.X86_64.Taint
import VerifiedGarbage.Proof.Framework.X86_64.UpperLock
import VerifiedGarbage.Proof.Framework.X86_64.CallInline
import VerifiedGarbage.Proof.Framework.X86_64.Syms
import VerifiedGarbage.Proof.Framework.Offset

/-!
# Returning without secret residue (x86-64)

`Verified.scrub`: code verified against a contract that `Sig.contract`
derives, whose frames and calls use at most the contract's `stack` bytes,
followed by `Impl.Scrub.X86_64.scrubTail` (`scrub`), is verified against the
same contract and returns without secret residue (`NoResidue`). The proof of
the code is used as it is: what `scrub` adds is checked once, here, for all
code (`tail_run`): it zeroes the stack below `rsp` (`wipe_run`), the SSE
registers and the caller-saved general-purpose registers, and its trace
depends only on `rsp`. What the code itself must satisfy is decidable
(`SpSafe`, its depth, the level of its vector instructions,
`ResidueKeep.lean`, and what it leaves in MXCSR, `Mxcsr.lean`), but for its
postcondition, which must read the memory
on return only within the buffers (`hpost`).
-/

@[expose] public section

open VG.Impl.Scrub.X86_64

namespace VG.X86_64.Scrub

open VG.X86_64 VG.X86_64.Residue

/-- The trace of `store1 ks off base k` from `rsp = p`. -/
def store1Tr (ks : List Nat) (off : Nat) (p : Addr) (base k : Nat) : List Leak :=
  if ks.contains (off + base + 16 * k) then [.addr (p + BitVec.ofNat 64 (base + 16 * k))] else []

/-- The trace of `stores16 w ks off base k` from `rsp = p`. -/
def storesTr (w : Bool) (ks : List Nat) (off : Nat) (p : Addr) (base : Nat) : Nat → List Leak
  | 0 => []
  | 1 => store1Tr ks off p base 0
  | k + 2 =>
    if w && ks.contains (off + base + 16 * (k + 1)) && ks.contains (off + base + 16 * k) then
      .addr (p + BitVec.ofNat 64 (base + 16 * k)) :: storesTr w ks off p base k
    else store1Tr ks off p base (k + 1) ++ storesTr w ks off p base (k + 1)

/-- The trace of `chunkStores w ks off b` from `rsp = p`. -/
def chunkTr (w : Bool) (ks : List Nat) (off : Nat) (p : Addr) (b : Nat) : List Leak :=
  storesTr w ks off p (b % 16) (b / 16) ++ (if b % 16 = 8 && ks.contains off then [.addr p] else [])

/-- Whether `chunkStores ks off b` zeroes the byte at offset `d` of its frame. -/
def covC (ks : List Nat) (off b d : Nat) : Bool :=
  if d < b % 16 then b % 16 == 8 && ks.contains off
  else ks.contains (off + b % 16 + 16 * ((d - b % 16) / 16))

/-- Whether `wipe ks cs` zeroes the byte at offset `i` from the bottom of the
`cs.sum` bytes it wipes. -/
def cov (ks : List Nat) : List Nat → Nat → Bool
  | [], _ => false
  | b :: bs, i => if i < bs.sum then cov ks bs i else decide (i - bs.sum < b) && covC ks bs.sum b (i - bs.sum)

theorem ea_rsp (u : State) (off : Nat) :
    u.ea { base := .rsp, disp := (off : Int) } = u.gpr .rsp + BitVec.ofNat 64 off := by
  simp [State.ea, BitVec.ofInt_natCast]

theorem ea_rsp2 (u : State) (a k : Nat) :
    u.ea { base := .rsp, disp := (a : Int) + 16 * (k : Int) } = u.gpr .rsp + BitVec.ofNat 64 (a + 16 * k) := by
  rw [show (a : Int) + 16 * (k : Int) = ((a + 16 * k : Nat) : Int) by push_cast; rfl, ea_rsp]

theorem off_lt (x p : Addr) (o n : Nat) (ho : o + n < 2 ^ 64) :
    (x - (p + BitVec.ofNat 64 o)).toNat < n ↔ o ≤ (x - p).toNat ∧ (x - p).toNat < o + n := by
  have e : (x - (p + BitVec.ofNat 64 o)) + BitVec.ofNat 64 o = x - p := by bv_omega
  have e' := congrArg BitVec.toNat e
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := o) (by omega_using [ho])] at e'
  have h1 := (x - (p + BitVec.ofNat 64 o)).isLt
  have h2 := (x - p).isLt
  generalize (x - (p + BitVec.ofNat 64 o)).toNat = r at *
  generalize (x - p).toNat = d at *
  by_cases hc : r + o < 2 ^ 64
  · rw [Nat.mod_eq_of_lt hc] at e'; omega_using [e']
  · rw [show r + o = (r + o - 2 ^ 64) + 2 ^ 64 by omega_using [hc], Nat.add_mod_right, Nat.mod_eq_of_lt (by omega_using [ho, h1])] at e'
    omega_using [ho, h1, e', hc]

theorem writeW_zero128 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 128) x = if (x - a).toNat < 16 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

theorem ite_t {p : Prop} [Decidable p] {α : Type} {a b : α} (h : p) : (if p then a else b) = a := by
  simp only [h, ↓reduceIte]

theorem ite_f {p : Prop} [Decidable p] {α : Type} {a b : α} (h : ¬ p) : (if p then a else b) = b := by
  simp only [h, ↓reduceIte]

/-- What `stores16 ks off base k` zeroes, at offset `d` of `rsp`. -/
def SCov (ks : List Nat) (off base k d : Nat) : Prop :=
  base ≤ d ∧ d < base + 16 * k ∧ ks.contains (off + base + 16 * ((d - base) / 16)) = true

theorem writeW_zero256 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 256) x = if (x - a).toNat < 32 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- One granule's store, before stores that zero the `j` granules below it. -/
theorem store1_run (w : Bool) (ks : List Nat) (off b base : Nat) (hb : b < 2 ^ 64) (j : Nat) (L : List Instr)
    (T : Addr → List Leak)
    (ih : ∀ u : State, ⟨u.gpr .rsp, b⟩ ∈ u.wr → (ks ≠ [] → u.xmm .xmm0 = 0) →
      (w = true → ks ≠ [] → u.ymmHi .xmm0 = 0) →
      ∃ m', execBlock isa L u = some ({ u with mem := m' }, T (u.gpr .rsp)) ∧
        (∀ x, SCov ks off base j (x - u.gpr .rsp).toNat → m' x = 0) ∧
        (∀ x, ¬ SCov ks off base j (x - u.gpr .rsp).toNat → m' x = u.mem x))
    (u : State) (hR : ⟨u.gpr .rsp, b⟩ ∈ u.wr) (hx : ks ≠ [] → u.xmm .xmm0 = 0)
    (hy : w = true → ks ≠ [] → u.ymmHi .xmm0 = 0) (hk : base + 16 * (j + 1) ≤ b) :
    ∃ m', execBlock isa (store1 ks off base j ++ L) u =
        some ({ u with mem := m' }, store1Tr ks off (u.gpr .rsp) base j ++ T (u.gpr .rsp)) ∧
      (∀ x, SCov ks off base (j + 1) (x - u.gpr .rsp).toNat → m' x = 0) ∧
      (∀ x, ¬ SCov ks off base (j + 1) (x - u.gpr .rsp).toNat → m' x = u.mem x) := by
  by_cases hkeep : ks.contains (off + base + 16 * j) = true
  · have hx := hx (fun h => by rw [h] at hkeep; cases hkeep)
    have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (base + 16 * j)) 16 := by
      refine ⟨_, hR, ?_⟩
      simp only [Region.Contains]
      rw [show u.gpr .rsp + BitVec.ofNat 64 (base + 16 * j) - u.gpr .rsp = BitVec.ofNat 64 (base + 16 * j) by
        bv_omega]
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb, hk])]; omega_using [hk]
    let a := u.gpr .rsp + BitVec.ofNat 64 (base + 16 * j)
    let u₁ : State := { u with mem := u.mem.writeW a (u.xmm .xmm0) }
    obtain ⟨m', he, hz, hu⟩ := ih u₁ hR (fun _ => hx) hy
    have hw : ∀ x, u₁.mem x = if base + 16 * j ≤ (x - u.gpr .rsp).toNat ∧
        (x - u.gpr .rsp).toNat < base + 16 * j + 16 then 0 else u.mem x := fun x => by
      simp only [u₁, hx, writeW_zero128, a, off_lt _ _ _ _ (show base + 16 * j + 16 < 2 ^ 64 by omega_using [hb, hk])]
    refine ⟨m', ?_, fun x h => ?_, fun x h => ?_⟩
    · simp only [store1, hkeep, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, zero16,
        ea_rsp, State.store128, hin]
      rw [show ({ u with mem := u.mem.writeW a (u.xmm .xmm0) } : State) = u₁ from rfl, he]
      simp [store1Tr, addrs, ea_rsp2, u₁, List.contains_iff_mem.mp hkeep]
    · obtain ⟨h1, h2, h3⟩ := h
      by_cases hc : (x - u.gpr .rsp).toNat < base + 16 * j
      · exact hz x ⟨h1, hc, h3⟩
      · rw [hu x (fun h' => hc h'.2.1), hw x, ite_t ⟨by omega_using [hc], by omega_using [h2]⟩]
    · have hk' : ¬ SCov ks off base j (x - u.gpr .rsp).toNat := fun h' => h ⟨h'.1, by have := h'.2.1; omega_using [this], h'.2.2⟩
      rw [hu x hk', hw x, ite_f fun hg => h ⟨by omega_using [hg], by omega_using [hg], by
        rw [show ((x - u.gpr .rsp).toNat - base) / 16 = j by omega_using [hg]]; exact hkeep⟩]
  · obtain ⟨m', he, hz, hu⟩ := ih u hR hx hy
    refine ⟨m', ?_, fun x h => ?_, fun x h => ?_⟩
    · simp only [store1, store1Tr, hkeep, Bool.false_eq_true, ↓reduceIte, List.nil_append, he]
    · obtain ⟨h1, h2, h3⟩ := h
      by_cases hc : (x - u.gpr .rsp).toNat < base + 16 * j
      · exact hz x ⟨h1, hc, h3⟩
      · rw [show ((x - u.gpr .rsp).toNat - base) / 16 = j by omega_using [h2, hc]] at h3
        exact absurd h3 hkeep
    · exact hu x fun h' => h ⟨h'.1, by have := h'.2.1; omega_using [this], h'.2.2⟩

theorem stores16_run (w : Bool) (ks : List Nat) (off b base : Nat) (hb : b < 2 ^ 64) : ∀ (k : Nat) (u : State),
    ⟨u.gpr .rsp, b⟩ ∈ u.wr → (ks ≠ [] → u.xmm .xmm0 = 0) → (w = true → ks ≠ [] → u.ymmHi .xmm0 = 0) →
    base + 16 * k ≤ b →
    ∃ m', execBlock isa (stores16 w ks off base k) u =
        some ({ u with mem := m' }, storesTr w ks off (u.gpr .rsp) base k) ∧
      (∀ x, SCov ks off base k (x - u.gpr .rsp).toNat → m' x = 0) ∧
      (∀ x, ¬ SCov ks off base k (x - u.gpr .rsp).toNat → m' x = u.mem x)
  | 0, u, _, _, _, _ => ⟨u.mem, rfl, fun _ h => absurd h.2.1 (by have := h.1; omega_using [this]), fun _ _ => rfl⟩
  | 1, u, hR, hx, hy, hk => by
    have := store1_run w ks off b base hb 0 [] (fun _ => [])
      (fun u _ _ _ => ⟨u.mem, rfl, fun _ h => absurd h.2.1 (by have := h.1; omega_using [this]), fun _ _ => rfl⟩) u hR hx hy hk
    simpa only [List.append_nil, stores16, storesTr] using this
  | k + 2, u, hR, hx, hy, hk => by
    by_cases hp : (w && ks.contains (off + base + 16 * (k + 1)) && ks.contains (off + base + 16 * k)) = true
    · -- Two granules, one store.
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hw', hk1⟩, hk0⟩ := hp
      subst hw'
      have hne : ks ≠ [] := fun h => by rw [h] at hk0; cases hk0
      have hx0 := hx hne
      have hy0 := hy rfl hne
      have hin : InRegions u.wr (u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k)) 32 := by
        refine ⟨_, hR, ?_⟩
        simp only [Region.Contains]
        rw [show u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k) - u.gpr .rsp = BitVec.ofNat 64 (base + 16 * k) by
          bv_omega]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hb, hk])]; omega_using [hk]
      have hymm : u.ymm .xmm0 = 0 := by
        simp only [State.ymm, hx0, hy0]; rfl
      let a := u.gpr .rsp + BitVec.ofNat 64 (base + 16 * k)
      let u₁ : State := { u with mem := u.mem.writeW a (0 : BitVec 256) }
      obtain ⟨m', he, hz, hu⟩ := stores16_run true ks off b base hb k u₁ hR hx hy (by omega_using [hk])
      have hwm : ∀ x, u₁.mem x = if base + 16 * k ≤ (x - u.gpr .rsp).toNat ∧
          (x - u.gpr .rsp).toNat < base + 16 * k + 32 then 0 else u.mem x := fun x => by
        simp only [u₁, writeW_zero256, a, off_lt _ _ _ _ (show base + 16 * k + 32 < 2 ^ 64 by omega_using [hb, hk])]
      refine ⟨m', ?_, fun x h => ?_, fun x h => ?_⟩
      · simp only [stores16, storesTr, hk1, hk0, Bool.and_self, ↓reduceIte, execBlock, isa, reduceExec,
          zero32, ea_rsp, State.store256, hin, hymm]
        rw [show ({ u with mem := u.mem.writeW a (0 : BitVec 256) } : State) = u₁ from rfl, he]
        simp [addrs, ea_rsp2, u₁]
      · obtain ⟨h1, h2, h3⟩ := h
        by_cases hc : (x - u.gpr .rsp).toNat < base + 16 * k
        · exact hz x ⟨h1, hc, h3⟩
        · rw [hu x (fun h' => hc h'.2.1), hwm x, ite_t ⟨by omega_using [hc], by omega_using [h2]⟩]
      · have hk' : ¬ SCov ks off base k (x - u.gpr .rsp).toNat := fun h' => h ⟨h'.1, by have := h'.2.1; omega_using [this], h'.2.2⟩
        rw [hu x hk', hwm x, ite_f fun hg => h ⟨by omega_using [hg], by omega_using [hg], by
          rcases (show ((x - u.gpr .rsp).toNat - base) / 16 = k ∨ ((x - u.gpr .rsp).toNat - base) / 16 = k + 1 by
            omega_using [hg]) with e | e <;> rw [e]
          · exact hk0
          · exact hk1⟩]
    · have := store1_run w ks off b base hb (k + 1) (stores16 w ks off base (k + 1))
        (fun p => storesTr w ks off p base (k + 1))
        (fun u hR hx hy => stores16_run w ks off b base hb (k + 1) u hR hx hy (by omega_using [hk])) u hR hx hy hk
      simpa only [stores16, storesTr, hp, Bool.false_eq_true, ↓reduceIte] using this

theorem writeW_zero64 (m : Mem) (a x : Addr) :
    m.writeW a (0 : BitVec 64) x = if (x - a).toNat < 8 then 0 else m x := by
  simp only [Mem.writeW, Mem.write]
  split <;> simp

/-- What `chunkStores ks off b` zeroes, at offset `d` of `rsp`. -/
def CCov (ks : List Nat) (off b d : Nat) : Prop := d < b ∧ covC ks off b d = true

theorem chunk_run (w : Bool) (ks : List Nat) (off b : Nat) (hb : b < 2 ^ 64) (h8 : b % 8 = 0) (u : State)
    (hR : ⟨u.gpr .rsp, b⟩ ∈ u.wr) (hx : ks ≠ [] → u.xmm .xmm0 = 0) (hy : w = true → ks ≠ [] → u.ymmHi .xmm0 = 0)
    (hr : ks ≠ [] → u.gpr .r11 = 0) :
    ∃ m', execBlock isa (chunkStores w ks off b) u = some ({ u with mem := m' }, chunkTr w ks off (u.gpr .rsp) b) ∧
      (∀ x, CCov ks off b (x - u.gpr .rsp).toNat → m' x = 0) ∧
      (∀ x, ¬ CCov ks off b (x - u.gpr .rsp).toNat → m' x = u.mem x) := by
  obtain ⟨m₁, he, hz, hu⟩ := stores16_run w ks off b (b % 16) hb (b / 16) u hR hx hy (by omega_using [])
  have hbb : b % 16 + 16 * (b / 16) = b := by omega_using []
  -- `SCov` within the chunk is `CCov` above its 8-byte granule.
  have hsc : ∀ d, SCov ks off (b % 16) (b / 16) d ↔ b % 16 ≤ d ∧ CCov ks off b d := by
    intro d
    simp only [SCov, CCov, covC, hbb]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by simp only [show ¬ d < b % 16 by omega_using [h1], ↓reduceIte]; exact h3⟩
    · rintro ⟨h1, h2, h3⟩; simp only [show ¬ d < b % 16 by omega_using [h1], ↓reduceIte] at h3; exact ⟨h1, h2, h3⟩
  unfold chunkStores store8s
  rw [execBlock_append, he]
  by_cases h16 : (b % 16 = 8 && ks.contains off) = true
  · have h0 : BitVec.ofInt 64 0 = 0 := rfl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h16
    have hr := hr (fun h => by have := h16.2; rw [h] at this; cases this)
    have hin8 : InRegions u.wr (u.gpr .rsp) 8 := by
      refine ⟨_, hR, ?_⟩; simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega
    have hea : u.gpr .rsp + BitVec.ofInt 64 0 = u.gpr .rsp := by rw [h0]; bv_omega
    refine ⟨m₁.writeW (u.gpr .rsp) (u.gpr .r11), ?_, fun x h => ?_, fun x h => ?_⟩
    · simp only [h16, decide_true, Bool.and_self, ↓reduceIte, Option.bind_some, execBlock, isa, reduceExec,
        State.store64, State.ea, hea, hin8]
      simp [chunkTr, addrs, State.ea, h16, List.contains_iff_mem.mp h16.2]
    · rw [hr, writeW_zero64]
      split
      · rfl
      · exact hz x ((hsc _).mpr ⟨by omega_arith, h⟩)
    · rw [hr, writeW_zero64]
      split
      · exact absurd ⟨by omega, by
          unfold covC; rw [h16.1]
          simp only [show (x - u.gpr .rsp).toNat < 8 by omega_arith, ↓reduceIte, beq_self_eq_true, h16.2,
            Bool.and_self]⟩ h
      · exact hu x fun h' => h ((hsc _).mp h').2
  · refine ⟨m₁, ?_, fun x h => ?_, fun x h => hu x fun h' => h ((hsc _).mp h').2⟩
    · have h16' : ¬ (b % 16 = 8 ∧ off ∈ ks) := fun ⟨a, c⟩ => h16 (by simp [a, c])
      simp [h16', chunkTr, execBlock]
    · by_cases hd : (x - u.gpr .rsp).toNat < b % 16
      · obtain ⟨-, h2⟩ := h
        simp only [covC, hd, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h2
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at h16
        exact absurd h2.2 (by simpa using h16 h2.1)
      · exact hz x ((hsc _).mpr ⟨by omega_using [hd], h⟩)

theorem below_split (p : Addr) (b n : Nat) (h : b + n ≤ p.toNat) (x : Addr) :
    (⟨p - BitVec.ofNat 64 (b + n), b + n⟩ : Region).Contains x 1 ↔
      (x - (p - BitVec.ofNat 64 b)).toNat < b ∨
        (⟨p - BitVec.ofNat 64 b - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1 := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize p.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := b + n) (by omega_using [h, hp]), Nat.mod_eq_of_lt (a := b) (by omega_using [h, hp]),
    Nat.mod_eq_of_lt (a := n) (by omega_using [h, hp])]
  omega_using []

/-- The offsets of `x` from the bottom of a frame of `b` bytes below `p` and
of the `n` bytes below that. -/
theorem below_idx (p : Addr) (b n : Nat) (h : b + n ≤ p.toNat) (x : Addr) :
    (x - (p - BitVec.ofNat 64 b - BitVec.ofNat 64 n)).toNat = (x - (p - BitVec.ofNat 64 (b + n))).toNat ∧
      (n ≤ (x - (p - BitVec.ofNat 64 (b + n))).toNat →
        (x - (p - BitVec.ofNat 64 b)).toNat = (x - (p - BitVec.ofNat 64 (b + n))).toNat - n) ∧
      ((x - (p - BitVec.ofNat 64 b)).toNat < b →
        (x - (p - BitVec.ofNat 64 (b + n))).toNat = n + (x - (p - BitVec.ofNat 64 b)).toNat) := by
  have hp := p.isLt
  have hx := x.isLt
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  generalize p.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := b + n) (by omega_using [h, hp]), Nat.mod_eq_of_lt (a := b) (by omega_using [h, hp]),
    Nat.mod_eq_of_lt (a := n) (by omega_using [h, hp])]
  refine ⟨by congr 1; omega_using [h, hp], fun h' => by omega_using [h, hp, h'], fun h' => by omega_using [h, hp, h']⟩

/-- What `wipe ks cs` from `rsp = p` zeroes. -/
def WCov (ks cs : List Nat) (p x : Addr) : Prop :=
  (⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1 ∧
    cov ks cs (x - (p - BitVec.ofNat 64 cs.sum)).toNat = true

/-- The trace of `wipe ks cs` from `rsp = p`. -/
def wipeTr (w : Bool) (ks : List Nat) : List Nat → Addr → List Leak
  | [], _ => []
  | b :: bs, p => chunkTr w ks bs.sum (p - BitVec.ofNat 64 b) b ++ wipeTr w ks bs (p - BitVec.ofNat 64 b)

instance (ks cs : List Nat) (p x : Addr) : Decidable (WCov ks cs p x) := by
  unfold WCov; infer_instance

/-- How many unknowns the frames of `wipe ks cs` use when they are released. -/
def wipeK : List Nat → Nat
  | [] => 0
  | b :: bs => wipeK bs + b / 4

/-- The memory `m` with what `wipe ks cs` from `rsp = p` zeroes zero. -/
def zeroW (ks cs : List Nat) (p : Addr) (m : Mem) : Mem :=
  fun x => if WCov ks cs p x then 0 else m x

/-- The memory `m` once the frames of `wipe cs` from `rsp = p`, from the
unknowns `U`, are released (`lose`): the innermost first. -/
def wipeLoseM : List Nat → Addr → (Nat → BitVec 64) → Mem → Mem
  | [], _, _, m => m
  | b :: bs, p, U, m =>
    lose (wipeLoseM bs (p - BitVec.ofNat 64 b) U m) (p - BitVec.ofNat 64 b) b (fun n => U (n + wipeK bs))

/-- A byte the wipe's releases leave depends only on that byte before them. -/
theorem wipeLoseM_congr : ∀ (cs : List Nat) (p : Addr) (U : Nat → BitVec 64) {m₁ m₂ : Mem} (x : Addr),
    m₁ x = m₂ x → wipeLoseM cs p U m₁ x = wipeLoseM cs p U m₂ x
  | [], _, _, _, _, _, h => h
  | _ :: bs, _, U, _, _, x, h => lose_congr _ _ _ (wipeLoseM_congr bs _ U x h)

/-- The wipe's releases change only the `cs.sum` bytes below `p`. -/
theorem wipeLoseM_frame : ∀ (cs : List Nat) (p : Addr) (U : Nat → BitVec 64) (m : Mem),
    Frame [⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩] m (wipeLoseM cs p U m)
  | [], _, _, _ => Frame.refl _ _
  | b :: bs, p, U, m => by
    have e : p - BitVec.ofNat 64 b - BitVec.ofNat 64 bs.sum = p - BitVec.ofNat 64 (b + bs.sum) := by
      rw [BitVec.sub_sub, ← BitVec.ofNat_add]
    refine ((wipeLoseM_frame bs _ U m).sub fun r hr => ?_).trans ((lose_frame _ _ _ _).sub fun r hr => ?_)
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [e, List.sum_cons]
      exact Region.sub_prefix (by omega_using [])
    · simp only [List.mem_singleton] at hr; subst hr
      refine ⟨_, List.mem_singleton_self _, ?_⟩
      rw [List.sum_cons]
      exact Offset.sub_below _ (by omega_using []) (by omega_using [])

/-- `wipe ks cs` from `u`: it zeroes what `WCov` says (`zeroW`), and its
frames' releases lose what they held (`wipeLoseM`), using `wipeK cs`
unknowns. -/
theorem wipe_run (w : Bool) (ks : List Nat) : ∀ (cs : List Nat) (u : State),
    (∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) →
    cs.sum ≤ (u.gpr .rsp).toNat → (ks ≠ [] → u.xmm .xmm0 = 0) → (w = true → ks ≠ [] → u.ymmHi .xmm0 = 0) →
    (ks ≠ [] → u.gpr .r11 = 0) →
    Exec isa (wipe w ks cs) u (wipeTr w ks cs (u.gpr .rsp))
      { u with
        mem := wipeLoseM cs (u.gpr .rsp) u.unknowns (zeroW ks cs (u.gpr .rsp) u.mem)
        unknowns := fun n => u.unknowns (n + wipeK cs) }
  | [], u, _, _, _, _, _ => by
    have e : ({ u with
        mem := wipeLoseM [] (u.gpr .rsp) u.unknowns (zeroW ks [] (u.gpr .rsp) u.mem)
        unknowns := fun n => u.unknowns (n + wipeK []) } : State) = u := by
      have hz : zeroW ks [] (u.gpr .rsp) u.mem = u.mem := by
        funext x; simp [zeroW, WCov, cov]
      simp only [wipeLoseM, hz, wipeK, Nat.add_zero]
    rw [e]; exact .block rfl
  | b :: bs, u, hv, hs, hx, hy, hr => by
    obtain ⟨hb0, hb4, hb8⟩ := hv b (List.mem_cons_self ..)
    simp only [List.sum_cons] at hs
    let p := u.gpr .rsp
    let q := p - BitVec.ofNat 64 b
    let u₁ : State := { u.setReg .rsp q with wr := ⟨q, b⟩ :: u.wr }
    have hpush : isa.push (.alloc b) u = some u₁ := by
      simp only [isa, push, u₁, q, p]; rw [ite_eq_left ⟨hb0, hb4, hb8, by omega_using [hs]⟩]
    have hq : u₁.gpr .rsp = q := by simp [u₁, State.setReg]
    obtain ⟨m₁, he₁, hz₁, hu₁⟩ := chunk_run w ks bs.sum b (by omega_using [hs]) hb8 u₁ (by rw [hq]; simp [u₁])
      (by simpa [u₁, State.setReg] using hx) (by simpa [u₁, State.setReg] using hy)
      (by simpa [u₁, State.setReg] using hr)
    let u₂ : State := { u₁ with mem := m₁ }
    have hqn : bs.sum ≤ q.toNat := by
      have := p.isLt
      have h' : b + bs.sum ≤ p.toNat := hs
      simp only [q, BitVec.toNat_sub, BitVec.toNat_ofNat]
      generalize p.toNat = P at *
      rw [Nat.mod_eq_of_lt (a := b) (by omega_using [hb4])]
      omega_using [hs, this]
    have he₂ := wipe_run w ks bs u₂ (fun b' h => hv b' (List.mem_cons_of_mem _ h))
      (by simpa [u₂, hq] using hqn) (by simpa [u₂, u₁, State.setReg] using hx)
      (by simpa [u₂, u₁, State.setReg] using hy) (by simpa [u₂, u₁, State.setReg] using hr)
    have e₂ : u₂.gpr .rsp = q := hq
    rw [e₂] at he₂
    -- What the chunk and the frames below it zero, as `WCov` says.
    have key : (∀ x, WCov ks (b :: bs) p x → zeroW ks bs q m₁ x = 0) ∧
        (∀ x, ¬ WCov ks (b :: bs) p x → zeroW ks bs q m₁ x = u.mem x) := by
      have hz₂ : ∀ x, WCov ks bs q x → zeroW ks bs q m₁ x = 0 := fun x h => by simp [zeroW, h]
      have hu₂ : ∀ x, ¬ WCov ks bs q x → zeroW ks bs q m₁ x = m₁ x := fun x h => by simp [zeroW, h]
      generalize zeroW ks bs q m₁ = m₂ at hz₂ hu₂ ⊢
      refine ⟨fun x hx' => ?_, fun x hx' => ?_⟩
      all_goals
        have hs' : b + bs.sum ≤ p.toNat := hs
        have hsplit := below_split p b bs.sum hs' x
        obtain ⟨hi1, hi2, hi3⟩ := below_idx p b bs.sum hs' x
        replace hi1 : (x - (q - BitVec.ofNat 64 bs.sum)).toNat = (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat := hi1
        replace hi2 : bs.sum ≤ (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat →
          (x - q).toNat = (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat - bs.sum := hi2
        replace hi3 : (x - q).toNat < b →
          (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat = bs.sum + (x - q).toNat := hi3
        replace hsplit : _ ↔ (x - q).toNat < b ∨ (⟨q - BitVec.ofNat 64 bs.sum, bs.sum⟩ : Region).Contains x 1 := hsplit
        have hz₂ := hz₂ x
        have hu₂ := hu₂ x
        have hz₁ := hz₁ x
        have hu₁ := hu₁ x
        simp only [WCov, List.sum_cons, hq, Region.Contains, CCov] at hx' hz₂ hu₂ hz₁ hu₁ hsplit ⊢
        rw [hi1] at hz₂ hu₂ hsplit
        generalize (x - (p - BitVec.ofNat 64 (b + bs.sum))).toNat = I at hi2 hi3 hsplit hx' hz₂ hu₂
      · -- Zeroed.
        obtain ⟨h1, h2⟩ := hx'
        try simp only [cov] at h2
        by_cases hlt : I < bs.sum
        · simp only [hlt, ↓reduceIte] at h2
          exact hz₂ ⟨by omega_using [hlt], h2⟩
        · simp only [hlt, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h2
          rw [hu₂ (fun h => by omega)]
          exact hz₁ ⟨by rw [hi2 (by omega_using [hlt])]; omega_using [hb0, h1], by rw [hi2 (by omega_using [hlt])]; exact h2.2⟩
      · -- Kept.
        rw [hu₂ (fun ⟨h1, h2⟩ => hx' ⟨by omega_using [h1], by simp only [cov, show I < bs.sum by omega_using [h1], ↓reduceIte]; exact h2⟩)]
        exact hu₁ (fun ⟨h1, h2⟩ => hx' ⟨by rw [hi3 h1]; omega_using [h1], by
          simp only [cov, hi3 h1, show ¬ (bs.sum + (x - q).toNat < bs.sum) by omega_using [], ↓reduceIte,
            Nat.add_sub_cancel_left, h1, decide_true, Bool.true_and]
          exact h2⟩)
    have hZ : zeroW ks bs q m₁ = zeroW ks (b :: bs) p u.mem := by
      funext x
      by_cases hw : WCov ks (b :: bs) p x
      · rw [key.1 x hw]; simp [zeroW, hw]
      · rw [key.2 x hw]; simp [zeroW, hw]
    let s₃ : State := { u₂ with
      mem := wipeLoseM bs q u₂.unknowns (zeroW ks bs q u₂.mem)
      unknowns := fun n => u₂.unknowns (n + wipeK bs) }
    have hpop : isa.pop (.free b) u₁ s₃ = some { s₃.setReg .rsp (s₃.gpr .rsp + BitVec.ofNat 64 b) with
        wr := s₃.wr.tail, mem := lose s₃.mem (s₃.gpr .rsp) b s₃.unknowns,
        unknowns := fun n => s₃.unknowns (n + b / 4) } := by
      simp only [isa, pop]
      exact ite_eq_left ⟨hb0, hb4, hb8, rfl, rfl, by simp [u₁, State.setReg]⟩
    have hfin : ({ s₃.setReg .rsp (s₃.gpr .rsp + BitVec.ofNat 64 b) with
        wr := s₃.wr.tail, mem := lose s₃.mem (s₃.gpr .rsp) b s₃.unknowns,
        unknowns := fun n => s₃.unknowns (n + b / 4) } : State) =
        { u with
          mem := wipeLoseM (b :: bs) p u.unknowns (zeroW ks (b :: bs) p u.mem)
          unknowns := fun n => u.unknowns (n + wipeK (b :: bs)) } := by
      have hs₃ : s₃.gpr .rsp = q := by simp [s₃, u₂, u₁, State.setReg]
      have hm : s₃.mem = wipeLoseM bs q u.unknowns (zeroW ks (b :: bs) p u.mem) := by
        simp only [s₃, u₂]; rw [hZ]; rfl
      rw [hs₃, hm]
      simp only [s₃, u₂, u₁, State.setReg, wipeLoseM, wipeK, List.tail_cons, State.mk.injEq, true_and, and_true]
      refine ⟨?_, rfl, ?_⟩
      · funext r
        by_cases h : r = .rsp
        · subst h; simp [q, p, BitVec.sub_add_cancel]
        · simp [h]
      · funext n; congr 1; omega_using []
    have e := Exec.frame (M := isa) hpush (.seq (.block he₁) he₂) hpop
    have htr : wipeTr w ks (b :: bs) p = (isa.addrs (.alloc b) u).map Leak.addr ++
        (chunkTr w ks bs.sum (u₁.gpr .rsp) b ++ wipeTr w ks bs q) ++
        (isa.addrs (.free b) s₃).map Leak.addr := by
      simp [wipeTr, addrs, hq, q]
    rw [htr, ← hfin]; exact e

/-! ## Clearing the registers -/

/-- The state after zeroing the SSE registers `xs` at level `v`. -/
def clearedV (v : VecLevel) (xs : List XReg) (s : State) : State :=
  { s with
    xmm := fun x => if x ∈ xs then 0 else s.xmm x
    ymmHi := fun x => if v ≠ .sse ∧ x ∈ xs then 0 else s.ymmHi x
    zmmHi := fun x => if v ≠ .sse ∧ x ∈ xs then 0 else s.zmmHi x }

theorem execBlock_vecs (v : VecLevel) (xs : List XReg) (s : State) :
    execBlock isa (xs.map (zeroX v)) s = some (clearedV v xs s, []) := by
  induction xs generalizing s with
  | nil => simp [execBlock, clearedV]
  | cons x xs ih =>
    cases v
    all_goals
      simp only [List.map_cons, execBlock, zeroX, isa, reduceExec, ih, Option.map_some, addrs,
        List.map_nil, List.nil_append]
      simp only [clearedV, XOp.exec, VOp.exec, State.setXmm, State.setV, XBinOp.eval, VBinOp.sse,
        BitVec.xor_self, List.mem_cons, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.mk.injEq, true_and, and_true]
      first
        | (funext y; by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;> simp [h1, h2])
        | (refine ⟨?_, ?_, ?_⟩ <;> funext y <;> by_cases h1 : y = x <;> by_cases h2 : y ∈ xs <;>
            simp [h1, h2])

/-- The state after `clearHigh v`: at the level `evex`, `zmm16`–`zmm31` zero. -/
def clearedH (v : VecLevel) (s : State) : State :=
  match v with
  | .evex => { s with ymmH := fun _ => 0, zmmHiH := fun _ => 0 }
  | _ => s

theorem mem_hregs (h : HReg) : h ∈ hregs := by cases h <;> decide

theorem execBlock_zeroH (hs : List HReg) (s : State) :
    execBlock isa (hs.map zeroH) s = some ({ s with
      ymmH := fun h => if h ∈ hs then 0 else s.ymmH h
      zmmHiH := fun h => if h ∈ hs then 0 else s.zmmHiH h }, []) := by
  induction hs generalizing s with
  | nil => simp [execBlock]
  | cons h hs ih =>
    simp only [List.map_cons, execBlock, zeroH, isa, reduceExec, ih, Option.map_some, addrs,
      List.map_nil, List.nil_append]
    simp only [E5Op.exec, State.setVz, State.setZH, EBinOp.sse, XBinOp.eval, BitVec.xor_self, List.mem_cons,
      Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [State.mk.injEq, true_and, and_true]
    refine ⟨?_, ?_⟩ <;> funext y <;> by_cases h1 : y = h <;> by_cases h2 : y ∈ hs <;> simp [h1, h2]

theorem execBlock_high (v : VecLevel) (s : State) :
    execBlock isa (clearHigh v) s = some (clearedH v s, []) := by
  cases v
  · rfl
  · rfl
  · rw [clearHigh, execBlock_zeroH]
    simp only [clearedH, mem_hregs, ↓reduceIte]

/-- The state after zeroing the general-purpose registers `rs` with `xor`. -/
def clearedG (rs : List Reg) (s : State) : State :=
  { s with
    gpr := fun r => if r ∈ rs then 0 else s.gpr r
    cf := some false, of := some false, zf := some true, sf := some false }

theorem execBlock_gprs (rs : List Reg) (hrs : rs ≠ []) (s : State) :
    execBlock isa (rs.map zeroR) s = some (clearedG rs s, []) := by
  induction rs generalizing s with
  | nil => exact absurd rfl hrs
  | cons r rs ih =>
    simp only [List.map_cons, execBlock, zeroR, isa, reduceExec, addrs, srcAddrs, execAlu32, readSrc32,
      Option.bind_some, BitVec.xor_self, List.map_nil, List.nil_append]
    by_cases hn : rs = []
    · subst hn
      simp only [List.map_nil, execBlock, Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_singleton]
      simp
    · rw [ih hn]
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg, List.mem_cons]
      simp only [State.mk.injEq, and_true]
      funext y; by_cases h1 : y = r <;> by_cases h2 : y ∈ rs <;> simp [h1, h2]

/-- What `retFix retBits` leaves in `rax`. -/
def retVal (retBits : Nat) (x : BitVec 64) : BitVec 64 :=
  if retBits = 0 then 0
  else if retBits < 32 then ((x.setWidth 32) &&& BitVec.ofNat 32 (2 ^ retBits - 1)).setWidth 64
  else if retBits = 32 then (x.setWidth 32).setWidth 64
  else x

/-- `rs` cleared, if any (`execBlock` of no instruction leaves the flags). -/
def clearedP (rs : List Reg) (s : State) : State := if rs = [] then s else clearedG rs s

theorem execBlock_gprsP (rs : List Reg) (s : State) :
    execBlock isa (rs.map zeroR) s = some (clearedP rs s, []) := by
  by_cases h : rs = []
  · subst h; simp [execBlock, clearedP]
  · rw [execBlock_gprs rs h]; simp [clearedP, h]

theorem execBlock_clearGpr (rb : Nat) (gs : List Reg) (hgs : gs ≠ []) (hax : .rax ∉ gs) (s : State) :
    execBlock isa (retFix rb ++ gs.map zeroR) s =
      some (clearedG gs (s.setReg .rax (retVal rb (s.gpr .rax))), []) := by
  unfold retFix retVal
  by_cases h0 : rb = 0
  · simp only [h0, ↓reduceIte, List.singleton_append]
    rw [show zeroR .rax :: gs.map zeroR = (Reg.rax :: gs).map zeroR from rfl,
      execBlock_gprs _ (by simp)]
    simp only [clearedG, State.setReg, Option.some.injEq, Prod.mk.injEq, and_true, State.mk.injEq]
    funext r; by_cases hr : r = .rax
    · subst hr; simp [hax]
    · simp [hr]
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, execAlu32, readSrc32,
      Option.bind_some, addrs, srcAddrs, execBlock_gprs _ hgs, Option.map_some, List.map_nil,
      List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [clearedG, arithFlags, State.setFlags, State.setReg32, State.setReg]
    try (funext r; by_cases hr : r = .rax <;> simp [hr, hax])
  by_cases h2 : rb = 32
  · subst h2
    simp only [h0, h1, ↓reduceIte, List.singleton_append, execBlock, isa, reduceExec, readSrc32,
      Option.map_some, addrs, srcAddrs, execBlock_gprs _ hgs, List.map_nil,
      List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
    simp only [clearedG, State.setReg32, State.setReg]
    try (funext r; by_cases hr : r = .rax <;> simp [hr, hax])
  · simp only [h0, h1, h2, ↓reduceIte, List.nil_append, execBlock_gprs _ hgs, Option.some.injEq,
      Prod.mk.injEq, and_true]
    simp only [clearedG, State.setReg, State.mk.injEq, and_true]
    funext r; by_cases hr : r = .rax
    · subst hr; simp [hax]
    · simp [hr]

/-! ## MXCSR -/

/-- Two runs of `c` along the same trace from the same MXCSR leave the same
MXCSR. -/
def MxSame (c : Prog isa) : Prop :=
  ∀ s₁ s₂ t s₁' s₂', Exec isa c s₁ t s₁' → Exec isa c s₂ t s₂' → s₁.mxcsr = s₂.mxcsr → s₁'.mxcsr = s₂'.mxcsr

/-- Code that leaves in MXCSR a function of MXCSR on entry. -/
theorem MxSame.of_fun {c : Prog isa} (h : ∃ f : BitVec 32 → BitVec 32, ∀ s t s', Exec isa c s t s' → s'.mxcsr = f s.mxcsr) :
    MxSame c := fun _ _ _ _ _ e₁ e₂ hm => by
  obtain ⟨f, hf⟩ := h
  rw [hf _ _ _ e₁, hf _ _ _ e₂, hm]

/-- MXCSR after `mxFix v`. -/
def fixMx (v : VecLevel) (x : BitVec 32) : BitVec 32 :=
  match v with
  | .evex => x &&& 0xFFC0 ||| 0x3F
  | _ => x

/-- The trace of `mxFix v` from `rsp = p`. -/
def mxTr (v : VecLevel) (p : Addr) : List Leak :=
  match v with
  | .evex => [.addr (p - 16#64), .addr (p - 16#64), .addr (p - 16#64), .addr (p - 16#64 + 4#64),
      .addr (p - 16#64 + 4#64), .addr (p - 16#64)]
  | _ => []

theorem ctl_hi (x : BitVec 32) : (x &&& 0xFFC0#32 ||| 0x3F#32).extractLsb' 16 16 = 0 := by
  rw [BitVec.extractLsb'_or, BitVec.extractLsb'_and, show (0xFFC0#32).extractLsb' 16 16 = 0#16 by decide,
    show (0x3F#32).extractLsb' 16 16 = 0#16 by decide, BitVec.and_zero, BitVec.or_zero]
  rfl

/-- `mxFix` keeps MXCSR's control bits. -/
theorem fixMx_ctl (v : VecLevel) (x : BitVec 32) : (fixMx v x).extractLsb' 6 10 = x.extractLsb' 6 10 := by
  cases v
  · rfl
  · rfl
  · show (x &&& 0xFFC0#32 ||| 0x3F#32).extractLsb' 6 10 = _
    rw [BitVec.extractLsb'_or, BitVec.extractLsb'_and, show (0xFFC0#32).extractLsb' 6 10 = BitVec.allOnes 10 by decide,
      show (0x3F#32).extractLsb' 6 10 = 0#10 by decide, BitVec.and_allOnes, BitVec.or_zero]

/-- What it leaves is a function of them. -/
theorem fixMx_congr (v : VecLevel) {x y : BitVec 32} (hv : v = .evex)
    (h : x.extractLsb' 6 10 = y.extractLsb' 6 10) : fixMx v x = fixMx v y := by
  subst hv
  show x &&& 0xFFC0#32 ||| 0x3F#32 = y &&& 0xFFC0#32 ||| 0x3F#32
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  by_cases hc : (0xFFC0#32).getLsbD i = true
  · have h6 : 6 ≤ i ∧ i < 16 := by
      have : ∀ i < 32, (0xFFC0#32).getLsbD i = true → 6 ≤ i ∧ i < 16 := by decide
      exact this i hi hc
    have e := congrArg (fun z : BitVec 10 => z.getLsbD (i - 6)) h
    simp only [BitVec.getLsbD_extractLsb', show i - 6 < 10 by omega_using [h6], decide_true, Bool.true_and,
      show 6 + (i - 6) = i by omega_using [h6]] at e
    rw [e]
  · simp only [Bool.not_eq_true] at hc
    rw [hc, Bool.and_false, Bool.and_false]

/-- How many unknowns `mxFix v` uses: its frame's, when it is released. -/
def mxK : VecLevel → Nat
  | .evex => 4
  | _ => 0

/-- The memory `m` once `mxFix v`'s frame, at `rsp = p`, from the unknowns
`U`, is released (`lose`). -/
def mxLose (v : VecLevel) (p : Addr) (U : Nat → BitVec 64) (m : Mem) : Mem :=
  match v with
  | .evex => lose m (p - 16#64) 16 U
  | _ => m

theorem mxLose_congr (v : VecLevel) (p : Addr) (U : Nat → BitVec 64) {m₁ m₂ : Mem} (x : Addr)
    (h : m₁ x = m₂ x) : mxLose v p U m₁ x = mxLose v p U m₂ x := by
  cases v
  · exact h
  · exact h
  · exact lose_congr _ _ _ h

theorem mxLose_frame (v : VecLevel) (p : Addr) (U : Nat → BitVec 64) (m : Mem) :
    Frame [⟨p - 16#64, 16⟩] m (mxLose v p U m) := by
  cases v
  · exact Frame.refl _ _
  · exact Frame.refl _ _
  · exact lose_frame _ _ _ _

/-- `mxFix v`, where `r11` is zero and the flags are those of an `xor` of a
register with itself (what clearing `ps` leaves): MXCSR as `fixMx` says, and
at the level `evex` 8 bytes of the 16 below the stack pointer. The frame,
released, holds what `mxLose` says of the rest. -/
theorem mxFix_run (v : VecLevel) (u : State) (h16 : v = .evex → 16 ≤ (u.gpr .rsp).toNat)
    (hr : v = .evex → u.gpr .r11 = 0 ∧ u.cf = some false ∧ u.of = some false ∧ u.zf = some true ∧
      u.sf = some false) :
    ∃ m', Exec isa (mxFix v) u (mxTr v (u.gpr .rsp))
        { u with mem := m', mxcsr := fixMx v u.mxcsr, unknowns := fun n => u.unknowns (n + mxK v) } ∧
      ∀ x, ¬ (v = .evex ∧ (x - (u.gpr .rsp - 16#64)).toNat < 8) →
        m' x = mxLose v (u.gpr .rsp) u.unknowns u.mem x := by
  cases v
  · exact ⟨u.mem, .block rfl, fun _ _ => rfl⟩
  · exact ⟨u.mem, .block rfl, fun _ _ => rfl⟩
  · obtain ⟨h0, hcf, hof, hzf, hsf⟩ := hr rfl
    have h16 := h16 rfl
    let p := u.gpr .rsp
    let q := p - 16#64
    let u₁ : State := { u.setReg .rsp q with wr := ⟨q, 16⟩ :: u.wr }
    have hpush : isa.push (.alloc 16) u = some u₁ := by
      simp only [isa, push, u₁, q, p]
      rw [ite_eq_left ⟨by decide, by decide, by decide, h16⟩]
    have hq : u₁.gpr .rsp = q := by simp [u₁, State.setReg]
    have hin : InRegions u₁.wr q 4 := by
      refine ⟨⟨q, 16⟩, by simp [u₁], ?_⟩
      simp only [Region.Contains, BitVec.sub_self, BitVec.toNat_zero]; omega_using []
    have hin' : InRegions (u₁.rd ++ u₁.wr) q 4 := by
      obtain ⟨r, hr, hc⟩ := hin; exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hea : u₁.gpr .rsp + BitVec.ofInt 64 0 = q := by rw [hq]; show q + 0#64 = q; rw [BitVec.add_zero]
    let w : BitVec 32 := u.mxcsr &&& 0xFFC0#32 ||| 0x3F#32
    let m₂ : Mem := ((u.mem.writeW q u.mxcsr).writeW q w).writeW (q + 4#64) (0x1FBF#32)
    have hw : w.extractLsb' 16 16 = 0 := ctl_hi _
    have hin4 : InRegions u₁.wr (q + 4#64) 4 := by
      refine ⟨⟨q, 16⟩, by simp [u₁], ?_⟩
      simp only [Region.Contains]
      bv_omega
    have hin4' : InRegions (u₁.rd ++ u₁.wr) (q + 4#64) 4 := by
      obtain ⟨r, hr, hc⟩ := hin4; exact ⟨r, List.mem_append_right _ hr, hc⟩
    have hea4 : u₁.gpr .rsp + BitVec.ofInt 64 4 = q + 4#64 := by rw [hq]; rfl
    have hsep : Mem.Sep q (32 / 8) (q + 4#64) (32 / 8) := by
      intro x hx
      have hx : (x - q).toNat < 4 := hx
      show ¬ (x - (q + 4#64)).toNat < 4
      bv_omega
    have hb : execBlock isa [.stmxcsr { base := .rsp }, .mov32 .r11 (.mem { base := .rsp }),
        .alu32 .and .r11 (.imm 0xFFC0), .alu32 .or .r11 (.imm 0x3F), .store32 { base := .rsp } .r11,
        .mov32 .r11 (.imm 0x1FBF), .store32 { base := .rsp, disp := 4 } .r11,
        .ldmxcsr { base := .rsp, disp := 4 }, .lfence, .lfence, .ldmxcsr { base := .rsp },
        .alu32 .xor .r11 (.reg .r11)] u₁ =
        some ({ u₁ with mem := m₂, mxcsr := w },
          [.addr q, .addr q, .addr q, .addr (q + 4#64), .addr (q + 4#64), .addr q]) := by
      have h11 : u₁.gpr .r11 = 0 := by simp [u₁, State.setReg, h0]
      have sw : ∀ x : BitVec 32, (x.setWidth 64).setWidth 32 = x := fun x => by
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_setWidth]
        have := x.isLt
        omega_using []
      simp only [execBlock, isa, reduceExec, State.store32, State.load32, State.ea, execAlu32, readSrc32, addrs,
        srcAddrs, arithFlags, State.setFlags, State.setReg32, State.setReg, reduceCtorEq, ↓reduceIte, hea, hea4,
        hin, hin', hin4, hin4', Option.bind_some, Option.map_some, Mem.readW_writeW_self32,
        Mem.readW_writeW_sep hsep (by decide), sw, BitVec.xor_self,
        show u₁.mxcsr = u.mxcsr from rfl, show u₁.mem = u.mem from rfl,
        show (u.mxcsr &&& 65472 ||| 63).extractLsb' 16 16 = 0 from hw,
        show (8127 : BitVec 32).extractLsb' 16 16 = 0 from by decide,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append, Option.some.injEq, Prod.mk.injEq, and_true]
      simp only [State.mk.injEq, and_true, true_and]
      refine ⟨?_, hcf.symm, ?_, ?_, hof.symm, rfl, rfl⟩
      · funext r
        by_cases hr : r = .r11
        · subst hr; rw [ite_eq_left rfl, h11]; rfl
        · rw [ite_eq_right hr, ite_eq_right hr, ite_eq_right hr, ite_eq_right hr, ite_eq_right hr]
      · exact hzf.symm
      · exact hsf.symm
    let u₂ : State := { u₁ with mem := m₂, mxcsr := w }
    have hpop : isa.pop (.free 16) u₁ u₂ =
        some { u with mem := lose m₂ q 16 u.unknowns, mxcsr := w, unknowns := fun n => u.unknowns (n + 4) } := by
      simp only [isa, pop, u₂]
      split
      rotate_left
      · rename_i hn; exact (hn ⟨by decide, by decide, by decide, trivial, trivial, by simp [u₁, State.setReg]⟩).elim
      congr 1
      simp only [u₁, State.setReg, State.mk.injEq, and_true, true_and, List.tail_cons]
      refine ⟨?_, rfl⟩
      funext r
      by_cases h : r = .rsp
      · subst h; simp [q, p, BitVec.sub_add_cancel]
      · simp [h]
    refine ⟨lose m₂ q 16 u.unknowns, ?_, fun x hx => ?_⟩
    · have e := Exec.frame (M := isa) hpush (.block hb) hpop
      have htr : mxTr .evex p = (isa.addrs (.alloc 16) u).map Leak.addr ++
          [.addr q, .addr q, .addr q, .addr (q + 4#64), .addr (q + 4#64), .addr q] ++
          (isa.addrs (.free 16) u₂).map Leak.addr := by
        simp [mxTr, addrs, q]
      rw [show mxTr .evex (u.gpr .rsp) = mxTr .evex p from rfl, htr]
      exact e
    · have hx' : ¬ (x - q).toNat < 8 := fun h => hx ⟨rfl, h⟩
      have hx4 : ¬ (x - (q + 4#64)).toNat < 4 := by bv_omega
      refine lose_congr _ _ _ ?_
      show (((u.mem.writeW q u.mxcsr).writeW q w).writeW (q + 4#64) (0x1FBF#32)) x = u.mem x
      simp only [Mem.writeW, Mem.write]
      rw [ite_eq_right (by omega_using [hx4]), ite_eq_right (by omega_using [hx']), ite_eq_right (by omega_using [hx'])]

/-- The state `scrubTail v rb xs ps gs ks cs f` leaves, given the memory `m'`
its wipe leaves and the unknowns `U'` its frames' releases leave. -/
def finState (v : VecLevel) (rb : Nat) (xs : List XReg) (ps gs : List Reg) (m' : Mem)
    (U' : Nat → BitVec 64) (u : State) (f : VecLevel := v) : State :=
  clearedG gs
    (({ clearedP ps (clearedH v (clearedV v xs u)) with
        mem := m'
        mxcsr := fixMx f u.mxcsr
        unknowns := U' } : State).setReg .rax
      (retVal rb (u.gpr .rax)))

theorem mem_xregs (x : XReg) : x ∈ xregs := by cases x <;> decide

/-- What `scrubTail` needs of what it clears. -/
structure TailOk (rb : Nat) (xs : List XReg) (ps gs : List Reg) (ks : List Nat) : Prop where
  x0 : ks ≠ [] → .xmm0 ∈ xs
  r11 : ks ≠ [] → .r11 ∈ ps
  psOk : ∀ r ∈ ps, r ∈ scratchRegs
  gsOk : ∀ r ∈ gs, r ∈ scratchRegs
  gne : gs ≠ []

/-- What the level `evex` needs of the wipe from `rsp = p`: that it zeroes
the bytes `mxFix` stores, in the 16 below the stack pointer. -/
def EvexOk (v : VecLevel) (ks cs : List Nat) (p : Addr) : Prop :=
  v = .evex → ks ≠ [] ∧ 16 ≤ cs.sum ∧ ∀ x, (x - (p - 16#64)).toNat < 8 → WCov ks cs p x

/-- The trace of `scrubTail` from `rsp = p`. -/
def tailTr (v : VecLevel) (ks cs : List Nat) (p : Addr) (f : VecLevel := v) : List Leak :=
  mxTr f p ++ wipeTr v.wide ks cs p

/-- What the clearing leaves in memory, from `rsp = p`, the unknowns `U` and
the memory `m`: `mxFix f`'s frame released, what the wipe zeroes zero, and
the wipe's frames released. -/
def tailMem (f : VecLevel) (ks cs : List Nat) (p : Addr) (U : Nat → BitVec 64) (m : Mem) : Mem :=
  wipeLoseM cs p (fun n => U (n + mxK f)) (zeroW ks cs p (mxLose f p U m))

/-- A byte the clearing leaves depends only on that byte before it, unless
the wipe zeroes it. -/
theorem tailMem_congr (f : VecLevel) (ks cs : List Nat) (p : Addr) (U : Nat → BitVec 64) {m₁ m₂ : Mem}
    (x : Addr) (h : ¬ WCov ks cs p x → m₁ x = m₂ x) : tailMem f ks cs p U m₁ x = tailMem f ks cs p U m₂ x := by
  refine wipeLoseM_congr _ _ _ x ?_
  by_cases hw : WCov ks cs p x
  · simp [zeroW, hw]
  · simp only [zeroW, hw, ite_false]
    exact mxLose_congr _ _ _ x (h hw)

/-- The clearing changes only the `cs.sum` bytes below `p`, if `mxFix f`'s
frame is among them. -/
theorem tailMem_frame (f : VecLevel) (ks cs : List Nat) (p : Addr) (U : Nat → BitVec 64) (m : Mem)
    (h16 : f = .evex → 16 ≤ cs.sum) : Frame [⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩] m (tailMem f ks cs p U m) := by
  have hz : Frame [⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩] (mxLose f p U m) (zeroW ks cs p (mxLose f p U m)) := by
    intro x hx
    have hw : ¬ WCov ks cs p x := fun hw => hx _ (List.mem_singleton_self _) hw.1
    simp [zeroW, hw]
  have hm : Frame [⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩] m (mxLose f p U m) := by
    cases f
    · exact Frame.refl _ _
    · exact Frame.refl _ _
    · refine (mxLose_frame .evex p U m).sub fun r hr => ?_
      simp only [List.mem_singleton] at hr; subst hr
      have h := h16 rfl
      exact ⟨_, List.mem_singleton_self _, Offset.sub_below _ h (by omega_using [h])⟩
  exact (hm.trans hz).trans (wipeLoseM_frame _ _ _ _)

theorem tail_run (v : VecLevel) (rb : Nat) {xs : List XReg} {ps gs : List Reg} {ks : List Nat} (cs : List Nat)
    {f : VecLevel} (ht : TailOk rb xs ps gs ks) (u : State)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0) (hs : cs.sum ≤ (u.gpr .rsp).toNat)
    (hev : EvexOk f ks cs (u.gpr .rsp)) :
    ∃ m', Exec isa (scrubTail v rb xs ps gs ks cs f) u (tailTr v ks cs (u.gpr .rsp) f)
        (finState v rb xs ps gs m' (fun n => u.unknowns (n + wipeK cs + mxK f)) u f) ∧
      ∀ x, m' x = tailMem f ks cs (u.gpr .rsp) u.unknowns u.mem x := by
  let u₁ := clearedP ps (clearedH v (clearedV v xs u))
  have h₁ : execBlock isa (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR) u = some (u₁, []) := by
    rw [execBlock_append, execBlock_append, execBlock_vecs]
    simp only [Option.bind_some]
    rw [execBlock_high]
    simp only [Option.bind_some, Option.map_some]
    rw [execBlock_gprsP]
    rfl
  have hcH : ∀ w : State, (clearedH v w).gpr = w.gpr ∧ (clearedH v w).xmm = w.xmm ∧ (clearedH v w).mem = w.mem ∧
      (clearedH v w).mxcsr = w.mxcsr ∧ (clearedH v w).ymmHi = w.ymmHi := fun w => by
    cases v <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hsp : u₁.gpr .rsp = u.gpr .rsp := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).1]; rfl
    · simp only [clearedG, show Reg.rsp ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rsp ∉ scratchRegs),
        ↓reduceIte]
      rw [(hcH _).1]; rfl
  have hx0 : ks ≠ [] → u₁.xmm .xmm0 = 0 := fun h => by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.1]; simp [clearedV, ht.x0 h]
    · show (clearedH v (clearedV v xs u)).xmm .xmm0 = 0
      rw [(hcH _).2.1]; simp [clearedV, ht.x0 h]
  have hy0 : v.wide = true → ks ≠ [] → u₁.ymmHi .xmm0 = 0 := fun hw h => by
    have hv' : v ≠ .sse := fun e => by rw [e] at hw; cases hw
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.2.2]; simp [clearedV, ht.x0 h, hv']
    · show (clearedH v (clearedV v xs u)).ymmHi .xmm0 = 0
      rw [(hcH _).2.2.2.2]; simp [clearedV, ht.x0 h, hv']
  have hr11 : ks ≠ [] → u₁.gpr .r11 = 0 := fun h => by
    simp only [u₁, clearedP]; split
    · rename_i hp; exact absurd (ht.r11 h) (by rw [hp]; simp)
    · simp [clearedG, ht.r11 h]
  have hmem : u₁.mem = u.mem := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.1]; rfl
    · show (clearedH v (clearedV v xs u)).mem = u.mem
      rw [(hcH _).2.2.1]; rfl
  have hmx : u₁.mxcsr = u.mxcsr := by
    simp only [u₁, clearedP]; split
    · rw [(hcH _).2.2.2.1]; rfl
    · show (clearedH v (clearedV v xs u)).mxcsr = u.mxcsr
      rw [(hcH _).2.2.2.1]; rfl
  have hunk : u₁.unknowns = u.unknowns := by
    simp only [u₁, clearedP]; split <;> (cases v <;> rfl)
  -- `mxFix`.
  obtain ⟨m₁, hem, hm₁⟩ := mxFix_run f u₁ (fun h => by rw [hsp]; have := (hev h).2.1; omega_using [hs, this]) (fun h => by
    have hp : ps ≠ [] := fun e => absurd (ht.r11 (hev h).1) (by rw [e]; simp)
    refine ⟨hr11 (hev h).1, ?_, ?_, ?_, ?_⟩ <;> simp only [u₁, clearedP, hp, ↓reduceIte, clearedG])
  rw [hsp, hmx, hunk] at hem
  rw [hsp, hmem, hunk] at hm₁
  let u₂ : State := { u₁ with mem := m₁, mxcsr := fixMx f u.mxcsr, unknowns := fun n => u.unknowns (n + mxK f) }
  have he := wipe_run v.wide ks cs u₂ hv (by show cs.sum ≤ (u₁.gpr .rsp).toNat; rw [hsp]; exact hs)
    hx0 hy0 hr11
  rw [show u₂.gpr .rsp = u.gpr .rsp from hsp] at he
  let m' := wipeLoseM cs (u.gpr .rsp) u₂.unknowns (zeroW ks cs (u.gpr .rsp) m₁)
  refine ⟨m', ?_, fun x => ?_⟩
  · have h₃ := execBlock_clearGpr rb gs ht.gne
      (fun h => absurd (ht.gsOk _ h) (by decide : Reg.rax ∉ scratchRegs))
      { u₂ with mem := m', unknowns := fun n => u₂.unknowns (n + wipeK cs) }
    have e := Exec.seq (M := isa) (.block h₁) (.seq hem (.seq he (.block h₃)))
    simp only [List.nil_append, List.append_nil] at e
    have hax : u₁.gpr .rax = u.gpr .rax := by
      simp only [u₁, clearedP]; split
      · rw [(hcH _).1]; rfl
      · simp only [clearedG, show Reg.rax ∉ ps from fun h => absurd (ht.psOk _ h) (by decide : Reg.rax ∉ scratchRegs),
          ↓reduceIte]
        rw [(hcH _).1]; rfl
    have hf : finState v rb xs ps gs m' (fun n => u.unknowns (n + wipeK cs + mxK f)) u f =
        clearedG gs (({ u₂ with mem := m', unknowns := fun n => u₂.unknowns (n + wipeK cs) } : State).setReg .rax
          (retVal rb (u₂.gpr .rax))) := by
      rw [show u₂.gpr .rax = u.gpr .rax from hax]; rfl
    rw [hf]
    exact e
  · refine wipeLoseM_congr _ _ _ x ?_
    by_cases hw : WCov ks cs (u.gpr .rsp) x
    · simp [zeroW, hw]
    · simp only [zeroW, hw, ite_false]
      exact hm₁ x fun ⟨h, hs4⟩ => hw ((hev h).2.2 x hs4)

/-! ## What `Sig.contract` gives -/

/-- What `Verified.scrub` needs of the calling convention a contract is for:
`abi`'s, possibly with tables of constants (`Abi.withConsts`), which add
readable regions apart from the stack the function uses, and with tables of
functions (`Abi.withTables`). -/
structure ScrubAbi (A : Abi isa) : Prop where
  ptrBits : A.ptrBits = 64
  reserved : A.reserved = abi.reserved
  wr : ∀ s, A.wr s = s.wr
  wf : ∀ ws n s, A.wf ws n s → (n = 0 ∨ n ≤ (s.gpr .rsp).toNat) ∧
    ∀ r ∈ s.rd, r ∉ A.rd s → ∀ q ∈ abi.reserved n s, q.Disjoint r
  pub : ∀ s₁ s₂, A.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp
  mem : ∀ s, A.mem s = s.mem
  ret : ∀ s, A.ret s = s.gpr .rax
  rdSub : ∀ s r, r ∈ A.rd s → r ∈ s.rd
  argsLen : ∀ ws f, A.args ws = some f → ∀ s, (f s).length = ws.length
  args : ∀ ws, A.args ws = abi.args ws
  argRo : ∀ ws s, ∀ p ∈ A.argArea ws s, p.2 = false
  argArea : ∀ ws s, A.argArea ws s = abi.argArea ws s
  wfAbi : ∀ ws n s, A.wf ws n s → abi.wf ws n s

theorem abi_args_len (ws : List Nat) (f : State → List (BitVec 64)) (h : abi.args ws = some f) (s : State) :
    (f s).length = ws.length := by
  have h6 : argRegs.length = 6 := rfl
  simp only [abi] at h
  split at h <;> cases h
  · rename_i hl; simp only [List.length_map, List.length_take]; omega_using [hl]
  · rename_i hl; simp only [List.length_append, List.length_map, List.length_range]; omega_using [hl]

theorem abi_wf_stack {ws : List Nat} {n : Nat} {s : State} (h : abi.wf ws n s) :
    n = 0 ∨ n ≤ (s.gpr .rsp).toNat := by
  simp only [abi] at h
  split at h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h
  · cases n with
    | zero => exact .inl rfl
    | succ n => exact .inr h.1

theorem abi_argRo (ws : List Nat) (s : State) : ∀ p ∈ abi.argArea ws s, p.2 = false := by
  intro p hp
  simp only [abi] at hp
  split at hp
  · cases hp
  · simp only [List.mem_singleton] at hp; subst hp; rfl

theorem ScrubAbi.plain : ScrubAbi abi :=
  ⟨rfl, rfl, fun _ => rfl, fun _ _ _ h => ⟨abi_wf_stack h, fun _ hr hn => absurd hr hn⟩,
    fun _ _ h => h.1, fun _ => rfl, fun _ => rfl, fun _ _ h => h, abi_args_len, fun _ => rfl, abi_argRo,
    fun _ _ => rfl, fun _ _ _ h => h⟩

theorem ScrubAbi.consts (cs : List (String × List (BitVec 64))) : ScrubAbi (abi.withConsts cs) := by
  cases cs with
  | nil => exact ScrubAbi.plain
  | cons c cs =>
    refine ⟨rfl, rfl, fun _ => rfl, fun ws n s h => ?_, fun _ _ h => h.1.1, fun _ => rfl, fun _ => rfl,
      fun _ _ h => List.mem_of_mem_take h, abi_args_len, fun _ => rfl, abi_argRo, fun _ _ => rfl,
      fun _ _ _ h => h.1⟩
    obtain ⟨hw, hdrop, -, hdis, -⟩ := h
    refine ⟨abi_wf_stack hw, fun r hr hn q hq => ?_⟩
    have hr' : r ∈ (abi.rd s).drop ((abi.rd s).length - (c :: cs).length) := by
      change r ∈ abi.rd s at hr
      rw [← List.take_append_drop ((abi.rd s).length - (c :: cs).length) (abi.rd s)] at hr
      rcases List.mem_append.mp hr with h | h
      · exact absurd h hn
      · exact h
    rw [hdrop] at hr'
    exact ((hdis r hr').2.2 q hq).symm

theorem ScrubAbi.tables {A : Abi isa} (hA : ScrubAbi A) (sig : Sig) (ts : List (String × List FnTable)) :
    ScrubAbi (A.withTables sig ts) := by
  cases ts with
  | nil => exact hA
  | cons t ts =>
    exact ⟨hA.ptrBits, hA.reserved, hA.wr, fun ws n s h => hA.wf ws n s h.1,
      fun s₁ s₂ h => hA.pub s₁ s₂ h.1, hA.mem, hA.ret, hA.rdSub, hA.argsLen, hA.args, hA.argRo, hA.argArea,
      fun ws n s h => hA.wfAbi ws n s h.1⟩

theorem withMode_ptrBits (A : Abi isa) (b : Bool) : (A.withMode b).ptrBits = A.ptrBits := by
  cases b <;> rfl

/-- With what two runs must also agree on to be related as public
(`Abi.withMode`). -/
theorem ScrubAbi.mode {A : Abi isa} (hA : ScrubAbi A) (b : Bool) : ScrubAbi (A.withMode b) := by
  cases b with
  | false => exact hA
  | true => exact { hA with pub := fun s₁ s₂ h => hA.pub s₁ s₂ h.1 }

/-- The calling convention of every x86-64 artifact (`Api.artifact`). -/
theorem ScrubAbi.of (cs : List (String × List (BitVec 64))) (sig : Sig) (ts : List (String × List FnTable))
    (b : Bool) : ScrubAbi (((abi.withConsts cs).withTables sig ts).withMode b) :=
  ((ScrubAbi.consts cs).tables sig ts).mode b

/-! ## What `Sig.contract` gives -/

theorem contract_pre_scrub {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s : State}
    (h : (sig.contract A pre post wa stack leak).pre s) :
    (stack = 0 ∨ stack ≤ (s.gpr .rsp).toNat) ∧
      ∀ r ∈ s.rd ++ s.wr, (⟨s.gpr .rsp, 8⟩ : Region).Disjoint r ∧
        (stack ≠ 0 → (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Disjoint r) := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  rename_i vals _
  obtain ⟨hwf, hrd, hwr, -, hres, -⟩ := h
  obtain ⟨hst, hcon⟩ := hA.wf _ _ _ hwf
  have hres' : ∀ r ∈ abi.reserved stack s, ∀ a ∈ (Sig.bufs sig.params (vals s) ++
      (Sig.lists A.ptrBits (A.mem s) sig.params (vals s)).map fun r => (r, false)) ++
      (A.argArea ((sig.words A.ptrBits).map (·.bits A.ptrBits)) s).map
        (fun (r, w) => (r, w && wa)), r.Disjoint a.1 := by
    rw [← hA.reserved]; exact hres
  have key : ∀ r ∈ s.rd ++ s.wr, ∀ q ∈ abi.reserved stack s, q.Disjoint r := by
    intro r hr q hq
    rcases List.mem_append.mp hr with hr | hr
    · by_cases hn : r ∈ A.rd s
      · rw [hrd] at hn
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hn
        exact hres' q hq a (List.mem_filter.mp ha).1
      · exact hcon r hr hn q hq
    · rw [← hA.wr, hwr] at hr
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
      exact hres' q hq a (List.mem_filter.mp ha).1
  refine ⟨hst, fun r hr => ⟨key r hr _ (by simp [abi]), fun hn => key r hr _ ?_⟩⟩
  cases stack with
  | zero => exact absurd rfl hn
  | succ n => simp [abi, stackBelow]

theorem contract_pub_rsp {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : s₁.gpr .rsp = s₂.gpr .rsp := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact hA.pub _ _ h.1
    | some f => exact hA.pub _ _ h.1.1

/-! ## The result -/

theorem retVal_low {rb : Nat} (hrb : rb ≤ 32 ∨ rb = 64) (x : BitVec 64) :
    (retVal rb x).setWidth rb = x.setWidth rb := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, retVal]
  by_cases h0 : rb = 0
  · subst h0; simp [Nat.mod_one]
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 2 ^ rb - 1) (by have := Nat.pow_lt_pow_right (a := 2) (by omega_using []) h1; omega_using [this]),
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using [hrb])),
      Nat.mod_eq_of_lt (a := x.toNat % 2 ^ 32 % 2 ^ rb) (by
        have := Nat.mod_lt (x.toNat % 2 ^ 32) (Nat.two_pow_pos rb)
        have := Nat.pow_le_pow_right (n := 2) (by omega_using []) (show rb ≤ 64 by omega_using [hrb]); omega_using []),
      Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega_using [h1]))]
  by_cases h2 : rb = 32
  · subst h2; simp [BitVec.toNat_setWidth, Nat.mod_mod_of_dvd]
  · have : rb = 64 := by omega_using [hrb, h1, h2]
    subst this; simp

theorem retVal_hi {rb : Nat} (hrb : rb ≤ 32 ∨ rb = 64) (x : BitVec 64) : retVal rb x >>> rb = 0 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, retVal, Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  by_cases h0 : rb = 0
  · subst h0; simp
  by_cases h1 : rb < 32
  · simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := 2 ^ rb - 1) (by have := Nat.pow_lt_pow_right (a := 2) (by omega_using []) h1; omega_using [this]),
      Nat.and_two_pow_sub_one_eq_mod]
    have h3 := Nat.mod_lt (x.toNat % 2 ^ 32) (Nat.two_pow_pos rb)
    have := Nat.pow_le_pow_right (n := 2) (by omega_using []) (show rb ≤ 64 by omega_using [hrb])
    rw [Nat.mod_eq_of_lt (by omega_using [this])]; exact h3
  by_cases h2 : rb = 32
  · subst h2; simp only [h0, h1, ↓reduceIte, BitVec.toNat_setWidth]
    have := Nat.mod_lt x.toNat (Nat.two_pow_pos 32)
    rw [Nat.mod_eq_of_lt (by omega_using [])]; exact this
  · have : rb = 64 := by omega_using [hrb, h1, h2]
    subst this; simp only [h0, h1, h2, ↓reduceIte]; exact x.isLt

/-- How `scrub` clears the vector registers, as an instruction level. -/
def _root_.VG.Impl.Scrub.X86_64.VecLevel.level : VecLevel → Nat
  | .sse => 0
  | .avx => 1
  | .evex => 2

/-! ## The theorem -/

theorem clearedH_keep (v : VecLevel) (w : State) :
    (clearedH v w).gpr = w.gpr ∧ (clearedH v w).xmm = w.xmm ∧ (clearedH v w).ymmHi = w.ymmHi ∧
      (clearedH v w).zmmHi = w.zmmHi ∧ (clearedH v w).mem = w.mem ∧ (clearedH v w).rd = w.rd ∧
      (clearedH v w).wr = w.wr ∧ (clearedH v w).mxcsr = w.mxcsr := by
  cases v <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem clearedP_gpr {ps : List Reg} {s : State} {r : Reg} :
    (clearedP ps s).gpr r = if r ∈ ps then 0 else s.gpr r := by
  unfold clearedP; split
  · rename_i h; subst h; simp
  · simp [clearedG]

theorem finState_gpr {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {U' : Nat → BitVec 64} {u : State} {f : VecLevel}
    {r : Reg} (hp : r ∉ ps) (hg : r ∉ gs) (h₂ : r ≠ .rax) :
    (finState v rb xs ps gs m' U' u f).gpr r = u.gpr r := by
  simp only [finState, clearedG, State.setReg, hg, h₂, ↓reduceIte, clearedP_gpr, hp]
  rw [(clearedH_keep v _).1]
  rfl

theorem finState_rax {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {U' : Nat → BitVec 64} {u : State} {f : VecLevel}
    (hg : Reg.rax ∉ gs) : (finState v rb xs ps gs m' U' u f).gpr .rax = retVal rb (u.gpr .rax) := by
  simp only [finState, clearedG, State.setReg, hg, ↓reduceIte]

theorem finState_xmm {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {U' : Nat → BitVec 64} {u : State} {f : VecLevel} :
    (finState v rb xs ps gs m' U' u f).xmm = fun x => if x ∈ xs then 0 else u.xmm x := by
  simp only [finState, clearedG, State.setReg, clearedP]
  split <;> exact (clearedH_keep v _).2.1

theorem finState_ymmHi {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {U' : Nat → BitVec 64} {u : State} {f : VecLevel} :
    (finState v rb xs ps gs m' U' u f).ymmHi = fun x => if v ≠ .sse ∧ x ∈ xs then 0 else u.ymmHi x := by
  simp only [finState, clearedG, State.setReg, clearedP]
  split <;> exact (clearedH_keep v _).2.2.1

theorem finState_zmmHi {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {U' : Nat → BitVec 64} {u : State} {f : VecLevel} :
    (finState v rb xs ps gs m' U' u f).zmmHi = fun x => if v ≠ .sse ∧ x ∈ xs then 0 else u.zmmHi x := by
  simp only [finState, clearedG, State.setReg, clearedP]
  split <;> exact (clearedH_keep v _).2.2.2.1

theorem finState_other {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {U' : Nat → BitVec 64} {u : State} {f : VecLevel} :
    (finState v rb xs ps gs m' U' u f).mem = m' ∧ (finState v rb xs ps gs m' U' u f).rd = u.rd ∧
      (finState v rb xs ps gs m' U' u f).wr = u.wr ∧ (finState v rb xs ps gs m' U' u f).ymmH = (clearedH v u).ymmH ∧
      (finState v rb xs ps gs m' U' u f).zmmHiH = (clearedH v u).zmmHiH ∧
      (finState v rb xs ps gs m' U' u f).mxcsr = fixMx f u.mxcsr ∧
      (finState v rb xs ps gs m' U' u f).cf = some false ∧ (finState v rb xs ps gs m' U' u f).zf = some true ∧
      (finState v rb xs ps gs m' U' u f).sf = some false ∧ (finState v rb xs ps gs m' U' u f).of = some false := by
  have k := clearedH_keep v (clearedV v xs u)
  have hy : (clearedH v (clearedV v xs u)).ymmH = (clearedH v u).ymmH := by cases v <;> rfl
  have hz : (clearedH v (clearedV v xs u)).zmmHiH = (clearedH v u).zmmHiH := by cases v <;> rfl
  unfold finState clearedP
  split
  · exact ⟨rfl, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1, hy, hz, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, k.2.2.2.2.2.1, k.2.2.2.2.2.2.1, hy, hz, rfl, rfl, rfl, rfl, rfl⟩

/-- The clearing ends with every flag defined: those of its last `xor`. -/
theorem finState_flags {v : VecLevel} {rb : Nat} {xs : List XReg} {ps gs : List Reg} {m' : Mem} {U' : Nat → BitVec 64} {u : State}
    {f : VecLevel} : FlagsDefined (finState v rb xs ps gs m' U' u f) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [finState_other.2.2.2.2.2.2.1]; exact Option.some_ne_none _
  · rw [finState_other.2.2.2.2.2.2.2.1]; exact Option.some_ne_none _
  · rw [finState_other.2.2.2.2.2.2.2.2.1]; exact Option.some_ne_none _
  · rw [finState_other.2.2.2.2.2.2.2.2.2]; exact Option.some_ne_none _

theorem slot_not_below {sp x : Addr} {n : Nat} (hn : n + 8 < 2 ^ 64)
    (hx : (⟨sp, 8⟩ : Region).Contains x 1) : ¬ (⟨sp - BitVec.ofNat 64 n, n⟩ : Region).Contains x 1 := by
  have := sp.isLt; have := x.isLt
  simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx ⊢
  generalize sp.toNat = P at *
  generalize x.toNat = X at *
  rw [Nat.mod_eq_of_lt (a := n) (by omega_using [hn])]
  omega_arith

/-! ## The unknowns two runs use

Two runs along the same trace, from the same unknowns, whose functions
called indirectly have the same addresses, end with the same unknowns:
each call and each frame's release uses a number of unknowns its
instruction fixes, the trace says which way each branch went, and which
function each indirect call called (`Exec.unknowns_agree`). -/

local macro "uk_leaf" : tactic => `(tactic| first
  | exact Pres.none'
  | (apply Pres.some'; rfl)
  | (apply Pres.map'; intro _; rfl)
  | (apply Pres.map'; intro _; split <;> rfl))

local syntax "uk_go" : tactic
macro_rules
  | `(tactic| uk_go) => `(tactic| first
    | uk_leaf
    | (apply Pres.bind'; intro _; uk_go)
    | (split <;> uk_go))

private theorem exec_unknowns_pres (i : Instr) (s : State) :
    Pres (fun x => x.unknowns = s.unknowns) (exec i s) := by
  cases i
  case vop op => simp only [reduceExec]; rw [Taint.VOp.exec_eq]; exact Pres.some' rfl
  case zop op => simp only [reduceExec]; rw [Taint.ZOp.exec_eq]; exact Pres.some' rfl
  case xop op => simp only [reduceExec]; rw [Taint.XOp.exec_eq]; exact Pres.some' rfl
  case eop op => simp only [reduceExec]; rw [Taint.EOp.exec_eq]; exact Pres.some' rfl
  case e5op op => simp only [reduceExec]; rw [Taint.E5Op.exec_eq]; exact Pres.some' rfl
  case vmovdquLoad len _ _ | vmovdquStore len _ _ | vbinLoad _ len _ _ _ =>
    cases len <;> simp only [reduceExec, State.store128, State.store256] <;> uk_go
  case evLoad d _ | evMadd52Load _ d _ _ | evBroadcastLoad d _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVy_eq]
  case e5InsertLoad d _ _ _ =>
    simp only [reduceExec]; apply Pres.map'; intro _; rw [Taint.setVz_eq]
  all_goals simp only [reduceExec, execAlu, execAluW, execAlu32, execShift32, execShift, execRorx32,
      execRorx, execShld, execBtr, execMulx, execAdcx, execAdox, execCmov, State.store64,
      State.store32, State.store8, State.store16, State.store128, State.store256, State.store512,
      State.storeMasked512, State.storeMasked512B]
  all_goals uk_go

private theorem exec_unknowns {i : Instr} {s s' : State} (h : exec i s = some s') : s'.unknowns = s.unknowns :=
  exec_unknowns_pres i s s' h

theorem execBlock_unknowns : ∀ {is : List Instr} {s₁ s₂ a b : State} {t₁ t₂ : List Leak},
    execBlock isa is s₁ = some (a, t₁) → execBlock isa is s₂ = some (b, t₂) →
      t₁.length = t₂.length ∧ a.unknowns = s₁.unknowns ∧ b.unknowns = s₂.unknowns
  | [], _, _, _, _, _, _, h₁, h₂ => by
    simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h₁ h₂
    obtain ⟨rfl, rfl⟩ := h₁; obtain ⟨rfl, rfl⟩ := h₂; exact ⟨rfl, rfl, rfl⟩
  | i :: is, s₁, s₂, a, b, t₁, t₂, h₁, h₂ => by
    simp only [execBlock] at h₁ h₂
    cases e₁ : exec i s₁ with
    | none => simp only [e₁] at h₁; cases h₁
    | some u₁ =>
      cases e₂ : exec i s₂ with
      | none => simp only [e₂] at h₂; cases h₂
      | some u₂ =>
        simp only [isa, e₁, e₂] at h₁ h₂
        obtain ⟨p₁, hp₁, hq₁⟩ := Option.map_eq_some_iff.mp h₁
        obtain ⟨p₂, hp₂, hq₂⟩ := Option.map_eq_some_iff.mp h₂
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₁
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj hq₂
        obtain ⟨hl, ha, hb⟩ := execBlock_unknowns (s₁ := u₁) (s₂ := u₂) (by rw [hp₁]) (by rw [hp₂])
        refine ⟨?_, ha.trans (exec_unknowns e₁), hb.trans (exec_unknowns e₂)⟩
        simp only [List.length_append, List.length_map, hl, addrs_length i s₁ s₂]

theorem pushRegs_unknowns : ∀ (s : State) (rs : List Reg), (pushRegs s rs).unknowns = s.unknowns
  | _, [] => rfl
  | _, _ :: rs => pushRegs_unknowns _ rs

theorem push_unknowns {i : Instr} {s s₁ : State} (h : isa.push i s = some s₁) : s₁.unknowns = s.unknowns := by
  cases i <;> simp only [isa, push, reduceCtorEq] at h <;> split at h <;> cases h
  · exact pushRegs_unknowns _ _
  · rfl

/-- The unknowns a frame's release uses. -/
def popK : Instr → Nat
  | .pop _ k => 2 * k
  | .free b => b / 4
  | _ => 0

theorem pop_unknowns {j : Instr} {s₁ s₂ s' : State} (h : isa.pop j s₁ s₂ = some s') :
    s'.unknowns = fun n => s₂.unknowns (n + popK j) := by
  cases j <;> simp only [isa, pop, reduceCtorEq] at h <;> split at h <;> cases h <;> rfl

theorem call_unknowns {s s₁ : State} (h : isa.call s = some s₁) :
    s₁.unknowns = fun n => s.unknowns (n + 1) := by
  rw [call_callEntry] at h; cases h; rfl

theorem ret_unknowns {s₁ s₂ s' : State} (h : isa.ret s₁ s₂ = some s') : s'.unknowns = s₂.unknowns := by
  simp only [isa, ret] at h; split at h <;> cases h; rfl

theorem branch_ne {r₁ r₂ : List Leak} : Leak.branch true :: r₁ ≠ Leak.branch false :: r₂ := by
  intro h; cases h

/-- Two runs of code from the same unknowns, whose functions called
indirectly have the same addresses (`UpperLock.inames`), one of whose
traces is a prefix of the other's continued, have the same trace and end
with the same unknowns. -/
theorem Exec.unknowns_agree {c : Prog isa} {s₁ s₁' : State} {t₁ : List Leak} (e₁ : Exec isa c s₁ t₁ s₁') :
    ∀ {s₂ s₂' : State} {t₂ : List Leak} (r₁ r₂ : List Leak), Exec isa c s₂ t₂ s₂' →
      (∀ n ∈ UpperLock.inames c, s₁.syms n = s₂.syms n) →
      s₁.unknowns = s₂.unknowns → t₁ ++ r₁ = t₂ ++ r₂ → t₁ = t₂ ∧ s₁'.unknowns = s₂'.unknowns := by
  induction e₁ with
  | block h₁ =>
    intro _ _ _ r₁ r₂ e₂ _ hu ht
    cases e₂ with
    | block h₂ =>
      obtain ⟨hl, ha, hb⟩ := execBlock_unknowns h₁ h₂
      exact ⟨(List.append_inj ht hl).1, ha.trans (hu.trans hb.symm)⟩
  | seq x₁ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    simp only [UpperLock.inames, List.mem_append] at hf
    cases e₂ with
    | seq a₂ b₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ _ _ a₂ (fun n hn => hf n (.inl hn)) hu ht
      obtain ⟨rfl, hu''⟩ := ih₂ _ _ b₂ (fun n hn => by rw [Exec.syms x₁, Exec.syms a₂]; exact hf n (.inr hn))
        hu' (List.append_cancel_left ht)
      exact ⟨rfl, hu''⟩
  | iteT _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    simp only [UpperLock.inames, List.mem_append] at hf
    cases e₂ with
    | iteT _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ a₂ (fun n hn => hf n (.inl hn)) hu ht
      exact ⟨rfl, hu'⟩
    | iteF _ _ => exact absurd ht branch_ne
  | iteF _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    simp only [UpperLock.inames, List.mem_append] at hf
    cases e₂ with
    | iteT _ _ => exact absurd ht.symm branch_ne
    | iteF _ a₂ =>
      simp only [List.cons_append, List.cons.injEq, true_and] at ht
      obtain ⟨rfl, hu'⟩ := ih _ _ a₂ (fun n hn => hf n (.inr hn)) hu ht
      exact ⟨rfl, hu'⟩
  | loopExit _ _ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih ([.branch false] ++ r₁) ([.branch false] ++ r₂) b₂ hf hu ht
      exact ⟨rfl, hu'⟩
    | loopNext b₂ _ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih _ _ b₂ hf hu ht
      exact absurd (List.append_cancel_left ht).symm branch_ne
  | loopNext x₁ _ _ ih₁ ih₂ =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | loopExit b₂ _ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := ih₁ _ _ b₂ hf hu ht
      exact absurd (List.append_cancel_left ht) branch_ne
    | loopNext b₂ _ n₂ =>
      rw [List.append_assoc, List.append_assoc] at ht
      obtain ⟨rfl, hu'⟩ := ih₁ _ _ b₂ hf hu ht
      have ht' := List.append_cancel_left ht
      simp only [List.cons_append, List.cons.injEq, true_and] at ht'
      obtain ⟨rfl, hu''⟩ := ih₂ _ _ n₂ (fun n hn => by rw [Exec.syms x₁, Exec.syms b₂]; exact hf n hn) hu' ht'
      exact ⟨rfl, hu''⟩
  | @call _ _ s₀ _ s₂ _ _ hc₁ _ hr ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | @call _ _ _ _ s₂' _ _ hc₂ b₂ hr₂ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at ht
      have hl : (List.map Leak.addr (isa.callAddrs s₀)).length =
          (List.map Leak.addr (isa.callAddrs s₀')).length := by
        simp only [List.length_map]; rfl
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      obtain ⟨rfl, hu'⟩ := ih _ _ b₂ (fun n hn => by
        rw [UpperLock.call_syms hc₁, UpperLock.call_syms hc₂]; exact hf n hn)
        (by rw [call_unknowns hc₁, call_unknowns hc₂, hu]) ht'
      have hl' : (List.map Leak.addr (isa.retAddrs s₂)).length =
          (List.map Leak.addr (isa.retAddrs s₂')).length := by
        simp only [List.length_map]; rfl
      have h₃ := (List.append_inj (List.append_cancel_left ht') hl').1
      refine ⟨by rw [h₀, h₃], ?_⟩
      rw [ret_unknowns hr, ret_unknowns hr₂, hu']
  | @frame i j _ s₀ _ s₂ _ _ hp _ hq ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | @frame _ _ _ _ _ s₂' _ _ hp₂ b₂ hq₂ =>
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map]; exact addrs_length i s₀ s₀'
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      obtain ⟨rfl, hu'⟩ := ih _ _ b₂ (fun n hn => by rw [push_syms hp, push_syms hp₂]; exact hf n hn)
        (by rw [push_unknowns hp, push_unknowns hp₂, hu]) ht'
      have hl' : (List.map Leak.addr (isa.addrs j s₂)).length = (List.map Leak.addr (isa.addrs j s₂')).length := by
        simp only [List.length_map]; exact addrs_length j s₂ s₂'
      have h₃ := (List.append_inj (List.append_cancel_left ht') hl').1
      refine ⟨by rw [h₀, h₃], ?_⟩
      rw [pop_unknowns hq, pop_unknowns hq₂, hu']
  | @icall i _ _ _ s₀ _ s₂ _ _ hi₁ hc₁ _ hr₁ ih =>
    intro s₀' _ _ r₁ r₂ e₂ hf hu ht
    have hn := hf _ (List.mem_cons_self ..)
    cases e₂ with
    | @icall _ _ _ _ _ _ s₂' _ _ hi₂ hc₂ x₂ hr₂ =>
      simp only [List.append_assoc, List.cons_append] at ht
      have hl : (List.map Leak.addr (isa.addrs i s₀)).length = (List.map Leak.addr (isa.addrs i s₀')).length := by
        simp only [List.length_map]; exact addrs_length i s₀ s₀'
      obtain ⟨h₀, ht'⟩ := List.append_inj ht hl
      simp only [List.cons.injEq] at ht'
      obtain ⟨ha, ht'⟩ := ht'
      have hl₂ : (List.map Leak.addr (isa.callAddrs s₀)).length =
          (List.map Leak.addr (isa.callAddrs s₀')).length := by
        simp only [List.length_map]; rfl
      obtain ⟨h₁, ht''⟩ := List.append_inj ht' hl₂
      obtain ⟨rfl, hu'⟩ := ih _ _ x₂ (fun m hm => by
        rw [UpperLock.call_syms hc₁, UpperLock.call_syms hc₂]; exact hf m (by simp [UpperLock.inames, hm]))
        (by rw [call_unknowns hc₁, call_unknowns hc₂, hu]) ht''
      have hl' : (List.map Leak.addr (isa.retAddrs s₂)).length =
          (List.map Leak.addr (isa.retAddrs s₂')).length := by
        simp only [List.length_map]; rfl
      have h₃ := (List.append_inj (List.append_cancel_left ht'') hl').1
      refine ⟨by rw [h₀, ha, h₁, h₃], ?_⟩
      rw [ret_unknowns hr₁, ret_unknowns hr₂, hu']
    | icallNext hi₂ hne₂ x₂ =>
      exfalso
      obtain ⟨a₂, rest, hi₂', ht₂⟩ := UpperLock.icall_trace x₂
      rw [hi₂] at hi₂'; cases hi₂'
      rw [ht₂] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := UpperLock.append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₂
      rw [← ht.1, hn]
  | icallNext hi₁ hne₁ x₁ ih =>
    intro _ _ _ r₁ r₂ e₂ hf hu ht
    cases e₂ with
    | icallNext hi₂ hne₂ x₂ =>
      exact ih _ _ x₂ (fun m hm => hf m (List.mem_cons_of_mem _ (List.mem_append_right _ hm))) hu ht
    | icall hi₂ hc₂ x₂ hr₂ =>
      exfalso
      obtain ⟨a₁, rest, hi₁', ht₁⟩ := UpperLock.icall_trace x₁
      rw [hi₁] at hi₁'; cases hi₁'
      rw [ht₁] at ht
      simp only [List.append_assoc, List.cons_append] at ht
      obtain ⟨-, ht⟩ := UpperLock.append_cancel (by simp only [List.length_map]; exact addrs_length _ _ _) ht
      simp only [List.cons.injEq, Leak.addr.injEq] at ht
      apply hne₁
      rw [ht.1]; exact (hf _ (List.mem_cons_self ..)).symm

/-- Two runs of `c` leave the same bytes in the `stack` bytes below the stack
pointer on entry but those `wipe ks cs` zeroes, from states whose functions
`c` calls indirectly have the same addresses (as `NoResidue` is asked of
such code: `Verified.scrub`). -/
def ResOk (c : Prog isa) (k : Contract isa) (stack : Nat) (ks cs : List Nat) : Prop :=
  ∀ s₁ s₂ t₁ t₂ u₁ u₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns →
    (∀ n ∈ UpperLock.inames c, s₁.syms n = s₂.syms n) → Exec isa c s₁ t₁ u₁ → Exec isa c s₂ t₂ u₂ →
    ∀ x, (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 →
      ¬ WCov ks cs (s₁.gpr .rsp) x → u₁.mem x = u₂.mem x

section
variable {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
  {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
  {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}

/-- Code verified against a contract that `Sig.contract` derives, whose
frames and calls use at most `stack` bytes, run by `scrub`, which clears
the granules `ks` of the `cs.sum = stack` bytes of stack below `rsp`:
verified against the same contract, and without secret residue, if the
postcondition reads the memory on return only within the buffers (`hpost`)
and the code leaves the same bytes in both runs in the rest of that stack
(`hres`, which `RTaint` derives from its analysis). Below the level `evex`,
which resets MXCSR's flags itself (`mxFix`), the code may load MXCSR if two
of its runs along the same trace from the same MXCSR leave the same MXCSR
(`hmx`, `MxSame`, as `mxClass` shows of Intel's MCDT prologue and
epilogue): the contract's runs have the same trace (`ConstantTime`), so it
is then the same in both. -/
theorem Verified.scrubM {c : Prog isa} {v f : VecLevel} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hcs : cs.sum = stack) (hst : stack + 8 < 2 ^ 64)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hlv : ∀ i ∈ instrs c, i.vecLevelR ≤ v.level)
    (hmx : f ≠ .evex → MxSame c)
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : ∀ s u u', (sig.contract A pre post wa stack leak).pre s →
      (sig.contract A pre post wa stack leak).post s u →
      (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
      (u'.gpr .rax).setWidth (sig.retBits A.ptrBits) = (u.gpr .rax).setWidth (sig.retBits A.ptrBits) →
      (sig.contract A pre post wa stack leak).post s u')
    (hres : ResOk c (sig.contract A pre post wa stack leak) stack ks cs)
    (ht : TailOk (sig.retBits A.ptrBits) xs ps gs ks)
    (hxs : (∀ x, x ∈ xs) ∨ ∀ i ∈ instrs c, writesVec i = false)
    (hxe : v = .evex → ∀ x, x ∈ xs) (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk f ks cs p)
    (hgk : ∀ r ∈ scratchRegs, r ∉ gs → r ∉ ps → ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    Verified target (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c f)
        (sig.contract A pre post wa stack leak) ∧
      ((∀ s₁ s₂, (sig.contract A pre post wa stack leak).pub s₁ s₂ → ∀ n ∈ UpperLock.inames c, s₁.syms n = s₂.syms n) →
        NoResidue (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c f)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) := by
  have hnps : ∀ r, r ∉ scratchRegs → r ∉ ps := fun r h h' => h (ht.psOk r h')
  have hngs : ∀ r, r ∉ scratchRegs → r ∉ gs := fun r h h' => h (ht.gsOk r h')
  obtain ⟨hcor, hct, hsat⟩ := h
  -- What a run of `c`, then of the clearing, gives.
  have run : ∀ s t u, (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      abiPreserved s u ∧ (sig.contract A pre post wa stack leak).post s u ∧
      u.gpr .rsp = s.gpr .rsp ∧ cs.sum ≤ (u.gpr .rsp).toNat := by
    intro s t u hs he
    obtain ⟨t', u', he', ha, hp⟩ := hcor s hs
    obtain ⟨-, rfl⟩ := Exec.det he he'
    have hr : u.gpr .rsp = s.gpr .rsp := ha.1 .rsp (by decide)
    refine ⟨ha, hp, hr, ?_⟩
    rcases (contract_pre_scrub hA hs).1 with h0 | h0
    · rw [hcs, h0]; exact Nat.zero_le _
    · rw [hcs, hr]; exact h0
  -- The clearing's run.
  have tail : ∀ s t u s' t', (sig.contract A pre post wa stack leak).pre s → Exec isa c s t u →
      Exec isa (Impl.Scrub.X86_64.scrubTail v (sig.retBits A.ptrBits) xs ps gs ks cs f) u t' s' →
      ∃ m', t' = tailTr v ks cs (s.gpr .rsp) f ∧
        s' = finState v (sig.retBits A.ptrBits) xs ps gs m' (fun n => u.unknowns (n + wipeK cs + mxK f)) u f ∧
        (∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x) ∧
        (∀ x, m' x = tailMem f ks cs (s.gpr .rsp) u.unknowns u.mem x) := by
    intro s t u s' t' hs he het
    obtain ⟨-, -, hr, hl⟩ := run s t u hs he
    obtain ⟨m', e, hm⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl (hev _ hl)
    obtain ⟨rfl, rfl⟩ := Exec.det het e
    rw [hr] at hm
    have ho : ∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x :=
      fun x h => (hm x).trans (tailMem_frame f ks cs (s.gpr .rsp) u.unknowns u.mem
        (fun h' => (hev _ (hr ▸ hl) h').2.1) x fun r hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'; rw [hcs]; exact h)
    exact ⟨m', by rw [hr], rfl, ho, hm⟩
  -- Buffers are not in the stack the clearing wipes.
  have outB : ∀ s, (sig.contract A pre post wa stack leak).pre s → ∀ x,
      (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) →
        ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 := by
    intro s hs x ⟨r, hr, hx⟩ hb
    by_cases h0 : stack = 0
    · subst h0; simp [Region.Contains] at hb
    · exact ((contract_pre_scrub hA hs).2 r hr).2 h0 x hb hx
  refine ⟨⟨fun s hs => ?_, fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ => ?_, hsat⟩,
    fun hsy s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp ho hun e₁ e₂ => ?_⟩
  · -- Correctness.
    obtain ⟨t, u, he, -⟩ := hcor s hs
    obtain ⟨ha, hq, hr, hl⟩ := run s t u hs he
    obtain ⟨m', et, hm⟩ := tail_run v (sig.retBits A.ptrBits) cs ht u hv hl (hev _ hl)
    rw [hr] at hm
    have hmo : ∀ x, ¬ (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 → m' x = u.mem x :=
      fun x h => (hm x).trans (tailMem_frame f ks cs (s.gpr .rsp) u.unknowns u.mem
        (fun h' => (hev _ (hr ▸ hl) h').2.1) x fun r hr' => by
          simp only [List.mem_singleton] at hr'; subst hr'; rw [hcs]; exact h)
    refine ⟨_, _, .seq he et, ⟨fun r hr' => ?_, ?_, ?_⟩, ?_⟩
    · have h1 : r ∉ scratchRegs := by revert hr'; revert r; decide
      have h2 : r ≠ .rax := by
        have : ∀ r ∈ calleeSaved, r ≠ Reg.rax := by decide
        exact this r hr'
      rw [finState_gpr (hnps r h1) (hngs r h1) h2]
      exact ha.1 r hr'
    · rw [← ha.2.1]
      apply Mem.readW_congr
      intro i hi
      rw [finState_other.1]
      exact hmo _ (slot_not_below hst (by
        simp only [Region.Contains]
        rw [show s.gpr .rsp + BitVec.ofNat 64 i - s.gpr .rsp = BitVec.ofNat 64 i by
          rw [BitVec.add_comm, BitVec.add_sub_cancel], BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega_using [hi])]
        simp only [Nat.reduceDiv] at hi; omega_using [hi]))
    · rw [finState_other.2.2.2.2.2.1, fixMx_ctl]; exact ha.2.2
    · refine hpost s u _ hs hq (fun x hx => hmo x (outB s hs x hx)) ?_
      rw [finState_rax (hngs _ (by decide))]
      exact retVal_low hrb _
  · -- Constant time.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    obtain ⟨m₁, rfl, -⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, rfl, -⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    rw [hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂, contract_pub_rsp hA hp]
  · -- No residue.
    cases e₁ with | seq a₁ b₁ =>
    cases e₂ with | seq a₂ b₂ =>
    rename_i u₁ _ _ u₂ _ _
    obtain ⟨m₁, -, rfl, hmo₁, ht₁⟩ := tail s₁ _ _ _ _ h₁ a₁ b₁
    obtain ⟨m₂, -, rfl, hmo₂, ht₂⟩ := tail s₂ _ _ _ _ h₂ a₂ b₂
    -- The two runs of `c` have the same trace, so they end with the same unknowns.
    obtain ⟨-, hU⟩ := Exec.unknowns_agree a₁ [] [] a₂ (hsy _ _ hp) hun
      (by rw [List.append_nil, List.append_nil]; exact hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂)
    obtain ⟨ha₁, -, -, -⟩ := run s₁ _ _ h₁ a₁
    obtain ⟨ha₂, -, -, -⟩ := run s₂ _ _ h₂ a₂
    have ho' := ho
    obtain ⟨hrd, hwr, hg, -, -, -, -, -, hxm, hy, hz, hyH, hzH, hmx', hm⟩ := ho
    have hsp' : s₁.gpr .rsp = s₂.gpr .rsp := hg .rsp (by decide)
    have rw₁ := Exec.rdwr a₁
    have rw₂ := Exec.rdwr a₂
    -- Below the level `evex`, the code keeps `zmm16`–`zmm31`, and leaves in
    -- MXCSR a function of MXCSR on entry, which is the same in both runs.
    have lv1 : v ≠ .evex → ∀ i ∈ instrs c, i.vecLevelR ≤ 1 := fun hne i hi => by
      have := hlv i hi
      cases v
      · simp only [VecLevel.level] at this; omega_using [this]
      · exact this
      · exact absurd rfl hne
    have k1 : v ≠ .evex → (u₁.ymmH = s₁.ymmH ∧ u₁.zmmHiH = s₁.zmmHiH) ∧
        (u₂.ymmH = s₂.ymmH ∧ u₂.zmmHiH = s₂.zmmHiH) := fun hne => by
      have k₁ := Exec.vecKeep1R (lv1 hne) a₁
      have k₂ := Exec.vecKeep1R (lv1 hne) a₂
      simp only [vk1R, Prod.mk.injEq] at k₁ k₂
      exact ⟨k₁, k₂⟩
    have kmx : f ≠ .evex → u₁.mxcsr = u₂.mxcsr := fun hne =>
      hmx hne _ _ _ _ _ a₁ (hct _ _ _ _ _ _ h₁ h₂ hp a₁ a₂ ▸ a₂) hmx'
    have cH : v ≠ .evex → ∀ w : State, (clearedH v w).ymmH = w.ymmH ∧ (clearedH v w).zmmHiH = w.zmmHiH :=
      fun hne w => by cases v <;> first | exact ⟨rfl, rfl⟩ | exact absurd rfl hne
    have hdep : c.x86_64Depth < 2 ^ 64 := by omega_using [hd, hst]
    have f₁ := Exec.stackFrame hsp a₁ hdep
    have f₂ := Exec.stackFrame hsp a₂ hdep
    have cs_ : ∀ r : Reg, r ∉ scratchRegs → r ≠ .rax → r ∈ calleeSaved := by intro r; cases r <;> decide
    -- With the vector registers' upper halves kept: code of level 0, or that writes none.
    have l0 : (∃ x, x ∉ xs ∧ v ≠ .sse) → ∀ i ∈ instrs c, i.vecLevelR = 0 := by
      rintro ⟨x, hx, -⟩ i hi
      by_cases he : v = .evex
      · exact absurd (hxe he x) hx
      · rcases hxs with h | h
        · exact absurd (h x) hx
        · exact vecLevelR_of_writesVec (h i hi) (lv1 he i hi)
    have upper : ∀ x, ¬ (v ≠ .sse ∧ x ∈ xs) → u₁.ymmHi x = u₂.ymmHi x ∧ u₁.zmmHi x = u₂.zmmHi x := by
      intro x hn
      have hl : ∀ i ∈ instrs c, i.vecLevelR = 0 := by
        by_cases hs : v = .sse
        · subst hs; exact fun i hi => by simpa [VecLevel.level] using hlv i hi
        · exact l0 ⟨x, fun h => hn ⟨hs, h⟩, hs⟩
      have k₁ := Exec.vecKeep0R hl a₁
      have k₂ := Exec.vecKeep0R hl a₂
      simp only [vk0R, Prod.mk.injEq] at k₁ k₂
      rw [k₁.2.2.1, k₂.2.2.1, k₁.2.2.2, k₂.2.2.2, hy, hz]
      exact ⟨rfl, rfl⟩
    refine ⟨⟨?_, ?_, fun r hr => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun x hx => ?_⟩,
      finState_flags⟩
    · rw [finState_other.2.1, finState_other.2.1, rw₁.1, rw₂.1, hrd]
    · rw [finState_other.2.2.1, finState_other.2.2.1, rw₁.2, rw₂.2, hwr]
    · by_cases hs : r ∈ scratchRegs
      · have h11 : r ≠ .rax := hr
        by_cases hg' : r ∈ gs
        · simp [finState, clearedG, hg']
        · by_cases hp' : r ∈ ps
          · simp [finState, clearedG, State.setReg, clearedP_gpr, hg', hp', h11]
          · rw [finState_gpr hp' hg' h11, finState_gpr hp' hg' h11, Exec.gpr (hgk r hs hg' hp') a₁,
              Exec.gpr (hgk r hs hg' hp') a₂]
            exact hg r hr
      · rw [finState_gpr (hnps r hs) (hngs r hs) hr, finState_gpr (hnps r hs) (hngs r hs) hr,
          ha₁.1 r (cs_ r hs hr), ha₂.1 r (cs_ r hs hr)]
        exact hg r hr
    · rw [finState_rax (hngs _ (by decide)), finState_rax (hngs _ (by decide)), retVal_hi hrb, retVal_hi hrb]
    · rw [finState_other.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.2.1, finState_other.2.2.2.2.2.2.2.2.1]
    · rw [finState_other.2.2.2.2.2.2.2.2.2, finState_other.2.2.2.2.2.2.2.2.2]
    · rw [finState_xmm, finState_xmm]
      funext x
      split
      · rfl
      · rename_i hx
        rcases hxs with h | h
        · exact absurd (h x) hx
        · rw [Exec.xmmKeep h a₁, Exec.xmmKeep h a₂, hxm]
    · rw [finState_ymmHi, finState_ymmHi]
      funext x
      split
      · rfl
      · rename_i hn; exact (upper x hn).1
    · rw [finState_zmmHi, finState_zmmHi]
      funext x
      split
      · rfl
      · rename_i hn; exact (upper x hn).2
    · rw [finState_other.2.2.2.1, finState_other.2.2.2.1]
      by_cases he : v = .evex
      · subst he; rfl
      · rw [(cH he _).1, (cH he _).1, (k1 he).1.1, (k1 he).2.1, hyH]
    · rw [finState_other.2.2.2.2.1, finState_other.2.2.2.2.1]
      by_cases he : v = .evex
      · subst he; rfl
      · rw [(cH he _).2, (cH he _).2, (k1 he).1.2, (k1 he).2.2, hzH]
    · rw [finState_other.2.2.2.2.2.1, finState_other.2.2.2.2.2.1]
      by_cases he : f = .evex
      · exact fixMx_congr f he (by rw [ha₁.2.2, ha₂.2.2, hmx'])
      · cases f
        · exact kmx he
        · exact kmx he
        · exact absurd rfl he
    · rw [finState_other.1, finState_other.1]
      have hx' : ∀ r ∈ s₁.rd ++ s₁.wr, ¬ r.Contains x 1 := by
        rw [finState_other.2.1, finState_other.2.2.1, rw₁.1, rw₁.2] at hx
        exact hx
      by_cases hb : (⟨s₁.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1
      · rw [ht₁ x, ht₂ x, ← hsp', hU]
        exact tailMem_congr _ _ _ _ _ x fun hw => hres _ _ _ _ _ _ h₁ h₂ hp ho' hun (hsy _ _ hp) a₁ a₂ x hb hw
      · have nd : ∀ sp : Addr, sp = s₁.gpr .rsp →
            ¬ (⟨sp - BitVec.ofNat 64 c.x86_64Depth, c.x86_64Depth⟩ : Region).Contains x 1 := by
          rintro sp rfl hc; exact hb (below_sub hd (by omega_using [hst]) x hc)
        have nw : ∀ r ∈ s₁.wr, ¬ r.Contains x 1 := fun r hr => hx' r (List.mem_append_right _ hr)
        rw [hmo₁ x hb, hmo₂ x (hsp' ▸ hb),
          f₁ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r hr
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ rfl),
          f₂ x (fun r hr => by
            rcases List.mem_append.mp hr with hr | hr
            · exact nw r (hwr ▸ hr)
            · simp only [List.mem_singleton] at hr; subst hr; exact nd _ hsp'.symm)]
        exact hm x hx'

/-- `Verified.scrubM`, for code of `vecLevel` at most `v.level`, which below
the level `evex` never loads MXCSR. -/
theorem Verified.scrub {c : Prog isa} {v : VecLevel} {xs : List XReg} {ps gs : List Reg} {ks cs : List Nat}
    (hA : ScrubAbi A)
    (h : Verified target c (sig.contract A pre post wa stack leak))
    (hsp : SpSafe c) (hd : c.x86_64Depth ≤ stack) (hcs : cs.sum = stack) (hst : stack + 8 < 2 ^ 64)
    (hv : ∀ b ∈ cs, 0 < b ∧ b < 4096 ∧ b % 8 = 0)
    (hlv : ∀ i ∈ instrs c, i.vecLevel ≤ v.level)
    (hrb : sig.retBits A.ptrBits ≤ 32 ∨ sig.retBits A.ptrBits = 64)
    (hpost : ∀ s u u', (sig.contract A pre post wa stack leak).pre s →
      (sig.contract A pre post wa stack leak).post s u →
      (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
      (u'.gpr .rax).setWidth (sig.retBits A.ptrBits) = (u.gpr .rax).setWidth (sig.retBits A.ptrBits) →
      (sig.contract A pre post wa stack leak).post s u')
    (hres : ResOk c (sig.contract A pre post wa stack leak) stack ks cs)
    (ht : TailOk (sig.retBits A.ptrBits) xs ps gs ks)
    (hxs : (∀ x, x ∈ xs) ∨ ∀ i ∈ instrs c, writesVec i = false)
    (hxe : v = .evex → ∀ x, x ∈ xs) (hev : ∀ p : Addr, cs.sum ≤ p.toNat → EvexOk v ks cs p)
    (hgk : ∀ r ∈ scratchRegs, r ∉ gs → r ∉ ps → ∀ i ∈ instrs c, Taint.clobbers i r = false) :
    Verified target (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c)
        (sig.contract A pre post wa stack leak) ∧
      ((∀ s₁ s₂, (sig.contract A pre post wa stack leak).pub s₁ s₂ → ∀ n ∈ UpperLock.inames c, s₁.syms n = s₂.syms n) →
        NoResidue (Impl.Scrub.X86_64.scrub v (sig.retBits A.ptrBits) xs ps gs ks cs c)
        (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits)) :=
  Verified.scrubM hA h hsp hd hcs hst hv (fun i hi => Nat.le_trans (vecLevelR_le i) (hlv i hi))
    (fun hne => MxSame.of_fun ⟨id, fun _ _ _ he => Exec.mxcsr (fun i hi => noLoad_of_vecLevel (by
      have := hlv i hi
      cases v
      · simp only [VecLevel.level] at this; omega_using [this]
      · exact this
      · exact absurd rfl hne)) he⟩)
    hrb hpost hres ht hxs hxe hev hgk

end

/-! ## Registering scrubbed code -/

/-- A postcondition that reads the memory on return only within the
buffers, and of the result only its `rb` bits (`Verified.scrub`'s `hpost`). -/
def PostOut (k : Contract isa) (rb : Nat) : Prop :=
  ∀ s u u', k.pre s → k.post s u →
    (∀ x, (∃ r ∈ s.rd ++ s.wr, r.Contains x 1) → u'.mem x = u.mem x) →
    (u'.gpr .rax).setWidth rb = (u.gpr .rax).setWidth rb → k.post s u'

/-- `PostOut` of a contract `Sig.contract` derives, from its postcondition's
reading the memory on return only within the buffers. -/
theorem postOut_of_local {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -⟩ := hs
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

/-- `postOut_of_local`, for a postcondition that reads the memory on return
only within the buffers where the precondition holds (e.g. one that reads
an output buffer by a length the precondition equates with the buffer's). -/
theorem postOut_of_local_pre {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))}
    (hl : ∀ vs m m₁ m₂ r, vs.length = (sig.words A.ptrBits).length →
      Curry.apply (sig.words A.ptrBits) pre vs m →
      (∀ b ∈ Sig.bufs sig.params vs, ∀ a, b.1.Contains a 1 → m₁ a = m₂ a) →
      Curry.apply (sig.words A.ptrBits) post vs m m₁ r →
        Curry.apply (sig.words A.ptrBits) post vs m m₂ r) :
    PostOut (sig.contract A pre post wa stack leak) (sig.retBits A.ptrBits) := by
  intro s u u' hs hp hm hr
  simp only [Sig.contract] at hs hp ⊢
  revert hs hp
  cases hargs : A.args ((sig.words A.ptrBits).map (·.bits A.ptrBits)) with
  | none => intro hs; exact hs.elim
  | some vals =>
    intro hs hp
    simp only at hs hp ⊢
    obtain ⟨-, hrd, hwr, -, -, -, hpre⟩ := hs
    have hpre' : Curry.apply (sig.words A.ptrBits) pre (vals s) (A.mem s) := by
      cases hal : A.alignsBufs
      · rw [hal] at hpre; exact hpre
      · rw [hal] at hpre; exact hpre.1
    rw [hA.ret, hA.mem, hA.mem] at hp ⊢
    rw [hA.mem] at hpre'
    rw [hr]
    refine hl (vals s) _ _ _ _ (by rw [hA.argsLen _ _ hargs s, List.length_map]) hpre' (fun b hb a ha => ?_) hp
    have hin : b.1 ∈ s.rd ++ s.wr := by
      cases hw : b.2
      · apply List.mem_append_left; apply hA.rdSub; rw [hrd]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          by simp [hw]⟩, rfl⟩
      · apply List.mem_append_right; rw [← hA.wr, hwr]
        exact List.mem_map.mpr ⟨b, List.mem_filter.mpr ⟨List.mem_append_left _ (List.mem_append_left _ hb),
          hw⟩, rfl⟩
    exact (hm a ⟨b.1, hin, ha⟩).symm

theorem stores16_spSafe (w : Bool) (ks : List Nat) (off base : Nat) :
    ∀ k, (stores16 w ks off base k).all (fun i => !isa.writesSp i) = true
  | 0 => rfl
  | 1 => by simp only [stores16, store1]; split <;> rfl
  | k + 2 => by
    simp only [stores16, store1]
    split
    · simp only [List.all_cons, stores16_spSafe w ks off base k, Bool.and_true]; rfl
    · simp only [List.all_append, stores16_spSafe w ks off base (k + 1), Bool.and_true]; split <;> rfl

theorem wipe_spSafe (w : Bool) (ks : List Nat) :
    ∀ cs : List Nat, (wipe w ks cs).all (fun i => !isa.writesSp i) = true
  | [] => rfl
  | b :: bs => by
    simp only [wipe, Code.all, chunkStores, List.all_append, stores16_spSafe, wipe_spSafe w ks bs,
      Bool.true_and, Bool.and_true, store8s]
    split <;> rfl

theorem zeroR_spSafe : ∀ r ∈ scratchRegs, (!isa.writesSp (zeroR r)) = true := by decide

theorem scrub_spSafe {c : Prog isa} (v : VecLevel) (rb : Nat) (xs : List XReg) (ps gs : List Reg)
    (ks cs : List Nat) {f : VecLevel} (hps : ∀ r ∈ ps, r ∈ scratchRegs) (hgs : ∀ r ∈ gs, r ∈ scratchRegs)
    (h : c.all (fun i => !isa.writesSp i) = true) :
    (scrub v rb xs ps gs ks cs c f).all (fun i => !isa.writesSp i) = true := by
  have hx : (xs.map (zeroX v)).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_map, List.all_eq_true]
    exact fun x _ => by cases v <;> rfl
  have hp : (ps.map zeroR).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_map, List.all_eq_true]
    exact fun r hr => zeroR_spSafe r (hps r hr)
  have hh : (clearHigh v).all (fun i => !isa.writesSp i) = true := by cases v <;> rfl
  have hm : (mxFix f).all (fun i => !isa.writesSp i) = true := by cases f <;> rfl
  have hv : (xs.map (zeroX v) ++ clearHigh v ++ ps.map zeroR).all (fun i => !isa.writesSp i) = true := by
    rw [List.all_append, List.all_append, hx, hh, hp]; rfl
  have hg : (retFix rb ++ gs.map zeroR).all (fun i => !isa.writesSp i) = true := by
    simp only [List.all_append, List.all_map, Bool.and_eq_true, List.all_eq_true]
    refine ⟨?_, fun r hr => zeroR_spSafe r (hgs r hr)⟩
    unfold retFix
    split
    · intro i hi; simp at hi; subst hi; rfl
    · split
      · intro i hi; simp at hi; subst hi; rfl
      · split
        · intro i hi; simp at hi; subst hi; rfl
        · intro i hi; simp at hi
  rw [scrub, scrubTail]
  simp only [Code.all]
  rw [h, hv, hm, wipe_spSafe v.wide ks cs, hg]
  rfl

/-! ## What `scrub` clears, from the code -/

theorem tailOk_of (rb : Nat) (c : Prog isa) (ks : List Nat) :
    TailOk rb (xsOf c ks) (psOf ks) (gsOf Taint.clobbers c) ks where
  x0 h := by unfold xsOf; split <;> first | simp [mem_xregs] | simp [h]
  r11 h := by simp [psOf, h]
  psOk r hr := by unfold psOf at hr; split at hr <;> simp_all [scratchRegs]
  gsOk r hr := by
    unfold gsOf at hr; simp only at hr; split at hr
    · simp_all [scratchRegs]
    · exact (List.mem_filter.mp hr).1
  gne := by unfold gsOf; simp only; split <;> simp_all

theorem xs_of (c : Prog isa) (ks : List Nat) :
    (∀ x, x ∈ xsOf c ks) ∨ ∀ i ∈ instrs c, writesVec i = false := by
  unfold xsOf; split
  · rename_i h; exact .inr fun i hi => by simpa using Code.all_instrs h i hi
  · exact .inl mem_xregs

theorem gs_of (c : Prog isa) (ks : List Nat) :
    ∀ r ∈ scratchRegs, r ∉ gsOf Taint.clobbers c → r ∉ psOf ks → ∀ i ∈ instrs c, Taint.clobbers i r = false := by
  intro r hr hg _ i hi
  have hall : c.all (fun i => !Taint.clobbers i r) = true := by
    unfold gsOf at hg; simp only at hg
    split at hg
    · rename_i hw
      by_contra hc
      have : r ∈ scratchRegs.filter fun r => !c.all (fun i => !Taint.clobbers i r) := by
        simp only [List.mem_filter, hr, true_and, Bool.not_eq_true']
        simpa using hc
      rw [hw] at this; cases this
    · by_contra hc
      exact hg (List.mem_filter.mpr ⟨hr, by simpa using hc⟩)
  simpa using Code.all_instrs hall i hi

theorem chunksAux_spec : ∀ f n, n / 4080 < f →
    (chunksAux f n).sum = n ∧ ∀ b ∈ chunksAux f n, 0 < b ∧ b ≤ 4080 ∧ (n % 8 = 0 → b % 8 = 0)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, 0, _ => ⟨rfl, fun _ h => by simp [chunksAux] at h⟩
  | f + 1, n + 1, h => by
    simp only [chunksAux]
    split
    · exact ⟨by simp, fun b hb => by simp at hb; subst hb; omega_arith⟩
    · obtain ⟨hs, hv⟩ := chunksAux_spec f (n + 1 - 4080) (by omega_arith)
      refine ⟨by rw [List.sum_cons, hs]; omega_arith, fun b hb => ?_⟩
      rcases List.mem_cons.mp hb with rfl | hb
      · omega_using []
      · have := hv b hb; omega_using [this]

theorem chunks_sum (n : Nat) : (chunks n).sum = n := (chunksAux_spec _ n (by omega_using [])).1

theorem chunks_valid {n : Nat} (h8 : n % 8 = 0) : ∀ b ∈ chunks n, 0 < b ∧ b < 4096 ∧ b % 8 = 0 :=
  fun b hb => by have := (chunksAux_spec _ n (by omega_using [])).2 b hb; omega_using [h8, this]

/-! ## Wiping every granule

With every granule of the stack in `ks`, `ResOk` asks nothing of the code:
what code the residue analysis cannot follow is scrubbed so. -/

/-- Every granule of `wipe _ cs`. -/
def allKs : List Nat → List Nat
  | [] => []
  | b :: bs => bs.sum :: ((List.range (b / 16)).map fun t => bs.sum + b % 16 + 16 * t) ++ allKs bs

theorem covC_mono {ks ks' : List Nat} (h : ∀ k ∈ ks, k ∈ ks') {off b d : Nat} (hc : covC ks off b d = true) :
    covC ks' off b d = true := by
  unfold covC at hc ⊢
  split
  · rename_i hd
    simp only [hd, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at hc
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨hc.1, List.contains_iff_mem.mpr (h _ (List.contains_iff_mem.mp hc.2))⟩
  · rename_i hd
    simp only [hd, ↓reduceIte] at hc
    exact List.contains_iff_mem.mpr (h _ (List.contains_iff_mem.mp hc))

theorem cov_mono {ks ks' : List Nat} (h : ∀ k ∈ ks, k ∈ ks') : ∀ (cs : List Nat) (i : Nat),
    cov ks cs i = true → cov ks' cs i = true
  | [], _, hc => by simp [cov] at hc
  | b :: bs, i, hc => by
    simp only [cov] at hc ⊢
    split
    · rename_i hlt
      simp only [hlt, ↓reduceIte] at hc
      exact cov_mono h bs i hc
    · rename_i hlt
      simp only [hlt, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hc
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hc.1, covC_mono h hc.2⟩

theorem cov_all : ∀ cs : List Nat, (∀ b ∈ cs, b % 8 = 0) → ∀ i < cs.sum, cov (allKs cs) cs i = true
  | [], _, i, hi => by simp at hi
  | b :: bs, h8, i, hi => by
    have hb8 := h8 b (List.mem_cons_self ..)
    simp only [List.sum_cons] at hi
    simp only [cov]
    split
    · rename_i hlt
      exact cov_mono (fun k hk => by simp only [allKs, List.mem_cons, List.mem_append]; exact .inr hk) bs i
        (cov_all bs (fun b' hb' => h8 b' (List.mem_cons_of_mem _ hb')) i hlt)
    · rename_i hlt
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨by omega_using [hi, hlt], ?_⟩
      unfold covC
      split
      · simp only [Bool.and_eq_true, beq_iff_eq]
        exact ⟨by omega_arith, List.contains_iff_mem.mpr (by simp [allKs])⟩
      · refine List.contains_iff_mem.mpr ?_
        simp only [allKs, List.mem_cons, List.mem_append, List.mem_map, List.mem_range]
        exact .inl (.inr ⟨(i - bs.sum - b % 16) / 16, by omega_arith, rfl⟩)

theorem wcov_all {cs : List Nat} (h8 : ∀ b ∈ cs, b % 8 = 0) {p x : Addr}
    (hx : (⟨p - BitVec.ofNat 64 cs.sum, cs.sum⟩ : Region).Contains x 1) : WCov (allKs cs) cs p x :=
  ⟨hx, cov_all cs h8 _ (by simp only [Region.Contains] at hx; omega_using [hx])⟩

/-- `ResOk`, with every granule wiped. -/
theorem resOk_all (c : Prog isa) (k : Contract isa) {stack : Nat} (h8 : stack % 8 = 0) :
    ResOk c k stack (allKs (chunks stack)) (chunks stack) := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ _ _ _ _ _ _ _ _ x hx hn
  exact absurd (wcov_all (fun b hb => (chunks_valid h8 b hb).2.2) (by rw [chunks_sum]; exact hx)) hn

/-- What `c` leaves in the `stack` bytes below the stack pointer on entry,
run by run: a run from `s` that meets `k.pre` leaves each byte `x` there
that `wipe ks cs` does not zero as `V s x` if that is `some b` (zero, or a
value it stores there last, such as a saved register), and as it found it if
it is `none`. -/
def StackLeaves (c : Prog isa) (k : Contract isa) (stack : Nat) (ks cs : List Nat)
    (V : State → Addr → Option (BitVec 8)) : Prop :=
  ∀ s t u, k.pre s → Exec isa c s t u →
    ∀ x, (⟨s.gpr .rsp - BitVec.ofNat 64 stack, stack⟩ : Region).Contains x 1 →
      ¬ WCov ks cs (s.gpr .rsp) x → u.mem x = (V s x).getD (s.mem x)

/-- What `V` says code leaves depends only on what two runs agree on: the
public data and everything outside the buffers on entry (`ResOk`'s
hypotheses). A constant (`fun _ _ => some 0` for bytes the code zeroes) does;
so does anything read from the registers, which `Outside 0` makes the same
but for `rax`, or from the return addresses (`State.unknowns`), or what
the unknowns a run of code from them ends with are (`innerU`), which two
runs agree on when the functions it calls indirectly, among `N`, have the
same addresses. -/
def LeavesPub (k : Contract isa) (N : List String) (V : State → Addr → Option (BitVec 8)) : Prop :=
  ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → Outside 0 s₁ s₂ → s₁.unknowns = s₂.unknowns →
    (∀ n ∈ N, s₁.syms n = s₂.syms n) → V s₁ = V s₂

/-- Code whose stack below `rsp` each run leaves as `V` says (`StackLeaves`),
where `V` depends only on what two runs agree on (`LeavesPub`), leaves the
same bytes there in two runs (`ResOk`): those it leaves as it found them
were the same on entry, being outside the buffers, and the others are the
same by `V`. So the bytes it zeroes, and those it leaves holding public
values, need no wipe. -/
theorem resOk_of_leaves {A : Abi isa} (hA : ScrubAbi A) {sig : Sig}
    {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {c : Prog isa} {ks cs : List Nat}
    {V : State → Addr → Option (BitVec 8)}
    (hl : StackLeaves c (sig.contract A pre post wa stack leak) stack ks cs V)
    (hv : LeavesPub (sig.contract A pre post wa stack leak) (UpperLock.inames c) V) :
    ResOk c (sig.contract A pre post wa stack leak) stack ks cs := by
  intro s₁ s₂ t₁ t₂ u₁ u₂ h₁ h₂ hp ho hu hsy e₁ e₂ x hx hw
  have hsp : s₂.gpr .rsp = s₁.gpr .rsp := (ho.2.2.1 .rsp (by decide)).symm
  rw [hl s₁ t₁ u₁ h₁ e₁ x hx hw, hl s₂ t₂ u₂ h₂ e₂ x (hsp ▸ hx) (hsp ▸ hw), hv s₁ s₂ h₁ h₂ hp ho hu hsy]
  cases V s₂ x with
  | some b => rfl
  | none =>
    refine ho.2.2.2.2.2.2.2.2.2.2.2.2.2.2 x fun r hr => ?_
    have hn : stack ≠ 0 := by
      rintro rfl; simp [Region.Contains] at hx
    exact (contract_pre_scrub hA h₁).2 r hr |>.2 hn x hx

theorem evexOk_all (v : VecLevel) {cs : List Nat} (h8 : ∀ b ∈ cs, b % 8 = 0) (h16 : 16 ≤ cs.sum)
    (hs : cs.sum < 2 ^ 64) {p : Addr} (hp : cs.sum ≤ p.toNat) : EvexOk v (allKs cs) cs p := by
  intro _
  refine ⟨?_, h16, fun x hx => wcov_all h8 ?_⟩
  · cases cs with
    | nil => simp at h16
    | cons b bs => simp [allKs]
  · have := p.isLt
    have := x.isLt
    simp only [Region.Contains, BitVec.toNat_sub, BitVec.toNat_ofNat] at hx ⊢
    generalize p.toNat = P at *
    generalize x.toNat = X at *
    generalize cs.sum = S at *
    rw [Nat.mod_eq_of_lt (a := S) (by omega_using [hs])]
    rw [Nat.mod_eq_of_lt (a := 16) (by decide)] at hx
    omega_using [hx, h16]

/-! ## Registering scrubbed code, continued -/

/-- What the level `evex` needs of a registration's clearing (nothing, below
it): every SSE register cleared, and `mxFix`'s bytes wiped. -/
def EvexReg (c : Prog isa) (v : VecLevel) (ks : List Nat) (stack : Nat) : Prop :=
  (v = .evex → ∀ x, x ∈ xsOf c ks) ∧ ∀ p : Addr, (chunks stack).sum ≤ p.toNat → EvexOk v ks (chunks stack) p

theorem evexReg_of_ne {c : Prog isa} {v : VecLevel} {ks : List Nat} {stack : Nat} (h : v ≠ .evex) :
    EvexReg c v ks stack := ⟨fun e => absurd e h, fun _ _ e => absurd e h⟩

/-- At the level `evex`, with every granule wiped, for code that writes a
vector register and has 16 bytes of stack. -/
theorem evexReg_all {c : Prog isa} {v : VecLevel} {stack : Nat} (h8 : stack % 8 = 0) (hst : stack + 8 < 2 ^ 64)
    (hev : v = .evex → 16 ≤ stack ∧ c.all (fun i => !writesVec i) = false) :
    EvexReg c v (allKs (chunks stack)) stack := by
  refine ⟨fun e x => ?_, fun p hp e => ?_⟩
  · unfold xsOf; rw [(hev e).2]; exact mem_xregs x
  · exact evexOk_all v (fun b hb => (chunks_valid h8 b hb).2.2) (by rw [chunks_sum]; exact (hev e).1)
      (by rw [chunks_sum]; omega_using [hst]) hp e

/-- The functions the tables `ts` name. -/
def tableFns (ts : List (String × List FnTable)) : List String := ts.flatMap fun t => t.2.flatMap (·.fns)

theorem contract_pub {A : Abi isa} {sig : Sig} {pre : Curry (sig.words A.ptrBits) (Mem → Prop)}
    {post : sig.Post A.ptrBits} {wa : Bool} {stack : Nat}
    {leak : Option (Curry (sig.words A.ptrBits) (Mem → List Nat))} {s₁ s₂ : State}
    (h : (sig.contract A pre post wa stack leak).pub s₁ s₂) : A.pub s₁ s₂ := by
  simp only [Sig.contract] at h
  split at h
  · exact h.elim
  · cases leak with
    | none => exact h.1
    | some f => exact h.1.1

/-- The functions of the tables have the same addresses in two runs that agree on what is public. -/
theorem tables_pub_syms {A : Abi isa} {sig : Sig} {ts : List (String × List FnTable)} {pm : Bool}
    {s₁ s₂ : State} (h : ((A.withTables sig ts).withMode pm).pub s₁ s₂) :
    ∀ f ∈ tableFns ts, s₁.syms f = s₂.syms f := by
  have h' : (A.withTables sig ts).pub s₁ s₂ := by
    cases pm
    · exact h
    · exact h.1
  intro f hf
  cases ts with
  | nil => simp [tableFns] at hf
  | cons t ts => exact h'.2.1 f hf

/-- The code calls indirectly only the functions of the tables `ts`, whose
addresses two runs agree on (`tables_pub_syms`). -/
def tablesCall (c : Prog isa) (ts : List (String × List FnTable)) : Bool :=
  (UpperLock.inames c).all fun f => decide (f ∈ tableFns ts)

theorem tablesCall_syms {api : Api} {r : Registration api target} (h : tablesCall r.code r.tables = true)
    {A : Abi isa} {pre : Curry (api.sig.words A.ptrBits) (Mem → Prop)} {post : api.sig.Post A.ptrBits}
    {wa : Bool} {stack : Nat} {leak : Option (Curry (api.sig.words A.ptrBits) (Mem → List Nat))}
    (hA : A = ((abi.withConsts r.consts).withTables api.sig r.tables).withMode api.pubMode) :
    ∀ s₁ s₂, (api.sig.contract A pre post wa stack leak).pub s₁ s₂ →
      ∀ n ∈ UpperLock.inames r.code, s₁.syms n = s₂.syms n := by
  subst hA
  intro s₁ s₂ hp n hn
  have := List.all_eq_true.mp h n hn
  simp only [decide_eq_true_eq] at this
  exact tables_pub_syms (contract_pub hp) n this

/-- `r`'s code, scrubbed as `scrubRegE` does, returns without secret residue. -/
theorem scrubCodeE_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : v ≠ .evex → (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) (he : EvexReg r.code v ks r.stack)
    (hic : tablesCall r.code r.tables = true) :
    NoResidue (scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
      (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code) r.contract
      (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) := by
  obtain ⟨pre, post, leak, e⟩ := r.ofSig
  have hv := r.verified
  have hp := hpost
  have hr := hres
  rw [e] at hv hp hr ⊢
  have hrb' := hrb
  rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
  exact (Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
    (chunks_sum r.stack) hst (chunks_valid h8)
    (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun hne => MxSame.of_fun (mxFun_of (hmx hne))) hrb' hp hr (tailOk_of _ _ _) (xs_of _ _) he.1 he.2
    (gs_of _ _)).2 (tablesCall_syms hic rfl)

/-- `r`, scrubbed: its code followed by the clearing (`scrub`), at level `v`,
with the granules `ks` of `r.stack` bytes of stack wiped. -/
def scrubRegE {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : v ≠ .evex → (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) (he : EvexReg r.code v ks r.stack)
    (hw : r.written = []) : Registration api target where
  suffix := r.suffix
  consts := r.consts
  tables := r.tables
  stack := r.stack
  code := scrub v (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)
    (xsOf r.code ks) (psOf ks) (gsOf Taint.clobbers r.code) ks (chunks r.stack) r.code
  contract := r.contract
  verified := by
    obtain ⟨pre, post, leak, e⟩ := r.ofSig
    have hv := r.verified
    have hp := hpost
    have hr := hres
    rw [e] at hv hp hr ⊢
    have hrb' := hrb
    rw [← withMode_ptrBits ((abi.withConsts r.consts).withTables api.sig r.tables) api.pubMode] at hrb' hp ⊢
    exact (Verified.scrubM (ScrubAbi.of r.consts api.sig r.tables api.pubMode) hv (SpSafe.of_all r.spSafe) hd
      (chunks_sum r.stack) hst (chunks_valid h8)
      (fun i hi => by simpa using Code.all_instrs hlv i hi) (fun hne => MxSame.of_fun (mxFun_of (hmx hne))) hrb' hp hr (tailOk_of _ _ _) (xs_of _ _) he.1 he.2
      (gs_of _ _)).1
  ofApi := r.ofApi
  ofSig := r.ofSig
  spSafe := scrub_spSafe v _ _ _ _ _ _ (tailOk_of 0 r.code ks).psOk (tailOk_of 0 r.code ks).gsOk r.spSafe
  written := r.written
  writtenOk := by
    rw [hw]; exact fun _ _ _ _ _ => True.intro
  extra := r.extra
  vendor := r.vendor
  notWith := r.notWith
  -- Without residue for code that calls indirectly only its tables' functions,
  -- whose two runs use the same unknowns (`Exec.unknowns_agree`); the emitter
  -- refuses any other.
  residue := if hic : tablesCall r.code r.tables = true then
    some ⟨scrubCodeE_noResidue r v ks hd hst h8 hlv hmx hrb hpost hres he hic⟩ else none

/-- `Code.all p` implies `Code.all q` if `p` implies `q`. -/
theorem all_mono {p q : Instr → Bool} (hpq : ∀ i, p i = true → q i = true) {c : Prog isa}
    (h : c.all p = true) : c.all q = true := by
  induction c <;> simp_all [Code.all, List.all_eq_true]

/-- Code of `vecLevel` at most `v.level` is of `vecLevelR` at most `v.level`. -/
theorem allR_of_all {c : Prog isa} {v : VecLevel} (h : c.all (fun i => decide (i.vecLevel ≤ v.level)) = true) :
    c.all (fun i => decide (i.vecLevelR ≤ v.level)) = true :=
  all_mono (fun i hi => by simp only [decide_eq_true_eq] at hi ⊢; exact Nat.le_trans (vecLevelR_le i) hi) h

/-- Code of `vecLevel` at most `v.level`, below the level `evex`, never loads MXCSR. -/
theorem mxOk_of_all {c : Prog isa} {v : VecLevel} (h : c.all (fun i => decide (i.vecLevel ≤ v.level)) = true) :
    v ≠ .evex → (mxClass c).isSome = true := fun hne => by
  have h1 : c.all (fun i => decide (i.vecLevel ≤ 1)) = true := all_mono (fun i hi => by
    simp only [decide_eq_true_eq] at hi ⊢
    cases v
    · simp only [VecLevel.level] at hi; omega_using [hi]
    · exact hi
    · exact absurd rfl hne) h
  rw [mxClass_of_noLoad (all_mono (fun i hi => by
    simp only [decide_eq_true_eq] at hi; simp [noLoad_of_vecLevel hi]) h1)]
  rfl

/-- `scrubRegE`, below the level `evex`, for code that may load MXCSR if it
leaves in it a function of MXCSR on entry (`mxClass`). -/
def scrubRegM {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevelR ≤ v.level)) = true)
    (hmx : (mxClass r.code).isSome = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hw : r.written = []) (hne : v ≠ .evex) : Registration api target :=
  scrubRegE r v ks hd hst h8 hlv (fun _ => hmx) hrb hpost hres (evexReg_of_ne hne) hw

/-- `scrubRegE`, below the level `evex`. -/
def scrubReg {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack))
    (hw : r.written = []) (hne : v ≠ .evex := by decide) : Registration api target :=
  scrubRegE r v ks hd hst h8 (allR_of_all hlv) (mxOk_of_all hlv) hrb hpost hres (evexReg_of_ne hne) hw

theorem scrubReg_noResidue {api : Api} (r : Registration api target) (v : VecLevel) (ks : List Nat)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hres : ResOk r.code r.contract r.stack ks (chunks r.stack)) (hw : r.written = [])
    (hne : v ≠ .evex := by decide) (hic : tablesCall r.code r.tables = true) :
    NoResidue (scrubReg r v ks hd hst h8 hlv hrb hpost hres hw hne).code r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits) :=
  scrubCodeE_noResidue r v ks hd hst h8 (allR_of_all hlv) (mxOk_of_all hlv) hrb hpost hres (evexReg_of_ne hne) hic

/-- `r`, scrubbed with every granule of its stack wiped: for code the
residue analysis does not follow. At the level `evex` (code that may write
`zmm16`–`zmm31` or MXCSR), it has 16 bytes of stack and writes a vector
register. -/
def scrubRegAll {api : Api} (r : Registration api target) (v : VecLevel)
    (hd : r.code.x86_64Depth ≤ r.stack) (hst : r.stack + 8 < 2 ^ 64) (h8 : r.stack % 8 = 0)
    (hlv : r.code.all (fun i => decide (i.vecLevel ≤ v.level)) = true)
    (hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨ api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits))
    (hev : v = .evex → 16 ≤ r.stack ∧ r.code.all (fun i => !writesVec i) = false)
    (hw : r.written = []) : Registration api target :=
  scrubRegE r v (allKs (chunks r.stack)) hd hst h8 (allR_of_all hlv) (mxOk_of_all hlv) hrb hpost (resOk_all _ _ h8)
    (evexReg_all h8 hst hev) hw

/-- The level `scrub` clears the vector registers at for `code`, the lowest
that covers its instructions. -/
def levelAll (code : Prog isa) : VecLevel :=
  if levelLeOnce VecLevel.sse.level code then .sse
  else if levelLeOnce VecLevel.avx.level code then .avx else .evex

/-- `r`, returning without secret residue with every granule of its stack
wiped (`scrubRegAll`), at the level of its code, if `scrub`'s side conditions
hold and the clearing needs no CPU feature that `r`'s code does not
(`Code.requiresDedup`); otherwise `r` itself, which then has no proof
(`Registration.residue`), as the emitter allows only of what
`ci/residue_allowlist.txt` lists. For a caller generic over the
implementations of the functions it calls, whose code the residue analysis
does not follow. The level is that of every instruction the code may run,
those of the functions of the tables it takes included (`Code.all`), whose
features are not the code's own: a function that needs no AVX but may run
an AVX2 hash function through a table is left as it is. -/
def withScrubAll {api : Api} (r : Registration api target)
    (hpost : PostOut r.contract (api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits)) :
    Registration api target :=
  let v := levelAll r.code
  if hd : r.code.x86_64Depth ≤ r.stack then
  if hst : r.stack + 8 < 2 ^ 64 then
  if h8 : r.stack % 8 = 0 then
  if hlv : levelLeOnce v.level r.code = true then
  if hrb : api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits ≤ 32 ∨
      api.sig.retBits ((abi.withConsts r.consts).withTables api.sig r.tables).ptrBits = 64 then
  if hw : r.written = [] then
  if hev : v = .evex → 16 ≤ r.stack ∧ noVec r.code = false then
    let r' := scrubRegAll r v hd hst h8 ((Code.allOnce_eq _ r.code).symm.trans hlv) hrb hpost hev hw
    if (Code.requiresDedup isa.requires r'.code).all
        (fun f => (Code.requiresDedup isa.requires r.code).contains f) then r' else r
  else r else r else r else r else r else r else r

end VG.X86_64.Scrub
