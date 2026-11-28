module

public import VerifiedGarbage.Proof.Framework.Mem
public import VerifiedGarbage.TCB.X86_64.State
import VerifiedGarbage.Proof.Framework.Omega

/-!
# The masked 512-bit moves

A masked store (`State.storeMasked512`, of quadwords, or
`State.storeMasked512B`, of bytes) writes only within its 64 bytes, so its
memory is a write of 64 bytes at its address: what the analyses and frames
know of a store of 64 bytes holds for it too.
-/

@[expose] public section

namespace VG.X86_64

/-- A memory that differs from `m` only in the `n` bytes at `a` is `m` with
those bytes written. -/
theorem Mem.eq_write_read {m m' : Mem} {a : Addr} {n : Nat}
    (h : ∀ x, n ≤ (x - a).toNat → m' x = m x) : m' = m.write a n (m'.read a n) := by
  funext x
  simp only [Mem.write]
  split
  · rename_i hx
    rw [Mem.extractLsb'_read _ _ hx, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_comm,
      BitVec.sub_add_cancel]
  · exact h x (by omega_arith)

/-- Writes of quadwords `j < 8` of the 64 bytes at `a` change no byte
outside them. -/
theorem foldl_qwrites {a : Addr} (f : Nat → BitVec 64) :
    ∀ (l : List Nat), (∀ j ∈ l, j < 8) → ∀ (m : Mem) x, 64 ≤ (x - a).toNat →
      l.foldl (fun m j => m.writeW (State.qAddr a j) (f j)) m x = m x
  | [], _, _, _, _ => rfl
  | j :: l, hl, m, x, hx => by
    simp only [List.foldl_cons]
    rw [foldl_qwrites f l (fun j h => hl j (List.mem_cons_of_mem _ h)) _ x hx]
    have hj := hl j List.mem_cons_self
    simp only [Mem.writeW, Mem.write]
    by_cases h : (x - State.qAddr a j).toNat < 64 / 8
    · exfalso
      have e : x - a = (x - State.qAddr a j) + BitVec.ofNat 64 (8 * j) := by
        simp only [State.qAddr]; bv_omega
      rw [e, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
      have : 8 * j % 2 ^ 64 = 8 * j := Nat.mod_eq_of_lt (by omega_using [hj])
      rw [this, Nat.mod_eq_of_lt (by omega_using [hx, hj])] at hx
      omega_using [hx, hj, h]
    · simp only [h, ↓reduceIte]

theorem qOn_lt (k : BitVec 64) : ∀ j ∈ State.qOn k, j < 8 := fun _ h =>
  List.mem_range.mp (List.mem_filter.mp h).1

/-- A masked store is a write of the 64 bytes at its address. -/
theorem State.storeMasked512_eq {s s' : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (h : s.storeMasked512 a k v = some s') : ∃ V, s' = { s with mem := s.mem.write a 64 V } := by
  simp only [State.storeMasked512] at h
  split at h
  · cases h
    exact ⟨_, congrArg (fun m => { s with mem := m })
      (Mem.eq_write_read fun x hx => foldl_qwrites _ _ (qOn_lt k) _ x hx)⟩
  · cases h

/-- Writes of quadwords each within one of `rs` change memory only within them. -/
theorem foldl_qwrites_frame {rs : List Region} {a : Addr} (f : Nat → BitVec 64) :
    ∀ (l : List Nat), (∀ j ∈ l, InRegions rs (State.qAddr a j) 8) → ∀ {m₀ m : Mem}, Frame rs m₀ m →
      Frame rs m₀ (l.foldl (fun m j => m.writeW (State.qAddr a j) (f j)) m)
  | [], _, _, _, h => h
  | j :: l, hl, _, _, h => by
    obtain ⟨r, hr, hc⟩ := hl j List.mem_cons_self
    exact foldl_qwrites_frame f l (fun j h => hl j (List.mem_cons_of_mem _ h)) (h.writeW hr _ hc)

/-- A masked store writes only within the writable regions. -/
theorem State.storeMasked512_frame {s s' : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (h : s.storeMasked512 a k v = some s') : Frame s.wr s.mem s'.mem := by
  simp only [State.storeMasked512] at h
  split at h
  · rename_i hi; cases h
    exact foldl_qwrites_frame _ _ hi (Frame.refl _ _)
  · cases h

/-- A masked load from states with the same memory, the second permitting
at least what the first does. -/
theorem State.loadMasked512_mono {s t : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (hc : ∀ a n, InRegions (s.rd ++ s.wr) a n → InRegions (t.rd ++ t.wr) a n) (hm : t.mem = s.mem)
    (h : s.loadMasked512 a k = some v) : t.loadMasked512 a k = some v := by
  simp only [State.loadMasked512] at h ⊢
  split at h
  · rename_i hi
    split
    · rw [hm]; exact h
    · rename_i hn; exact absurd (fun j hj => hc _ _ (hi j hj)) hn
  · cases h

/-- A masked store from states with the same memory, the second permitting
at least the writes the first does. -/
theorem State.storeMasked512_mono {s s' t : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (hc : ∀ a n, InRegions s.wr a n → InRegions t.wr a n) (hm : t.mem = s.mem)
    (h : s.storeMasked512 a k v = some s') : t.storeMasked512 a k v = some { t with mem := s'.mem } := by
  simp only [State.storeMasked512] at h ⊢
  split at h
  · rename_i hi; cases h
    split
    · rw [hm]
    · rename_i hn; exact absurd (fun j hj => hc _ _ (hi j hj)) hn
  · cases h

/-- Writes of bytes `j < 64` of the 64 bytes at `a` change no byte outside
them. -/
theorem foldl_bwrites {a : Addr} (f : Nat → BitVec 8) :
    ∀ (l : List Nat), (∀ j ∈ l, j < 64) → ∀ (m : Mem) x, 64 ≤ (x - a).toNat →
      l.foldl (fun m j => m.writeW (a + BitVec.ofNat 64 j) (f j)) m x = m x
  | [], _, _, _, _ => rfl
  | j :: l, hl, m, x, hx => by
    simp only [List.foldl_cons]
    rw [foldl_bwrites f l (fun j h => hl j (List.mem_cons_of_mem _ h)) _ x hx]
    have hj := hl j List.mem_cons_self
    simp only [Mem.writeW, Mem.write]
    by_cases h : (x - (a + BitVec.ofNat 64 j)).toNat < 8 / 8
    · exfalso
      have e : x - a = (x - (a + BitVec.ofNat 64 j)) + BitVec.ofNat 64 j := by bv_omega
      rw [e, BitVec.toNat_add, BitVec.toNat_ofNat] at hx
      have : j % 2 ^ 64 = j := Nat.mod_eq_of_lt (by omega_using [hj])
      rw [this, Nat.mod_eq_of_lt (by omega_using [hx, hj])] at hx
      omega_using [hx, hj, h]
    · simp only [h, ↓reduceIte]

theorem bOn_lt (k : BitVec 64) : ∀ j ∈ State.bOn k, j < 64 := fun _ h =>
  List.mem_range.mp (List.mem_filter.mp h).1

/-- A byte-masked store is a write of the 64 bytes at its address. -/
theorem State.storeMasked512B_eq {s s' : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (h : s.storeMasked512B a k v = some s') : ∃ V, s' = { s with mem := s.mem.write a 64 V } := by
  simp only [State.storeMasked512B] at h
  split at h
  · cases h
    exact ⟨_, congrArg (fun m => { s with mem := m })
      (Mem.eq_write_read fun x hx => foldl_bwrites _ _ (bOn_lt k) _ x hx)⟩
  · cases h

/-- Writes of bytes each within one of `rs` change memory only within them. -/
theorem foldl_bwrites_frame {rs : List Region} {a : Addr} (f : Nat → BitVec 8) :
    ∀ (l : List Nat), (∀ j ∈ l, InRegions rs (a + BitVec.ofNat 64 j) 1) → ∀ {m₀ m : Mem}, Frame rs m₀ m →
      Frame rs m₀ (l.foldl (fun m j => m.writeW (a + BitVec.ofNat 64 j) (f j)) m)
  | [], _, _, _, h => h
  | j :: l, hl, _, _, h => by
    obtain ⟨r, hr, hc⟩ := hl j List.mem_cons_self
    exact foldl_bwrites_frame f l (fun j h => hl j (List.mem_cons_of_mem _ h)) (h.writeW hr _ hc)

/-- A byte-masked store writes only within the writable regions. -/
theorem State.storeMasked512B_frame {s s' : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (h : s.storeMasked512B a k v = some s') : Frame s.wr s.mem s'.mem := by
  simp only [State.storeMasked512B] at h
  split at h
  · rename_i hi; cases h
    exact foldl_bwrites_frame _ _ hi (Frame.refl _ _)
  · cases h

/-- A byte-masked load from states with the same memory, the second
permitting at least what the first does. -/
theorem State.loadMasked512B_mono {s t : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (hc : ∀ a n, InRegions (s.rd ++ s.wr) a n → InRegions (t.rd ++ t.wr) a n) (hm : t.mem = s.mem)
    (h : s.loadMasked512B a k = some v) : t.loadMasked512B a k = some v := by
  simp only [State.loadMasked512B] at h ⊢
  split at h
  · rename_i hi
    split
    · rw [hm]; exact h
    · rename_i hn; exact absurd (fun j hj => hc _ _ (hi j hj)) hn
  · cases h

/-- A byte-masked store from states with the same memory, the second
permitting at least the writes the first does. -/
theorem State.storeMasked512B_mono {s s' t : State} {a : Addr} {k : BitVec 64} {v : BitVec 512}
    (hc : ∀ a n, InRegions s.wr a n → InRegions t.wr a n) (hm : t.mem = s.mem)
    (h : s.storeMasked512B a k v = some s') : t.storeMasked512B a k v = some { t with mem := s'.mem } := by
  simp only [State.storeMasked512B] at h ⊢
  split at h
  · rename_i hi; cases h
    split
    · rw [hm]
    · rename_i hn; exact absurd (fun j hj => hc _ _ (hi j hj)) hn
  · cases h

end VG.X86_64
