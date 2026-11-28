module

import VerifiedGarbage.Proof.Framework.X86_64.Inline
public import VerifiedGarbage.Proof.Framework.Contract
public import VerifiedGarbage.Proof.Framework.X86_64.Taint
public import VerifiedGarbage.TCB.X86_64.Target

/-!
# Calls as inlined code (x86-64)

A call (`Code.call`) of code that uses no stack of its own runs as that code
inlined would, but for the return address the call stores below `rsp`.
`Code.inline c` is `c` with each call replaced by the code it calls. Code
whose proofs say that memory changes only where they name (and nothing of
the 8 bytes below `rsp`, which no buffer overlaps) is proved for its
inlined form; this file moves the proof to `c`:

* a run of `c.inline` from `s` gives a run of `c` from `s`, whose final
  state is that of `c.inline` but for the 8 bytes below `rsp` and the
  unknowns the calls consume (`State.patch`, `run_of_inline`);
* the run's leakage is a function of the inlined run's (`liftT`), so `c` is
  constant time if `c.inline` is (`ct_of_inline`).

It requires of `c` (`Code.InlineOk`) that no instruction outside its calls
writes `rsp`, that it has no frames, and that each function it calls calls
none and uses only instructions that neither read nor write `rsp`
(`Instr.rspFree`): inside a call, `rsp` is 8 lower than in the inlined
run, and nothing else differs.
-/

@[expose] public section

namespace VG

/-- `c` with each call replaced by the code it calls. -/
def Code.inline {I C : Type} : Code I C → Code I C
  | .block l => .block l
  | .seq a b => .seq a.inline b.inline
  | .ite c t e => .ite c t.inline e.inline
  | .loop b c => .loop b.inline c
  | .call _ b => b
  | .frame i b j => .frame i b.inline j
  | .icall i n b nx => .icall i n b nx

end VG

namespace VG.X86_64

/-! ## Memory with a hole -/

/-- `m`, but the bytes of `H` from `hv`. -/
def overlay (H : Region) (hv m : Mem) : Mem := fun x => if H.Contains x 1 then hv x else m x

/-- `s`, but the bytes of `H` from `hv`, and the unknowns `u`. -/
def State.patch (H : Region) (hv : Mem) (u : Nat → BitVec 64) (s : State) : State :=
  { s with mem := overlay H hv s.mem, unknowns := u }

/-- No region `s` may access overlaps `H`. -/
def Clear (H : Region) (s : State) : Prop := ∀ r ∈ s.rd ++ s.wr, r.Disjoint H

theorem overlay_self (H : Region) (m : Mem) : overlay H m m = m := by
  funext x; simp only [overlay]; split <;> rfl

theorem State.patch_self (H : Region) (s : State) : s.patch H s.mem s.unknowns = s := by
  simp only [State.patch, overlay_self]

/-- An access within the regions of `s` misses `H`. -/
theorem Clear.miss {H : Region} {s : State} (hc : Clear H s) {rs : List Region} (hrs : ∀ r ∈ rs, r ∈ s.rd ++ s.wr)
    {a : Addr} {n : Nat} (h : InRegions rs a n) {x : Addr} (hx : (x - a).toNat < n) : ¬ H.Contains x 1 := by
  obtain ⟨r, hr, hc'⟩ := h
  exact hc r (hrs r hr) x (hc'.byte hx)

theorem overlay_read {H : Region} {hv m : Mem} {a : Addr} {n : Nat} (hn : n < 2 ^ 64)
    (h : ∀ x, (x - a).toNat < n → ¬ H.Contains x 1) : (overlay H hv m).read a n = m.read a n :=
  Mem.read_congr fun i hi => by
    have := h (a + BitVec.ofNat 64 i) (by rw [Mem.sub_ofNat_toNat a (by omega_arith)]; exact hi)
    simp only [overlay, this, ite_false]

theorem overlay_readW {H : Region} {hv m : Mem} {a : Addr} {w : Nat} (hn : w / 8 < 2 ^ 64)
    (h : ∀ x, (x - a).toNat < w / 8 → ¬ H.Contains x 1) : (overlay H hv m).readW a w = m.readW a w := by
  simp only [Mem.readW, overlay_read hn h]

theorem overlay_write {H : Region} {hv m : Mem} {a : Addr} {n : Nat} {v : BitVec (8 * n)}
    (h : ∀ x, (x - a).toNat < n → ¬ H.Contains x 1) :
    (overlay H hv m).write a n v = overlay H hv (m.write a n v) := by
  funext x
  simp only [Mem.write, overlay]
  by_cases hx : (x - a).toNat < n
  · simp only [hx, ite_true, h x hx, ite_false]
  · simp only [hx, ite_false]

theorem overlay_writeW {H : Region} {hv m : Mem} {a : Addr} {w : Nat} {v : BitVec w}
    (h : ∀ x, (x - a).toNat < w / 8 → ¬ H.Contains x 1) :
    (overlay H hv m).writeW a v = overlay H hv (m.writeW a v) := by
  simp only [Mem.writeW, overlay_write h]

section
variable {H : Region} {hv : Mem} {u : Nat → BitVec 64} {s : State}

theorem load64_patch (hc : Clear H s) (a : Addr) : (s.patch H hv u).load64 a = s.load64 a := by
  simp only [State.load64, State.patch]
  by_cases hi : InRegions (s.rd ++ s.wr) a 8 <;> simp only [hi, ite_true, ite_false]
  rw [overlay_readW (by decide) fun x hx => hc.miss (fun _ h => h) hi hx]

theorem load32_patch (hc : Clear H s) (a : Addr) : (s.patch H hv u).load32 a = s.load32 a := by
  simp only [State.load32, State.patch]
  by_cases hi : InRegions (s.rd ++ s.wr) a 4 <;> simp only [hi, ite_true, ite_false]
  rw [overlay_readW (by decide) fun x hx => hc.miss (fun _ h => h) hi hx]

theorem load8_patch (hc : Clear H s) (a : Addr) : (s.patch H hv u).load8 a = s.load8 a := by
  simp only [State.load8, State.patch]
  by_cases hi : InRegions (s.rd ++ s.wr) a 1 <;> simp only [hi, ite_true, ite_false]
  have := hc.miss (fun _ h => h) hi (x := a) (by simp)
  simp only [overlay, this, ite_false]

theorem load16_patch (hc : Clear H s) (a : Addr) : (s.patch H hv u).load16 a = s.load16 a := by
  simp only [State.load16, State.patch]
  by_cases hi : InRegions (s.rd ++ s.wr) a 2 <;> simp only [hi, ite_true, ite_false]
  rw [overlay_readW (by decide) fun x hx => hc.miss (fun _ h => h) hi hx]

theorem load128_patch (hc : Clear H s) (a : Addr) : (s.patch H hv u).load128 a = s.load128 a := by
  simp only [State.load128, State.patch]
  by_cases hi : InRegions (s.rd ++ s.wr) a 16 <;> simp only [hi, ite_true, ite_false]
  rw [overlay_readW (by decide) fun x hx => hc.miss (fun _ h => h) hi hx]

theorem load256_patch (hc : Clear H s) (a : Addr) : (s.patch H hv u).load256 a = s.load256 a := by
  simp only [State.load256, State.patch]
  by_cases hi : InRegions (s.rd ++ s.wr) a 32 <;> simp only [hi, ite_true, ite_false]
  rw [overlay_readW (by decide) fun x hx => hc.miss (fun _ h => h) hi hx]

theorem load512_patch (hc : Clear H s) (a : Addr) : (s.patch H hv u).load512 a = s.load512 a := by
  simp only [State.load512, State.patch]
  by_cases hi : InRegions (s.rd ++ s.wr) a 64 <;> simp only [hi, ite_true, ite_false]
  rw [overlay_readW (by decide) fun x hx => hc.miss (fun _ h => h) hi hx]

theorem wr_mem {s : State} : ∀ r ∈ s.wr, r ∈ s.rd ++ s.wr := fun _ h => List.mem_append_right _ h

theorem store64_patch (hc : Clear H s) (a : Addr) (v : BitVec 64) :
    (s.patch H hv u).store64 a v = (s.store64 a v).map (State.patch H hv u) := by
  simp only [State.store64, State.patch]
  by_cases hi : InRegions s.wr a 8 <;> simp only [hi, ite_true, ite_false, Option.map_some, Option.map_none]
  rw [overlay_writeW fun x hx => hc.miss wr_mem hi hx]; rfl

theorem store32_patch (hc : Clear H s) (a : Addr) (v : BitVec 32) :
    (s.patch H hv u).store32 a v = (s.store32 a v).map (State.patch H hv u) := by
  simp only [State.store32, State.patch]
  by_cases hi : InRegions s.wr a 4 <;> simp only [hi, ite_true, ite_false, Option.map_some, Option.map_none]
  rw [overlay_writeW fun x hx => hc.miss wr_mem hi hx]; rfl

theorem store8_patch (hc : Clear H s) (a : Addr) (v : Byte) :
    (s.patch H hv u).store8 a v = (s.store8 a v).map (State.patch H hv u) := by
  simp only [State.store8, State.patch]
  by_cases hi : InRegions s.wr a 1 <;> simp only [hi, ite_true, ite_false, Option.map_some, Option.map_none]
  rw [overlay_writeW fun x hx => hc.miss wr_mem hi hx]; rfl

theorem store16_patch (hc : Clear H s) (a : Addr) (v : BitVec 16) :
    (s.patch H hv u).store16 a v = (s.store16 a v).map (State.patch H hv u) := by
  simp only [State.store16, State.patch]
  by_cases hi : InRegions s.wr a 2 <;> simp only [hi, ite_true, ite_false, Option.map_some, Option.map_none]
  rw [overlay_writeW fun x hx => hc.miss wr_mem hi hx]; rfl

theorem store128_patch (hc : Clear H s) (a : Addr) (v : BitVec 128) :
    (s.patch H hv u).store128 a v = (s.store128 a v).map (State.patch H hv u) := by
  simp only [State.store128, State.patch]
  by_cases hi : InRegions s.wr a 16 <;> simp only [hi, ite_true, ite_false, Option.map_some, Option.map_none]
  rw [overlay_writeW fun x hx => hc.miss wr_mem hi hx]; rfl

theorem store256_patch (hc : Clear H s) (a : Addr) (v : BitVec 256) :
    (s.patch H hv u).store256 a v = (s.store256 a v).map (State.patch H hv u) := by
  simp only [State.store256, State.patch]
  by_cases hi : InRegions s.wr a 32 <;> simp only [hi, ite_true, ite_false, Option.map_some, Option.map_none]
  rw [overlay_writeW fun x hx => hc.miss wr_mem hi hx]; rfl

theorem store512_patch (hc : Clear H s) (a : Addr) (v : BitVec 512) :
    (s.patch H hv u).store512 a v = (s.store512 a v).map (State.patch H hv u) := by
  simp only [State.store512, State.patch]
  by_cases hi : InRegions s.wr a 64 <;> simp only [hi, ite_true, ite_false, Option.map_some, Option.map_none]
  rw [overlay_writeW fun x hx => hc.miss wr_mem hi hx]; rfl

theorem loadMasked512_patch (hc : Clear H s) (a : Addr) (k : BitVec 64) :
    (s.patch H hv u).loadMasked512 a k = s.loadMasked512 a k := by
  simp only [State.loadMasked512, State.patch]
  by_cases hi : ∀ j ∈ State.qOn k, InRegions (s.rd ++ s.wr) (State.qAddr a j) 8
  · -- Not `cases` on the bit and `rfl`: on a clear bit, `rfl` first tries to
    -- unify the two reads, unfolding them.
    have hq : ∀ j, j < 8 →
        (if k.getLsbD j then (overlay H hv s.mem).readW (State.qAddr a j) 64 else 0) =
          (if k.getLsbD j then s.mem.readW (State.qAddr a j) 64 else 0) := fun j hj =>
      ite_congr rfl (fun hk => overlay_readW (by decide) fun _ hx =>
        hc.miss (fun _ h => h) (hi j (List.mem_filter.mpr ⟨List.mem_range.mpr hj, hk⟩)) hx) fun _ => rfl
    simp only [hq 0 (by decide), hq 1 (by decide), hq 2 (by decide), hq 3 (by decide),
      hq 4 (by decide), hq 5 (by decide), hq 6 (by decide), hq 7 (by decide)]
  · simp only [hi, ↓reduceIte]

theorem foldl_qwrites_patch (hc : Clear H s) {a : Addr} (f : Nat → BitVec 64) :
    ∀ (l : List Nat), (∀ j ∈ l, InRegions s.wr (State.qAddr a j) 8) → ∀ m : Mem,
      l.foldl (fun m j => m.writeW (State.qAddr a j) (f j)) (overlay H hv m) =
        overlay H hv (l.foldl (fun m j => m.writeW (State.qAddr a j) (f j)) m)
  | [], _, _ => rfl
  | j :: l, hl, m => by
    simp only [List.foldl_cons]
    rw [overlay_writeW fun x hx => hc.miss wr_mem (hl j List.mem_cons_self) hx]
    exact foldl_qwrites_patch hc f l (fun j h => hl j (List.mem_cons_of_mem _ h)) _

theorem storeMasked512_patch (hc : Clear H s) (a : Addr) (k : BitVec 64) (v : BitVec 512) :
    (s.patch H hv u).storeMasked512 a k v = (s.storeMasked512 a k v).map (State.patch H hv u) := by
  unfold State.storeMasked512
  rw [show (s.patch H hv u).wr = s.wr from rfl]
  by_cases hi : ∀ j ∈ State.qOn k, InRegions s.wr (State.qAddr a j) 8
  · rw [ite_eq_left hi, ite_eq_left hi, Option.map_some]
    simp only [State.patch]
    rw [foldl_qwrites_patch hc _ _ hi]
  · rw [ite_eq_right hi, ite_eq_right hi]; rfl

theorem loadMasked512B_patch (hc : Clear H s) (a : Addr) (k : BitVec 64) :
    (s.patch H hv u).loadMasked512B a k = s.loadMasked512B a k := by
  unfold State.loadMasked512B
  rw [show (s.patch H hv u).rd = s.rd from rfl, show (s.patch H hv u).wr = s.wr from rfl]
  by_cases hi : ∀ j ∈ State.bOn k, InRegions (s.rd ++ s.wr) (a + BitVec.ofNat 64 j) 1
  · rw [ite_eq_left hi, ite_eq_left hi]
    refine congrArg some (Mem.readW_congr fun j hj => ?_)
    rw [Mem.sub_ofNat_toNat a (by omega_arith)]
    by_cases hk : k.getLsbD j
    · simp only [hk, ite_true, State.patch, overlay]
      rw [ite_eq_right (hc.miss (fun _ h => h) (hi j (List.mem_filter.mpr ⟨List.mem_range.mpr (by omega_arith), hk⟩))
        (show (a + BitVec.ofNat 64 j - (a + BitVec.ofNat 64 j)).toNat < 1 by simp))]
    · simp only [hk, Bool.false_eq_true, ↓reduceIte]
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem foldl_bwrites_patch (hc : Clear H s) {a : Addr} (f : Nat → BitVec 8) :
    ∀ (l : List Nat), (∀ j ∈ l, InRegions s.wr (a + BitVec.ofNat 64 j) 1) → ∀ m : Mem,
      l.foldl (fun m j => m.writeW (a + BitVec.ofNat 64 j) (f j)) (overlay H hv m) =
        overlay H hv (l.foldl (fun m j => m.writeW (a + BitVec.ofNat 64 j) (f j)) m)
  | [], _, _ => rfl
  | j :: l, hl, m => by
    simp only [List.foldl_cons]
    rw [overlay_writeW fun x hx => hc.miss wr_mem (hl j List.mem_cons_self) hx]
    exact foldl_bwrites_patch hc f l (fun j h => hl j (List.mem_cons_of_mem _ h)) _

theorem storeMasked512B_patch (hc : Clear H s) (a : Addr) (k : BitVec 64) (v : BitVec 512) :
    (s.patch H hv u).storeMasked512B a k v = (s.storeMasked512B a k v).map (State.patch H hv u) := by
  unfold State.storeMasked512B
  rw [show (s.patch H hv u).wr = s.wr from rfl]
  by_cases hi : ∀ j ∈ State.bOn k, InRegions s.wr (a + BitVec.ofNat 64 j) 1
  · rw [ite_eq_left hi, ite_eq_left hi, Option.map_some]
    simp only [State.patch]
    rw [foldl_bwrites_patch hc _ _ hi]
  · rw [ite_eq_right hi, ite_eq_right hi]; rfl

theorem readSrc_patch (hc : Clear H s) (src : Src) : readSrc (s.patch H hv u) src = readSrc s src := by
  cases src with
  | mem m => exact load64_patch hc _
  | _ => rfl

theorem readSrc32_patch (hc : Clear H s) (src : Src) : readSrc32 (s.patch H hv u) src = readSrc32 s src := by
  cases src with
  | mem m => exact load32_patch hc _
  | _ => rfl


theorem eval_patch (c : Cond) : eval c (s.patch H hv u) = eval c s := by cases c <;> rfl

theorem bind_map_patch {α : Type} (o : Option α) (f : α → Option State) :
    (o.bind f).map (State.patch H hv u) = o.bind fun a => (f a).map (State.patch H hv u) := by
  cases o <;> rfl

/-- An instruction runs from `s` with the bytes of `H` (outside its regions)
and the unknowns changed as from `s`, and changes neither. -/
theorem exec_patch (hc : Clear H s) (i : Instr) :
    exec i (s.patch H hv u) = (exec i s).map (State.patch H hv u) := by
  cases i with
  | mov d src => simp only [exec, readSrc_patch hc, Option.map_map]; rfl
  | mov32 d src => simp only [exec, readSrc32_patch hc, Option.map_map]; rfl
  | movzx8 d m => simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load8_patch hc]; rfl
  | movzx16 d m => simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load16_patch hc]; rfl
  | store m r => exact store64_patch hc _ _
  | store32 m r => exact store32_patch hc _ _
  | store8 m r => exact store8_patch hc _ _
  | store16 m r => exact store16_patch hc _ _
  | alu op d src =>
    simp only [exec, execAlu, readSrc_patch hc, bind_map_patch]
    congr 1; funext b; cases op <;> simp only [Option.map_some, Option.map_map] <;> rfl
  | alu32 op d src =>
    simp only [exec, execAlu32, readSrc32_patch hc, bind_map_patch]
    congr 1; funext b; cases op <;> simp only [Option.map_some, Option.map_map] <;> rfl
  | shift32 op d n => simp only [exec, execShift32]; split <;> [cases op <;> rfl; rfl]
  | shift op d n => simp only [exec, execShift]; split <;> [cases op <;> rfl; rfl]
  | shld d r n => simp only [exec, execShld]; split <;> rfl
  | btr d n => simp only [exec, execBtr]; split <;> rfl
  | rorx32 d r n => simp only [exec, execRorx32]; split <;> rfl
  | rorx d r n => simp only [exec, execRorx]; split <;> rfl
  | movdquLoad d m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load128_patch hc]; rfl
  | movdquStore m r => exact store128_patch hc _ _
  | xop op => simp only [exec, Option.map_some]; congr 1; cases op <;> rfl
  | vop op => simp only [exec, Option.map_some]; congr 1; cases op <;> simp only [VOp.exec] <;> (try split) <;> rfl
  | vmovdquLoad len d m =>
    cases len <;> simp only [exec, Option.map_map] <;>
      rw [show (s.patch H hv u).ea m = s.ea m from rfl] <;> simp only [load128_patch hc, load256_patch hc] <;> rfl
  | vmovdquStore len m r =>
    cases len
    · exact store128_patch hc _ _
    · exact store256_patch hc _ _
  | vbroadcasti128 d m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load128_patch hc]; rfl
  | vbinLoad op len d a m =>
    cases len <;> simp only [exec, Option.map_map] <;>
      rw [show (s.patch H hv u).ea m = s.ea m from rfl] <;> simp only [load128_patch hc, load256_patch hc] <;> rfl
  | zop op => simp only [exec, Option.map_some]; congr 1; cases op <;> rfl
  | eop op =>
    simp only [exec, Option.map_some]; congr 1
    cases op <;> simp only [EOp.exec, State.setVy] <;> (try split) <;> rfl
  | e5op op =>
    simp only [exec, Option.map_some]; congr 1
    cases op <;> simp only [E5Op.exec, State.setVz] <;> (try split) <;> rfl
  | vmovdqu32Load d m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load512_patch hc]; rfl
  | vmovdqu32Store m r => exact store512_patch hc _ _
  | vbroadcasti32x4 d m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load128_patch hc]; rfl
  | vbroadcasti32x4H d m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load128_patch hc]; rfl
  | zbcst op d a m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load64_patch hc]; rfl
  | vpbroadcastdZ d m | zbcstd _ d _ m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load32_patch hc]; rfl
  | vpmadd52Load hi d a m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load256_patch hc]; rfl
  | evLoad d m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load256_patch hc]
    congr 1; funext v; cases d <;> rfl
  | evStore m r | e5ExtractStore m r _ => exact store256_patch hc _ _
  | evBroadcastLoad d m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load64_patch hc]
    congr 1; funext v; cases d <;> rfl
  | e5InsertLoad d a m n =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load256_patch hc]
    congr 1; funext v; cases d <;> cases a <;> rfl
  | kLoad k d m =>
    simp only [exec, Option.map_map]
    rw [show (s.patch H hv u).ea m = s.ea m from rfl, show (s.patch H hv u).gpr k = s.gpr k from rfl,
      loadMasked512_patch hc]; rfl
  | kStore m k r => exact storeMasked512_patch hc _ _ _
  | kLoad8 k d m =>
    simp only [exec, Option.map_map]
    rw [show (s.patch H hv u).ea m = s.ea m from rfl, show (s.patch H hv u).gpr k = s.gpr k from rfl,
      loadMasked512B_patch hc]; rfl
  | kStore8 m k r => exact storeMasked512B_patch hc _ _ _
  | evMadd52Load hi d a m =>
    simp only [exec, Option.map_map]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load256_patch hc]
    congr 1; funext v; cases d <;> rfl
  | stmxcsr m => exact store32_patch hc _ _
  | ldmxcsr m =>
    simp only [exec]; rw [show (s.patch H hv u).ea m = s.ea m from rfl, load32_patch hc, bind_map_patch]
    congr 1; funext v; split <;> rfl
  | mulx hi lo src =>
    simp only [exec, execMulx]; cases src <;> simp only [readSrc_patch hc, Option.map_map] <;> rfl
  | adcx d src =>
    simp only [exec, execAdcx]; cases src <;> simp only [readSrc_patch hc, bind_map_patch] <;>
      first | rfl | (congr 1; funext b; simp only [Option.map_map]; rfl)
  | adox d src =>
    simp only [exec, execAdox]; cases src <;> simp only [readSrc_patch hc, bind_map_patch] <;>
      first | rfl | (congr 1; funext b; simp only [Option.map_map]; rfl)
  | cmov cc d src =>
    simp only [exec, execCmov]; cases src <;> simp only [readSrc_patch hc, bind_map_patch] <;>
      first | rfl | (congr 1; funext b; simp only [Option.map_map, Function.comp_def,
        apply_ite (State.patch H hv u), eval_patch]; rfl)
  | aluTbl op d m n ws =>
    simp only [exec]
    rw [show (s.patch H hv u).ea m = s.ea m from rfl, show (s.patch H hv u).syms = s.syms from rfl,
      show (s.patch H hv u).gpr = s.gpr from rfl]
    split
    · cases op <;> first | rfl | (simp only [execAluW, Option.map_map]; rfl)
    · rfl
  | vmovdquTbl d m n ws | movdquTbl d m n ws =>
    simp only [exec]
    rw [show (s.patch H hv u).ea m = s.ea m from rfl, show (s.patch H hv u).syms = s.syms from rfl,
      show (s.patch H hv u).gpr = s.gpr from rfl]
    split <;> rfl
  | push | pop | alloc | free | callr => rfl
  | _ => rfl

theorem addrs_patch (i : Instr) : addrs i (s.patch H hv u) = addrs i s := by
  cases i <;> rfl

end


/-! ## Code that never touches `rsp` -/

/-- A memory operand that does not use `rsp`. -/
def MemOp.noRsp (m : MemOp) : Bool := m.base != .rsp && m.index != some .rsp

/-- A source operand that does not use `rsp`. -/
def Src.noRsp : Src → Bool
  | .reg r => r != .rsp
  | .imm _ => true
  | .mem m => m.noRsp

/-- A vector operation that does not touch `rsp`: those of vector registers
alone, and `vmovq` from a register but `rsp`. -/
def VOp.rspFree : VOp → Bool
  | .vbin .. | .vmovdqa .. | .vpbroadcastd .. | .vzeroupper => true
  | .vmovq _ r => r != .rsp
  | _ => false

/-- An instruction that neither reads nor writes `rsp`: those of the
functions `Code.InlineOk` lets code call (a short list; the others are
`false`). -/
def Instr.rspFree : Instr → Bool
  | .mov d src | .mov32 d src | .alu _ d src | .alu32 _ d src | .adcx d src | .adox d src
  | .cmov _ d src => d != .rsp && src.noRsp
  | .store m r => m.noRsp && r != .rsp
  | .shift _ d _ => d != .rsp
  | .mul r => r != .rsp
  | .imul d r | .imul3 d r _ => d != .rsp && r != .rsp
  | .shld d r _ => d != .rsp && r != .rsp
  | .mulx hi lo src => hi != .rsp && lo != .rsp && src.noRsp
  | .movImm64 d _ => d != .rsp
  | .bswap d => d != .rsp
  | .xop (.movq _ r) => r != .rsp
  | .xop _ => true
  | .movqR d _ => d != .rsp
  | .movdquLoad _ m | .movdquStore m _ => m.noRsp
  | .movzx8 d m => d != .rsp && m.noRsp
  | .movzx16 d m => d != .rsp && m.noRsp
  | .store8 m r => m.noRsp && r != .rsp
  | .store16 m r => m.noRsp && r != .rsp
  | .leaSym d _ => d != .rsp
  | .vop op => op.rspFree
  | .vbinLoad _ _ _ _ m | .vmovdquStore _ m _ => m.noRsp
  | _ => false

section
variable {s : State} {x : BitVec 64}

theorem setRsp_gpr {r : Reg} (h : r ≠ .rsp) : (s.setReg .rsp x).gpr r = s.gpr r := by
  simp [State.setReg, h]

theorem setReg_setRsp {d : Reg} (h : d ≠ .rsp) (v : BitVec 64) :
    (s.setReg .rsp x).setReg d v = (s.setReg d v).setReg .rsp x := by
  simp only [State.setReg, State.mk.injEq, and_true]
  funext r; by_cases hr : r = d <;> by_cases hs : r = .rsp <;> simp_all

theorem setFlags_setRsp (a b c d : Option Bool) :
    (s.setReg .rsp x).setFlags a b c d = (s.setFlags a b c d).setReg .rsp x := rfl

theorem arithFlags_setRsp {w : Nat} (r : BitVec w) (c o : Bool) :
    arithFlags (s.setReg .rsp x) r c o = (arithFlags s r c o).setReg .rsp x := rfl

theorem ea_setRsp {m : MemOp} (h : m.noRsp = true) : (s.setReg .rsp x).ea m = s.ea m := by
  simp only [MemOp.noRsp, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  unfold State.ea
  cases hi : m.index with
  | none => simp [setRsp_gpr h.1]
  | some i =>
    have : i ≠ .rsp := fun e => h.2 (by rw [hi, e])
    simp [setRsp_gpr h.1, setRsp_gpr this]

theorem readSrc_setRsp {src : Src} (h : src.noRsp = true) : readSrc (s.setReg .rsp x) src = readSrc s src := by
  cases src with
  | reg r => simp only [Src.noRsp, bne_iff_ne, ne_eq] at h; simp [readSrc, setRsp_gpr h]
  | imm _ => rfl
  | mem m => simp only [readSrc]; rw [ea_setRsp h]; rfl

theorem readSrc32_setRsp {src : Src} (h : src.noRsp = true) :
    readSrc32 (s.setReg .rsp x) src = readSrc32 s src := by
  cases src with
  | reg r => simp only [Src.noRsp, bne_iff_ne, ne_eq] at h; simp [readSrc32, setRsp_gpr h]
  | imm _ => rfl
  | mem m => simp only [readSrc32]; rw [ea_setRsp h]; rfl

theorem store64_setRsp (a : Addr) (v : BitVec 64) :
    (s.setReg .rsp x).store64 a v = (s.store64 a v).map (·.setReg .rsp x) := by
  simp only [State.store64, show (s.setReg .rsp x).wr = s.wr from rfl]
  by_cases h : InRegions s.wr a 8 <;> simp only [h, ite_true, ite_false, Option.map_some, Option.map_none] <;> rfl

theorem store128_setRsp (a : Addr) (v : BitVec 128) :
    (s.setReg .rsp x).store128 a v = (s.store128 a v).map (·.setReg .rsp x) := by
  simp only [State.store128, show (s.setReg .rsp x).wr = s.wr from rfl]
  by_cases h : InRegions s.wr a 16 <;> simp only [h, ite_true, ite_false, Option.map_some, Option.map_none] <;> rfl

theorem store8_setRsp (a : Addr) (v : Byte) :
    (s.setReg .rsp x).store8 a v = (s.store8 a v).map (·.setReg .rsp x) := by
  simp only [State.store8, show (s.setReg .rsp x).wr = s.wr from rfl]
  by_cases h : InRegions s.wr a 1 <;> simp only [h, ite_true, ite_false, Option.map_some, Option.map_none] <;> rfl

theorem store16_setRsp (a : Addr) (v : BitVec 16) :
    (s.setReg .rsp x).store16 a v = (s.store16 a v).map (·.setReg .rsp x) := by
  simp only [State.store16, show (s.setReg .rsp x).wr = s.wr from rfl]
  by_cases h : InRegions s.wr a 2 <;> simp only [h, ite_true, ite_false, Option.map_some, Option.map_none] <;> rfl

theorem store256_setRsp (a : Addr) (v : BitVec 256) :
    (s.setReg .rsp x).store256 a v = (s.store256 a v).map (·.setReg .rsp x) := by
  simp only [State.store256, show (s.setReg .rsp x).wr = s.wr from rfl]
  by_cases h : InRegions s.wr a 32 <;> simp only [h, ite_true, ite_false, Option.map_some, Option.map_none] <;> rfl

theorem eval_setRsp (c : Cond) : eval c (s.setReg .rsp x) = eval c s := by cases c <;> rfl

theorem bind_map_setRsp {α : Type} (o : Option α) (f : α → Option State) :
    (o.bind f).map (·.setReg .rsp x) = o.bind fun a => (f a).map (·.setReg .rsp x) := by
  cases o <;> rfl

/-- An instruction that does not touch `rsp` runs from `s` with another
`rsp` as from `s`. -/
theorem exec_setRsp {i : Instr} (hi : i.rspFree = true) :
    exec i (s.setReg .rsp x) = (exec i s).map (·.setReg .rsp x) := by
  cases i with
  | mov d src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, readSrc_setRsp hi.2, Option.map_map, Function.comp_def, setReg_setRsp hi.1]
  | mov32 d src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, readSrc32_setRsp hi.2, Option.map_map, Function.comp_def, State.setReg32,
      setReg_setRsp hi.1]
  | alu op d src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execAlu, readSrc_setRsp hi.2, bind_map_setRsp, setRsp_gpr hi.1]
    congr 1; funext b
    cases op <;> simp only [Option.map_some, Option.map_map, Function.comp_def, arithFlags_setRsp,
      setReg_setRsp hi.1] <;> rfl
  | alu32 op d src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execAlu32, readSrc32_setRsp hi.2, bind_map_setRsp, setRsp_gpr hi.1]
    congr 1; funext b
    cases op <;> simp only [Option.map_some, Option.map_map, Function.comp_def, arithFlags_setRsp,
      State.setReg32, setReg_setRsp hi.1] <;> rfl
  | store m r =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, ea_setRsp hi.1, setRsp_gpr hi.2, store64_setRsp]
  | shift op d n =>
    simp only [Instr.rspFree, bne_iff_ne, ne_eq] at hi
    simp only [exec, execShift, setRsp_gpr hi]
    split
    · cases op <;> simp only [Option.map_some, setFlags_setRsp, setReg_setRsp hi] <;> rfl
    · rfl
  | mul r =>
    simp only [Instr.rspFree, bne_iff_ne, ne_eq] at hi
    simp only [exec, execMul, Option.map_some, setRsp_gpr hi, setRsp_gpr (show Reg.rax ≠ .rsp by decide),
      setFlags_setRsp, setReg_setRsp (show Reg.rax ≠ .rsp by decide),
      setReg_setRsp (show Reg.rdx ≠ .rsp by decide)]
  | imul d r =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execImul, Option.map_some, setRsp_gpr hi.1, setRsp_gpr hi.2, setFlags_setRsp,
      setReg_setRsp hi.1]
  | imul3 d r k =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execImul3, Option.map_some, setRsp_gpr hi.2, setFlags_setRsp,
      setReg_setRsp hi.1]
  | shld d r n =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execShld, setRsp_gpr hi.1, setRsp_gpr hi.2]
    split
    · simp only [Option.map_some, setFlags_setRsp, setReg_setRsp hi.1]
    · rfl
  | mulx hi' lo src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execMulx]
    cases src with
    | imm _ => rfl
    | _ => simp only [readSrc_setRsp hi.2, Option.map_map, Function.comp_def,
        setRsp_gpr (show Reg.rdx ≠ .rsp by decide), setReg_setRsp hi.1.1, setReg_setRsp hi.1.2]
  | adcx d src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execAdcx]
    cases src with
    | imm _ => rfl
    | _ =>
      simp only [readSrc_setRsp hi.2, bind_map_setRsp, setRsp_gpr hi.1]
      congr 1; funext b
      simp only [Option.map_map, Function.comp_def, setFlags_setRsp, setReg_setRsp hi.1]; rfl
  | adox d src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execAdox]
    cases src with
    | imm _ => rfl
    | _ =>
      simp only [readSrc_setRsp hi.2, bind_map_setRsp, setRsp_gpr hi.1]
      congr 1; funext b
      simp only [Option.map_map, Function.comp_def, setFlags_setRsp, setReg_setRsp hi.1]; rfl
  | cmov cc d src =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, execCmov]
    cases src with
    | imm _ => rfl
    | _ =>
      simp only [readSrc_setRsp hi.2, bind_map_setRsp, eval_setRsp]
      congr 1; funext b
      simp only [Option.map_map, Function.comp_def, apply_ite (fun t : State => t.setReg .rsp x), setReg_setRsp hi.1]
  | movImm64 d v =>
    simp only [Instr.rspFree, bne_iff_ne, ne_eq] at hi
    simp only [exec, Option.map_some, setReg_setRsp hi]
  | bswap d =>
    simp only [Instr.rspFree, bne_iff_ne, ne_eq] at hi
    simp only [exec, Option.map_some, setRsp_gpr hi, setReg_setRsp hi]
  | xop op =>
    simp only [exec, Option.map_some]; congr 1
    cases op with
    | movq d r =>
      simp only [Instr.rspFree, bne_iff_ne, ne_eq] at hi
      simp only [XOp.exec, setRsp_gpr hi]; rfl
    | _ => rfl
  | movqR d r =>
    simp only [Instr.rspFree, bne_iff_ne, ne_eq] at hi
    simp only [exec, Option.map_some, setReg_setRsp hi]; rfl
  | movdquLoad d m =>
    simp only [Instr.rspFree] at hi
    simp only [exec, Option.map_map]; rw [ea_setRsp hi]; rfl
  | movdquStore m r =>
    simp only [Instr.rspFree] at hi
    simp only [exec, ea_setRsp hi, store128_setRsp]; rfl
  | movzx8 d m =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, Option.map_map]; rw [ea_setRsp hi.2]
    simp only [Function.comp_def, setReg_setRsp hi.1]; rfl
  | movzx16 d m =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, Option.map_map]; rw [ea_setRsp hi.2]
    simp only [Function.comp_def, setReg_setRsp hi.1]; rfl
  | store8 m r =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, ea_setRsp hi.1, setRsp_gpr hi.2, store8_setRsp]
  | store16 m r =>
    simp only [Instr.rspFree, Bool.and_eq_true, bne_iff_ne, ne_eq] at hi
    simp only [exec, ea_setRsp hi.1, setRsp_gpr hi.2, store16_setRsp]
  | leaSym d n =>
    simp only [Instr.rspFree, bne_iff_ne, ne_eq] at hi
    simp only [exec, Option.map_some, setReg_setRsp hi]; rfl
  | vop op =>
    simp only [exec, Option.map_some]; congr 1
    cases op <;> simp only [Instr.rspFree, VOp.rspFree, Bool.false_eq_true, bne_iff_ne, ne_eq] at hi
    case vmovq d r => simp only [VOp.exec, setRsp_gpr hi]; rfl
    all_goals rfl
  | vbinLoad op len d a m =>
    simp only [Instr.rspFree] at hi
    cases len <;> simp only [exec, Option.map_map] <;> rw [ea_setRsp hi] <;> rfl
  | vmovdquStore len m r =>
    simp only [Instr.rspFree] at hi
    cases len
    · simp only [exec, ea_setRsp hi, store128_setRsp]; rfl
    · simp only [exec, ea_setRsp hi, store256_setRsp]; rfl
  | _ => cases hi

theorem srcAddrs_setRsp {src : Src} (h : src.noRsp = true) : srcAddrs (s.setReg .rsp x) src = srcAddrs s src := by
  cases src with
  | mem m => simp only [srcAddrs]; rw [ea_setRsp h]
  | _ => rfl

theorem addrs_setRsp {i : Instr} (hi : i.rspFree = true) : addrs i (s.setReg .rsp x) = addrs i s := by
  cases i
  case mov | mov32 | alu | alu32 | adcx | adox | cmov | mulx =>
    simp only [Instr.rspFree, Bool.and_eq_true] at hi; simp only [addrs]; rw [srcAddrs_setRsp hi.2]
  case store | store8 | store16 =>
    simp only [Instr.rspFree, Bool.and_eq_true] at hi; simp only [addrs]; rw [ea_setRsp hi.1]
  case movdquLoad | movdquStore | vbinLoad | vmovdquStore =>
    simp only [Instr.rspFree] at hi; simp only [addrs]; rw [ea_setRsp hi]
  case movzx8 | movzx16 =>
    simp only [Instr.rspFree, Bool.and_eq_true] at hi; simp only [addrs]; rw [ea_setRsp hi.2]
  all_goals first | rfl | cases hi

end


/-! ## Runs -/

/-- A state with nothing in it, to count the addresses an instruction leaks
(their number does not depend on the state: `addrs_length`). -/
def State.zero : State :=
  { gpr := fun _ => 0, cf := none, zf := none, sf := none, of := none, mem := fun _ => 0, rd := [], wr := [] }

theorem srcAddrs_length (src : Src) (s s' : State) : (srcAddrs s src).length = (srcAddrs s' src).length := by
  cases src <;> rfl

theorem addrs_length (i : Instr) (s s' : State) : (addrs i s).length = (addrs i s').length := by
  cases i <;> simp only [addrs, List.length_map, List.length_range, List.length_cons, List.length_nil] <;>
    first | rfl | exact srcAddrs_length _ _ _

/-- The number of addresses a block leaks. -/
def blockLen (l : List Instr) : Nat := (l.map fun i => (addrs i State.zero).length).sum

theorem execBlock_length {l : List Instr} {s s' : State} {t : List Leak} (h : execBlock isa l s = some (s', t)) :
    t.length = blockLen l := by
  induction l generalizing s s' t with
  | nil => simp only [execBlock, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
  | cons i is ih =>
    simp only [execBlock] at h
    split at h
    · cases h
    · rename_i s₁ _
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨⟨s₂, t₂⟩, h₂, he⟩ := h
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      simp only [List.length_append, List.length_map, ih h₂, blockLen, List.map_cons, List.sum_cons]
      rw [addrs_length i s State.zero]

/-- Code whose calls can be inlined: no instruction outside a call writes
`rsp`, there are no frames, and each function called calls none and has
only instructions that do not touch `rsp`. Only the kernel evaluates it (as
`Code.allInstrs`). -/
noncomputable def _root_.VG.Code.InlineOk : Prog isa → Bool
  | .block l => KList.all l fun i => !Taint.clobbers i .rsp
  | .seq a b => a.InlineOk && b.InlineOk
  | .ite _ t e => t.InlineOk && e.InlineOk
  | .loop b _ => b.InlineOk
  | .call _ b => b.noCalls && b.allInstrs Instr.rspFree
  | .frame .. => false
  | .icall .. => false

/-- Inlined code whose calls call none calls none. -/
theorem _root_.VG.Code.noCalls_inline {c : Prog isa} (h : c.InlineOk = true) : c.inline.noCalls = true := by
  induction c with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.inline, Code.noCalls, Bool.and_eq_true]
    exact ⟨iha h.1, ihb h.2⟩
  | ite _ t e iht ihe =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.inline, Code.noCalls, Bool.and_eq_true]
    exact ⟨iht h.1, ihe h.2⟩
  | loop b _ ih =>
    simp only [Code.InlineOk] at h
    simp only [Code.inline, Code.noCalls]
    exact ih h
  | call _ b _ =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    exact h.1
  | frame _ _ _ _ => simp only [Code.InlineOk, Bool.false_eq_true] at h
  | icall => simp only [Code.InlineOk, Bool.false_eq_true] at h

/-- An instruction that neither reads nor writes `rsp` does not write it. -/
theorem _root_.VG.X86_64.Instr.clobbers_rsp_of_rspFree {i : Instr} (h : i.rspFree = true) :
    Taint.clobbers i .rsp = false := by
  cases i <;> (try cases h) <;> simp_all [Instr.rspFree, Taint.clobbers, Taint.dstOf, @eq_comm _ Reg.rsp]

/-- No instruction of inlined code writes `rsp`: what `Code.InlineOk` checks
of the code outside the calls, and of the calls' instructions (`rspFree`). -/
theorem _root_.VG.Code.clobbers_rsp_of_inlineOk {c : Prog isa} (h : c.InlineOk = true) :
    ∀ i ∈ instrs c.inline, Taint.clobbers i .rsp = false := by
  induction c with
  | block l =>
    simp only [Code.InlineOk, KList.all_eq, List.all_eq_true, Bool.not_eq_true'] at h
    exact h
  | seq a b iha ihb =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.inline, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iha h.1 i hi, ihb h.2 i hi]
  | ite _ t e iht ihe =>
    simp only [Code.InlineOk, Bool.and_eq_true] at h
    simp only [Code.inline, instrs, List.mem_append]
    rintro i (hi | hi)
    exacts [iht h.1 i hi, ihe h.2 i hi]
  | loop b _ ih =>
    simp only [Code.InlineOk] at h
    exact ih h
  | call _ b _ =>
    simp only [Code.InlineOk, Bool.and_eq_true, Code.allInstrs_eq, List.all_eq_true] at h
    exact fun i hi => Instr.clobbers_rsp_of_rspFree (h.2 i hi)
  | frame _ _ _ _ => simp only [Code.InlineOk, Bool.false_eq_true] at h
  | icall => simp only [Code.InlineOk, Bool.false_eq_true] at h

/-- Code without calls is its own inlined form. -/
theorem _root_.VG.Code.inline_of_noCalls {c : Prog isa} (h : c.noCalls = true) : c.inline = c := by
  induction c with
  | block _ => rfl
  | seq a b iha ihb =>
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [Code.inline, iha h.1, ihb h.2]
  | ite _ t e iht ihe =>
    simp only [Code.noCalls, Bool.and_eq_true] at h
    simp only [Code.inline, iht h.1, ihe h.2]
  | loop b _ ih =>
    simp only [Code.noCalls] at h
    simp only [Code.inline, ih h]
  | call _ _ _ => simp only [Code.noCalls, Bool.false_eq_true] at h
  | frame _ _ _ _ => simp only [Code.noCalls, Bool.false_eq_true] at h
  | icall => simp only [Code.noCalls, Bool.false_eq_true] at h

/-- The leakage of a run of `c`, from that of `c.inline` (a prefix of
`t`): each call adds the address of its return address `h` before and after
the leakage of the code it calls. With `f` steps of fuel; with the remainder
of `t`. -/
def liftT (h : Addr) : Nat → Prog isa → List Leak → Option (List Leak × List Leak)
  | 0, _, _ => none
  | _ + 1, .block l, t => if blockLen l ≤ t.length then some (t.take (blockLen l), t.drop (blockLen l)) else none
  | f + 1, .seq a b, t => (liftT h f a t).bind fun (p : List Leak × List Leak) => (liftT h f b p.2).map fun (q : List Leak × List Leak) => (p.1 ++ q.1, q.2)
  | f + 1, .ite _ th _, .branch true :: t => (liftT h f th t).map fun (p : List Leak × List Leak) => (.branch true :: p.1, p.2)
  | f + 1, .ite _ _ el, .branch false :: t => (liftT h f el t).map fun (p : List Leak × List Leak) => (.branch false :: p.1, p.2)
  | _ + 1, .ite .., _ => none
  | f + 1, .loop b c, t => (liftT h f b t).bind fun (p : List Leak × List Leak) => match p.2 with
      | .branch false :: r => some (p.1 ++ [.branch false], r)
      | .branch true :: r => (liftT h f (.loop b c) r).map fun (q : List Leak × List Leak) => (p.1 ++ .branch true :: q.1, q.2)
      | _ => none
  | f + 1, .call _ b, t => (liftT h f b t).map fun (p : List Leak × List Leak) => (.addr h :: (p.1 ++ [.addr h]), p.2)
  | _ + 1, .frame .., _ => none
  | _ + 1, .icall .., _ => none

/-- `ta` is the leakage `liftT` gives for `t`, with enough fuel, whatever follows. -/
def Lifts (h : Addr) (c : Prog isa) (ta t : List Leak) : Prop :=
  ∃ N, ∀ f, N ≤ f → ∀ r, liftT h f c (t ++ r) = some (ta, r)

section
variable {H : Region}

theorem execBlock_F {F : State → State} {l : List Instr}
    (hF : ∀ i ∈ l, ∀ s, Clear H s → exec i (F s) = (exec i s).map F ∧ addrs i (F s) = addrs i s) :
    ∀ {s : State}, Clear H s → execBlock isa l (F s) = (execBlock isa l s).map fun p => (F p.1, p.2) := by
  induction l with
  | nil => intro s _; rfl
  | cons i is ih =>
    intro s hc
    obtain ⟨he, ha⟩ := hF i (List.mem_cons_self ..) s hc
    simp only [execBlock]
    simp only [he, ha]
    cases hx : exec i s with
    | none => rfl
    | some s₁ =>
      have hc₁ : Clear H s₁ := by
        obtain ⟨h1, h2⟩ := exec_regions hx; unfold Clear; rw [h1, h2]; exact hc
      simp only [Option.map_some]
      rw [ih (fun j hj => hF j (List.mem_cons_of_mem _ hj)) hc₁]
      cases execBlock isa is s₁ <;> rfl

theorem Clear.of_exec {c : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa c s t s') (hc : Clear H s) :
    Clear H s' := by
  obtain ⟨h1, h2⟩ := Exec.rdwr h; unfold Clear; rw [h1, h2]; exact hc

/-- Code that calls nothing runs from `F s` as from `s`, if each of its
instructions does. -/
theorem Exec.F {F : State → State} {c : Prog isa} (hc : c.noCalls = true)
    (hF : ∀ i ∈ instrs c, ∀ s, Clear H s → exec i (F s) = (exec i s).map F ∧ addrs i (F s) = addrs i s)
    (hev : ∀ (k : Cond) s, eval k (F s) = eval k s) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') (hs : Clear H s) : Exec isa c (F s) t (F s') := by
  induction h with
  | @block is _ _ _ h => exact .block (by rw [execBlock_F (l := is) hF hs, h]; rfl)
  | seq h₁ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    exact .seq (ih₁ hc.1 (fun i hi => hF i (List.mem_append_left _ hi)) hs)
      (ih₂ hc.2 (fun i hi => hF i (List.mem_append_right _ hi)) (hs.of_exec h₁))
  | iteT hk _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    exact .iteT ((hev _ _).trans hk) (ih hc.1 (fun i hi => hF i (List.mem_append_left _ hi)) hs)
  | iteF hk _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    exact .iteF ((hev _ _).trans hk) (ih hc.2 (fun i hi => hF i (List.mem_append_right _ hi)) hs)
  | loopExit _ hk ih => exact .loopExit (ih hc hF hs) ((hev _ _).trans hk)
  | loopNext h₁ hk _ ih₁ ih₂ => exact .loopNext (ih₁ hc hF hs) ((hev _ _).trans hk) (ih₂ hc hF (hs.of_exec h₁))
  | call => simp [Code.noCalls] at hc
  | frame => simp [Code.noCalls] at hc
  | icall | icallNext => simp [Code.noCalls] at hc

/-- The leakage of code that calls nothing lifts to itself. -/
theorem Exec.lifts_self (h' : Addr) {c : Prog isa} (hc : c.noCalls = true) {s s' : State} {t : List Leak}
    (h : Exec isa c s t s') : Lifts h' c t t := by
  induction h with
  | block h =>
    refine ⟨1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    have hl := execBlock_length h
    simp only [liftT, List.length_append, hl, Nat.le_add_right, ite_true, List.take_left', List.drop_left']
  | @seq c₁ c₂ _ _ _ t₁ t₂ _ _ ih₁ ih₂ =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    obtain ⟨N₁, h₁⟩ := ih₁ hc.1
    obtain ⟨N₂, h₂⟩ := ih₂ hc.2
    refine ⟨max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, List.append_assoc, h₁ f (by omega_arith) (t₂ ++ r), Option.bind_some, h₂ f (by omega_arith) r,
      Option.map_some]
  | @iteT _ _ _ _ _ t _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    obtain ⟨N, h₁⟩ := ih hc.1
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, List.cons_append, h₁ f (by omega_arith) r, Option.map_some]
  | @iteF _ _ _ _ _ t _ _ ih =>
    simp only [Code.noCalls, Bool.and_eq_true] at hc
    obtain ⟨N, h₁⟩ := ih hc.2
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, List.cons_append, h₁ f (by omega_arith) r, Option.map_some]
  | @loopExit _ _ _ _ t _ _ ih =>
    obtain ⟨N, h₁⟩ := ih hc
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, List.append_assoc, List.cons_append, List.nil_append, h₁ f (by omega_arith), Option.bind_some]
  | @loopNext _ _ _ _ _ t t' _ _ _ ih₁ ih₂ =>
    obtain ⟨N₁, h₁⟩ := ih₁ hc
    obtain ⟨N₂, h₂⟩ := ih₂ hc
    refine ⟨max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, List.append_assoc, List.cons_append, h₁ f (by omega_arith), Option.bind_some]
    rw [h₂ f (by omega_arith) r]; rfl
  | call => simp [Code.noCalls] at hc
  | frame => simp [Code.noCalls] at hc
  | icall | icallNext => simp [Code.noCalls] at hc

end


/-! ## Calls as inlined code -/

theorem Exec.seq_inv {a b : Prog isa} {s s' : State} {t : List Leak} (h : Exec isa (.seq a b) s t s') :
    ∃ t₁ t₂ s₁, Exec isa a s t₁ s₁ ∧ Exec isa b s₁ t₂ s' ∧ t = t₁ ++ t₂ := by
  cases h with | seq h₁ h₂ => exact ⟨_, _, _, h₁, h₂, rfl⟩

theorem Exec.ite_inv {k : Cond} {th el : Prog isa} {s s' : State} {t : List Leak}
    (h : Exec isa (.ite k th el) s t s') :
    (∃ t', t = .branch true :: t' ∧ eval k s = some true ∧ Exec isa th s t' s') ∨
      (∃ t', t = .branch false :: t' ∧ eval k s = some false ∧ Exec isa el s t' s') := by
  cases h with
  | iteT hk h => exact .inl ⟨_, rfl, hk, h⟩
  | iteF hk h => exact .inr ⟨_, rfl, hk, h⟩

/-- The return address a call from `sp` stores. -/
def hole (sp : Addr) : Region := ⟨sp - 8, 8⟩

theorem hole_contains {sp x : Addr} : (hole sp).Contains x 1 ↔ (x - (sp - 8)).toNat < 8 := by
  simp only [hole, Region.Contains]; omega_arith

theorem overlay_hole_writeW (sp : Addr) (hv m : Mem) (v : BitVec 64) :
    (overlay (hole sp) hv m).writeW (sp - 8) v = overlay (hole sp) (hv.writeW (sp - 8) v) m := by
  funext x
  simp only [Mem.writeW, Mem.write, overlay, hole_contains]
  split <;> rfl

theorem overlay_hole_readW (sp : Addr) (hv m : Mem) :
    (overlay (hole sp) hv m).readW (sp - 8) 64 = hv.readW (sp - 8) 64 :=
  Mem.readW_congr fun i hi => by
    have : (hole sp).Contains (sp - 8 + BitVec.ofNat 64 i) 1 := by
      rw [hole_contains, Mem.sub_ofNat_toNat _ (by omega_arith)]; omega_arith
    simp only [overlay, this, ite_true]

theorem setReg_self (s : State) (r : Reg) : s.setReg r (s.gpr r) = s := by
  simp only [State.setReg]
  congr 1; funext r'; split <;> simp_all

theorem setReg_setReg (s : State) (r : Reg) (a b : BitVec 64) : (s.setReg r a).setReg r b = s.setReg r b := by
  simp only [State.setReg]
  congr 1; funext r'; split <;> simp_all

@[simp] theorem State.patch_gpr (H : Region) (hv : Mem) (u : Nat → BitVec 64) (s : State) :
    (s.patch H hv u).gpr = s.gpr := rfl
@[simp] theorem State.patch_rd (H : Region) (hv : Mem) (u : Nat → BitVec 64) (s : State) :
    (s.patch H hv u).rd = s.rd := rfl
@[simp] theorem State.patch_wr (H : Region) (hv : Mem) (u : Nat → BitVec 64) (s : State) :
    (s.patch H hv u).wr = s.wr := rfl
@[simp] theorem State.patch_mxcsr (H : Region) (hv : Mem) (u : Nat → BitVec 64) (s : State) :
    (s.patch H hv u).mxcsr = s.mxcsr := rfl

theorem State.patch_mem {H : Region} {hv : Mem} {u : Nat → BitVec 64} {s : State} {x : Addr}
    (hx : ¬ H.Contains x 1) : (s.patch H hv u).mem x = s.mem x := by
  simp only [State.patch, overlay, hx, ite_false]

theorem State.patch_readW {H : Region} {hv : Mem} {u : Nat → BitVec 64} {s : State} {a : Addr} {w : Nat}
    (hn : w / 8 < 2 ^ 64) (h : ∀ x, (x - a).toNat < w / 8 → ¬ H.Contains x 1) :
    (s.patch H hv u).mem.readW a w = s.mem.readW a w :=
  overlay_readW hn h

theorem loop_uninline {body : Prog isa} {k : Cond} {sp : Addr}
    (ih : ∀ {b b' : State} {t : List Leak}, Exec isa body.inline b t b' → Clear (hole sp) b → b.gpr .rsp = sp →
      ∀ (hv : Mem) (u : Nat → BitVec 64), ∃ hv' u' ta,
        Exec isa body (b.patch (hole sp) hv u) ta (b'.patch (hole sp) hv' u') ∧ b'.gpr .rsp = sp ∧
          Lifts (sp - 8) body ta t)
    {b b' : State} {t : List Leak} (h : Exec isa (.loop body.inline k) b t b') (hb : Clear (hole sp) b)
    (hsp : b.gpr .rsp = sp) (hv : Mem) (u : Nat → BitVec 64) :
    ∃ hv' u' ta, Exec isa (.loop body k) (b.patch (hole sp) hv u) ta (b'.patch (hole sp) hv' u') ∧
      b'.gpr .rsp = sp ∧ Lifts (sp - 8) (.loop body k) ta t := by
  generalize e : (Code.loop body.inline k : Prog isa) = L at h
  induction h generalizing hv u with
  | block | seq | iteT | iteF | call | frame | icall | icallNext => cases e
  | @loopExit body' k' s s' t h₁ hk _ =>
    cases e
    obtain ⟨hv', u', ta, ha, hs', ⟨N, hl⟩⟩ := ih h₁ hb hsp hv u
    refine ⟨hv', u', ta ++ [.branch false], .loopExit ha ((eval_patch _).trans hk), hs', N + 1,
      fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, List.append_assoc, List.cons_append, List.nil_append, hl f (by omega_arith), Option.bind_some]
  | @loopNext body' k' s s₁ s' t t' h₁ hk _ _ ih₂ =>
    cases e
    obtain ⟨hv₁, u₁, ta₁, ha₁, hs₁, ⟨N₁, hl₁⟩⟩ := ih h₁ hb hsp hv u
    obtain ⟨hv', u', ta₂, ha₂, hs', ⟨N₂, hl₂⟩⟩ := ih₂ (hb.of_exec h₁) hs₁ hv₁ u₁ rfl
    refine ⟨hv', u', ta₁ ++ .branch true :: ta₂, .loopNext ha₁ ((eval_patch _).trans hk) ha₂, hs',
      max N₁ N₂ + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, List.append_assoc, List.cons_append, hl₁ f (by omega_arith), Option.bind_some]
    rw [hl₂ f (by omega_arith) r]; rfl

/-- A run of `c.inline` gives one of `c`, from the same state but for the
bytes of the return address below `rsp` and the unknowns, to the same state
but for those, with the leakage `liftT` gives. -/
theorem Exec.uninline {c : Prog isa} (hc : c.InlineOk = true) {sp : Addr} {b b' : State} {t : List Leak}
    (h : Exec isa c.inline b t b') (hb : Clear (hole sp) b) (hsp : b.gpr .rsp = sp) (hv : Mem)
    (u : Nat → BitVec 64) :
    ∃ hv' u' ta, Exec isa c (b.patch (hole sp) hv u) ta (b'.patch (hole sp) hv' u') ∧ b'.gpr .rsp = sp ∧
      Lifts (sp - 8) c ta t := by
  induction c generalizing b b' t hv u with
  | icall => simp only [Code.InlineOk, Bool.false_eq_true] at hc
  | block l =>
    simp only [Code.inline] at h
    simp only [Code.InlineOk, KList.all_eq, List.all_eq_true, Bool.not_eq_true'] at hc
    refine ⟨hv, u, t, Exec.F (H := hole sp) rfl (fun i _ s hs => ⟨exec_patch hs i, addrs_patch i⟩)
      (fun k _ => eval_patch k) h hb, ?_, Exec.lifts_self _ rfl h⟩
    rw [Exec.gpr (c := .block l) (fun i hi => hc i hi) h, hsp]
  | seq a c ih₁ ih₂ =>
    simp only [Code.InlineOk, Bool.and_eq_true] at hc
    simp only [Code.inline] at h
    obtain ⟨t₁, t₂, s₁, h₁, h₂, rfl⟩ := Exec.seq_inv h
    · obtain ⟨hv₁, u₁, ta₁, ha₁, hs₁, ⟨N₁, hl₁⟩⟩ := ih₁ hc.1 h₁ hb hsp hv u
      obtain ⟨hv', u', ta₂, ha₂, hs', ⟨N₂, hl₂⟩⟩ := ih₂ hc.2 h₂ (hb.of_exec h₁) hs₁ hv₁ u₁
      refine ⟨hv', u', ta₁ ++ ta₂, .seq ha₁ ha₂, hs', max N₁ N₂ + 1, fun f hf r => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
      simp only [liftT, List.append_assoc, hl₁ f (by omega_arith), Option.bind_some, hl₂ f (by omega_arith) r,
        Option.map_some]
  | ite k th el ih₁ ih₂ =>
    simp only [Code.InlineOk, Bool.and_eq_true] at hc
    simp only [Code.inline] at h
    rcases Exec.ite_inv h with ⟨t, rfl, hk, h₁⟩ | ⟨t, rfl, hk, h₁⟩
    · obtain ⟨hv', u', ta, ha, hs', ⟨N, hl⟩⟩ := ih₁ hc.1 h₁ hb hsp hv u
      refine ⟨hv', u', .branch true :: ta, .iteT ((eval_patch _).trans hk) ha, hs', N + 1, fun f hf r => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
      simp only [liftT, List.cons_append, hl f (by omega_arith) r, Option.map_some]
    · obtain ⟨hv', u', ta, ha, hs', ⟨N, hl⟩⟩ := ih₂ hc.2 h₁ hb hsp hv u
      refine ⟨hv', u', .branch false :: ta, .iteF ((eval_patch _).trans hk) ha, hs', N + 1,
        fun f hf r => ?_⟩
      obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
      simp only [liftT, List.cons_append, hl f (by omega_arith) r, Option.map_some]
  | loop body k ih =>
    simp only [Code.InlineOk] at hc
    simp only [Code.inline] at h
    exact loop_uninline (fun h₁ hb₁ hsp₁ hv₁ u₁ => ih hc h₁ hb₁ hsp₁ hv₁ u₁) h hb hsp hv u
  | call n body _ =>
    simp only [Code.InlineOk, Bool.and_eq_true] at hc
    obtain ⟨hn, hr⟩ := hc
    have hr' : ∀ i ∈ instrs body, i.rspFree = true := by
      rw [Code.allInstrs_eq, List.all_eq_true] at hr; exact hr
    simp only [Code.inline] at h
    have hrsp : b'.gpr .rsp = sp := by
      rw [Exec.gpr (fun i hi => Instr.clobbers_rsp_of_rspFree (hr' i hi)) h, hsp]
    -- After the call: `rsp` 8 lower and the return address in the hole.
    let hv₁ : Mem := hv.writeW (sp - 8) (u 0)
    let u₁ : Nat → BitVec 64 := fun n => u (n + 1)
    let F : State → State := fun s => (s.patch (hole sp) hv₁ u₁).setReg .rsp (sp - 8)
    have hcall : isa.call (b.patch (hole sp) hv u) = some (F b) := by
      simp only [isa, call, State.patch_gpr, hsp, F, hv₁, u₁]
      congr 1
      simp only [State.patch, State.setReg, ← overlay_hole_writeW]
    have hbody : Exec isa body (F b) t (F b') :=
      Exec.F (H := hole sp) hn (fun i hi s hs => ⟨by
          have hi' := hr' i hi
          simp only [F]; rw [exec_setRsp hi', exec_patch hs, Option.map_map]; rfl,
        by simp only [F]; rw [addrs_setRsp (hr' i hi), addrs_patch]⟩)
        (fun k s => by simp only [F]; rw [eval_setRsp, eval_patch]) h hb
    have hret : isa.ret (F b) (F b') = some (b'.patch (hole sp) hv₁ u₁) := by
      have g₁ : ∀ s : State, (F s).gpr .rsp = sp - 8 := fun s => by simp [F, State.setReg]
      have m₁ : ∀ s : State, (F s).mem.readW (sp - 8) 64 = hv₁.readW (sp - 8) 64 := fun s =>
        overlay_hole_readW sp hv₁ s.mem
      simp only [isa, ret, g₁, m₁, and_self, ite_true, Option.some.injEq]
      simp only [F, setReg_setReg, BitVec.sub_add_cancel]
      rw [← hrsp]
      exact setReg_self _ _
    refine ⟨hv₁, u₁, _, .call hcall hbody hret, hrsp, ?_⟩
    obtain ⟨N, hl⟩ := Exec.lifts_self (sp - 8) hn h
    refine ⟨N + 1, fun f hf r => ?_⟩
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega_arith⟩
    simp only [liftT, hl f (by omega_arith) r, Option.map_some, State.patch_gpr, hsp, F, State.setReg, ite_true,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  | frame => simp [Code.InlineOk] at hc

/-- A run of `c.inline` from `s` gives one of `c` from `s`. -/
theorem Exec.of_inline {c : Prog isa} (hc : c.InlineOk = true) {s s' : State} {t : List Leak}
    (h : Exec isa c.inline s t s') (hs : Clear (hole (s.gpr .rsp)) s) :
    ∃ hv u ta, Exec isa c s ta (s'.patch (hole (s.gpr .rsp)) hv u) ∧ s'.gpr .rsp = s.gpr .rsp ∧
      Lifts (s.gpr .rsp - 8) c ta t := by
  obtain ⟨hv, u, ta, he, hr, hl⟩ := Exec.uninline hc h hs rfl s.mem s.unknowns
  rw [State.patch_self] at he
  exact ⟨hv, u, ta, he, hr, hl⟩

/-- `c` runs as `c.inline` does, but for the return address. -/
theorem WP.of_inline {c : Prog isa} (hc : c.InlineOk = true) {s : State} (hs : Clear (hole (s.gpr .rsp)) s)
    {Q : State → Prop} (h : WP isa c.inline s Q) :
    WP isa c s fun s' => ∃ b hv u, s' = b.patch (hole (s.gpr .rsp)) hv u ∧ b.gpr .rsp = s.gpr .rsp ∧ Q b := by
  obtain ⟨t, b, he, hq⟩ := h
  obtain ⟨hv, u, ta, ha, hr, _⟩ := Exec.of_inline hc he hs
  exact ⟨ta, _, ha, b, hv, u, rfl, hr, hq⟩

theorem Lifts.unique {h : Addr} {c : Prog isa} {ta₁ ta₂ t : List Leak} (h₁ : Lifts h c ta₁ t)
    (h₂ : Lifts h c ta₂ t) : ta₁ = ta₂ := by
  obtain ⟨N₁, l₁⟩ := h₁
  obtain ⟨N₂, l₂⟩ := h₂
  have := (l₁ (max N₁ N₂) (by omega_arith) []).symm.trans (l₂ (max N₁ N₂) (by omega_arith) [])
  simp only [Option.some.injEq, Prod.mk.injEq] at this
  exact this.1

/-- `c` is constant time if `c.inline` is, and runs from every state its
precondition allows. -/
theorem ConstantTime.of_inline {c : Prog isa} (hc : c.InlineOk = true) {P : State → Prop}
    {Pub : State → State → Prop} (hrun : ∀ s, P s → ∃ t s', Exec isa c.inline s t s')
    (hclear : ∀ s, P s → Clear (hole (s.gpr .rsp)) s) (hpub : ∀ s₁ s₂, P s₁ → P s₂ → Pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp)
    (hct : ConstantTime isa P Pub c.inline) : ConstantTime isa P Pub c := by
  intro s₁ s₂ t₁ t₂ s₁' s₂' p₁ p₂ hp e₁ e₂
  obtain ⟨tb₁, b₁, f₁⟩ := hrun s₁ p₁
  obtain ⟨tb₂, b₂, f₂⟩ := hrun s₂ p₂
  obtain ⟨_, _, ta₁, a₁, _, l₁⟩ := Exec.of_inline hc f₁ (hclear s₁ p₁)
  obtain ⟨_, _, ta₂, a₂, _, l₂⟩ := Exec.of_inline hc f₂ (hclear s₂ p₂)
  obtain ⟨rfl, -⟩ := Exec.det e₁ a₁
  obtain ⟨rfl, -⟩ := Exec.det e₂ a₂
  have ht := hct s₁ s₂ tb₁ tb₂ b₁ b₂ p₁ p₂ hp f₁ f₂
  subst ht
  rw [hpub s₁ s₂ p₁ p₂ hp] at l₁
  exact l₁.unique l₂


/-- The return address above `rsp` is not in the hole below it. -/
theorem not_hole_of_above {sp x : Addr} (h : (x - sp).toNat < 8) : ¬ (hole sp).Contains x 1 := by
  rw [hole_contains]
  have : x - (sp - 8) = (x - sp) + 8 := by
    rw [BitVec.sub_eq_add_neg x (sp - 8), BitVec.neg_sub, BitVec.sub_eq_add_neg x sp, BitVec.add_assoc]
  rw [this, BitVec.toNat_add, show (8 : BitVec 64).toNat = 8 from rfl]
  omega_arith

/-- The calling convention's obligations hold of the run of `c` if they do of `c.inline`'s. -/
theorem abiPreserved_patch {s b : State} (hv : Mem) (u : Nat → BitVec 64) (h : abiPreserved s b) :
    abiPreserved s (b.patch (hole (s.gpr .rsp)) hv u) := by
  refine ⟨h.1, ?_, h.2.2⟩
  rw [State.patch_readW (by decide) fun x hx => not_hole_of_above hx]
  exact h.2.1

/-- `c` is verified against `k` if `c.inline` is correct and constant time
against a contract `k₀` that `k` implies, `k₀`'s postcondition does not read
the 8 bytes below `rsp`, and `k` keeps every buffer away from them. -/
theorem Verified.of_inline {c : Prog isa} (hc : c.InlineOk = true) {k₀ k : Contract isa}
    (hcor : ∀ s, k₀.pre s → ∃ t s', Exec isa c.inline s t s' ∧ abiPreserved s s' ∧ k₀.post s s')
    (hct : ConstantTime isa k₀.pre k₀.pub c.inline) (himp : k₀.Implies k)
    (hclear : ∀ s, k.pre s → Clear (hole (s.gpr .rsp)) s)
    (hpost : ∀ s b hv u, k.pre s → k₀.post s b → k₀.post s (b.patch (hole (s.gpr .rsp)) hv u))
    (hrsp : ∀ s₁ s₂, k.pre s₁ → k.pre s₂ → k.pub s₁ s₂ → s₁.gpr .rsp = s₂.gpr .rsp) : Verified target c k := by
  refine ⟨fun s hs => ?_, ?_, himp.sat⟩
  · obtain ⟨t, b, he, ha, hp⟩ := hcor s (himp.pre s hs)
    obtain ⟨hv, u, ta, ha', _, _⟩ := Exec.of_inline hc he (hclear s hs)
    exact ⟨ta, _, ha', abiPreserved_patch hv u ha, himp.post s _ hs (hpost s b hv u hs hp)⟩
  · refine ConstantTime.of_inline hc (fun s hs => ?_) hclear hrsp fun s₁ s₂ t₁ t₂ s₁' s₂' h₁ h₂ hp e₁ e₂ =>
      hct s₁ s₂ t₁ t₂ s₁' s₂' (himp.pre _ h₁) (himp.pre _ h₂) (himp.pub _ _ h₁ h₂ hp) e₁ e₂
    obtain ⟨t, b, he, -, -⟩ := hcor s (himp.pre s hs)
    exact ⟨t, b, he⟩

end VG.X86_64
