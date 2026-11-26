module

public import VerifiedGarbage.Impl.P256.X86_64.Ifma.Vec

/-!
# P-256 on x86-64 with AVX512_IFMA: the field

A field element is five signed limbs `x₀ + 2⁵² x₁ + … + 2²⁰⁸ x₄`, standing
for its residue modulo `p`, in Montgomery form with `R = 2²⁶⁰`; four of them
are the lanes of five values (`F5`).

* `mulCore`, `sqrCore`: the Montgomery product `a b / 2²⁶⁰ mod p` of
  operands whose limbs are in `[0, 2⁵²)`, in limbs that are not carried. Each
  product `a_i b_j` of two limbs is `lo + 2⁵² hi` (`vpmadd52luq`,
  `vpmadd52huq`); `lo` goes to column `i + j` and `hi` to column
  `i + j + 1`. `p ≡ -1 (mod 2⁵²)`, so the reduction adds `m p 2^(52 i)`
  for `m` the low 52 bits of column `i`, for `i` from 0 to 4 (`redStep`):
  `p = 2²⁰⁸ (2⁴⁸ - 2¹⁶) + 2¹⁵⁶ 2³⁶ + 2⁵² 2⁴⁴ - 1`, and the result is the
  columns 5 to 9.
* `norm`: the top limb's bits from 48 up, `h`, are folded (`2²⁵⁶ ≡ 2²²⁴ -
  2¹⁹² - 2⁹⁶ + 1`), then each limb passes its bits from 52 up to the next,
  signed (`vpsraq`): the value less `h p`, in limbs in `[0, 2⁵²)` if the
  value was in `[0, 2²⁶⁰)`.
* A difference is taken limb by limb, and a multiple of `p` (`bias`) added
  before the next `norm` so that the value is not negative.
-/

@[expose] public section

namespace VG.Impl.P256.X86_64.Ifma

open VG VG.X86_64

/-- The prime of P-256. -/
def pN : Nat := 2 ^ 256 - 2 ^ 224 + 2 ^ 192 + 2 ^ 96 - 1

/-- Five limbs of each of four lanes. -/
structure F5 (α : Type) where
  l0 : α
  l1 : α
  l2 : α
  l3 : α
  l4 : α

def F5.get {α : Type} (v : F5 α) (i : Nat) : α :=
  match i with
  | 0 => v.l0
  | 1 => v.l1
  | 2 => v.l2
  | 3 => v.l3
  | _ => v.l4

def F5.toList {α : Type} (v : F5 α) : List α := [v.l0, v.l1, v.l2, v.l3, v.l4]

section
variable {m : Type → Type} [Monad m] {α : Type}

def F5.mapM (v : F5 α) (f : α → m α) : m (F5 α) := do
  let x0 ← f v.l0; let x1 ← f v.l1; let x2 ← f v.l2; let x3 ← f v.l3; let x4 ← f v.l4
  pure ⟨x0, x1, x2, x3, x4⟩

def F5.zipM (a b : F5 α) (f : α → α → m α) : m (F5 α) := do
  let x0 ← f a.l0 b.l0; let x1 ← f a.l1 b.l1; let x2 ← f a.l2 b.l2; let x3 ← f a.l3 b.l3
  let x4 ← f a.l4 b.l4
  pure ⟨x0, x1, x2, x3, x4⟩

/-- The mask of the low 52 bits, and of the low 48. -/
def kMask : K4 := K4.all (2 ^ 52 - 1)
def kM48 : K4 := K4.all (2 ^ 48 - 1)
/-- The limbs of `p` above its lowest two that are not zero: `2³⁶` and `2⁴⁸ - 2¹⁶`. -/
def k36 : K4 := K4.all (2 ^ 36)
def kP4 : K4 := K4.all (2 ^ 48 - 2 ^ 16)

def fadd (o : Ops m α) (a b : F5 α) : m (F5 α) := a.zipM b o.add
def fsub (o : Ops m α) (a b : F5 α) : m (F5 α) := a.zipM b o.sub
/-- `2^n a`. -/
def fshl (o : Ops m α) (a : F5 α) (n : Nat) : m (F5 α) := a.mapM fun x => if n = 1 then o.add x x else o.sll x n
/-- Lane `k` from lane `i_k`. -/
def fperm (o : Ops m α) (a : F5 α) (i0 i1 i2 i3 : Nat) : m (F5 α) :=
  a.mapM fun x => o.perm x (i0 + 4 * i1 + 16 * i2 + 64 * i3)
/-- The lanes of `msk` from `b`, the others from `a`. -/
def fblend (o : Ops m α) (a b : F5 α) (msk : Nat) : m (F5 α) := a.zipM b fun x y => o.blend x y msk
/-- `acc + b` in the lanes of `msk`, `acc` in the others. -/
def fmadd (o : Ops m α) (acc b : F5 α) (msk : Nat) : m (F5 α) :=
  acc.zipM b fun x y => do let t ← o.andc y (K4.lanes msk); o.add x t
/-- `acc - b` in the lanes of `msk`, `acc` in the others. -/
def fmsub (o : Ops m α) (acc b : F5 α) (msk : Nat) : m (F5 α) :=
  acc.zipM b fun x y => do let t ← o.andc y (K4.lanes msk); o.sub x t
/-- `a - acc` in the lanes of `msk`, `acc` in the others. -/
def fmrsub (o : Ops m α) (acc a : F5 α) (msk : Nat) : m (F5 α) :=
  acc.zipM a fun x y => do let t ← o.sub y x; o.blend x t msk

/-- Limb `i` of `k p`, the top one with what is above `2²⁶⁰`. -/
def limbOf (v i : Nat) : Nat := if i = 4 then v / 2 ^ 208 else v / 2 ^ (52 * i) % 2 ^ 52

/-- Limb `i` of `k_l p` in each lane `l`. -/
def biasK (k0 k1 k2 k3 i : Nat) : K4 :=
  ⟨limbOf (k0 * pN) i, limbOf (k1 * pN) i, limbOf (k2 * pN) i, limbOf (k3 * pN) i⟩

/-- `a + k_l p` in each lane `l`. -/
def fbias (o : Ops m α) (a : F5 α) (k0 k1 k2 k3 : Nat) : m (F5 α) := do
  let x0 ← o.addc a.l0 (biasK k0 k1 k2 k3 0); let x1 ← o.addc a.l1 (biasK k0 k1 k2 k3 1)
  let x2 ← o.addc a.l2 (biasK k0 k1 k2 k3 2); let x3 ← o.addc a.l3 (biasK k0 k1 k2 k3 3)
  let x4 ← o.addc a.l4 (biasK k0 k1 k2 k3 4)
  pure ⟨x0, x1, x2, x3, x4⟩

/-- The limbs of a constant in each lane. -/
def fconst (o : Ops m α) (c0 c1 c2 c3 : Nat) : m (F5 α) := do
  let k (i : Nat) : K4 := ⟨limbOf c0 i, limbOf c1 i, limbOf c2 i, limbOf c3 i⟩
  let x0 ← o.const (k 0); let x1 ← o.const (k 1); let x2 ← o.const (k 2); let x3 ← o.const (k 3)
  let x4 ← o.const (k 4)
  pure ⟨x0, x1, x2, x3, x4⟩

/-- The top limb's bits from 48 up folded, then a signed carry. -/
def norm (o : Ops m α) (v : F5 α) : m (F5 α) := do
  let h ← o.sra v.l4 48
  let v4 ← o.andc v.l4 kM48
  let v0 ← o.add v.l0 h
  let h44 ← o.sll h 44
  let v1 ← o.sub v.l1 h44
  let h36 ← o.sll h 36
  let v3 ← o.sub v.l3 h36
  let h16 ← o.sll h 16
  let v4 ← o.add v4 h16
  let c ← o.sra v0 52
  let v0 ← o.andc v0 kMask
  let v1 ← o.add v1 c
  let c ← o.sra v1 52
  let v1 ← o.andc v1 kMask
  let v2 ← o.add v.l2 c
  let c ← o.sra v2 52
  let v2 ← o.andc v2 kMask
  let v3 ← o.add v3 c
  let c ← o.sra v3 52
  let v3 ← o.andc v3 kMask
  let v4 ← o.add v4 c
  pure ⟨v0, v1, v2, v3, v4⟩

/-- A step of the reduction, at column `i` of the columns `t` (`d` stands for a missing one): the
products are of the low 52 bits of the column. -/
def redStep (o : Ops m α) (d : α) (t : List α) (i : Nat) : m (List α) := do
  let ti := t.getD i d
  let mm ← o.andc ti kMask
  let c ← o.srl ti 52
  -- `(t_i mod 2⁸) 2⁴⁴`: the low 52 bits of `m 2⁴⁴`
  let s ← o.slr ti 56 12
  let x ← o.add (t.getD (i + 1) d) c
  let x ← o.add x s
  let t := t.set (i + 1) x
  let y ← o.srl mm 8
  let y ← o.add (t.getD (i + 2) d) y
  let t := t.set (i + 2) y
  let z ← o.maddc false (some (t.getD (i + 3) d)) ti k36
  let t := t.set (i + 3) z
  let w ← o.maddc true (some (t.getD (i + 4) d)) ti k36
  let w ← o.maddc false (some w) ti kP4
  let t := t.set (i + 4) w
  let v ← o.maddc true (some (t.getD (i + 5) d)) ti kP4
  pure (t.set (i + 5) v)

/-- The reduction of ten columns: the columns 5 to 9 after five steps. -/
def reduce (o : Ops m α) (d : α) (t : List α) : m (F5 α) := do
  let t ← redStep o d t 0
  let t ← redStep o d t 1
  let t ← redStep o d t 2
  let t ← redStep o d t 3
  let t ← redStep o d t 4
  pure ⟨t.getD 5 d, t.getD 6 d, t.getD 7 d, t.getD 8 d, t.getD 9 d⟩

/-- A half (the high one if `h`) of the product of the limbs `i` of one operand and `j` of the other. -/
structure Half where
  h : Bool
  i : Nat
  j : Nat

/-- `t` in `ts`, kept in the order of the later limb of each: limb `i` of a carried value is ready
after limb `i - 1`. -/
def Half.ins (t : Half) : List Half → List Half
  | [] => [t]
  | u :: us => if max t.i t.j < max u.i u.j then t :: u :: us else u :: t.ins us

/-- `xs` dealt into `n` lists, in turn. -/
def deal {β : Type} (n : Nat) (xs : List β) : List (List β) :=
  (List.range n).map fun r => (xs.zipIdx.filter fun p => p.2 % n = r).map (·.1)

/-- The sum of the halves `ts` of products of limbs of `a` and `b` (none if there is none): the
halves whose limbs are ready first are added first, in chains of three at most, which are then added. -/
def colSum (o : Ops m α) (a b : F5 α) (ts : List Half) : m (Option α) := do
  let ts := ts.foldr Half.ins []
  let accs ← (deal ((ts.length + 2) / 3) ts).mapM fun g =>
    g.foldlM (fun (acc : Option α) (t : Half) => do
      let x ← o.madd t.h acc (a.get t.i) (b.get t.j)
      pure (some x)) none
  accs.foldlM (fun (s : Option α) (x : Option α) =>
    match s, x with
    | some s, some x => do let y ← o.add s x; pure (some y)
    | none, x => pure x
    | s, none => pure s) none

/-- The ten columns of the products of the limbs of `a` and `b`: column `k` has the low halves of
those of limbs `i` and `k - i`, and the high halves of those of limbs `i` and `k - 1 - i`. -/
def mulCols (o : Ops m α) (a b : F5 α) : m (List α) :=
  (List.range 10).mapM fun k => do
    let lo := ((List.range 5).filter fun i => i ≤ k ∧ k - i ≤ 4).map fun i => Half.mk false i (k - i)
    let hi := ((List.range 5).filter fun i => i + 1 ≤ k ∧ k - 1 - i ≤ 4).map fun i => Half.mk true i (k - 1 - i)
    let x ← colSum o a b (lo ++ hi)
    pure (x.getD a.l0)

/-- The Montgomery product of the lanes of `a` and `b`. -/
def mulCore (o : Ops m α) (a b : F5 α) : m (F5 α) := do
  let t ← mulCols o a b
  reduce o a.l0 t

/-- The ten columns of the square of `a`: the products of two different limbs once, doubled, then
the square of a limb. -/
def sqrCols (o : Ops m α) (a : F5 α) : m (List α) :=
  (List.range 10).mapM fun k => do
    let lo := ((List.range 5).filter fun i => i < k - i ∧ k - i ≤ 4).map fun i => Half.mk false i (k - i)
    let hi := ((List.range 5).filter fun i => i + 1 ≤ k ∧ i < k - 1 - i ∧ k - 1 - i ≤ 4).map fun i =>
      Half.mk true i (k - 1 - i)
    let cr ← colSum o a a (lo ++ hi)
    let cr ← match cr with
      | some c => do let y ← o.add c c; pure (some y)
      | none => pure none
    o.madd (k % 2 == 1) cr (a.get (k / 2)) (a.get (k / 2))

/-- The Montgomery square of the lanes of `a`. -/
def sqrCore (o : Ops m α) (a : F5 α) : m (F5 α) := do
  let t ← sqrCols o a
  reduce o a.l0 t

end

end VG.Impl.P256.X86_64.Ifma
