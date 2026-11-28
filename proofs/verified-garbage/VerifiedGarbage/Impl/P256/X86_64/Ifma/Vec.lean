module

public import VerifiedGarbage.Impl.Rsa.X86_64.CrtIfma

/-!
# P-256 on x86-64 with AVX512_IFMA: straight-line vector code

The field arithmetic of the joint multiplication computes on the four
quadwords (lanes) of `ymm` registers. Its code is written once, over the
operations `Ops` on values of any type in any monad, and read twice:

* as a list of operations (`Op`), each naming the earlier ones whose values
  it takes (`ssa`), for which `alloc` chooses registers: all thirty-two, a
  value that does not fit kept in the working space (at `rdi`) from when its
  register is taken until its next use, the one used furthest ahead first;
* as terms in what the block starts from (`tops`, in the proofs), lane by
  lane: the proofs check that the code computes them, and say what integers
  they are.

Constants are loaded from a table (`Cfg.pool`, at `Cfg.cb`) where they are
used, or are the memory operand of a multiplication.
-/

@[expose] public section

namespace VG.Impl.P256.X86_64.Ifma

open VG VG.X86_64
open VG.Impl.Rsa.X86_64.CrtIfma (vreg at_)

/-- Four quadwords of constants. -/
structure K4 where
  w0 : Nat
  w1 : Nat
  w2 : Nat
  w3 : Nat
  deriving DecidableEq, Repr

/-- The same constant in each lane. -/
def K4.all (w : Nat) : K4 := ⟨w, w, w, w⟩

/-- All ones in the lanes of `m` (bit `k` for lane `k`), zero in the others. -/
def K4.lanes (m : Nat) : K4 :=
  ⟨if m.testBit 0 then 2 ^ 64 - 1 else 0, if m.testBit 1 then 2 ^ 64 - 1 else 0,
    if m.testBit 2 then 2 ^ 64 - 1 else 0, if m.testBit 3 then 2 ^ 64 - 1 else 0⟩

/-- Quadword `k`. -/
def K4.get (c : K4) (k : Nat) : Nat :=
  match k with
  | 0 => c.w0
  | 1 => c.w1
  | 2 => c.w2
  | _ => c.w3

/-- The operations of the code, on values `α` in the monad `m`: quadword by
quadword, but `perm` (`vpermq`'s order) and `blend` (the lanes of `m` from
the second value). `madd h acc a b` is `acc` (zero if none) plus the low
(`h` false) or high 52 bits of the product of the low 52 bits of `a` and
`b`; `andc`'s constants are `2^j - 1`; `slr a n k` is `a` shifted left by
`n` in its 64 bits, then right by `k`; `sel c a b` is `b` where the
quadword of `c` is all ones and `a` where it is zero. -/
structure Ops (m : Type → Type) (α : Type) where
  add : α → α → m α
  sub : α → α → m α
  sll : α → Nat → m α
  srl : α → Nat → m α
  sra : α → Nat → m α
  addc : α → K4 → m α
  andc : α → K4 → m α
  perm : α → Nat → m α
  blend : α → α → Nat → m α
  madd : Bool → Option α → α → α → m α
  maddc : Bool → Option α → α → K4 → m α
  slr : α → Nat → Nat → m α
  sel : α → α → α → m α
  zero : m α
  const : K4 → m α

/-! ## As operations -/

/-- An operation of a block, on the values of earlier ones (by their places);
`reg` is what a register holds when the block starts, `ld` 32 bytes of
memory. -/
inductive Op
  | reg (r : Nat)
  | ld (b : Reg) (d : Nat)
  | add (a b : Nat)
  | sub (a b : Nat)
  | sll (a n : Nat)
  | srl (a n : Nat)
  | sra (a n : Nat)
  | addc (a : Nat) (c : K4)
  | andc (a : Nat) (c : K4)
  | perm (a o : Nat)
  | blend (a b m : Nat)
  | madd (h : Bool) (acc : Option Nat) (a b : Nat)
  | maddc (h : Bool) (acc : Option Nat) (a : Nat) (c : K4)
  | slr (a n k : Nat)
  | sel (c a b : Nat)
  | zero
  | const (c : K4)
  deriving Repr

/-- The values an operation takes. -/
def Op.srcs : Op → List Nat
  | .reg _ | .ld .. | .zero | .const _ => []
  | .add a b | .sub a b | .blend a b _ => [a, b]
  | .sll a _ | .srl a _ | .sra a _ | .addc a _ | .andc a _ | .perm a _ | .slr a _ _ => [a]
  | .sel c a b => [c, a, b]
  | .madd _ (some c) a b => [c, a, b]
  | .madd _ none a b => [a, b]
  | .maddc _ (some c) a _ => [c, a]
  | .maddc _ none a _ => [a]

/-- A block being written: its operations, the last first, and their number. -/
structure Blk where
  n : Nat
  ops : List Op

/-- Writing a block. -/
abbrev B := StateM Blk

def emit (op : Op) : B Nat := modifyGet fun b => (b.n, ⟨b.n + 1, op :: b.ops⟩)

def ssa : Ops B Nat where
  add a b := emit (.add a b)
  sub a b := emit (.sub a b)
  sll a n := emit (.sll a n)
  srl a n := emit (.srl a n)
  sra a n := emit (.sra a n)
  addc a c := emit (.addc a c)
  andc a c := emit (.andc a c)
  perm a o := emit (.perm a o)
  blend a b m := emit (.blend a b m)
  madd h acc a b := emit (.madd h acc a b)
  maddc h acc a c := emit (.maddc h acc a c)
  slr a n k := emit (.slr a n k)
  sel c a b := emit (.sel c a b)
  zero := emit .zero
  const c := emit (.const c)

/-- The operations of a block, in order. -/
def B.ops {α : Type} (b : B α) : List Op := (b.run ⟨0, []⟩).2.ops.reverse

/-! ## Registers -/

/-- Where the code's constants are (`cb`, and `pool`: constant `i` at
`32 i`), and where in the working space it keeps values that have no
register (`sbase`, a multiple of 32: slot `i` at `rdi + sbase + 32 i`). -/
structure Cfg where
  cb : Reg
  pool : List K4
  sbase : Nat

def Cfg.kmem (c : Cfg) (k : K4) : MemOp := at_ c.cb (32 * c.pool.idxOf k)

def Cfg.smem (c : Cfg) (i : Nat) : MemOp := at_ .rdi (c.sbase + 32 * i)

/-- The allocation as it goes: the register of each value that has one, with
the place of its next use; the slot of each value that was stored; the free
registers; the number of slots used; and the instructions, the last first. -/
structure AS where
  reg : List (Nat × Nat × Nat)
  slot : List (Nat × Nat)
  free : List Nat
  nslots : Nat
  out : List Instr
  /-- The register each value is wanted in, if it is free when the value is made. -/
  want : List (Nat × Nat) := []

def find (l : List (Nat × Nat)) (v : Nat) : Option Nat := (l.find? fun e => e.1 == v).map (·.2)

/-- The register of `v`, if it has one. -/
def AS.regOf (a : AS) (v : Nat) : Option Nat := (a.reg.find? fun e => e.1 == v).map (·.2.1)

def AS.drop (a : AS) (v : Nat) : AS := { a with reg := a.reg.filter fun e => !(e.1 == v) }

/-- The place of the block's end, for the next use of a value it leaves. -/
def atEnd : Nat := 1000000

/-- For each operation, from the last back: the place of the first use of its
value, and of the next use after it of each value it takes (as `Op.srcs`
lists them). `last` holds the next use of each value, the first entry of a
value being the one that counts. -/
def annGo : List (Op × Nat) → List (Nat × Nat) → List (Option Nat × List (Option Nat)) →
    List (Option Nat × List (Option Nat))
  | [], _, acc => acc
  | (op, idx) :: rest, last, acc =>
    annGo rest (op.srcs.map (fun s => (s, idx)) ++ last) ((find last idx, op.srcs.map (find last)) :: acc)

/-- The next uses of the operations' values (`annGo`), in order. -/
def annOf (ops : List Op) (outs : List Nat) : List (Option Nat × List (Option Nat)) :=
  annGo ops.zipIdx.reverse (outs.map fun v => (v, atEnd)) []

def AS.emit (a : AS) (i : Instr) : AS := { a with out := i :: a.out }

/-- Take the register of `v`, storing it if it is not yet stored. -/
def AS.spill (c : Cfg) (a : AS) (v : Nat) : AS × Nat :=
  let r := (a.regOf v).getD 0
  let a := a.drop v
  if (find a.slot v).isNone then
    ({ a with slot := (v, a.nslots) :: a.slot, nslots := a.nslots + 1,
              out := .evStore (c.smem a.nslots) (vreg r) :: a.out }, r)
  else (a, r)

/-- A register: the highest free one, else that of the value (not in `keep`)
used furthest ahead. -/
def AS.getReg (c : Cfg) (a : AS) (keep : List Nat) : AS × Nat :=
  match a.free with
  | f :: fs =>
    let r := fs.foldl max f
    ({ a with free := a.free.erase r }, r)
  | [] =>
    let lt (x y : Nat × Nat × Nat) : Bool := x.2.2 < y.2.2 || (x.2.2 == y.2.2 && x.1 < y.1)
    let cand := a.reg.filter fun e => !keep.contains e.1
    let best := cand.foldl (fun b e => if lt b e then e else b) (cand.headD (0, 0, 0))
    a.spill c best.1

/-- A register for the value `v`: the one it is wanted in, if that is free, else `getReg`'s. -/
def AS.getRegFor (c : Cfg) (a : AS) (v : Nat) (keep : List Nat) : AS × Nat :=
  match find a.want v with
  | some r => if a.free.contains r then ({ a with free := a.free.erase r }, r) else a.getReg c keep
  | none => a.getReg c keep

/-- `v` in a register, loaded from its slot if it has none; its next use is at `idx`. -/
def AS.ensure (c : Cfg) (a : AS) (v idx : Nat) (keep : List Nat) : AS :=
  match a.regOf v with
  | some _ => a
  | none =>
    let (a, r) := a.getReg c keep
    { a with reg := (v, r, idx) :: a.reg, out := .evLoad (vreg r) (c.smem ((find a.slot v).getD 0)) :: a.out }

/-- The register of `v`, which has one. -/
def AS.r (a : AS) (v : Nat) : VReg := vreg ((a.regOf v).getD 0)

/-- A constant in a register of its own: the one the value `v` is wanted in, if it is free. -/
def AS.const (c : Cfg) (a : AS) (k : K4) (keep : List Nat) (v : Nat := atEnd) : AS × Nat :=
  let (a, r) := a.getRegFor c v keep
  (a.emit (.evLoad (vreg r) (c.kmem k)), r)

/-- Free the registers of the values `vs`. -/
def AS.release (a : AS) (vs : List Nat) : AS :=
  vs.foldl (fun a v => match a.regOf v with
    | some r => { a.drop v with free := r :: a.free }
    | none => a) a

/-- The register for the result of an operation that writes over `acc`:
`acc`'s own if this is its last use (and it is not also `rest`'s), else a
copy. -/
def AS.over (c : Cfg) (a : AS) (acc : Nat) (keep dying rest : List Nat) (v : Nat := atEnd) : AS × Nat × List Nat :=
  if dying.contains acc ∧ ¬ rest.contains acc then
    let r := (a.regOf acc).getD 0
    (a.drop acc, r, dying.erase acc)
  else
    let (a, r) := a.getRegFor c v keep
    (a.emit (.eop (.vmovdqa64 (vreg r) (a.r acc))), r, dying)

/-- One operation, numbered `idx`, with the next uses `ann` of its value and
of the values it takes: these into registers, then its instructions. -/
def AS.step (c : Cfg) (a : AS) (op : Op) (idx : Nat) (ann : Option Nat × List (Option Nat)) : AS :=
  let srcs := op.srcs
  let a := srcs.foldl (fun a s => a.ensure c s idx srcs) a
  let nexts := srcs.zip ann.2
  let dying := (nexts.filter fun e => e.2.isNone).map (·.1) |>.eraseDups
  -- the result in `r`, and the next uses of the values taken
  let bind (a : AS) (r : Nat) : AS :=
    let reg := a.reg.map fun e => match nexts.find? fun x => x.1 == e.1 with
      | some x => (e.1, e.2.1, x.2.getD atEnd)
      | none => e
    match ann.1 with
    | some n => { a with reg := (idx, r, n) :: reg }
    | none => { a with reg := reg, free := r :: a.free }
  -- an operation of its sources' registers into any register
  let plain (mk : VReg → Instr) : AS :=
    let a' := a.release dying
    let (a', r) := a'.getRegFor c idx []
    bind (a'.emit (mk (vreg r))) r
  match op with
  | .reg _ => a
  | .ld b d => plain fun r => .evLoad r (at_ b d)
  | .const k => plain fun r => .evLoad r (c.kmem k)
  | .zero => plain fun r => .eop (.bin .vpxorq r r r)
  | .slr x n k =>
    let a' := a.release dying
    let (a', r) := a'.getRegFor c idx []
    let a' := a'.emit (.eop (.shift .vpsllq (vreg r) (a.r x) (BitVec.ofNat 8 n)))
    bind (a'.emit (.eop (.shift .vpsrlq (vreg r) (vreg r) (BitVec.ofNat 8 k)))) r
  | .sel m x y =>
    let (a, r, dying) := a.over c x srcs dying [y, m] idx
    let a := a.emit (.eop (.vpternlogq (vreg r) (a.r y) (a.r m) 0xD8))
    bind (a.release dying) r
  | .add x y => plain fun r => .eop (.bin .vpaddq r (a.r x) (a.r y))
  | .sub x y => plain fun r => .eop (.bin .vpsubq r (a.r x) (a.r y))
  | .sll x n => plain fun r => .eop (.shift .vpsllq r (a.r x) (BitVec.ofNat 8 n))
  | .srl x n => plain fun r => .eop (.shift .vpsrlq r (a.r x) (BitVec.ofNat 8 n))
  | .sra x n => plain fun r => .eop (.vpsraq r (a.r x) (BitVec.ofNat 8 n))
  | .perm x o => plain fun r => .eop (.vpermq r (a.r x) (BitVec.ofNat 8 o))
  | .addc x k =>
    let (a, t) := a.const c k srcs idx
    let a := a.emit (.eop (.bin .vpaddq (vreg t) (a.r x) (vreg t)))
    bind (a.release dying) t
  | .andc x k =>
    let (a, t) := a.const c k srcs idx
    let a := a.emit (.eop (.bin .vpandq (vreg t) (a.r x) (vreg t)))
    bind (a.release dying) t
  | .blend x y m =>
    let (a, t) := a.const c (K4.lanes m) srcs
    let (a, r, dying) := a.over c x srcs dying [y] idx
    let a := a.emit (.eop (.vpternlogq (vreg r) (a.r y) (vreg t) 0xD8))
    bind ({ a with free := t :: a.free }.release dying) r
  | .madd h acc x y =>
    let (a, r, dying) := match acc with
      | some z => a.over c z srcs dying [x, y] idx
      | none =>
        let (a, r) := a.getRegFor c idx srcs
        (a.emit (.eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))), r, dying)
    let a := a.emit (.eop (.vpmadd52 h (vreg r) (a.r x) (a.r y)))
    bind (a.release dying) r
  | .maddc h acc x k =>
    let (a, r, dying) := match acc with
      | some z => a.over c z srcs dying [x] idx
      | none =>
        let (a, r) := a.getRegFor c idx srcs
        (a.emit (.eop (.bin .vpxorq (vreg r) (vreg r) (vreg r))), r, dying)
    let a := a.emit (.evMadd52Load h (vreg r) (a.r x) (c.kmem k))
    bind (a.release dying) r

/-- The moves `ms` (register to register, all at once), `fuel` of them at
most: one whose destination no other reads, else the first's source into
`tmp`. -/
def pmove (tmp : Nat) : Nat → List (Nat × Nat) → List Instr
  | 0, _ => []
  | fuel + 1, ms =>
    match ms.find? fun e => !(ms.any fun e' => e'.2 == e.1) with
    | some e => .eop (.vmovdqa64 (vreg e.1) (vreg e.2)) :: pmove tmp fuel (ms.filter fun e' => !(e'.1 == e.1))
    | none =>
      match ms with
      | [] => []
      | e :: _ =>
        .eop (.vmovdqa64 (vreg tmp) (vreg e.2)) ::
          pmove tmp fuel (ms.map fun e' => if e'.2 == e.2 then (e'.1, tmp) else e')

/-- Where a value is: in a register, or in a slot of the working space. -/
inductive Loc
  | reg (r : Nat)
  | slot (i : Nat)
  deriving DecidableEq, Repr

/-- Where `v` is: its register, else its slot. -/
def AS.loc (a : AS) (v : Nat) : Loc :=
  match a.regOf v with
  | some r => .reg r
  | none => .slot ((find a.slot v).getD 0)

/-- The operations from the one numbered `idx`, with their next uses, a piece at a time. -/
def allocGo (c : Cfg) (cuts : List (Nat × List Nat)) :
    List (Op × Option Nat × List (Option Nat)) → Nat → AS × List (List Instr) × List (List Loc) →
      AS × List (List Instr) × List (List Loc)
  | [], _, st => st
  | (op, ann) :: rest, idx, (a, ps, ls) =>
    match cuts.find? fun e => e.1 == idx with
    | some e =>
      let a' : AS := { a with slot := a.slot.filter (fun x => (a.regOf x.1).isNone), out := [] }
      allocGo c cuts rest (idx + 1) (a'.step c op idx ann, a.out.reverse :: ps, e.2.map a.loc :: ls)
    | none => allocGo c cuts rest (idx + 1) (a.step c op idx ann, ps, ls)

/-- The value an operation writes over, if it is that value's last use: the operation's result is
then in its register. -/
def Op.over : Op → Option Nat
  | .madd _ (some z) _ _ | .maddc _ (some z) _ _ => some z
  | .sel _ x _ | .blend x _ _ => some x
  | _ => none

/-- The registers the values are wanted in: those of `outs`, and for a value an operation writes
over, the register its result is wanted in. -/
def wants (ops : List Op) (outs : List (Nat × Nat)) : List (Nat × Nat) :=
  ops.zipIdx.reverse.foldl (fun w (op, idx) => match find w idx, op.over with
    | some r, some z => if (find w z).isNone then (z, r) :: w else w
    | _, _ => w) outs

/-- The code of a block, in pieces: each value of `outs` is left in the
register given with it; a new piece starts before each operation of `cuts`,
and with the pieces come the places, there, of the values given with it (a
value that has a register then is no longer taken to be in its slot, so that
each has one place). -/
def allocCuts (c : Cfg) (ops : List Op) (cuts : List (Nat × List Nat)) (outs : List (Nat × Nat)) :
    List (List Instr) × List (List Loc) :=
  let ov := outs.map (·.1)
  let ann := annOf ops ov
  let oa := ops.zip ann
  -- what the registers hold when the block starts, where it is used
  let live : List (Nat × Nat × Nat) := oa.zipIdx.filterMap fun ((op, an), idx) => match op, an.1 with
    | .reg r, some n => some (idx, r, n)
    | _, _ => none
  let a : AS := ⟨live, [], (List.range 32).filter fun r => !(live.any fun e => e.2.1 == r), 0, [], wants ops outs⟩
  let (a, ps, ls) := allocGo c cuts oa 0 (a, [], [])
  let a := outs.foldl (fun a o => a.ensure c o.1 atEnd ov) a
  let ms := outs.filterMap fun o =>
    let r := (a.regOf o.1).getD 0
    if r == o.2 then none else some (o.2, r)
  let used := outs.map (·.2) ++ outs.map fun o => (a.regOf o.1).getD 0
  let tmp := ((List.range 32).reverse.find? fun r => !used.contains r).getD 31
  (((a.out.reverse ++ pmove tmp (2 * ms.length + 1) ms) :: ps).reverse, ls.reverse)

/-- The code of a block in one piece. -/
def alloc (c : Cfg) (ops : List Op) (outs : List (Nat × Nat)) : List Instr :=
  (allocCuts c ops [] outs).1.flatten

end VG.Impl.P256.X86_64.Ifma
