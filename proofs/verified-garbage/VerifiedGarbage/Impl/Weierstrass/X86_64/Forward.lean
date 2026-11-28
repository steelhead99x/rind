module

public import VerifiedGarbage.TCB.X86_64.Isa

/-! Forward known scratch words through registers, invalidating stale entries. -/

@[expose] public section

namespace VG.Impl.Weierstrass.X86_64.Forward
open VG.X86_64

abbrev Cache := List (Int × Reg)

/-- Words stored consecutively from `rs`, starting at scratch offset `o`. -/
def ofStores : List Reg → Nat → Cache
  | [],_ => []
  | r::rs,o => (Int.ofNat o,r)::ofStores rs (o+8)

def lookup (d : Int) : Cache → Option Reg
  | [] => none
  | (o,r)::cs => if d=o then some r else lookup d cs

/-- `none` invalidates the cache, including every memory-writing instruction. -/
def writes (i : Instr) : Option (List Reg) :=
  match i with
  | .mul _ => some [.rax,.rdx]
  | .mulx hi lo _ => some [hi,lo]
  | _ => i.dst.map fun r => [r]

def next (cs : Cache) (i : Instr) : Cache :=
  match writes i with
  | none => []
  | some rs => if rs.contains .rdi then [] else cs.filter fun c => !rs.contains c.2

def instruction (cs : Cache) (i : Instr) : Instr :=
  match i with
  | .mov r (.mem m) =>
    if m.base=.rdi ∧ m.index=none then
      match lookup m.disp cs with
      | some src => .mov r (.reg src)
      | none => i
    else i
  | _ => i

/-- The input cache is a proof obligation of the caller. -/
def block : Cache → List Instr → List Instr
  | _,[] => []
  | cs,i::is => instruction cs i :: block (next cs i) is

end VG.Impl.Weierstrass.X86_64.Forward
