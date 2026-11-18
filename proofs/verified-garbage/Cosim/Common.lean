/-!
# What the cosimulation of every target shares

The random source, the layout the runner (`admin/vg-cosim-runner.rs`) maps,
and the stream of cases it reads. Each case is an instruction's machine code
and, for each of a number of random states, the state it starts in and the
one VG's model says it ends in, which the runner compares with what the CPU
leaves.
-/

namespace Cosim

/-- Lists as the nondeterminism monad, so a parser can say "each of these". -/
instance : Monad List where
  pure x := [x]
  bind l f := l.flatMap f

/-- SplitMix64 (Steele, Lea and Flood, "Fast splittable pseudorandom number
generators", 2014): a seed gives the same cases on every run. -/
abbrev Gen := StateM UInt64

def u64 : Gen UInt64 := modifyGet fun (s : UInt64) =>
  let s : UInt64 := s + 0x9E3779B97F4A7C15
  let z : UInt64 := (s ^^^ (s >>> (30 : UInt64))) * 0xBF58476D1CE4E5B9
  let z : UInt64 := (z ^^^ (z >>> (27 : UInt64))) * 0x94D049BB133111EB
  (z ^^^ (z >>> (31 : UInt64)), s)

/-- A number below `n` (`n > 0`). -/
def below (n : Nat) : Gen Nat := return (← u64).toNat % n

def bool : Gen Bool := return (← u64) &&& 1 == 1

/-- A 64-bit value, weighted toward the edges where semantics go wrong:
zero, all ones, one bit, the sign boundaries, and values of 8, 16 and 32
bits, each with probability 1/16, and otherwise uniform. -/
def val64 : Gen (BitVec 64) := do
  let x ← u64
  let r ← u64
  let v : UInt64 := match (← below 16) with
    | 0 => 0
    | 1 => 0xFFFFFFFFFFFFFFFF
    | 2 => 1 <<< (r % 64)
    | 3 => ~~~(1 <<< (r % 64))
    | 4 => 0x7FFFFFFFFFFFFFFF + (r % 3)
    | 5 => x &&& 0xFF
    | 6 => x &&& 0xFFFF
    | 7 => x &&& 0xFFFFFFFF
    | 8 => x ||| 0xFFFFFFFF00000000
    | _ => x
  return BitVec.ofNat 64 v.toNat

/-- A value of `w` bits, from 64-bit words of `val64` (lanes of 8 to 32 bits
take a word's edges as a whole: each word is an edge or uniform). -/
def bits (w : Nat) : Gen (BitVec w) := do
  let mut v := 0
  for i in [0:(w + 63) / 64] do
    v := v ||| ((← val64).toNat <<< (64 * i))
  return BitVec.ofNat w v

def bytes (n : Nat) : Gen ByteArray := do
  let mut b := ByteArray.emptyWithCapacity n
  for _ in [0:n] do
    b := b.push (← u64).toUInt8
  return b

/-- The runner maps its code at `codeBase`, puts each case's instruction at
`insnAddr`, and its target at `targetAddr`: a branch goes there when taken,
and a call reaches the `ret` there. -/
def codeBase : Nat := 0x1000000000
def insnAddr : Nat := codeBase + 0x1000
def targetAddr : Nat := insnAddr + 0x100

/-- The data the runner maps, at `dataBase`, `dataLen` bytes of it, all
compared after each case. The model may access only the middle half,
`window`, so a CPU access the model does not make shows as a changed byte
outside it. -/
def dataBase : Nat := 0x2000000000
def dataLen : Nat := 2048
def windowBase : Nat := dataBase + 512
def windowLen : Nat := 1024

/-- What a case runs: `insn` falls through, `branch` reports whether it went
to `targetAddr`, and `call` returns from the `ret` there. -/
inductive Kind | insn | branch | call
  deriving BEq, Repr

def Kind.byte : Kind → UInt8
  | .insn => 0
  | .branch => 1
  | .call => 2

def pushU16 (b : ByteArray) (v : Nat) : ByteArray :=
  (b.push (v % 256).toUInt8).push ((v / 256) % 256).toUInt8

def pushU32 (b : ByteArray) (v : Nat) : ByteArray :=
  pushU16 (pushU16 b (v % 65536)) (v / 65536)

/-- `v`, little-endian, in `n` bytes. -/
def pushLE (b : ByteArray) (v : Nat) (n : Nat) : ByteArray := Id.run do
  let mut b := b
  let mut v := v
  for _ in [0:n] do
    b := b.push (v % 256).toUInt8
    v := v / 256
  return b

def pushU64 (b : ByteArray) (v : UInt64) : ByteArray := Id.run do
  let mut b := b
  for i in [0:8] do
    b := b.push (v >>> (8 * i).toUInt64).toUInt8
  return b

/-- `v`, little-endian, a 64-bit word at a time. -/
def pushBV {w : Nat} (b : ByteArray) (v : BitVec w) : ByteArray :=
  if w % 64 == 0 then Id.run do
    let mut b := b
    let n := v.toNat
    for i in [0:w / 64] do
      b := pushU64 b (n >>> (64 * i)).toUInt64
    return b
  else pushLE b v.toNat (w / 8)

/-- A block of the stream: an instruction and its cases, each the start
state, the end state, the branch outcome, and a byte of the end state's
flags that are defined (a flag the model leaves undefined is not compared).
`text` is what the runner prints with a mismatch. -/
structure Block where
  text : String
  kind : Kind
  code : ByteArray
  cases : Array ByteArray

/-- The stream's header: its magic, `arch` (0 for x86_64, 1 for aarch64),
and the size of a state, which the runner checks against its own. -/
def header (arch : UInt8) (stateLen : Nat) : ByteArray :=
  pushU32 ("VGCS".toUTF8.push arch) stateLen

def Block.encode (k : Block) : ByteArray := Id.run do
  let t := k.text.toUTF8
  let mut b := (ByteArray.empty.push 1)
  b := pushU16 b t.size ++ t
  b := b.push k.kind.byte
  b := pushU16 b k.code.size ++ k.code
  b := pushU32 b k.cases.size
  for c in k.cases do
    b := b ++ c
  return b

/-- The end of the stream. -/
def trailer : ByteArray := ByteArray.empty.push 0

/-- `s`, split at `sep`, each part trimmed. -/
def fields (s : String) (sep : String) : List String :=
  (s.splitOn sep).map (·.trimAscii.toString)

/-- A decimal integer, with an optional leading minus. -/
def parseInt (s : String) : Option Int :=
  if s.startsWith "-" then (s.drop 1).toString.toNat?.map (- ·) else s.toNat?

/-- Hex bytes, two digits each. -/
def parseHex (s : String) : Option ByteArray := Id.run do
  let cs := s.toList.toArray
  if cs.size % 2 != 0 then return none
  let digit (c : Char) : Option Nat :=
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10) else none
  let mut b := ByteArray.emptyWithCapacity (cs.size / 2)
  for i in [0:cs.size / 2] do
    match digit cs[2 * i]!, digit cs[2 * i + 1]! with
    | some h, some l => b := b.push (16 * h + l).toUInt8
    | _, _ => return none
  return some b

end Cosim
