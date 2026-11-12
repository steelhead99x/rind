import Rind.Sha2
open Aeneas.Std rind.spec

/-!
Known-answer tests of `Rind.Sha2`, whose transliteration of FIPS 180-4 is
trusted: its examples of SHA-512, SHA-384, and SHA-512/256 over "abc" and the
896-bit message.
-/

/-- The ASCII bytes of `s`. -/
def asciiU8 (s : String) : List U8 := s.toList.map fun c => ⟨BitVec.ofNat 8 c.toNat⟩

/-- The bytes `s` spells in hex, as numbers. -/
def hexNats (s : String) : List Nat :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List Nat
    | a :: b :: rest => (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

def long := "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"

#guard (sha512 (asciiU8 "abc")).map (·.val) == hexNats
  "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"
#guard (sha512 (asciiU8 long)).map (·.val) == hexNats
  "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909"
#guard (sha384 (asciiU8 "abc")).map (·.val) == hexNats
  "cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed8086072ba1e7cc2358baeca134c825a7"
#guard (sha512_256 (asciiU8 "abc")).map (·.val) == hexNats
  "53048e2681941ef99b2e29b76b4c7dabe4c2d0c634fc6d46e0e2f13107e7af23"
