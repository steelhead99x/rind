import Rind.Spec
open rind.spec

/-!
Known-answer tests of `Rind.Spec`'s transliterations of ChaCha20's encryption,
Poly1305, ChaCha20-Poly1305, HChaCha20, and XChaCha20-Poly1305, which are
trusted: RFC 8439's sections 2.4.2, 2.5.2, and 2.8.2, and
draft-irtf-cfrg-xchacha-03's sections 2.2.1 and A.3.1.
-/

namespace rind.spec.test

/-- The bytes `s` spells in hex. -/
def hex (s : String) : List (BitVec 8) :=
  let d (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toNat - 'a'.toNat + 10
  let rec go : List Char → List (BitVec 8)
    | a :: b :: rest => BitVec.ofNat 8 (16 * d a + d b) :: go rest
    | _ => []
  go s.toList

/-- The bytes of `s`'s ASCII. -/
def ascii (s : String) : List (BitVec 8) := s.toList.map fun c => BitVec.ofNat 8 c.toNat

def sunscreen : List (BitVec 8) :=
  ascii "Ladies and Gentlemen of the class of '99: If I could offer you only one tip for the future, sunscreen would be it."

#guard chacha20.encrypt (hex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f") 1
    (hex "000000000000004a00000000") sunscreen ==
  hex ("6e2e359a2568f98041ba0728dd0d6981e97e7aec1d4360c20a27afccfd9fae0b" ++
    "f91b65c5524733ab8f593dabcd62b3571639d624e65152ab8f530c359f0861d8" ++
    "07ca0dbf500d6a6156a38e088a22b65e52bc514d16ccf806818ce91ab7793736" ++
    "5af90bbf74a35be6b40b8eedf2785e42874d")

#guard poly1305.mac (hex "85d6be7857556d337f4452fe42d506a80103808afb0db2fd4abff6af4149f51b")
    (ascii "Cryptographic Forum Research Group") ==
  hex "a8061dc1305136c6c22b8baf0c0127a9"

def aeadKey := hex "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"
def aeadAad := hex "50515253c0c1c2c3c4c5c6c7"
def aeadCt := hex ("d31a8d34648e60db7b86afbc53ef7ec2a4aded51296e08fea9e2b5a736ee62d63dbea45e8ca9671282" ++
  "fafb69da92728b1a71de0a9e060b2905d6a5b67ecd3b3692ddbd7f2d778b8c9803aee328091b58fab324e4fad675945585" ++
  "808b4831d7bc3ff4def08e4b7a9de576d26586cec64b6116")
def aeadTag := hex "1ae10b594f09e26a7e902ecbd0600691"

#guard chacha20poly1305.seal aeadKey (hex "070000004041424344454647") aeadAad sunscreen == (aeadCt, aeadTag)
#guard chacha20poly1305.open aeadKey (hex "070000004041424344454647") aeadAad aeadCt aeadTag ==
  (sunscreen, true)
#guard chacha20poly1305.open aeadKey (hex "070000004041424344454647") aeadAad aeadCt
  (hex "1ae10b594f09e26a7e902ecbd0600690") == (sunscreen, false)

#guard chacha20.hchacha20 (hex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f")
    (hex "000000090000004a0000000031415927") ==
  hex "82413b4227b27bfed30e42508a877d73a0f9e4d58a74a853c12ec41326d3ecdc"

def xCt := hex ("bd6d179d3e83d43b9576579493c0e939572a1700252bfaccbed2902c21396cbb731c7f1b0b4aa6440bf3a8" ++
  "2f4eda7e39ae64c6708c54c216cb96b72e1213b4522f8c9ba40db5d945b11b69b982c1bb9e3f3fac2bc369488f76b2383565" ++
  "d3fff921f9664c97637da9768812f615c68b13b52e")
def xTag := hex "c0875924c1c7987947deafd8780acf49"

#guard chacha20poly1305.xseal aeadKey (ascii "@ABCDEFGHIJKLMNOPQRSTUVW") aeadAad sunscreen == (xCt, xTag)
#guard chacha20poly1305.xopen aeadKey (ascii "@ABCDEFGHIJKLMNOPQRSTUVW") aeadAad xCt xTag == (sunscreen, true)

end rind.spec.test
