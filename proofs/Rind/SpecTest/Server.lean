import Rind.S2nSha256
import Rind.S2nSha512
import Rind.Sha3
import Rind.SymCrypt.MlKem
import Rind.S2nChaCha20Poly1305
import Rind.AesKw
import Rind.SpecTest.Rsa
import Rind.SpecTest.Gcm
import Rind.SpecTest.Ed25519

/-!
# The spec server

The executable `admin/spec-tests` drives: it reads one request a line on
stdin, a spec's name and its inputs, and answers each with the spec's output
on one line. Byte strings are lowercase hex, `-` for none, and numbers
decimal. A spec that does not run is run through the twin `Rind.SpecTest`
proves equal to it, and an opaque constant through the stand-in
`Rind.SpecTest.Upstream` gives it. An answer the spec does not define, such
as a point off the curve, is a word saying why; a request this cannot parse
answers `error`, which fails the driver.
-/

open Aeneas Aeneas.Std rind.spec

namespace rind.spec.server

/-- The bytes a hex string spells, `-` for none. -/
def unhex (s : String) : Except String (List Byte) := do
  if s == "-" then return []
  let digit (c : Char) : Except String Nat :=
    if '0' ≤ c ∧ c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c ∧ c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else throw s!"not hex: {s}"
  let rec go : List Char → Except String (List Byte)
    | a :: b :: rest => do
      let hi ← digit a
      let lo ← digit b
      return BitVec.ofNat 8 (16 * hi + lo) :: (← go rest)
    | [] => pure []
    | [_] => throw s!"odd hex: {s}"
  go s.toList

/-- `bytes` as hex, `-` for none. -/
def hex (bytes : List Byte) : String :=
  if bytes.isEmpty then "-"
  else
    let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
    String.ofList (bytes.flatMap fun b => [digit (b.toNat / 16), digit (b.toNat % 16)])

def nat (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => pure n
  | none => throw s!"not a number: {s}"

/-- A big-endian number. -/
def beNum (bytes : List Byte) : Nat := bytes.foldl (fun a b => 256 * a + b.toNat) 0

/-- `n` as `k` big-endian bytes. -/
def beBytesOf (k n : Nat) : List Byte := (List.range k).reverse.map fun i => BitVec.ofNat 8 (n / 256 ^ i)

def toU8 (b : List Byte) : List U8 := b.map fun x => ⟨x⟩
def ofU8 (b : List U8) : List Byte := b.map (·.bv)

def sha384B (m : List Byte) : List Byte := ofU8 (sha384 (toU8 m))
def sha512B (m : List Byte) : List Byte := ofU8 (sha512 (toU8 m))

/-- A hash by name, and its block length. -/
def hashOf : String → Except String ((List Byte → List Byte) × Nat × Nat)
  | "sha1" => pure (sha1.hash, 64, 20)
  | "sha256" => pure (sha256.hash, 64, 32)
  | "sha384" => pure (sha384B, 128, 48)
  | "sha512" => pure (sha512B, 128, 64)
  | h => throw s!"no hash {h}"

/-- SHA-256 over s2n-bignum's block function: FIPS 180-4's padding, its
words, and `sha256_hash_blocks` from the initial value. -/
def sha256S2n (m : List Byte) : List Byte :=
  let bs := blocks 64 (pad m)
  (s2n.hashBlocks (fun i => words bs[i]!) sha256.H0 bs.length).flatMap BitVec.toBEBytes

/-- The SHA-512 family over s2n-bignum's block function, from `iv`. -/
def sha512S2n (iv : List U64) (len : Nat) (m : List Byte) : List Byte :=
  let p := sha512Pad (toU8 m)
  let n := p.length / 128
  let h := s2n.sha512.hashBlocks (fun i => (blockWords ((p.drop (128 * i)).take 128)).map (·.bv))
    (iv.map (·.bv)) n
  (h.flatMap BitVec.toBEBytes).take len

/-- A 32-bit counter, as its decimal value. -/
def word (s : String) : Except String (BitVec 32) := do
  let n ← nat s
  if n < 2 ^ 32 then pure (BitVec.ofNat 32 n) else throw s!"not a 32-bit counter: {s}"

def aesAlg (key : List Byte) : Except String vale.Algorithm :=
  match key.length with
  | 16 => pure .AES_128
  | 24 => pure .AES_192
  | 32 => pure .AES_256
  | n => throw s!"no AES key of {n} bytes"

/-- `b`, refused unless it is `n` bytes: the models index fixed-length
inputs, such as a ChaCha20 key's eight words, without checking. -/
def sized (n : Nat) (b : List Byte) : Except String (List Byte) :=
  if b.length = n then pure b else throw s!"{b.length} bytes, not {n}"

/-- The bytes of hex `s`, refused unless they are `n`. -/
def unhexN (n : Nat) (s : String) : Except String (List Byte) := do sized n (← unhex s)

def opt (o : Option (List Byte)) : String := match o with
  | some b => hex b
  | none => "none"

def bool (b : Bool) : String := if b then "1" else "0"

/-! ## The NIST curves -/

structure Curve where
  p : Nat
  n : Nat
  b : Nat
  G : nist.Point
  len : Nat
  hash : List Byte → List Byte

def curveOf : String → Except String Curve
  | "p256" => pure ⟨p256, n256, b256, p256G, 32, sha256.hash⟩
  | "p384" => pure ⟨p384, n384, b384, p384G, 48, sha384B⟩
  | c => throw s!"no curve {c}"

def point (C : Curve) : nist.Point → String
  | some (x, y) => s!"{hex (beBytesOf C.len x)} {hex (beBytesOf C.len y)}"
  | none => "infinity"

/-! ## ML-KEM -/

open Spec.MLKEM in
def paramOf : String → Except String ParameterSet
  | "512" => pure .ML_KEM_512
  | "768" => pure .ML_KEM_768
  | "1024" => pure .ML_KEM_1024
  | s => throw s!"no ML-KEM-{s}"

def vec (n : Nat) (b : List Byte) : Except String (Spec.𝔹 n) :=
  if h : b.length = n then pure ⟨b.toArray, by simpa using h⟩
  else throw s!"{b.length} bytes, not {n}"

/-! ## Requests -/

def answer (args : List String) : Except String String := do
  match args with
  | ["sha1", m] => return hex (sha1.hash (← unhex m))
  | ["sha256", m] => return hex (sha256.hash (← unhex m))
  | ["sha256-s2n", m] => return hex (sha256S2n (← unhex m))
  | ["sha384", m] => return hex (sha384B (← unhex m))
  | ["sha384-s2n", m] => return hex (sha512S2n sha384Iv 48 (← unhex m))
  | ["sha512", m] => return hex (sha512B (← unhex m))
  | ["sha512-s2n", m] => return hex (sha512S2n sha512Iv 64 (← unhex m))
  | ["sha512_256", m] => return hex (ofU8 (sha512_256 (toU8 (← unhex m))))
  | ["sha512_256-s2n", m] => return hex (sha512S2n sha512_256Iv 32 (← unhex m))
  | ["sha3_256", m] => return hex (sha3_256 (← unhex m))
  | ["sha3_384", m] => return hex (sha3_384 (← unhex m))
  | ["sha3_512", m] => return hex (sha3_512 (← unhex m))
  | ["shake128", m, n] => return hex (shake128 (← unhex m) (← nat n))
  | ["shake256", m, n] => return hex (shake256 (← unhex m) (← nat n))
  | ["sha3_256-symcrypt", m] => return hex (Spec.SHA3.sha3_256 (toB (← unhex m))).toList
  | ["shake128-symcrypt", m, n] => return hex (Spec.SHA3.shake128 (toB (← unhex m)) (← nat n)).toList
  | ["hmac", h, k, m] =>
    let (H, B, _) ← hashOf h
    return hex (hmac H B (← unhex k) (← unhex m))
  | ["hkdf", h, ikm, salt, info, L] =>
    let (H, B, len) ← hashOf h
    let prk := hkdfExtract (hmac H B) (← unhex salt) (← unhex ikm)
    let (info, L) := (← unhex info, ← nat L)
    -- RFC 5869 bounds L at 255 blocks, past which the spec's one-byte
    -- counter wraps.
    if L > 255 * len then return "none"
    return hex (hkdfExpand (hmac H B) len prk info L)
  | ["pbkdf2", h, pw, salt, c, L] =>
    let (H, B, len) ← hashOf h
    let (pw, salt, c, L) := (← unhex pw, ← unhex salt, ← nat c, ← nat L)
    -- RFC 8018 takes a positive count, and the spec would answer 0 as 1.
    if c = 0 then return "none"
    return hex (pbkdf2 (hmac H B) len pw salt c L)
  -- ChaCha20 on the blocks RFC 8439's 32-bit counter covers from `ctr`,
  -- the theorems' domain, `none` past them.
  | ["chacha20", k, ctr, n, m] =>
    let (k, ctr, n, m) := (← unhexN 32 k, ← word ctr, ← unhexN 12 n, ← unhex m)
    if ctr.toNat + (m.length + 63) / 64 > 2 ^ 32 then return "none"
    return hex (chacha20.encrypt k ctr n m)
  | ["chacha20-s2n", k, ctr, n, m] =>
    let (k, ctr, n, m) := (← unhexN 32 k, ← word ctr, ← unhexN 12 n, ← unhex m)
    if ctr.toNat + (m.length + 63) / 64 > 2 ^ 32 then return "none"
    return hex (s2n.chacha20Encrypt k ctr n m)
  | ["hchacha20", k, n] => return hex (chacha20.hchacha20 (← unhexN 32 k) (← unhexN 16 n))
  | ["poly1305", k, m] => return hex (poly1305.mac (← unhexN 32 k) (← unhex m))
  | ["poly1305-s2n", k, m] => return hex (s2n.poly1305Mac (← unhexN 32 k) (← unhex m))
  | ["chacha20poly1305-seal", k, n, a, m] =>
    let (c, t) := chacha20poly1305.seal (← unhexN 32 k) (← unhexN 12 n) (← unhex a) (← unhex m)
    return s!"{hex c} {hex t}"
  | ["chacha20poly1305-open", k, n, a, c, t] =>
    let (m, ok) := chacha20poly1305.open (← unhexN 32 k) (← unhexN 12 n) (← unhex a) (← unhex c) (← unhex t)
    return s!"{hex m} {bool ok}"
  | ["chacha20poly1305-s2n-seal", k, n, a, m] =>
    let (c, t) := s2n.chacha20Poly1305Seal (← unhexN 32 k) (← unhexN 12 n) (← unhex a) (← unhex m)
    return s!"{hex c} {hex t}"
  | ["chacha20poly1305-s2n-open", k, n, a, c, t] =>
    let (m, ok) := s2n.chacha20Poly1305Open (← unhexN 32 k) (← unhexN 12 n) (← unhex a) (← unhex c) (← unhex t)
    return s!"{hex m} {bool ok}"
  | ["xchacha20poly1305-seal", k, n, a, m] =>
    let (c, t) := chacha20poly1305.xseal (← unhexN 32 k) (← unhexN 24 n) (← unhex a) (← unhex m)
    return s!"{hex c} {hex t}"
  | ["xchacha20poly1305-open", k, n, a, c, t] =>
    let (m, ok) := chacha20poly1305.xopen (← unhexN 32 k) (← unhexN 24 n) (← unhex a) (← unhex c) (← unhex t)
    return s!"{hex m} {bool ok}"
  | ["hp-chacha20", k, s] => return hex (chacha20.headerProtectionMask (← unhexN 32 k) (← unhexN 16 s))
  | ["hp-aes", k, s] =>
    let k ← unhex k
    return hex (vale.aesHeaderMask (← aesAlg k) k (← unhexN 16 s))
  | ["aes-encrypt", k, b] =>
    let k ← unhex k
    return hex (vale.aesBlock (← aesAlg k) k (← unhexN 16 b))
  | ["aes-decrypt", k, b] =>
    let k ← unhex k
    return hex (vale.aesBlockDecrypt (← aesAlg k) k (← unhexN 16 b))
  | ["aes-gcm-seal", k, iv, a, m] =>
    let k ← unhex k
    let (c, t) := vale.gcmEncryptC (← aesAlg k) k (← unhex iv) (← unhex m) (← unhex a)
    return s!"{hex c} {hex t}"
  | ["aes-gcm-open", k, iv, a, c, t] =>
    let k ← unhex k
    let (m, ok) := vale.gcmDecryptC (← aesAlg k) k (← unhex iv) (← unhex c) (← unhex a) (← unhex t)
    return s!"{hex m} {bool ok}"
  | ["aes-ctr", k, bits, t0, d] =>
    let (k, bits, t0, d) := (← unhex k, ← nat bits, ← unhexN 16 t0, ← unhex d)
    let alg ← aesAlg k
    -- The theorems' domain: a width from 1 to 128 bits, and no more blocks
    -- than the counter's 2^bits, past which the spec would reuse them.
    if bits = 0 ∨ bits > 128 then return "none"
    if 2 ^ bits < (d.length + 15) / 16 then return "none"
    return hex (vale.aesCtr alg k bits t0 d)
  | ["aes-cbc-encrypt", k, iv, m] =>
    let k ← unhex k
    return hex (vale.cbcEncrypt (← aesAlg k) k (← unhexN 16 iv) (vale.pkcs7Pad (← unhex m)))
  | ["aes-cbc-decrypt", k, iv, c] =>
    let k ← unhex k
    let (iv, c) := (← unhexN 16 iv, ← unhex c)
    -- The spec drops a partial last block, which rind's theorems refuse.
    if c.length % 16 ≠ 0 then return "none"
    return opt (vale.pkcs7Unpad (vale.cbcDecrypt (← aesAlg k) k iv c))
  -- Key wrap on the lengths `AesKek`'s theorems pass the specs, `none`
  -- outside them: KW wraps two semiblocks or more and unwraps three or more,
  -- KWP wraps a byte or more and unwraps two semiblocks or more.
  | ["aes-kw-wrap", k, m] =>
    let (k, m) := (← unhex k, ← unhex m)
    let alg ← aesAlg k
    if m.length < 16 ∨ m.length % 8 ≠ 0 then return "none"
    return hex (vale.kwAE alg k m)
  | ["aes-kw-unwrap", k, c] =>
    let (k, c) := (← unhex k, ← unhex c)
    let alg ← aesAlg k
    if c.length < 24 ∨ c.length % 8 ≠ 0 then return "none"
    return opt (vale.kwAD alg k c)
  | ["aes-kwp-wrap", k, m] =>
    let (k, m) := (← unhex k, ← unhex m)
    let alg ← aesAlg k
    if m.length < 1 then return "none"
    return hex (vale.kwpAE alg k m)
  | ["aes-kwp-unwrap", k, c] =>
    let (k, c) := (← unhex k, ← unhex c)
    let alg ← aesAlg k
    if c.length < 16 ∨ c.length % 8 ≠ 0 then return "none"
    return opt (vale.kwpAD alg k c)
  | ["ec-mul", c, d, qx, qy] =>
    let C ← curveOf c
    let (d, Q) := (beNum (← unhex d), some (beNum (← unhex qx), beNum (← unhex qy)))
    if nist.OnCurve C.p C.b Q then return point C (nist.powC C.p Q d)
    else return "offcurve"
  | ["ec-base", c, d] =>
    let C ← curveOf c
    return point C (nist.powC C.p C.G (beNum (← unhex d)))
  | ["ecdsa-sign", c, d, k, e] =>
    let C ← curveOf c
    match nist.ecdsaSignC C.p C.n C.G (beNum (← unhex d)) (beNum (← unhex k)) (beNum (← unhex e)) with
    | some (r, s) => return s!"{hex (beBytesOf C.len r)} {hex (beBytesOf C.len s)}"
    | none => return "none"
  | ["ecdsa-verify", c, qx, qy, m, r, s] =>
    let C ← curveOf c
    let Q := some (beNum (← unhex qx), beNum (← unhex qy))
    let (m, r, s) := (← unhex m, beNum (← unhex r), beNum (← unhex s))
    if nist.OnCurve C.p C.b Q then
      return bool (nist.ecdsaVerifiesC C.p C.n C.G Q (beNum (C.hash m)) r s)
    else return "offcurve"
  | ["ed25519-public", seed] =>
    return hex (ofU8 (publicKeyWith upstream.edPow (toU8 (← unhex seed))))
  | ["ed25519-sign", seed, m] =>
    return hex (ofU8 (signWith upstream.edPow (toU8 (← unhex seed)) (toU8 (← unhex m))))
  | ["ed25519-verify", key, m, sig] =>
    let (key, m, sig) := (← unhex key, ← unhex m, ← unhex sig)
    if key.length ≠ 32 then return "badkey"
    match decodeC (leNat (toU8 key)) with
    | some A => return bool (verifiesWith upstream.edPow upstream.edMul A (toU8 key) (toU8 m) (toU8 sig))
    | none => return "badkey"
  | ["ed25519-small-key", key] =>
    -- Whether rind's theorems refuse `key` as of small order before verifying.
    return bool (decide (leNat (toU8 (← unhex key)) % 2 ^ 255 ∈ edSmallOrderY))
  | ["ed25519-small-order"] =>
    -- Each listed y is of a point whose order divides 8, and the distinct
    -- ones are the y of all eight such points.
    let ok := edSmallOrderY.all fun y => [0, 2 ^ 255].any fun sign =>
      match decodeC (sign + y % p25519) with
      | some P => upstream.edPow P 8 == (0, 1)
      | none => false
    let count := (edSmallOrderY.eraseDups.filter (· < p25519)).foldl (fun c y =>
      c + ([0, 2 ^ 255].filter fun sign => (decodeC (sign + y)).isSome).length) 0
    return bool (ok && count == 8)
  | ["x25519", k, u] =>
    return hex (ofU8 (leBytesOf 32 (upstream.x25519 (leNat (toU8 (← unhex k))) (leNat (toU8 (← unhex u))))))
  | ["rsa-pkcs1-verify", h, n, e, m, s] =>
    let (H, _, _) ← hashOf h
    let di ← match h with
      | "sha1" => pure rsa.digestInfoSha1
      | "sha256" => pure rsa.digestInfoSha256
      | "sha384" => pure rsa.digestInfoSha384
      | "sha512" => pure rsa.digestInfoSha512
      | _ => throw s!"no DigestInfo for {h}"
    return bool (rsa.pkcs1v15VerifyC (beNum (← unhex n)) (beNum (← unhex e)) H di (← unhex m) (← unhex s))
  | ["rsa-pss-verify", h, n, e, m, s, sLen] =>
    let (H, _, len) ← hashOf h
    return bool (rsa.pssVerifyC (beNum (← unhex n)) (beNum (← unhex e)) H len (← unhex m) (← unhex s)
      (← nat sLen))
  | ["mlkem-keygen", set, d, z] =>
    let p ← paramOf set
    let (ek, dk) := Spec.MLKEM.KeyGen_internal p (← vec 32 (← unhex d)) (← vec 32 (← unhex z))
    return s!"{hex ek.toList} {hex dk.toList}"
  | ["mlkem-encaps", set, ek, m] =>
    let p ← paramOf set
    let ek ← vec _ (← unhex ek)
    let m ← vec 32 (← unhex m)
    if Spec.MLKEM.Encaps.KeyCheck p ek then
      let (K, c) := Spec.MLKEM.Encaps_internal p ek m
      return s!"{hex K.toList} {hex c.toList}"
    else return "badkey"
  | ["mlkem-decaps", set, dk, c] =>
    let p ← paramOf set
    let dk ← vec _ (← unhex dk)
    match Spec.MLKEM.Decaps p dk (← vec _ (← unhex c)) with
    | some K => return hex K.toList
    | none => return "badkey"
  | _ => throw s!"no request {args}"

end rind.spec.server

open rind.spec.server in
def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let args := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
    match answer args with
    | .ok out => stdout.putStrLn out
    | .error e => stdout.putStrLn s!"error {e}"
    stdout.flush
  return 0
