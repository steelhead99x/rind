module
public import Aeneas
public import Rind.Aarch64.Types
public import Rind.Aarch64.Neon
public import Rind.GhashSpec
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# rind's PMULL GHASH and one-pass AES-GCM, modelled by hand

These transmute between vectors, integers, and word arrays, load and store
through raw pointers, split slices with `as_chunks` and `chunks_mut`, and zip
iterators, which Aeneas cannot translate, so the translation leaves them
opaque and this file models them over `Rind.Aarch64.Neon`'s intrinsics, each
statement as the Rust runs it. A `u128` and the vector it is transmuted to
are the same 128 bits, lane 0 least significant, as both are little endian.
`admin/prove` fails unless these quotes are still that Rust, so a change to
it is a change to this model:

```rust
macro_rules! mul {
    ($lo:ident, $mi:ident, $hi:ident, $x:expr, $hs:expr, $m:expr, $mul_m:ident) => {
        let x = $x;
        let xs = vextq_u64(x, x, 1);

        let tlo = vmull_high_p64_fix(xs, $hs);
        $lo = veorq_u64(tlo, $lo);

        let xx = veorq_u64(xs, x);

        let thi = vmull_p64_fix(xs, $hs);
        $hi = veorq_u64(thi, $hi);

        let tmi = $mul_m(xx, $m);
        $mi = veorq_u64(tmi, $mi);
    };
}

macro_rules! reduce {
    ($lo:ident, $mi:ident, $hi:ident) => {{
        let $mi = veorq_u64($mi, $lo);
        let $mi = veorq_u64($mi, $hi);

        let ls = vextq_u64($lo, $lo, 1);
        let $lo = vmull_p64_fix(GF128_POLY_HI, $lo);
        let $mi = veorq_u64($mi, ls);
        let $mi = veorq_u64($mi, $lo);

        let ms = vextq_u64($mi, $mi, 1);
        let $mi = vmull_p64_fix(GF128_POLY_HI, $mi);
        let $hi = veorq_u64($hi, ms);
        let $hi = veorq_u64($hi, $mi);
        $hi
    }};
}

    pub(crate) fn add(&mut self, bytes: &[u8]) {
        let table = match self.table {
            GhashTable::Pmull(table) => table,
            GhashTable::Neon(table) => {
                let mut xi = self.state();
                let (blocks, tail) = bytes.as_chunks::<16>();
                table.ghash(&mut xi, blocks);
                if !tail.is_empty() {
                    let mut last = [0u8; 16];
                    last[..tail.len()].copy_from_slice(tail);
                    table.ghash(&mut xi, &[last]);
                }
                return self.set_state(xi);
            }
        };

        let (by8_blocks, remainder) = bytes.as_chunks::<128>();

        for chunk8 in by8_blocks {
            self.eight_blocks(
                table,
                u128::from_be_bytes(chunk8[0..16].try_into().unwrap()),
                u128::from_be_bytes(chunk8[16..32].try_into().unwrap()),
                u128::from_be_bytes(chunk8[32..48].try_into().unwrap()),
                u128::from_be_bytes(chunk8[48..64].try_into().unwrap()),
                u128::from_be_bytes(chunk8[64..80].try_into().unwrap()),
                u128::from_be_bytes(chunk8[80..96].try_into().unwrap()),
                u128::from_be_bytes(chunk8[96..112].try_into().unwrap()),
                u128::from_be_bytes(chunk8[112..128].try_into().unwrap()),
            );
        }

        let (whole_blocks, remainder) = remainder.as_chunks::<16>();

        for chunk in whole_blocks {
            let u = u128::from_be_bytes(*chunk);
            self.one_block(table, u);
        }

        let bytes = remainder;
        if !bytes.is_empty() {
            let mut block = [0u8; 16];
            block[..bytes.len()].copy_from_slice(bytes);

            let u = u128::from_be_bytes(block);
            self.one_block(table, u);
        }
    }

    fn one_block(&mut self, table: &PmullTable, block: u128) {
        // SAFETY: this crate requires the `neon` cpu feature
        self.current = unsafe { veorq_u64(self.current, from_u128(block)) };
        // SAFETY: only a `HaveCryptoExt` token builds `table`, and rind
        // requires NEON.
        self.current = unsafe { _mul_h(table, self.current) };
    }

    fn eight_blocks(
        &mut self,
        table: &PmullTable,
        b1: u128,
        b2: u128,
        b3: u128,
        b4: u128,
        b5: u128,
        b6: u128,
        b7: u128,
        b8: u128,
    ) {
        // SAFETY: this crate requires the `neon` cpu feature
        let b1 = unsafe { veorq_u64(self.current, from_u128(b1)) };
        self.current = mul8(
            table,
            b1,
            from_u128(b2),
            from_u128(b3),
            from_u128(b4),
            from_u128(b5),
            from_u128(b6),
            from_u128(b7),
            from_u128(b8),
        );
    }

fn mul8(
    table: &PmullTable,
    a: uint64x2_t,
    b: uint64x2_t,
    c: uint64x2_t,
    d: uint64x2_t,
    e: uint64x2_t,
    f: uint64x2_t,
    g: uint64x2_t,
    h: uint64x2_t,
) -> uint64x2_t {
    // SAFETY: only a `HaveCryptoExt` token builds `table`, and rind requires
    // NEON.
    unsafe { _mul8(table, a, b, c, d, e, f, g, h) }
}

fn _mul_h(table: &PmullTable, a: uint64x2_t) -> uint64x2_t {
    let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
    let t = &table.htable;
    mul!(lo, mi, hi, a, t[0], t[1], vmull_p64_fix);
    reduce!(lo, mi, hi)
}

fn _mul8(
    table: &PmullTable,
    a: uint64x2_t,
    b: uint64x2_t,
    c: uint64x2_t,
    d: uint64x2_t,
    e: uint64x2_t,
    f: uint64x2_t,
    g: uint64x2_t,
    h: uint64x2_t,
) -> uint64x2_t {
    let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
    let t = &table.htable;
    mul!(lo, mi, hi, a, t[11], t[10], vmull_high_p64_fix);
    mul!(lo, mi, hi, b, t[9], t[10], vmull_p64_fix);
    mul!(lo, mi, hi, c, t[8], t[7], vmull_high_p64_fix);
    mul!(lo, mi, hi, d, t[6], t[7], vmull_p64_fix);
    mul!(lo, mi, hi, e, t[5], t[4], vmull_high_p64_fix);
    mul!(lo, mi, hi, f, t[3], t[4], vmull_p64_fix);
    mul!(lo, mi, hi, g, t[2], t[1], vmull_high_p64_fix);
    mul!(lo, mi, hi, h, t[0], t[1], vmull_p64_fix);
    reduce!(lo, mi, hi)
}

pub(crate) struct Aggregate<'a> {
    table: &'a PmullTable,
    /// The power of H the next block is multiplied by, or zero when it
    /// starts a group.
    power: usize,
    lo: uint64x2_t,
    mi: uint64x2_t,
    hi: uint64x2_t,
}

impl<'a> Aggregate<'a> {
    /// Starts a hash of `n` blocks, at least one.
    pub(crate) fn new(table: &'a PmullTable, n: usize) -> Self {
        assert!(n > 0);
        Self {
            table,
            power: (n - 1) % 8 + 1,
            lo: zero(),
            mi: zero(),
            hi: zero(),
        }
    }

    /// Adds the next block, in memory order.
    #[target_feature(enable = "neon,aes")]
    #[inline]
    pub(crate) fn add(&mut self, block: uint8x16_t) {
        // For H^p, `htable`'s index of its swapped halves, and of the 64-bit
        // word holding its Karatsuba middle term.
        const POWERS: [(usize, usize); 8] = [
            (0, 2),
            (2, 3),
            (3, 8),
            (5, 9),
            (6, 14),
            (8, 15),
            (9, 20),
            (11, 21),
        ];
        let (mut lo, mut mi, mut hi) = (self.lo, self.mi, self.hi);
        let mut x = reverse(block);
        if self.power == 0 {
            x = veorq_u64(x, reduce!(lo, mi, hi));
            (lo, mi, hi) = (zero(), zero(), zero());
            self.power = 8;
        }
        self.power -= 1;
        let (hs, m) = POWERS[self.power];
        // SAFETY: a `uint64x2_t` is two `u64`s, low lane first.
        let words: &[u64; 24] = unsafe { mem::transmute(&self.table.htable) };
        mul!(
            lo,
            mi,
            hi,
            x,
            self.table.htable[hs],
            vdupq_n_u64(words[m]),
            vmull_p64_fix
        );
        (self.lo, self.mi, self.hi) = (lo, mi, hi);
    }

    /// The hash, in memory order.
    #[target_feature(enable = "neon,aes")]
    #[inline]
    pub(crate) fn finish(self) -> uint8x16_t {
        let (lo, mi, hi) = (self.lo, self.mi, self.hi);
        vreinterpretq_u8_u64(reverse(vreinterpretq_u8_u64(reduce!(lo, mi, hi))))
    }
}

fn reverse(block: uint8x16_t) -> uint64x2_t {
    let r = vreinterpretq_u64_u8(vrev64q_u8(block));
    vextq_u64(r, r, 1)
}

fn vmull_p64_fix(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    let a = vgetq_lane_u64::<0>(a);
    let b = vgetq_lane_u64::<0>(b);
    let p = vmull_p64(a, b);
    // SAFETY: uint64x2_t and u128 have the same representation
    unsafe { mem::transmute(p) }
}

fn vmull_high_p64_fix(a: uint64x2_t, b: uint64x2_t) -> uint64x2_t {
    let a = vgetq_lane_u64::<1>(a);
    let b = vgetq_lane_u64::<1>(b);
    let p = vmull_p64(a, b);
    // SAFETY: uint64x2_t and u128 have the same representation
    unsafe { mem::transmute(p) }
}

fn zero() -> uint64x2_t {
    // SAFETY: u128 and uint64x2_t have the same size and meaning of bits
    unsafe { mem::transmute(0u128) }
}

fn from_u128(u: u128) -> uint64x2_t {
    // SAFETY: u128 and uint64x2_t have the same size and meaning of bits
    unsafe { mem::transmute(u) }
}

fn to_u128(u: uint64x2_t) -> u128 {
    // SAFETY: u128 and uint64x2_t have the same size and meaning of bits
    unsafe { mem::transmute(u) }
}

const GF128_POLY_HI: uint64x2_t =
    unsafe { mem::transmute(0xc2000000_00000000_c2000000_00000000u128) };

const GF128_POLY_CARRY_MASK: uint64x2_t =
    unsafe { mem::transmute(0xc2000000_00000001_00000000_00000001u128) };

fn short<const ENC: bool, const ROUND_KEYS: usize>(
    round_keys: &[uint8x16_t; ROUND_KEYS],
    table: &PmullTable,
    y0: [u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) -> [u8; 16] {
    let blocks = aad.len().div_ceil(16) + cipher_inout.len().div_ceil(16) + 1;
    let mut ghash = Aggregate::new(table, blocks);

    let y0_block = load(&y0);
    let tag_mask = encrypt(round_keys, y0_block);
    for chunk in aad.chunks(16) {
        ghash.add(load(chunk));
    }

    let y0_ctr = u32::from_be_bytes([y0[12], y0[13], y0[14], y0[15]]);
    let y0_words = vreinterpretq_u32_u8(y0_block);
    for (i, chunk) in (1u32..).zip(cipher_inout.chunks_mut(16)) {
        let counter = vsetq_lane_u32::<3>(y0_ctr.wrapping_add(i).to_be(), y0_words);
        let keystream = encrypt(round_keys, vreinterpretq_u8_u32(counter));
        let input = load(chunk);
        if !ENC {
            ghash.add(input);
        }
        let output = veorq_u8(input, keystream);
        store(chunk, output);
        if ENC {
            // The keystream past a short chunk is no ciphertext.
            ghash.add(vandq_u8(output, load(&KEEP[16 - chunk.len()..][..16])));
        }
    }
    ghash.add(load(&lengths(aad.len(), cipher_inout.len())));

    let mut tag = [0u8; 16];
    store(&mut tag, veorq_u8(tag_mask, ghash.finish()));
    tag
}

static KEEP: [u8; 32] = {
    let mut keep = [0; 32];
    let mut i = 0;
    while i < 16 {
        keep[i] = 0xff;
        i += 1;
    }
    keep
};

fn encrypt<const N: usize>(round_keys: &[uint8x16_t; N], mut block: uint8x16_t) -> uint8x16_t {
    let [rounds @ .., penultimate, last] = round_keys.as_slice() else {
        unreachable!()
    };
    for rk in rounds {
        block = vaesmcq_u8(vaeseq_u8(block, *rk));
    }
    veorq_u8(vaeseq_u8(block, *penultimate), *last)
}

fn load(bytes: &[u8]) -> uint8x16_t {
    if let Ok(block) = <&[u8; 16]>::try_from(bytes) {
        // SAFETY: `block` is 16 readable bytes.
        return unsafe { vld1q_u8(block.as_ptr()) };
    }

    // A shorter one in at most four moves through general registers, as a
    // `memcpy` call would spill every vector register, and its bytes stored
    // to the stack would not forward to one vector load.
    let mut word = 0u128;
    let mut at = 0;
    for size in [8, 4, 2, 1] {
        if bytes.len() & size != 0 {
            let mut part = [0u8; 8];
            part[..size].copy_from_slice(&bytes[at..at + size]);
            word |= u128::from(u64::from_le_bytes(part)) << (8 * at);
            at += size;
        }
    }
    // SAFETY: u128 and uint8x16_t have the same size, and both are little
    // endian.
    unsafe { mem::transmute(word) }
}

fn store(bytes: &mut [u8], block: uint8x16_t) {
    if let Ok(out) = <&mut [u8; 16]>::try_from(&mut *bytes) {
        // SAFETY: `out` is 16 writable bytes.
        return unsafe { vst1q_u8(out.as_mut_ptr(), block) };
    }

    // SAFETY: as in `load`.
    let word: u128 = unsafe { mem::transmute(block) };
    let mut at = 0;
    for size in [8, 4, 2, 1] {
        if bytes.len() & size != 0 {
            let part = ((word >> (8 * at)) as u64).to_le_bytes();
            bytes[at..at + size].copy_from_slice(&part[..size]);
            at += size;
        }
    }
}

```
-/

namespace rind.aarch64

open rind.vale rind.simd core.core_arch.arm_shared.neon.generated core.core_arch.aarch64.neon.generated

local notation "V" => core.core_arch.arm_shared.neon.uint64x2_t

/-! ## Transmutes and constants -/

/-- `zero`. -/
def low.aarch64.ghash.zero : Result V := ok 0

/-- `from_u128`: the same bits. -/
def low.aarch64.ghash.from_u128 (u : Std.U128) : Result V := ok u.bv

/-- `to_u128`: the same bits. -/
def low.aarch64.ghash.to_u128 (u : V) : Result Std.U128 := ok ⟨u⟩

/-- `GF128_POLY_HI`. -/
def low.aarch64.ghash.GF128_POLY_HI : Result V := ok 0xc2000000_00000000_c2000000_00000000#128

/-- `GF128_POLY_CARRY_MASK`. -/
def low.aarch64.ghash.GF128_POLY_CARRY_MASK : Result V := ok 0xc2000000_00000001_00000000_00000001#128

/-- `vmull_p64_fix`: `PMULL` of the low lanes. -/
def low.aarch64.ghash.vmull_p64_fix (a b : V) : Result V := do
  let a ← vgetq_lane_u64 0#i32 a
  let b ← vgetq_lane_u64 0#i32 b
  let p ← vmull_p64 a b
  ok p.bv

/-- `vmull_high_p64_fix`: `PMULL` of the high lanes. -/
def low.aarch64.ghash.vmull_high_p64_fix (a b : V) : Result V := do
  let a ← vgetq_lane_u64 1#i32 a
  let b ← vgetq_lane_u64 1#i32 b
  let p ← vmull_p64 a b
  ok p.bv

/-! ## `mul!`, `reduce!`, and the multiplies -/

/-- `mul!`, adding `x` times the power whose halves `hs` holds swapped, its
middle term the lane of `m` that `mul_m` reads: `vmull_high_p64_fix` if
`high`, else `vmull_p64_fix`. -/
def low.aarch64.ghash.mulStep (lo mi hi x hs m : V) (high : Bool) : Result (V × V × V) := do
  let xs ← vextq_u64 1#i32 x x
  let tlo ← low.aarch64.ghash.vmull_high_p64_fix xs hs
  let lo ← veorq_u64 tlo lo
  let xx ← veorq_u64 xs x
  let thi ← low.aarch64.ghash.vmull_p64_fix xs hs
  let hi ← veorq_u64 thi hi
  let tmi ← if high then low.aarch64.ghash.vmull_high_p64_fix xx m
    else low.aarch64.ghash.vmull_p64_fix xx m
  let mi ← veorq_u64 tmi mi
  ok (lo, mi, hi)

/-- `reduce!`. -/
def low.aarch64.ghash.reduce (lo mi hi : V) : Result V := do
  let mi ← veorq_u64 mi lo
  let mi ← veorq_u64 mi hi
  let ls ← vextq_u64 1#i32 lo lo
  let poly ← low.aarch64.ghash.GF128_POLY_HI
  let lo ← low.aarch64.ghash.vmull_p64_fix poly lo
  let mi ← veorq_u64 mi ls
  let mi ← veorq_u64 mi lo
  let ms ← vextq_u64 1#i32 mi mi
  let mi ← low.aarch64.ghash.vmull_p64_fix poly mi
  let hi ← veorq_u64 hi ms
  veorq_u64 hi mi

/-- `_mul_h`. -/
def low.aarch64.ghash._mul_h (table : low.aarch64.ghash.PmullTable) (a : V) : Result V := do
  let z ← low.aarch64.ghash.zero
  let t := table.htable.val
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep z z z a t[0]! t[1]! false
  low.aarch64.ghash.reduce lo mi hi

/-- `_mul8`, and `mul8`, which calls it. -/
def low.aarch64.ghash._mul8 (table : low.aarch64.ghash.PmullTable) (a b c d e f g h : V) : Result V := do
  let z ← low.aarch64.ghash.zero
  let t := table.htable.val
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep z z z a t[11]! t[10]! true
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi b t[9]! t[10]! false
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi c t[8]! t[7]! true
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi d t[6]! t[7]! false
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi e t[5]! t[4]! true
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi f t[3]! t[4]! false
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi g t[2]! t[1]! true
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi h t[0]! t[1]! false
  low.aarch64.ghash.reduce lo mi hi

/-! ## `Ghash::add` -/

/-- `u128::from_be_bytes` of a block, the first byte most significant: its
bytes reversed, as a little-endian load reads them. -/
def low.aarch64.ghash.fromBeBytes (block : List U8) : Std.U128 :=
  ⟨reverseBytesQuad32 (loadBytes block)⟩

/-- `one_block`. -/
def low.aarch64.ghash.one_block (table : low.aarch64.ghash.PmullTable) (current : V) (block : Std.U128) :
    Result V := do
  let b ← low.aarch64.ghash.from_u128 block
  let current ← veorq_u64 current b
  low.aarch64.ghash._mul_h table current

/-- `eight_blocks`, on a 128-byte chunk's eight blocks. -/
def low.aarch64.ghash.eight_blocks (table : low.aarch64.ghash.PmullTable) (current : V) (chunk8 : List U8) :
    Result V := do
  let b := fun i => low.aarch64.ghash.from_u128
    (low.aarch64.ghash.fromBeBytes ((chunk8.drop (16 * i)).take 16))
  let b1 ← b 0
  let b1 ← veorq_u64 current b1
  let b2 ← b 1
  let b3 ← b 2
  let b4 ← b 3
  let b5 ← b 4
  let b6 ← b 5
  let b7 ← b 6
  let b8 ← b 7
  low.aarch64.ghash._mul8 table b1 b2 b3 b4 b5 b6 b7 b8

/-- `Ghash::add` on aws-lc's NEON table, which no proof covers. -/
opaque low.aarch64.ghash.Ghash.add_neon : low.aarch64.ghash.Ghash → List U8 → Result low.aarch64.ghash.Ghash

/-- `Ghash::add` on a PMULL table: its 128-byte chunks eight blocks at a
time, the rest's whole blocks one at a time, then its tail zero-padded. -/
def low.aarch64.ghash.Ghash.addPmull (table : low.aarch64.ghash.PmullTable) (current : V) (bytes : List U8) :
    Result V := do
  let current ← (chunksOf 128 bytes).foldlM (low.aarch64.ghash.eight_blocks table) current
  let remainder := chunksRest 128 bytes
  let current ← (chunksOf 16 remainder).foldlM
    (fun c chunk => low.aarch64.ghash.one_block table c (low.aarch64.ghash.fromBeBytes chunk)) current
  let tail := chunksRest 16 remainder
  if tail = [] then ok current else
    low.aarch64.ghash.one_block table current
      (low.aarch64.ghash.fromBeBytes (tail ++ List.replicate (16 - tail.length) 0#u8))

/-- `Ghash::add`. -/
def low.aarch64.ghash.Ghash.add (self : low.aarch64.ghash.Ghash) (bytes : Slice U8) :
    Result low.aarch64.ghash.Ghash :=
  match self.table with
  | .Pmull table => do
    let current ← low.aarch64.ghash.Ghash.addPmull table self.current bytes.val
    ok { self with current }
  | .Neon _ => low.aarch64.ghash.Ghash.add_neon self bytes.val

/-! ## `Aggregate` -/

/-- `Aggregate`: its table, the power of H the next block is multiplied by
(`usize` in Rust, whose arithmetic here stays within 0 to 8), and the
Karatsuba terms summed so far. -/
structure low.aarch64.ghash.Aggregate where
  table : low.aarch64.ghash.PmullTable
  power : Nat
  lo : V
  mi : V
  hi : V

/-- `Aggregate::new`, which panics on no blocks. -/
def low.aarch64.ghash.Aggregate.new (table : low.aarch64.ghash.PmullTable) (n : Nat) :
    Result low.aarch64.ghash.Aggregate := do
  if n > 0 then
    let z ← low.aarch64.ghash.zero
    ok { table, power := (n - 1) % 8 + 1, lo := z, mi := z, hi := z }
  else fail .panic

/-- `reverse`. -/
def low.aarch64.ghash.reverse (block : core.core_arch.arm_shared.neon.uint8x16_t) : Result V := do
  let r ← vrev64q_u8 block
  let r ← vreinterpretq_u64_u8 r
  vextq_u64 1#i32 r r

/-- `Aggregate::add`'s `POWERS`. -/
def low.aarch64.ghash.Aggregate.POWERS : List (Nat × Nat) :=
  [(0, 2), (2, 3), (3, 8), (5, 9), (6, 14), (8, 15), (9, 20), (11, 21)]

/-- Word `m` of `htable` transmuted to `[u64; 24]`: lane `m % 2` of entry
`m / 2`, the low lane first. -/
def low.aarch64.ghash.word (htable : List V) (m : Nat) : Std.U64 := ⟨lane64 htable[m / 2]! (m % 2)⟩

/-- `Aggregate::add`. -/
def low.aarch64.ghash.Aggregate.add (self : low.aarch64.ghash.Aggregate)
    (block : core.core_arch.arm_shared.neon.uint8x16_t) : Result low.aarch64.ghash.Aggregate := do
  let x ← low.aarch64.ghash.reverse block
  let (x, lo, mi, hi, power) ← if self.power = 0 then do
      let r ← low.aarch64.ghash.reduce self.lo self.mi self.hi
      let x ← veorq_u64 x r
      let z ← low.aarch64.ghash.zero
      ok (x, z, z, z, 8)
    else ok (x, self.lo, self.mi, self.hi, self.power)
  let power := power - 1
  let (hs, m) := low.aarch64.ghash.Aggregate.POWERS[power]!
  let t := self.table.htable.val
  let md ← vdupq_n_u64 (low.aarch64.ghash.word t m)
  let (lo, mi, hi) ← low.aarch64.ghash.mulStep lo mi hi x t[hs]! md false
  ok { self with power, lo, mi, hi }

/-- `Aggregate::finish`. -/
def low.aarch64.ghash.Aggregate.finish (self : low.aarch64.ghash.Aggregate) :
    Result core.core_arch.arm_shared.neon.uint8x16_t := do
  let r ← low.aarch64.ghash.reduce self.lo self.mi self.hi
  let r ← vreinterpretq_u8_u64 r
  let r ← low.aarch64.ghash.reverse r
  vreinterpretq_u8_u64 r

/-! ## The one-pass AES-GCM -/

/-- `encrypt`: AES of `block` under the round keys, which panics on fewer
than two. -/
def low.aarch64.aes_gcm.encrypt (round_keys : List core.core_arch.arm_shared.neon.uint8x16_t)
    (block : core.core_arch.arm_shared.neon.uint8x16_t) : Result core.core_arch.arm_shared.neon.uint8x16_t := do
  if round_keys.length < 2 then fail .panic
  else
    let block ← (round_keys.take (round_keys.length - 2)).foldlM
      (fun b rk => do let b ← vaeseq_u8 b rk; vaesmcq_u8 b) block
    let b ← vaeseq_u8 block round_keys[round_keys.length - 2]!
    veorq_u8 b round_keys[round_keys.length - 1]!

/-- `load`'s moves of a slice shorter than a block, by the sizes in turn: the
word so far and how many bytes it holds. `bytes[at..pos + size]` is in
bounds, since the sizes taken sum to the length. -/
def low.aarch64.aes_gcm.loadParts (bytes : List U8) : List Nat → BitVec 128 × Nat → BitVec 128 × Nat
  | [], acc => acc
  | size :: sizes, (word, pos) =>
    low.aarch64.aes_gcm.loadParts bytes sizes
      (if bytes.length &&& size ≠ 0 then
        let part := (bytes.drop pos).take size ++ List.replicate (8 - size) 0#u8
        (word ||| (loadBytes part <<< (8 * pos)), pos + size)
      else (word, pos))

/-- `load`: a whole block's 16 bytes, or a shorter slice moved through a
`u128` by `u64::from_le_bytes` of zero-padded parts of 8, 4, 2, and 1 bytes,
the first byte least significant. -/
def low.aarch64.aes_gcm.load (bytes : List U8) : Result core.core_arch.arm_shared.neon.uint8x16_t :=
  if bytes.length = 16 then ok (loadBytes bytes)
  else ok (low.aarch64.aes_gcm.loadParts bytes [8, 4, 2, 1] (0, 0)).1

/-- `store`'s moves into a slice shorter than a block, by the sizes in turn:
the bytes so far and how many it has written. -/
def low.aarch64.aes_gcm.storeParts (n : Nat) (word : BitVec 128) : List Nat → List U8 × Nat → List U8 × Nat
  | [], acc => acc
  | size :: sizes, (out, pos) =>
    low.aarch64.aes_gcm.storeParts n word sizes
      (if n &&& size ≠ 0 then
        let part := ((storeBytes (word >>> (8 * pos))).val.take 8).take size
        (out.take pos ++ part ++ out.drop (pos + size), pos + size)
      else (out, pos))

/-- `store`: the first `bytes.len()` bytes of `block`, written over `bytes`,
a whole block by one store and a shorter slice in parts of 8, 4, 2, and 1
bytes of the transmuted `u128`, each its low bytes `to_le_bytes` lays out
first. -/
def low.aarch64.aes_gcm.store (bytes : List U8) (block : core.core_arch.arm_shared.neon.uint8x16_t) :
    Result (List U8) :=
  if bytes.length = 16 then ok (storeBytes block).val
  else ok (low.aarch64.aes_gcm.storeParts bytes.length block [8, 4, 2, 1] (bytes, 0)).1

/-- `KEEP`: sixteen ones then sixteen zeros. -/
def low.aarch64.aes_gcm.KEEP : List U8 := List.replicate 16 0xff#u8 ++ List.replicate 16 0#u8

/-- `lengths(aad, msg)`'s bytes: the bit lengths, big-endian, the AAD's
first, each `as u128 * 8` and the AAD's shifted left 64, wrapping. -/
def low.aarch64.aes_gcm.lengthsBytes (aad msg : Nat) : List U8 :=
  (core.num.U128.to_be_bytes
    ⟨(BitVec.ofNat 128 (aad * 8) <<< 64) ||| BitVec.ofNat 128 (msg * 8)⟩).val

/-- `short`'s loop over the message's chunks of up to 16 bytes, from the
counter `i`: the hash and the output so far. `i` is a `Nat`, where Rust's
`1u32..` panics on reaching `u32::MAX` with overflow checks and wraps
without them; `short_spec`'s bound of at most 31 chunks from `i = 1` keeps
both out of reach. -/
def low.aarch64.aes_gcm.short_loop (ENC : Bool) (round_keys : List core.core_arch.arm_shared.neon.uint8x16_t)
    (y0_ctr : Std.U32) (y0_words : core.core_arch.arm_shared.neon.uint32x4_t) :
    List (List U8) → Nat → low.aarch64.ghash.Aggregate → Result (low.aarch64.ghash.Aggregate × List U8)
  | [], _, ghash => ok (ghash, [])
  | chunk :: chunks, i, ghash => do
    let ctr : Std.U32 := ⟨y0_ctr.bv + BitVec.ofNat 32 i⟩
    -- `to_be` on a little-endian CPU: the word's bytes reversed.
    let be : Std.U32 := ⟨ctr.bv.extractLsb' 0 8 ++ ctr.bv.extractLsb' 8 8 ++ ctr.bv.extractLsb' 16 8 ++
      ctr.bv.extractLsb' 24 8⟩
    let counter ← vsetq_lane_u32 3#i32 be y0_words
    let c ← vreinterpretq_u8_u32 counter
    let keystream ← low.aarch64.aes_gcm.encrypt round_keys c
    let input ← low.aarch64.aes_gcm.load chunk
    let ghash ← if !ENC then ghash.add input else ok ghash
    let output ← veorq_u8 input keystream
    let out ← low.aarch64.aes_gcm.store chunk output
    let ghash ← if ENC then do
        let keep ← low.aarch64.aes_gcm.load ((low.aarch64.aes_gcm.KEEP.drop (16 - chunk.length)).take 16)
        let masked ← vandq_u8 output keep
        ghash.add masked
      else ok ghash
    let (ghash, rest) ← low.aarch64.aes_gcm.short_loop ENC round_keys y0_ctr y0_words chunks (i + 1) ghash
    ok (ghash, out ++ rest)

/-- `short`. Its block count is `usize` arithmetic in Rust, which cannot
wrap for slices that fit in memory. -/
def low.aarch64.aes_gcm.short (ENC : Bool) {ROUND_KEYS : Std.Usize}
    (round_keys : Std.Array core.core_arch.arm_shared.neon.uint8x16_t ROUND_KEYS)
    (table : low.aarch64.ghash.PmullTable) (y0 : Std.Array U8 16#usize) (aad cipher_inout : Slice U8) :
    Result (Std.Array U8 16#usize × Slice U8) := do
  let blocks := (aad.length + 15) / 16 + (cipher_inout.length + 15) / 16 + 1
  let ghash ← low.aarch64.ghash.Aggregate.new table blocks
  let y0_block ← low.aarch64.aes_gcm.load y0.val
  let tag_mask ← low.aarch64.aes_gcm.encrypt round_keys.val y0_block
  let ghash ← (chunksUpTo 16 aad.val).foldlM (fun (g : low.aarch64.ghash.Aggregate) chunk => do
    let b ← low.aarch64.aes_gcm.load chunk
    g.add b) ghash
  -- `u32::from_be_bytes`: the first byte most significant.
  let y0_ctr : Std.U32 := ⟨y0.val[12]!.bv ++ y0.val[13]!.bv ++ y0.val[14]!.bv ++ y0.val[15]!.bv⟩
  let y0_words ← vreinterpretq_u32_u8 y0_block
  let (ghash, out) ← low.aarch64.aes_gcm.short_loop ENC round_keys.val y0_ctr y0_words
    (chunksUpTo 16 cipher_inout.val) 1 ghash
  let lb ← low.aarch64.aes_gcm.load (low.aarch64.aes_gcm.lengthsBytes aad.length cipher_inout.length)
  let ghash ← ghash.add lb
  let h ← ghash.finish
  let t ← veorq_u8 tag_mask h
  let tag ← low.aarch64.aes_gcm.store (List.replicate 16 0#u8) t
  if h1 : tag.length = 16 then
    if h2 : out.length ≤ Usize.max then ok (Std.Array.make 16#usize tag (by simpa using h1), Slice.from out h2)
    else fail .panic
  else fail .panic

end rind.aarch64
