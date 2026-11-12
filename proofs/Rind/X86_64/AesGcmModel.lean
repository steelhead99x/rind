module
public import Aeneas
public import Rind.X86_64.Types
public import Rind.X86_64.Simd
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# rind's PCLMULQDQ GHASH and by-8 AES-GCM, modelled by hand

These load and store through raw pointers, `transmute` constants, split
slices with `as_chunks`, and zip iterators, which Aeneas cannot translate, so
the translation leaves them opaque and this file models them over
`Rind.X86_64.Simd`'s intrinsics. `admin/prove` fails unless these quotes are
still that Rust, so a change to it is a change to this model:

```rust
macro_rules! mul {
    ($lo:ident, $mi:ident, $hi:ident, $x:ident, $h:expr, $hx:expr) => {
        let tlo = _mm_clmulepi64_si128($x, $h, 0x00);
        $lo = _mm_xor_si128(tlo, $lo);

        let xx = _mm_shuffle_epi32($x, 0b01_00_11_10);
        let xx = _mm_xor_si128(xx, $x);

        let thi = _mm_clmulepi64_si128($x, $h, 0x11);
        $hi = _mm_xor_si128(thi, $hi);

        let tmi = _mm_clmulepi64_si128(xx, $hx, 0x00);
        $mi = _mm_xor_si128(tmi, $mi);
    };
}

macro_rules! reduce {
    ($lo:ident, $mi:ident, $hi:ident) => {{
        let $mi = _mm_xor_si128($mi, $lo);
        let $mi = _mm_xor_si128($mi, $hi);

        let ls = _mm_shuffle_epi32($lo, 0b01_00_11_10);
        let $lo = _mm_clmulepi64_si128(u128_to_m128i(GF128_POLY_HI), $lo, 0x00);
        let $mi = _mm_xor_si128($mi, ls);
        let $mi = _mm_xor_si128($mi, $lo);

        let ms = _mm_shuffle_epi32($mi, 0b01_00_11_10);
        let $mi = _mm_clmulepi64_si128(u128_to_m128i(GF128_POLY_HI), $mi, 0x00);
        let $hi = _mm_xor_si128($hi, ms);
        let $hi = _mm_xor_si128($hi, $mi);
        $hi
    }};
}

    fn add(&self, bytes: &[u8], mut current: __m128i) -> __m128i {
        let (eight_blocks, remainder) = bytes.as_chunks::<128>();

        for chunk8 in eight_blocks {
            let [b1, b2, b3, b4, b5, b6, b7, b8] = chunk8.as_chunks::<16>().0 else {
                unreachable!()
            };
            let b1 = _mm_xor_si128(current, load_be(b1));
            current = _mul8(
                self,
                b1,
                load_be(b2),
                load_be(b3),
                load_be(b4),
                load_be(b5),
                load_be(b6),
                load_be(b7),
                load_be(b8),
            );
        }

        self.add_tail(remainder, current)
    }

    fn mul_h(&self, x: __m128i) -> __m128i {
        let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
        mul!(lo, mi, hi, x, self.powers[0], self.powers_xor[0]);
        reduce!(lo, mi, hi)
    }

    fn add_tail(&self, bytes: &[u8], current: __m128i) -> __m128i {
        if bytes.is_empty() {
            return current;
        }

        let n = bytes.len().div_ceil(16);
        let mut powers = self.powers[..n].iter().zip(&self.powers_xor[..n]).rev();

        let (blocks, partial) = bytes.as_chunks::<16>();
        let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
        let mut x = current;
        for (block, (h, hx)) in blocks.iter().zip(&mut powers) {
            let b = _mm_xor_si128(x, load_be(block));
            mul!(lo, mi, hi, b, *h, *hx);
            x = zero();
        }
        if let Some((h, hx)) = powers.next() {
            let b = _mm_xor_si128(x, _mm_shuffle_epi8(load_partial(partial), BYTESWAP));
            mul!(lo, mi, hi, b, *h, *hx);
        }
        reduce!(lo, mi, hi)
    }

    pub(crate) fn add(&mut self, bytes: &[u8]) {
        self.current = match self.table {
            GhashTable::Clmul(table)
            | GhashTable::VaesAvx2(table, ..)
            | GhashTable::Avx(table, _) => {
                // SAFETY: only a `HaveAesHardware` token builds `table`,
                // proving PCLMULQDQ.
                unsafe { table.add(bytes, self.current) }
            }
            // SAFETY: avx512.token proves features were dynamically checked
            GhashTable::Avx512(avx512) => unsafe { avx512.add(bytes, self.current) },
            GhashTable::Ssse3(table) => {
                return self.add_by(bytes, |xi, blocks| table.ghash(xi, blocks));
            }
            GhashTable::Nohw(table) => {
                return self.add_by(bytes, |xi, blocks| table.ghash(xi, blocks));
            }
        };
    }

    pub(crate) fn tag(self, mask: &[u8; 16]) -> [u8; 16] {
        let mut tag = [0u8; 16];
        // SAFETY: every x86_64 CPU has SSE2, and `mask` and `tag` are 16
        // readable and writable bytes
        unsafe {
            let mask = _mm_loadu_si128(mask.as_ptr().cast());
            let tag_v = _mm_xor_si128(byte_reverse(self.current), mask);
            _mm_storeu_si128(tag.as_mut_ptr().cast(), tag_v);
        }
        tag
    }

pub(crate) fn _mul8(
    table: &ClmulTable,
    x1: __m128i,
    x2: __m128i,
    x3: __m128i,
    x4: __m128i,
    x5: __m128i,
    x6: __m128i,
    x7: __m128i,
    x8: __m128i,
) -> __m128i {
    let (mut lo, mut mi, mut hi) = (zero(), zero(), zero());
    mul!(lo, mi, hi, x1, table.powers[7], table.powers_xor[7]);
    mul!(lo, mi, hi, x2, table.powers[6], table.powers_xor[6]);
    mul!(lo, mi, hi, x3, table.powers[5], table.powers_xor[5]);
    mul!(lo, mi, hi, x4, table.powers[4], table.powers_xor[4]);
    mul!(lo, mi, hi, x5, table.powers[3], table.powers_xor[3]);
    mul!(lo, mi, hi, x6, table.powers[2], table.powers_xor[2]);
    mul!(lo, mi, hi, x7, table.powers[1], table.powers_xor[1]);
    mul!(lo, mi, hi, x8, table.powers[0], table.powers_xor[0]);
    reduce!(lo, mi, hi)
}

fn byte_reverse(x: __m128i) -> __m128i {
    // SAFETY: every x86_64 CPU has SSE2
    unsafe {
        let x = _mm_shuffle_epi32(x, 0b00_01_10_11);
        let x = _mm_shufflehi_epi16(_mm_shufflelo_epi16(x, 0b10_11_00_01), 0b10_11_00_01);
        _mm_or_si128(_mm_slli_epi16(x, 8), _mm_srli_epi16(x, 8))
    }
}

fn load_be(block: &[u8; 16]) -> __m128i {
    // SAFETY: `block` is 16 readable bytes
    _mm_shuffle_epi8(unsafe { _mm_loadu_si128(block.as_ptr().cast()) }, BYTESWAP)
}

const BYTESWAP: __m128i = unsafe { mem::transmute(0x00010203_04050607_08090a0b_0c0d0e0fu128) };

    pub(crate) fn round_keys(&self) -> (__m128i, &[__m128i], __m128i) {
        match self {
            Self::Aes128(a128) => (
                a128.round_keys[0],
                &a128.round_keys[1..10],
                a128.round_keys[10],
            ),
            Self::Aes192(a192) => (
                a192.round_keys[0],
                &a192.round_keys[1..12],
                a192.round_keys[12],
            ),
            Self::Aes256(a256) => (
                a256.round_keys[0],
                &a256.round_keys[1..14],
                a256.round_keys[14],
            ),
        }
    }

fn counter_block(nonce: &[u8; 12]) -> [u8; 16] {
    let lo = u64::from_le_bytes(nonce[..8].try_into().unwrap());
    let hi = u64::from(u32::from_le_bytes(nonce[8..].try_into().unwrap())) | 1 << 56;
    let mut y0 = [0u8; 16];
    // SAFETY: every x86_64 CPU has SSE2, and `y0` is 16 writable bytes. One
    // vector store, so the 16-byte loads that read it are forwarded, where
    // separate stores of its parts would stall them.
    unsafe { _mm_storeu_si128(y0.as_mut_ptr().cast(), _mm_set_epi64x(hi as i64, lo as i64)) };
    y0
}

fn by8<const ENC: bool>(
    key: &HwKey,
    table: &ClmulTable,
    ghash: &mut Ghash<'_>,
    initial_counter: &[u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
) {
    ghash.add(aad);

    let (rk_first, rks, rk_last) = key.round_keys();

    let mut counter = Counter::new(initial_counter);
    let (by8_iter, remainder) = cipher_inout.as_chunks_mut::<128>();

    for blocks in by8_iter {
        // prefetch to avoid any stall later
        super::cpu::prefetch(blocks, 64);

        let c1 = counter.next();
        let c2 = counter.next();
        let c3 = counter.next();
        let c4 = counter.next();
        let c5 = counter.next();
        let c6 = counter.next();
        let c7 = counter.next();
        let c8 = counter.next();

        let mut c1 = _mm_xor_si128(c1, rk_first);
        let mut c2 = _mm_xor_si128(c2, rk_first);
        let mut c3 = _mm_xor_si128(c3, rk_first);
        let mut c4 = _mm_xor_si128(c4, rk_first);
        let mut c5 = _mm_xor_si128(c5, rk_first);
        let mut c6 = _mm_xor_si128(c6, rk_first);
        let mut c7 = _mm_xor_si128(c7, rk_first);
        let mut c8 = _mm_xor_si128(c8, rk_first);

        for rk in rks {
            c1 = _mm_aesenc_si128(c1, *rk);
            c2 = _mm_aesenc_si128(c2, *rk);
            c3 = _mm_aesenc_si128(c3, *rk);
            c4 = _mm_aesenc_si128(c4, *rk);
            c5 = _mm_aesenc_si128(c5, *rk);
            c6 = _mm_aesenc_si128(c6, *rk);
            c7 = _mm_aesenc_si128(c7, *rk);
            c8 = _mm_aesenc_si128(c8, *rk);
        }

        let c1 = _mm_aesenclast_si128(c1, rk_last);
        let c2 = _mm_aesenclast_si128(c2, rk_last);
        let c3 = _mm_aesenclast_si128(c3, rk_last);
        let c4 = _mm_aesenclast_si128(c4, rk_last);
        let c5 = _mm_aesenclast_si128(c5, rk_last);
        let c6 = _mm_aesenclast_si128(c6, rk_last);
        let c7 = _mm_aesenclast_si128(c7, rk_last);
        let c8 = _mm_aesenclast_si128(c8, rk_last);

        // SAFETY: `blocks` is 128 bytes and readable
        let (p1, p2, p3, p4, p5, p6, p7, p8) = unsafe {
            (
                _mm_loadu_si128(blocks.as_ptr().add(0).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(16).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(32).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(48).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(64).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(80).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(96).cast()),
                _mm_loadu_si128(blocks.as_ptr().add(112).cast()),
            )
        };

        let c1 = _mm_xor_si128(c1, p1);
        let c2 = _mm_xor_si128(c2, p2);
        let c3 = _mm_xor_si128(c3, p3);
        let c4 = _mm_xor_si128(c4, p4);
        let c5 = _mm_xor_si128(c5, p5);
        let c6 = _mm_xor_si128(c6, p6);
        let c7 = _mm_xor_si128(c7, p7);
        let c8 = _mm_xor_si128(c8, p8);

        // SAFETY: `blocks` is 128 bytes and writable, due to `as_chunks_mut`
        unsafe {
            _mm_storeu_si128(blocks.as_mut_ptr().add(0).cast(), c1);
            _mm_storeu_si128(blocks.as_mut_ptr().add(16).cast(), c2);
            _mm_storeu_si128(blocks.as_mut_ptr().add(32).cast(), c3);
            _mm_storeu_si128(blocks.as_mut_ptr().add(48).cast(), c4);
            _mm_storeu_si128(blocks.as_mut_ptr().add(64).cast(), c5);
            _mm_storeu_si128(blocks.as_mut_ptr().add(80).cast(), c6);
            _mm_storeu_si128(blocks.as_mut_ptr().add(96).cast(), c7);
            _mm_storeu_si128(blocks.as_mut_ptr().add(112).cast(), c8);
        }

        let (a1, a2, a3, a4, a5, a6, a7, a8) = if ENC {
            (c1, c2, c3, c4, c5, c6, c7, c8)
        } else {
            (p1, p2, p3, p4, p5, p6, p7, p8)
        };

        let a1 = _mm_shuffle_epi8(a1, BYTESWAP);
        let a2 = _mm_shuffle_epi8(a2, BYTESWAP);
        let a3 = _mm_shuffle_epi8(a3, BYTESWAP);
        let a4 = _mm_shuffle_epi8(a4, BYTESWAP);
        let a5 = _mm_shuffle_epi8(a5, BYTESWAP);
        let a6 = _mm_shuffle_epi8(a6, BYTESWAP);
        let a7 = _mm_shuffle_epi8(a7, BYTESWAP);
        let a8 = _mm_shuffle_epi8(a8, BYTESWAP);

        let a1 = _mm_xor_si128(ghash.current, a1);
        ghash.current = ghash::_mul8(table, a1, a2, a3, a4, a5, a6, a7, a8);
    }

    let cipher_inout = remainder;

    if !ENC {
        ghash.add(cipher_inout);
    }

    {
        let (blocks_iter, remainder) = cipher_inout.as_chunks_mut::<16>();
        for block in blocks_iter {
            let c1 = counter.next();

            let mut c1 = _mm_xor_si128(c1, rk_first);

            for rk in rks {
                c1 = _mm_aesenc_si128(c1, *rk);
            }

            let c1 = _mm_aesenclast_si128(c1, rk_last);

            // SAFETY: `block` is 16 bytes due to `as_chunks_mut`
            let p1 = unsafe { _mm_loadu_si128(block.as_ptr().cast()) };
            let c1 = _mm_xor_si128(c1, p1);

            // SAFETY: `block` is 16 bytes and writable, due to `as_chunks_mut`
            unsafe { _mm_storeu_si128(block.as_mut_ptr().cast(), c1) };
        }

        let cipher_inout = remainder;
        if !cipher_inout.is_empty() {
            let c1 = counter.next();
            let mut c1 = _mm_xor_si128(c1, rk_first);

            for rk in rks {
                c1 = _mm_aesenc_si128(c1, *rk);
            }

            let c1 = _mm_aesenclast_si128(c1, rk_last);
            let c1 = _mm_xor_si128(c1, ghash::load_partial(cipher_inout));
            ghash::store_partial(cipher_inout, c1);
        }
    }

    if ENC {
        ghash.add(cipher_inout);
    }
}

impl Counter {
    #[inline]
    #[target_feature(enable = "sse2,sse3,ssse3")]
    fn new(bytes: &[u8; 16]) -> Self {
        // SAFETY: `bytes` is a 128-bit value and can be loaded from
        let c = unsafe { _mm_lddqu_si128(bytes.as_ptr().cast()) };
        let c = _mm_shuffle_epi8(c, BYTESWAP_EPI64);
        let c = _mm_add_epi32(c, COUNTER_1); // skip first counter (it was already used as y0)

        Self(c)
    }

    #[target_feature(enable = "sse2,ssse3")]
    #[must_use]
    #[inline]
    fn next(&mut self) -> __m128i {
        let r = _mm_shuffle_epi8(self.0, BYTESWAP_EPI64);
        self.0 = _mm_add_epi32(self.0, COUNTER_1);
        r
    }
}

const COUNTER_1: __m128i = unsafe { mem::transmute(1u128 << 64) };

const BYTESWAP: __m128i = unsafe { mem::transmute(0x00010203_04050607_08090a0b_0c0d0e0fu128) };

const BYTESWAP_EPI64: __m128i =
    unsafe { mem::transmute(0x08090a0b_0c0d0e0f_00010203_04050607u128) };

```

The model departs from the Rust in these ways, and adds no axiom:

- A load of 16 bytes, `_mm_loadu_si128` or `_mm_lddqu_si128`, is the vector
  of its bytes, the first lowest, and `_mm_storeu_si128` writes the vector's
  bytes the same way: `Rind.Lanes`'s `loadBytes` and `storeBytes`.
- `zero()` is `_mm_setzero_si128()`, its body, and `mul!` and `reduce!` are
  functions of the terms they update. `reduce!`'s `u128_to_m128i(GF128_POLY_HI)`
  is its value, `polyHi`, which `Rind.X86_64.GhashClmul`'s `polyHi_eq` proves
  the translation computes.
- `as_chunks` and `as_chunks_mut` split a slice into its whole chunks and the
  rest; a loop over the chunks, or over zipped iterators, is a recursion.
- `ghash::load_partial` is the zero-padded block, and `ghash::store_partial`
  writes the block's first bytes, as `Rind.X86_64.PartialBlock` proves of
  their translations, and `prefetch`, which changes no state, is left out.
- `by8`'s eight blocks of a chunk, independent until `_mul8`, are computed one
  after another, each through all its rounds.
- The 512-bit GHASH and the SSSE3 and integer tables' `add_by`, which no
  theorem here is about, stay opaque.
-/

namespace rind.x86_64

open rind.vale rind.simd

/-- `as_chunks`: the whole chunks of `k` elements, in order. -/
def chunksOf {α : Type} (k : Nat) (l : List α) : List (List α) :=
  (List.range (l.length / k)).map fun i => (l.drop (k * i)).take k

/-- What `as_chunks` leaves after the whole chunks of `k` elements. -/
def chunksRest {α : Type} (k : Nat) (l : List α) : List α := l.drop (k * (l.length / k))

/-- `ghash::BYTESWAP`. -/
def low.x86_64.ghash.BYTESWAP : Result core.core_arch.x86.__m128i :=
  ok 0x00010203_04050607_08090a0b_0c0d0e0f#128

/-- `load_be`. -/
def low.x86_64.ghash.load_be (block : List U8) : Result core.core_arch.x86.__m128i := do
  let s ← low.x86_64.ghash.BYTESWAP
  core.core_arch.x86.ssse3._mm_shuffle_epi8 (loadBytes block) s

/-- `ghash::load_partial`: fewer than 16 bytes, zero-padded to a block. -/
def low.x86_64.ghash.loadPadded (bytes : List U8) : core.core_arch.x86.__m128i :=
  loadBytes (bytes ++ List.replicate (16 - bytes.length) 0#u8)

/-- `byte_reverse`. -/
def low.x86_64.ghash.byte_reverse (x : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := do
  let x ← core.core_arch.x86.sse2._mm_shuffle_epi32 27#i32 x
  let lo ← core.core_arch.x86.sse2._mm_shufflelo_epi16 177#i32 x
  let x ← core.core_arch.x86.sse2._mm_shufflehi_epi16 177#i32 lo
  let l ← core.core_arch.x86.sse2._mm_slli_epi16 8#i32 x
  let r ← core.core_arch.x86.sse2._mm_srli_epi16 8#i32 x
  core.core_arch.x86.sse2._mm_or_si128 l r

/-- `mul!`: the Karatsuba terms of `x` times `h` XORed into `lo`, `mi`, and
`hi`, given `hx`, `h`'s halves XORed. -/
def low.x86_64.ghash.mul (lo mi hi x h hx : core.core_arch.x86.__m128i) :
    Result (core.core_arch.x86.__m128i × core.core_arch.x86.__m128i × core.core_arch.x86.__m128i) := do
  let tlo ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 x h
  let lo ← core.core_arch.x86.sse2._mm_xor_si128 tlo lo
  let xx ← core.core_arch.x86.sse2._mm_shuffle_epi32 78#i32 x
  let xx ← core.core_arch.x86.sse2._mm_xor_si128 xx x
  let thi ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 17#i32 x h
  let hi ← core.core_arch.x86.sse2._mm_xor_si128 thi hi
  let tmi ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 xx hx
  let mi ← core.core_arch.x86.sse2._mm_xor_si128 tmi mi
  ok (lo, mi, hi)

/-- `u128_to_m128i(GF128_POLY_HI)`. -/
def low.x86_64.ghash.polyHi : core.core_arch.x86.__m128i := 0xc2000000_00000000#128

/-- `reduce!`. -/
def low.x86_64.ghash.reduce (lo mi hi : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := do
  let mi ← core.core_arch.x86.sse2._mm_xor_si128 mi lo
  let mi ← core.core_arch.x86.sse2._mm_xor_si128 mi hi
  let ls ← core.core_arch.x86.sse2._mm_shuffle_epi32 78#i32 lo
  let p := low.x86_64.ghash.polyHi
  let lo ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 p lo
  let mi ← core.core_arch.x86.sse2._mm_xor_si128 mi ls
  let mi ← core.core_arch.x86.sse2._mm_xor_si128 mi lo
  let ms ← core.core_arch.x86.sse2._mm_shuffle_epi32 78#i32 mi
  let mi ← core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 p mi
  let hi ← core.core_arch.x86.sse2._mm_xor_si128 hi ms
  core.core_arch.x86.sse2._mm_xor_si128 hi mi

/-- `_mul8`. -/
def low.x86_64.ghash._mul8 (table : low.x86_64.ghash.ClmulTable)
    (x1 x2 x3 x4 x5 x6 x7 x8 : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i := do
  let z ← core.core_arch.x86.sse2._mm_setzero_si128
  let p := table.powers.val
  let px := table.powers_xor.val
  let (lo, mi, hi) ← low.x86_64.ghash.mul z z z x1 p[7]! px[7]!
  let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi x2 p[6]! px[6]!
  let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi x3 p[5]! px[5]!
  let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi x4 p[4]! px[4]!
  let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi x5 p[3]! px[3]!
  let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi x6 p[2]! px[2]!
  let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi x7 p[1]! px[1]!
  let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi x8 p[0]! px[0]!
  low.x86_64.ghash.reduce lo mi hi

/-- `ClmulTable::mul_h`. -/
def low.x86_64.ghash.ClmulTable.mul_h (self : low.x86_64.ghash.ClmulTable)
    (x : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i := do
  let z ← core.core_arch.x86.sse2._mm_setzero_si128
  let (lo, mi, hi) ← low.x86_64.ghash.mul z z z x self.powers.val[0]! self.powers_xor.val[0]!
  low.x86_64.ghash.reduce lo mi hi

/-- `add_tail`'s loop over the whole blocks, each zipped with the next power:
each block XORed with `x`, then zero, times its power. It returns `x` and
the terms after them, and the powers it did not reach. -/
def low.x86_64.ghash.ClmulTable.add_tail_loop :
    List (List U8) → List (core.core_arch.x86.__m128i × core.core_arch.x86.__m128i) →
    core.core_arch.x86.__m128i → core.core_arch.x86.__m128i → core.core_arch.x86.__m128i →
    core.core_arch.x86.__m128i →
    Result (core.core_arch.x86.__m128i × core.core_arch.x86.__m128i × core.core_arch.x86.__m128i ×
      core.core_arch.x86.__m128i × List (core.core_arch.x86.__m128i × core.core_arch.x86.__m128i))
  | block :: blocks, (h, hx) :: powers, x, lo, mi, hi => do
    let l ← low.x86_64.ghash.load_be block
    let b ← core.core_arch.x86.sse2._mm_xor_si128 x l
    let (lo, mi, hi) ← low.x86_64.ghash.mul lo mi hi b h hx
    let x ← core.core_arch.x86.sse2._mm_setzero_si128
    low.x86_64.ghash.ClmulTable.add_tail_loop blocks powers x lo mi hi
  | _, powers, x, lo, mi, hi => ok (x, lo, mi, hi, powers)

/-- `ClmulTable::add_tail`. -/
def low.x86_64.ghash.ClmulTable.add_tail (self : low.x86_64.ghash.ClmulTable) (bytes : List U8)
    (current : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i := do
  if bytes.isEmpty then ok current else
  let n := (bytes.length + 15) / 16
  if n > 8 then fail .panic else
  let powers := ((self.powers.val.take n).zip (self.powers_xor.val.take n)).reverse
  let z ← core.core_arch.x86.sse2._mm_setzero_si128
  let (x, lo, mi, hi, powers) ←
    low.x86_64.ghash.ClmulTable.add_tail_loop (chunksOf 16 bytes) powers current z z z
  let (lo, mi, hi) ← match powers with
    | (h, hx) :: _ => do
      let s ← low.x86_64.ghash.BYTESWAP
      let p ← core.core_arch.x86.ssse3._mm_shuffle_epi8
        (low.x86_64.ghash.loadPadded (chunksRest 16 bytes)) s
      let b ← core.core_arch.x86.sse2._mm_xor_si128 x p
      low.x86_64.ghash.mul lo mi hi b h hx
    | [] => ok (lo, mi, hi)
  low.x86_64.ghash.reduce lo mi hi

/-- `ClmulTable::add`'s loop over the 128-byte chunks. -/
def low.x86_64.ghash.ClmulTable.add_loop (self : low.x86_64.ghash.ClmulTable) :
    List (List U8) → core.core_arch.x86.__m128i → Result core.core_arch.x86.__m128i
  | [], current => ok current
  | chunk8 :: chunks, current => do
    let b := chunksOf 16 chunk8
    let l1 ← low.x86_64.ghash.load_be b[0]!
    let b1 ← core.core_arch.x86.sse2._mm_xor_si128 current l1
    let b2 ← low.x86_64.ghash.load_be b[1]!
    let b3 ← low.x86_64.ghash.load_be b[2]!
    let b4 ← low.x86_64.ghash.load_be b[3]!
    let b5 ← low.x86_64.ghash.load_be b[4]!
    let b6 ← low.x86_64.ghash.load_be b[5]!
    let b7 ← low.x86_64.ghash.load_be b[6]!
    let b8 ← low.x86_64.ghash.load_be b[7]!
    let current ← low.x86_64.ghash._mul8 self b1 b2 b3 b4 b5 b6 b7 b8
    low.x86_64.ghash.ClmulTable.add_loop self chunks current

/-- `ClmulTable::add`. -/
def low.x86_64.ghash.ClmulTable.add (self : low.x86_64.ghash.ClmulTable) (bytes : List U8)
    (current : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i := do
  let current ← low.x86_64.ghash.ClmulTable.add_loop self (chunksOf 128 bytes) current
  low.x86_64.ghash.ClmulTable.add_tail self (chunksRest 128 bytes) current

/-- `GhashTableAvx512::add`, the 512-bit GHASH. -/
opaque low.x86_64.ghash.GhashTableAvx512.add :
  low.x86_64.ghash.GhashTableAvx512 → List U8 → core.core_arch.x86.__m128i →
    Result core.core_arch.x86.__m128i

/-- `Ghash::add_by` for the SSSE3 and integer tables. -/
opaque low.x86_64.ghash.Ghash.add_by : low.x86_64.ghash.Ghash → List U8 → Result low.x86_64.ghash.Ghash

/-- `Ghash::add`, of the bytes as a list. -/
def low.x86_64.ghash.Ghash.addBytes (self : low.x86_64.ghash.Ghash) (bytes : List U8) :
    Result low.x86_64.ghash.Ghash :=
  match self.table with
  | .Clmul table | .VaesAvx2 table _ _ | .Avx table _ => do
    let current ← low.x86_64.ghash.ClmulTable.add table bytes self.current
    ok { self with current }
  | .Avx512 avx512 => do
    let current ← low.x86_64.ghash.GhashTableAvx512.add avx512 bytes self.current
    ok { self with current }
  | .Ssse3 _ | .Nohw _ => low.x86_64.ghash.Ghash.add_by self bytes

/-- `Ghash::add`. -/
def low.x86_64.ghash.Ghash.add (self : low.x86_64.ghash.Ghash) (bytes : Slice U8) :
    Result low.x86_64.ghash.Ghash :=
  low.x86_64.ghash.Ghash.addBytes self bytes.val

/-- `Ghash::tag`. -/
def low.x86_64.ghash.Ghash.tag (self : low.x86_64.ghash.Ghash) (mask : Std.Array U8 16#usize) :
    Result (Std.Array U8 16#usize) := do
  let r ← low.x86_64.ghash.byte_reverse self.current
  let t ← core.core_arch.x86.sse2._mm_xor_si128 r (loadBytes mask.val)
  ok (storeBytes t)

/-- `HwKey::round_keys`. -/
def low.x86_64.aes.HwKey.round_keys : low.x86_64.aes.HwKey →
    core.core_arch.x86.__m128i × List core.core_arch.x86.__m128i × core.core_arch.x86.__m128i
  | .Aes128 k => (k.round_keys.val[0]!, (k.round_keys.val.drop 1).take 9, k.round_keys.val[10]!)
  | .Aes192 k => (k.round_keys.val[0]!, (k.round_keys.val.drop 1).take 11, k.round_keys.val[12]!)
  | .Aes256 k => (k.round_keys.val[0]!, (k.round_keys.val.drop 1).take 13, k.round_keys.val[14]!)

/-- `counter_block`. -/
def low.x86_64.aes_gcm.counter_block (nonce : Std.Array U8 12#usize) :
    Result (Std.Array U8 16#usize) := do
  let lo : BitVec 64 := BitVec.fromLEBytes ((nonce.val.take 8).map (·.bv)) |>.setWidth 64
  let hi : BitVec 64 :=
    ((BitVec.fromLEBytes ((nonce.val.drop 8).map (·.bv))).setWidth 32).setWidth 64 ||| 1#64 <<< 56
  let y0 ← core.core_arch.x86.sse2._mm_set_epi64x ⟨hi⟩ ⟨lo⟩
  ok (storeBytes y0)

/-- `aes_gcm::COUNTER_1`. -/
def low.x86_64.aes_gcm.COUNTER_1 : Result core.core_arch.x86.__m128i :=
  ok 0x1_00000000_00000000#128

/-- `aes_gcm::BYTESWAP`. -/
def low.x86_64.aes_gcm.BYTESWAP : Result core.core_arch.x86.__m128i :=
  ok 0x00010203_04050607_08090a0b_0c0d0e0f#128

/-- `aes_gcm::BYTESWAP_EPI64`. -/
def low.x86_64.aes_gcm.BYTESWAP_EPI64 : Result core.core_arch.x86.__m128i :=
  ok 0x08090a0b_0c0d0e0f_00010203_04050607#128

/-- `Counter::new`: the counter, each 64-bit half byte-swapped, past `bytes`. -/
def low.x86_64.aes_gcm.Counter.new (bytes : Std.Array U8 16#usize) :
    Result core.core_arch.x86.__m128i := do
  let s ← low.x86_64.aes_gcm.BYTESWAP_EPI64
  let c ← core.core_arch.x86.ssse3._mm_shuffle_epi8 (loadBytes bytes.val) s
  let one ← low.x86_64.aes_gcm.COUNTER_1
  core.core_arch.x86.sse2._mm_add_epi32 c one

/-- `Counter::next`: the counter block, and the counter after it. -/
def low.x86_64.aes_gcm.Counter.next (self : core.core_arch.x86.__m128i) :
    Result (core.core_arch.x86.__m128i × core.core_arch.x86.__m128i) := do
  let s ← low.x86_64.aes_gcm.BYTESWAP_EPI64
  let r ← core.core_arch.x86.ssse3._mm_shuffle_epi8 self s
  let one ← low.x86_64.aes_gcm.COUNTER_1
  let c ← core.core_arch.x86.sse2._mm_add_epi32 self one
  ok (r, c)

/-- One block of `by8`'s AES: the first round key XORed, `AESENC` with each of
`rks`, and `AESENCLAST` with the last. -/
def low.x86_64.aes_gcm.encrypt (c rk_first : core.core_arch.x86.__m128i)
    (rks : List core.core_arch.x86.__m128i) (rk_last : core.core_arch.x86.__m128i) :
    Result core.core_arch.x86.__m128i := do
  let c ← core.core_arch.x86.sse2._mm_xor_si128 c rk_first
  let c ← rks.foldlM core.core_arch.x86.aes._mm_aesenc_si128 c
  core.core_arch.x86.aes._mm_aesenclast_si128 c rk_last

/-- One block of keystream XORed into `p`, from the counter, and the counter
after it. -/
def low.x86_64.aes_gcm.ctr_block (counter rk_first : core.core_arch.x86.__m128i)
    (rks : List core.core_arch.x86.__m128i) (rk_last p : core.core_arch.x86.__m128i) :
    Result (core.core_arch.x86.__m128i × core.core_arch.x86.__m128i) := do
  let (c, counter) ← low.x86_64.aes_gcm.Counter.next counter
  let k ← low.x86_64.aes_gcm.encrypt c rk_first rks rk_last
  let c ← core.core_arch.x86.sse2._mm_xor_si128 k p
  ok (c, counter)

/-- `by8`'s eight blocks of a chunk, in order: each block's output, and the
counter after them. -/
def low.x86_64.aes_gcm.ctr_blocks (rk_first : core.core_arch.x86.__m128i)
    (rks : List core.core_arch.x86.__m128i) (rk_last : core.core_arch.x86.__m128i) :
    List core.core_arch.x86.__m128i → core.core_arch.x86.__m128i →
    Result (List core.core_arch.x86.__m128i × core.core_arch.x86.__m128i)
  | [], counter => ok ([], counter)
  | p :: ps, counter => do
    let (c, counter) ← low.x86_64.aes_gcm.ctr_block counter rk_first rks rk_last p
    let (cs, counter) ← low.x86_64.aes_gcm.ctr_blocks rk_first rks rk_last ps counter
    ok (c :: cs, counter)

/-- A vector's bytes, as `_mm_storeu_si128` writes them. -/
def low.x86_64.aes_gcm.bytes (v : core.core_arch.x86.__m128i) : List U8 := (storeBytes v).val

/-- `by8`'s loop over the 128-byte chunks: the counter and hash after them,
and their output. -/
def low.x86_64.aes_gcm.by8_loop (ENC : Bool) (table : low.x86_64.ghash.ClmulTable)
    (rk_first : core.core_arch.x86.__m128i) (rks : List core.core_arch.x86.__m128i)
    (rk_last : core.core_arch.x86.__m128i) :
    List (List U8) → core.core_arch.x86.__m128i → core.core_arch.x86.__m128i →
    Result (core.core_arch.x86.__m128i × core.core_arch.x86.__m128i × List U8)
  | [], counter, current => ok (counter, current, [])
  | blocks :: chunks, counter, current => do
    let ps := (chunksOf 16 blocks).map loadBytes
    let (cs, counter) ← low.x86_64.aes_gcm.ctr_blocks rk_first rks rk_last ps counter
    let hs := if ENC then cs else ps
    let s ← low.x86_64.aes_gcm.BYTESWAP
    let a1 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[0]! s
    let a2 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[1]! s
    let a3 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[2]! s
    let a4 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[3]! s
    let a5 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[4]! s
    let a6 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[5]! s
    let a7 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[6]! s
    let a8 ← core.core_arch.x86.ssse3._mm_shuffle_epi8 hs[7]! s
    let a1 ← core.core_arch.x86.sse2._mm_xor_si128 current a1
    let current ← low.x86_64.ghash._mul8 table a1 a2 a3 a4 a5 a6 a7 a8
    let (counter, current, out) ←
      low.x86_64.aes_gcm.by8_loop ENC table rk_first rks rk_last chunks counter current
    ok (counter, current, cs.flatMap low.x86_64.aes_gcm.bytes ++ out)

/-- `by8`. -/
def low.x86_64.aes_gcm.by8 (ENC : Bool) (key : low.x86_64.aes.HwKey)
    (table : low.x86_64.ghash.ClmulTable) (ghash : low.x86_64.ghash.Ghash)
    (initial_counter : Std.Array U8 16#usize) (aad cipher_inout : Slice U8) :
    Result (low.x86_64.ghash.Ghash × Slice U8) := do
  let ghash ← low.x86_64.ghash.Ghash.addBytes ghash aad.val
  let (rk_first, rks, rk_last) := low.x86_64.aes.HwKey.round_keys key
  let counter ← low.x86_64.aes_gcm.Counter.new initial_counter
  let (counter, current, head) ← low.x86_64.aes_gcm.by8_loop ENC table rk_first rks rk_last
    (chunksOf 128 cipher_inout.val) counter ghash.current
  let ghash := { ghash with current }
  let rest := chunksRest 128 cipher_inout.val
  let ghash ← if ENC then ok ghash else low.x86_64.ghash.Ghash.addBytes ghash rest
  let (blocks, counter) ← low.x86_64.aes_gcm.ctr_blocks rk_first rks rk_last
    ((chunksOf 16 rest).map loadBytes) counter
  let tail := chunksRest 16 rest
  let last ← if tail.isEmpty then ok [] else do
    let (c, _) ← low.x86_64.aes_gcm.ctr_block counter rk_first rks rk_last
      (low.x86_64.ghash.loadPadded tail)
    ok ((low.x86_64.aes_gcm.bytes c).take tail.length)
  let rest := blocks.flatMap low.x86_64.aes_gcm.bytes ++ last
  let ghash ← if ENC then low.x86_64.ghash.Ghash.addBytes ghash rest else ok ghash
  if h : (head ++ rest).length ≤ Usize.max then ok (ghash, Slice.from (head ++ rest) h) else fail .panic

/-! The other AES-GCM kernels, which no theorem here is about. -/

opaque low.x86_64.aes_gcm.composed
  (ENC : Bool) :
  low.x86_64.aes.AesKey → low.x86_64.ghash.Ghash → Std.Array U8 16#usize → Slice U8 → Slice U8 →
    Result (low.x86_64.ghash.Ghash × Slice U8)

opaque low.x86_64.aes_gcm._cipher_avx512
  (ENC : Bool) :
  low.x86_64.aes.HwKey → low.x86_64.ghash.Ghash → Std.Array U8 16#usize → Slice U8 → Slice U8 →
    low.x86_64.cpu.HaveAvx512ForAesGcm → Result (low.x86_64.ghash.Ghash × Slice U8)

opaque low.x86_64.aes_gcm_vaes.VaesKernel.cipher
  (ENC : Bool) :
  low.x86_64.aes_gcm_vaes.VaesKernel → low.x86_64.aes.HwKey → Std.Array U8 16#usize →
    low.x86_64.ghash.Ghash → Slice U8 → Result (low.x86_64.ghash.Ghash × Slice U8)

end rind.x86_64
