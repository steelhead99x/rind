module
public import Aeneas
public import Rind.X86_64.Types
public import Rind.X86_64.Simd
public import Rind.GhashSpec
@[expose] public section
open Aeneas Aeneas.Std Result
set_option linter.dupNamespace false

/-!
# rind's PCLMULQDQ and AVX-512 GHASH and its by-8 and by-16 AES-GCM, modelled by hand

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

impl GhashTableAvx512 {
    pub(crate) fn new(h: u128, hw: HaveAesHardware, token: HaveAvx512ForAesGcm) -> Self {
        let vaes = VaesKernel::avx512(h, token);
        let clmul = ClmulTable::from_powers(vaes.powers(), hw);
        Self { clmul, vaes, token }
    }

    /// H^16, H^15, ... H^1: descending, so a tail of `n` blocks multiplies
    /// by the last `n`.
    fn powers(&self) -> &[__m512i; 4] {
        let powers = self.vaes.powers();
        assert_eq!(powers.len(), 16);
        // SAFETY: the 512-bit kernel's table holds 16 powers, 64-byte
        // aligned as `__m512i` needs, and any bits are a valid `__m512i`.
        unsafe { &*powers.as_ptr().cast() }
    }

    #[target_feature(enable = "vpclmulqdq,avx512bw,avx512f,avx512vl")]
    fn add(&self, bytes: &[u8], mut current: __m128i) -> __m128i {
        let bswap_mask = _mm512_broadcast_i32x4(BYTESWAP);

        let (by_16_blocks, remainder) = bytes.as_chunks::<256>();
        for chunk16 in by_16_blocks {
            // SAFETY: `chunk16` is 256 bytes and readable, via `chunks_exact`
            let (m0123, m4567, m89ab, mcdef) = unsafe {
                (
                    _mm512_loadu_epi8(chunk16.as_ptr().add(0).cast()),
                    _mm512_loadu_epi8(chunk16.as_ptr().add(64).cast()),
                    _mm512_loadu_epi8(chunk16.as_ptr().add(128).cast()),
                    _mm512_loadu_epi8(chunk16.as_ptr().add(192).cast()),
                )
            };

            let m0123 = _mm512_shuffle_epi8(m0123, bswap_mask);
            let m4567 = _mm512_shuffle_epi8(m4567, bswap_mask);
            let m89ab = _mm512_shuffle_epi8(m89ab, bswap_mask);
            let mcdef = _mm512_shuffle_epi8(mcdef, bswap_mask);

            let c0___ = _mm512_inserti32x4::<0>(_mm512_setzero_si512(), current);
            let m0123 = _mm512_xor_epi64(m0123, c0___);

            current = _mul16(self, m0123, m4567, m89ab, mcdef);
        }

        // A short input, such as AAD or the length block, has too few blocks
        // to fill vectors, so it is quicker to hash it by the PCLMULQDQ path.
        self.clmul.add(remainder, current)
    }
}

pub(crate) fn _mul16(
    table: &GhashTableAvx512,
    x0123: __m512i,
    x4567: __m512i,
    x89ab: __m512i,
    xcdef: __m512i,
) -> __m128i {
    let powers = table.powers();
    let gfpoly = _mm512_broadcast_i32x4(GF128_POLY_LO);

    let lo0 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x00);
    let lo1 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x00);
    let lo2 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x00);

    let lo01 = _mm512_xor_epi32(lo0, lo1);
    let lo3 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x00);
    let lo = _mm512_ternarylogic_epi64(lo2, lo3, lo01, TERNARY_XOR);
    let mi0 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x01);

    let mi1 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x01);
    let mi2 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x01);
    let mi012 = _mm512_ternarylogic_epi32(mi0, mi1, mi2, TERNARY_XOR);
    let mi3 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x01);

    let mi4 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x10);
    let mi01234 = _mm512_ternarylogic_epi32(mi012, mi3, mi4, TERNARY_XOR);
    let mi5 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x10);
    let mi6 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x10);

    let mi = _mm512_ternarylogic_epi64(mi01234, mi5, mi6, TERNARY_XOR);
    let lo_r = _mm512_clmulepi64_epi128(gfpoly, lo, 0x01);
    let mi7 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x10);
    let mi = _mm512_xor_epi32(mi7, mi);

    let lo_s = _mm512_shuffle_epi32(lo, 0b01_00_11_10);
    let hi0 = _mm512_clmulepi64_epi128(x0123, powers[0], 0x11);
    let hi1 = _mm512_clmulepi64_epi128(x4567, powers[1], 0x11);
    let hi2 = _mm512_clmulepi64_epi128(x89ab, powers[2], 0x11);

    let mi = _mm512_ternarylogic_epi32(lo_r, lo_s, mi, TERNARY_XOR);
    let hi3 = _mm512_clmulepi64_epi128(xcdef, powers[3], 0x11);
    let hi012 = _mm512_ternarylogic_epi32(hi0, hi1, hi2, TERNARY_XOR);
    let mi_r = _mm512_clmulepi64_epi128(gfpoly, mi, 0x01);

    let hi = _mm512_xor_epi32(hi012, hi3);
    let mi_s = _mm512_shuffle_epi32(mi, 0b01_00_11_10);
    let r = _mm512_ternarylogic_epi32(mi_r, mi_s, hi, TERNARY_XOR);

    // xor together all terms of `r`
    let a = _mm512_extracti32x4_epi32::<0>(r);
    let b = _mm512_extracti32x4_epi32::<1>(r);
    let c = _mm512_extracti32x4_epi32::<2>(r);
    let d = _mm512_extracti32x4_epi32::<3>(r);
    let ab = _mm_xor_si128(a, b);
    _mm_ternarylogic_epi32(ab, c, d, TERNARY_XOR)
}

pub(crate) fn _mul_tail(
    table: &GhashTableAvx512,
    current: __m128i,
    x: [__m512i; 4],
    len: usize,
) -> __m128i {
    // `x` holds at most 16 blocks, and the table 16 powers.
    assert!(len <= 256);
    let n = len.div_ceil(16);
    if n == 0 {
        return current;
    }

    // The powers descend to H^1, so H^n is `n` blocks before their end.
    let powers = table.vaes.powers();
    let (mut lo, mut mi, mut hi) = (
        _mm512_setzero_si512(),
        _mm512_setzero_si512(),
        _mm512_setzero_si512(),
    );
    for (j, x) in x.into_iter().enumerate().take(n.div_ceil(4)) {
        let x = match j {
            0 => _mm512_xor_epi64(x, _mm512_inserti32x4::<0>(_mm512_setzero_si512(), current)),
            _ => x,
        };
        // Up to four blocks left from here on, from H^(n-4j); slicing them
        // bounds the load by the table, whatever the arithmetic.
        let h = &powers[16 - n + 4 * j..][..(n - 4 * j).min(4)];
        // Two quadwords per block.
        let mask = u8::MAX >> (8 - 2 * h.len());
        // SAFETY: the mask covers `h`; masked-off lanes are not read.
        let h = unsafe { _mm512_maskz_loadu_epi64(mask, h.as_ptr().cast()) };
        lo = _mm512_xor_epi32(lo, _mm512_clmulepi64_epi128(x, h, 0x00));
        mi = _mm512_ternarylogic_epi32(
            mi,
            _mm512_clmulepi64_epi128(x, h, 0x01),
            _mm512_clmulepi64_epi128(x, h, 0x10),
            TERNARY_XOR,
        );
        hi = _mm512_xor_epi32(hi, _mm512_clmulepi64_epi128(x, h, 0x11));
    }

    let gfpoly = _mm512_broadcast_i32x4(GF128_POLY_LO);
    let lo_r = _mm512_clmulepi64_epi128(gfpoly, lo, 0x01);
    let lo_s = _mm512_shuffle_epi32(lo, 0b01_00_11_10);
    let mi = _mm512_ternarylogic_epi32(lo_r, lo_s, mi, TERNARY_XOR);
    let mi_r = _mm512_clmulepi64_epi128(gfpoly, mi, 0x01);
    let mi_s = _mm512_shuffle_epi32(mi, 0b01_00_11_10);
    let r = _mm512_ternarylogic_epi32(mi_r, mi_s, hi, TERNARY_XOR);

    // xor together all terms of `r`
    let a = _mm512_extracti32x4_epi32::<0>(r);
    let b = _mm512_extracti32x4_epi32::<1>(r);
    let c = _mm512_extracti32x4_epi32::<2>(r);
    let d = _mm512_extracti32x4_epi32::<3>(r);
    let ab = _mm_xor_si128(a, b);
    _mm_ternarylogic_epi32(ab, c, d, TERNARY_XOR)
}

const TERNARY_XOR: i32 = 0x96;

const GF128_POLY_LO: __m128i =
    unsafe { mem::transmute([0xc2000000_00000000_00000000_00000000u128]) };

    pub(crate) fn round_keys_512(&self) -> RoundKeys512 {
        match self {
            Self::Aes128(AesKey128 {
                round_keys: [a, b, c, d, e, f, g, h, i, j, k],
                ..
            }) => RoundKeys512::Aes128([
                _mm512_broadcast_i32x4(*a),
                _mm512_broadcast_i32x4(*b),
                _mm512_broadcast_i32x4(*c),
                _mm512_broadcast_i32x4(*d),
                _mm512_broadcast_i32x4(*e),
                _mm512_broadcast_i32x4(*f),
                _mm512_broadcast_i32x4(*g),
                _mm512_broadcast_i32x4(*h),
                _mm512_broadcast_i32x4(*i),
                _mm512_broadcast_i32x4(*j),
                _mm512_broadcast_i32x4(*k),
            ]),
            Self::Aes192(a192) => {
                let mut rks = [_mm512_setzero_si512(); 13];
                for (out, rk) in rks.iter_mut().zip(&a192.round_keys) {
                    *out = _mm512_broadcast_i32x4(*rk);
                }
                RoundKeys512::Aes192(rks)
            }
            Self::Aes256(AesKey256 {
                round_keys: [a, b, c, d, e, f, g, h, i, j, k, l, m, n, o],
                ..
            }) => RoundKeys512::Aes256([
                _mm512_broadcast_i32x4(*a),
                _mm512_broadcast_i32x4(*b),
                _mm512_broadcast_i32x4(*c),
                _mm512_broadcast_i32x4(*d),
                _mm512_broadcast_i32x4(*e),
                _mm512_broadcast_i32x4(*f),
                _mm512_broadcast_i32x4(*g),
                _mm512_broadcast_i32x4(*h),
                _mm512_broadcast_i32x4(*i),
                _mm512_broadcast_i32x4(*j),
                _mm512_broadcast_i32x4(*k),
                _mm512_broadcast_i32x4(*l),
                _mm512_broadcast_i32x4(*m),
                _mm512_broadcast_i32x4(*n),
                _mm512_broadcast_i32x4(*o),
            ]),
        }
    }

impl RoundKeys512 {
    pub(crate) fn split(&self) -> (__m512i, &[__m512i], __m512i) {
        match self {
            Self::Aes128(rks) => (rks[0], &rks[1..10], rks[10]),
            Self::Aes192(rks) => (rks[0], &rks[1..12], rks[12]),
            Self::Aes256(rks) => (rks[0], &rks[1..14], rks[14]),
        }
    }
}

fn _cipher_avx512<const ENC: bool>(
    key: &HwKey,
    ghash: &mut Ghash<'_>,
    initial_counter: &[u8; 16],
    aad: &[u8],
    cipher_inout: &mut [u8],
    _feature_token: HaveAvx512ForAesGcm,
) {
    ghash.add(aad);

    let round_keys = key.round_keys_512();
    let (rk_first, rks, rk_last) = round_keys.split();

    let mut counter = Counter512::new(initial_counter);
    let (by16_iter, remainder) = cipher_inout.as_chunks_mut::<AVX512_MINIMUM_CIPHER_LEN>();

    let ghash_avx512 = match ghash.table {
        GhashTable::Avx512(ghash_avx512) => ghash_avx512,
        _ => panic!("unexpected ghash table variant"),
    };

    for blocks in by16_iter {
        // prefetch to avoid any stall later
        super::cpu::prefetch(blocks, 256);

        let c0123 = counter.next4();
        let c4567 = counter.next4();
        let c89ab = counter.next4();
        let ccdef = counter.next4();

        let mut c0123 = _mm512_xor_epi32(c0123, rk_first);
        let mut c4567 = _mm512_xor_epi32(c4567, rk_first);
        let mut c89ab = _mm512_xor_epi32(c89ab, rk_first);
        let mut ccdef = _mm512_xor_epi32(ccdef, rk_first);

        for rk in rks {
            c0123 = _mm512_aesenc_epi128(c0123, *rk);
            c4567 = _mm512_aesenc_epi128(c4567, *rk);
            c89ab = _mm512_aesenc_epi128(c89ab, *rk);
            ccdef = _mm512_aesenc_epi128(ccdef, *rk);
        }

        let c0123 = _mm512_aesenclast_epi128(c0123, rk_last);
        let c4567 = _mm512_aesenclast_epi128(c4567, rk_last);
        let c89ab = _mm512_aesenclast_epi128(c89ab, rk_last);
        let ccdef = _mm512_aesenclast_epi128(ccdef, rk_last);

        // SAFETY: `blocks` is 256 bytes due to `as_chunks_mut`
        let (p0123, p4567, p89ab, pcdef) = unsafe {
            (
                _mm512_loadu_si512(blocks.as_ptr().add(0).cast()),
                _mm512_loadu_si512(blocks.as_ptr().add(64).cast()),
                _mm512_loadu_si512(blocks.as_ptr().add(128).cast()),
                _mm512_loadu_si512(blocks.as_ptr().add(192).cast()),
            )
        };

        let c0123 = _mm512_xor_epi32(c0123, p0123);
        let c4567 = _mm512_xor_epi32(c4567, p4567);
        let c89ab = _mm512_xor_epi32(c89ab, p89ab);
        let ccdef = _mm512_xor_epi32(ccdef, pcdef);

        // SAFETY: `blocks` is 256 bytes and writable due to `as_chunks_mut`
        unsafe {
            _mm512_storeu_si512(blocks.as_mut_ptr().add(0).cast(), c0123);
            _mm512_storeu_si512(blocks.as_mut_ptr().add(64).cast(), c4567);
            _mm512_storeu_si512(blocks.as_mut_ptr().add(128).cast(), c89ab);
            _mm512_storeu_si512(blocks.as_mut_ptr().add(192).cast(), ccdef);
        }

        let (a0123, a4567, a89ab, acdef) = if ENC {
            (c0123, c4567, c89ab, ccdef)
        } else {
            (p0123, p4567, p89ab, pcdef)
        };

        let a0123 = _mm512_shuffle_epi8(a0123, BYTESWAP_512);
        let a4567 = _mm512_shuffle_epi8(a4567, BYTESWAP_512);
        let a89ab = _mm512_shuffle_epi8(a89ab, BYTESWAP_512);
        let acdef = _mm512_shuffle_epi8(acdef, BYTESWAP_512);

        let c0___ = _mm512_inserti32x4::<0>(_mm512_setzero_si512(), ghash.current);
        let a0123 = _mm512_xor_epi64(a0123, c0___);

        ghash.current = ghash::_mul16(ghash_avx512, a0123, a4567, a89ab, acdef);
    }

    if remainder.is_empty() {
        return;
    }

    // The tail, under 256 bytes, in one pass of four vectors masked to its
    // length. AES is latency-bound here, so the unused vectors cost little.
    let mut ks = [
        counter.next4(),
        counter.next4(),
        counter.next4(),
        counter.next4(),
    ];
    for k in &mut ks {
        *k = _mm512_xor_epi32(*k, rk_first);
    }
    for rk in rks {
        for k in &mut ks {
            *k = _mm512_aesenc_epi128(*k, *rk);
        }
    }

    let mut tail = [_mm512_setzero_si512(); 4];
    for ((t, k), chunk) in tail.iter_mut().zip(ks).zip(remainder.chunks_mut(64)) {
        // The first `chunk.len()` bytes, at least one.
        let mask = u64::MAX >> (64 - chunk.len());
        // SAFETY: the mask covers `chunk`, and masked-off bytes are not read
        let p = unsafe { _mm512_maskz_loadu_epi8(mask, chunk.as_ptr().cast()) };
        let c = _mm512_xor_epi32(
            _mm512_maskz_mov_epi8(mask, _mm512_aesenclast_epi128(k, rk_last)),
            p,
        );
        // SAFETY: the mask covers `chunk`, and masked-off bytes are not written
        unsafe { _mm512_mask_storeu_epi8(chunk.as_mut_ptr().cast(), mask, c) };
        *t = _mm512_shuffle_epi8(if ENC { c } else { p }, BYTESWAP_512);
    }
    ghash.current = ghash::_mul_tail(ghash_avx512, ghash.current, tail, remainder.len());
}

impl Counter512 {
    #[inline]
    #[target_feature(enable = "sse3,ssse3,avx,avx2,avx512f")]
    fn new(bytes: &[u8; 16]) -> Self {
        // SAFETY: `bytes` is a 128-bits and can be loaded from
        Self(unsafe {
            let mut cnt = Counter::new(bytes);
            let a = cnt.next();
            let b = cnt.next();
            let c = cnt.next();
            let d = cnt.next();

            let r: __m512i = mem::transmute(_mm512_undefined());
            let r = _mm512_inserti32x4::<0>(r, _mm_shuffle_epi8(a, BYTESWAP_EPI64));
            let r = _mm512_inserti32x4::<1>(r, _mm_shuffle_epi8(b, BYTESWAP_EPI64));
            let r = _mm512_inserti32x4::<2>(r, _mm_shuffle_epi8(c, BYTESWAP_EPI64));
            _mm512_inserti32x4::<3>(r, _mm_shuffle_epi8(d, BYTESWAP_EPI64))
        })
    }

    #[target_feature(enable = "sse3,ssse3,avx,avx2,avx512f,avx512bw")]
    #[must_use]
    #[inline]
    fn next4(&mut self) -> __m512i {
        let r = _mm512_shuffle_epi8(self.0, BYTESWAP_512_EPI64);
        // 32-bit lanes, so each counter wraps within its last four bytes, as
        // GCM's from any IV must.
        self.0 = _mm512_add_epi32(self.0, COUNTER_512_4);
        r
    }
}

const COUNTER_512_4: __m512i = unsafe {
    mem::transmute([
        0u8, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
        0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
        0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
        0, 0, 0, 0, 0, 0, 0, 0, 4, 0, 0, 0, 0, 0, 0, 0, //
    ])
};

const BYTESWAP_512: __m512i = unsafe {
    mem::transmute([
        15u8, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0, //
        31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16, //
        47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32, //
        63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48, //
    ])
};

const BYTESWAP_512_EPI64: __m512i = unsafe {
    mem::transmute([
        7, 6, 5, 4, 3, 2, 1, 0, 15u8, 14, 13, 12, 11, 10, 9, 8, //
        23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24, //
        39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40, //
        55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
    ])
};

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
  after another, each through all its rounds, and so are `_cipher_avx512`'s
  four vectors of a chunk and of the tail.
- A load of 64 bytes, `_mm512_loadu_si512` or `_mm512_loadu_epi8`, is the
  vector of the four 16-byte loads in its lanes, lane 0 first
  (`loadBytes512`), and `_mm512_storeu_si512` writes the lanes' bytes the same
  way (`bytes512`). `_mm512_maskz_loadu_epi8` under a mask of a chunk's first
  bytes loads the chunk zero-padded to 64 bytes, `_mm512_mask_storeu_epi8`
  under it writes the first bytes of the vector's, and
  `_mm512_maskz_loadu_epi64` under a mask of `h`'s quadwords loads `h`'s
  blocks into the low lanes and zeros above them. A `&[__m512i; 4]` cast from
  16 `__m128i` holds them four to a vector, the first in lane 0.
- `_mm512_undefined()`, whose every lane `Counter512::new` overwrites, is
  `_mm512_setzero_si512()`, and `_mm512_broadcast_i32x4(BYTESWAP)` is computed
  once, before `GhashTableAvx512::add`'s loop, as it is.
- `round_keys_512` and `RoundKeys512::split` are `round_keys`' first, middle,
  and last keys, each broadcast to every lane, which is what they compute.
- `VaesKernel::powers`, the powers BoringSSL's key setup writes, stays opaque:
  [the VAES quest](/quest/m4/verified/aes-gcm-x86-vaes.md) models it, and the
  theorems about the 512-bit GHASH take what it holds as a hypothesis.
- The SSSE3 and integer tables' `add_by`, which no theorem here is about, stays
  opaque.
-/

namespace rind.x86_64

open rind.vale rind.simd

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

/-- 64 bytes as a 512-bit load reads them: the 16-byte loads of each lane's,
lane 0 first. -/
def loadBytes512 (bytes : List U8) : BitVec 512 :=
  ofLanes128 fun j => loadBytes ((bytes.drop (16 * j)).take 16)

/-- A 512-bit vector's bytes, as `_mm512_storeu_si512` writes them. -/
def bytes512 (v : BitVec 512) : List U8 :=
  (List.range 4).flatMap fun j => (storeBytes (lane128 v j)).val

/-- `VaesKernel::powers`: the GHASH key's powers in the kernel's table, from
the highest down to H. -/
opaque low.x86_64.aes_gcm_vaes.VaesKernel.powers :
  low.x86_64.aes_gcm_vaes.VaesKernel → Result (Slice core.core_arch.x86.__m128i)

/-- `GhashTableAvx512::powers`: H^16 down to H, four to a vector. -/
def low.x86_64.ghash.GhashTableAvx512.powers (self : low.x86_64.ghash.GhashTableAvx512) :
    Result (List core.core_arch.x86.__m512i) := do
  let p ← low.x86_64.aes_gcm_vaes.VaesKernel.powers self.vaes
  if p.val.length = 16 then ok ((List.range 4).map fun i => ofLanes128 fun j => p.val[4 * i + j]!)
  else fail .panic

/-- `ghash::TERNARY_XOR`. -/
def low.x86_64.ghash.ternaryXor : Std.I32 := 150#i32

/-- `ghash::GF128_POLY_LO`. -/
def low.x86_64.ghash.polyLo : core.core_arch.x86.__m128i := 0xc2000000_00000000_00000000_00000000#128

/-- `ghash::_mm512_extracti32x4_epi32` of each lane, XORed: the four lanes'
sum. -/
def low.x86_64.ghash.sumLanes (r : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m128i := do
  let a ← core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 0#i32 r
  let b ← core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 1#i32 r
  let c ← core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 2#i32 r
  let d ← core.core_arch.x86.avx512f._mm512_extracti32x4_epi32 3#i32 r
  let ab ← core.core_arch.x86.sse2._mm_xor_si128 a b
  core.core_arch.x86.avx512f._mm_ternarylogic_epi32 low.x86_64.ghash.ternaryXor ab c d

/-- `_mul16`. -/
def low.x86_64.ghash._mul16 (table : low.x86_64.ghash.GhashTableAvx512)
    (x0123 x4567 x89ab xcdef : core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m128i := do
  let powers ← low.x86_64.ghash.GhashTableAvx512.powers table
  let p0 := powers[0]!
  let p1 := powers[1]!
  let p2 := powers[2]!
  let p3 := powers[3]!
  let gfpoly ← core.core_arch.x86.avx512f._mm512_broadcast_i32x4 low.x86_64.ghash.polyLo
  let tx := low.x86_64.ghash.ternaryXor
  let lo0 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 0#i32 x0123 p0
  let lo1 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 0#i32 x4567 p1
  let lo2 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 0#i32 x89ab p2
  let lo01 ← core.core_arch.x86.avx512f._mm512_xor_epi32 lo0 lo1
  let lo3 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 0#i32 xcdef p3
  let lo ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi64 tx lo2 lo3 lo01
  let mi0 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 x0123 p0
  let mi1 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 x4567 p1
  let mi2 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 x89ab p2
  let mi012 ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 tx mi0 mi1 mi2
  let mi3 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 xcdef p3
  let mi4 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 16#i32 x0123 p0
  let mi01234 ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 tx mi012 mi3 mi4
  let mi5 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 16#i32 x4567 p1
  let mi6 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 16#i32 x89ab p2
  let mi ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi64 tx mi01234 mi5 mi6
  let lo_r ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 gfpoly lo
  let mi7 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 16#i32 xcdef p3
  let mi ← core.core_arch.x86.avx512f._mm512_xor_epi32 mi7 mi
  let lo_s ← core.core_arch.x86.avx512f._mm512_shuffle_epi32 78#i32 lo
  let hi0 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 17#i32 x0123 p0
  let hi1 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 17#i32 x4567 p1
  let hi2 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 17#i32 x89ab p2
  let mi ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 tx lo_r lo_s mi
  let hi3 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 17#i32 xcdef p3
  let hi012 ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 tx hi0 hi1 hi2
  let mi_r ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 gfpoly mi
  let hi ← core.core_arch.x86.avx512f._mm512_xor_epi32 hi012 hi3
  let mi_s ← core.core_arch.x86.avx512f._mm512_shuffle_epi32 78#i32 mi
  let r ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 tx mi_r mi_s hi
  low.x86_64.ghash.sumLanes r

/-- `_mul_tail`'s loop over the vectors of blocks `j` on: each times its
powers, `powers`' blocks from `16 - n + 4j`, XORed into `lo`, `mi`, and `hi`,
`current` into the first. -/
def low.x86_64.ghash.mul_tail_loop (powers : List core.core_arch.x86.__m128i) (n : Nat)
    (current : core.core_arch.x86.__m128i) :
    Nat → List core.core_arch.x86.__m512i →
    core.core_arch.x86.__m512i × core.core_arch.x86.__m512i × core.core_arch.x86.__m512i →
    Result (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i × core.core_arch.x86.__m512i)
  | _, [], acc => ok acc
  | j, x :: xs, (lo, mi, hi) => do
    let x ← if j = 0 then do
        let z ← core.core_arch.x86.avx512f._mm512_setzero_si512
        let c ← core.core_arch.x86.avx512f._mm512_inserti32x4 0#i32 z current
        core.core_arch.x86.avx512f._mm512_xor_epi64 x c
      else ok x
    let start := 16 - n + 4 * j
    if start > powers.length then fail .panic else
    let rest := powers.drop start
    let k := min (n - 4 * j) 4
    if k > rest.length then fail .panic else
    let h := ofLanes128 fun i => if i < k then rest[i]! else 0
    let t ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 0#i32 x h
    let lo ← core.core_arch.x86.avx512f._mm512_xor_epi32 lo t
    let t1 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 x h
    let t2 ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 16#i32 x h
    let mi ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 low.x86_64.ghash.ternaryXor mi t1 t2
    let t ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 17#i32 x h
    let hi ← core.core_arch.x86.avx512f._mm512_xor_epi32 hi t
    low.x86_64.ghash.mul_tail_loop powers n current (j + 1) xs (lo, mi, hi)

/-- `_mul_tail`. -/
def low.x86_64.ghash._mul_tail (table : low.x86_64.ghash.GhashTableAvx512)
    (current : core.core_arch.x86.__m128i) (x : List core.core_arch.x86.__m512i) (len : Nat) :
    Result core.core_arch.x86.__m128i := do
  if len > 256 then fail .panic else
  let n := (len + 15) / 16
  if n = 0 then ok current else
  let powers ← low.x86_64.aes_gcm_vaes.VaesKernel.powers table.vaes
  let z ← core.core_arch.x86.avx512f._mm512_setzero_si512
  let (lo, mi, hi) ← low.x86_64.ghash.mul_tail_loop powers.val n current 0 (x.take ((n + 3) / 4)) (z, z, z)
  let gfpoly ← core.core_arch.x86.avx512f._mm512_broadcast_i32x4 low.x86_64.ghash.polyLo
  let tx := low.x86_64.ghash.ternaryXor
  let lo_r ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 gfpoly lo
  let lo_s ← core.core_arch.x86.avx512f._mm512_shuffle_epi32 78#i32 lo
  let mi ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 tx lo_r lo_s mi
  let mi_r ← core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 1#i32 gfpoly mi
  let mi_s ← core.core_arch.x86.avx512f._mm512_shuffle_epi32 78#i32 mi
  let r ← core.core_arch.x86.avx512f._mm512_ternarylogic_epi32 tx mi_r mi_s hi
  low.x86_64.ghash.sumLanes r

/-- Four byte-reversed vectors of blocks, `current` XORed into the first
block, multiplied by `_mul16`. -/
def low.x86_64.ghash.hash16 (table : low.x86_64.ghash.GhashTableAvx512)
    (mask : core.core_arch.x86.__m512i) (m : List core.core_arch.x86.__m512i)
    (current : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i := do
  let m0 ← core.core_arch.x86.avx512bw._mm512_shuffle_epi8 m[0]! mask
  let m1 ← core.core_arch.x86.avx512bw._mm512_shuffle_epi8 m[1]! mask
  let m2 ← core.core_arch.x86.avx512bw._mm512_shuffle_epi8 m[2]! mask
  let m3 ← core.core_arch.x86.avx512bw._mm512_shuffle_epi8 m[3]! mask
  let z ← core.core_arch.x86.avx512f._mm512_setzero_si512
  let c ← core.core_arch.x86.avx512f._mm512_inserti32x4 0#i32 z current
  let m0 ← core.core_arch.x86.avx512f._mm512_xor_epi64 m0 c
  low.x86_64.ghash._mul16 table m0 m1 m2 m3

/-- `GhashTableAvx512::add`'s loop over the 256-byte chunks. -/
def low.x86_64.ghash.GhashTableAvx512.add_loop (self : low.x86_64.ghash.GhashTableAvx512)
    (mask : core.core_arch.x86.__m512i) :
    List (List U8) → core.core_arch.x86.__m128i → Result core.core_arch.x86.__m128i
  | [], current => ok current
  | chunk16 :: chunks, current => do
    let current ← low.x86_64.ghash.hash16 self mask ((chunksOf 64 chunk16).map loadBytes512) current
    low.x86_64.ghash.GhashTableAvx512.add_loop self mask chunks current

/-- `GhashTableAvx512::add`, the 512-bit GHASH. -/
def low.x86_64.ghash.GhashTableAvx512.add (self : low.x86_64.ghash.GhashTableAvx512) (bytes : List U8)
    (current : core.core_arch.x86.__m128i) : Result core.core_arch.x86.__m128i := do
  let s ← low.x86_64.ghash.BYTESWAP
  let mask ← core.core_arch.x86.avx512f._mm512_broadcast_i32x4 s
  let current ← low.x86_64.ghash.GhashTableAvx512.add_loop self mask (chunksOf 256 bytes) current
  low.x86_64.ghash.ClmulTable.add self.clmul (chunksRest 256 bytes) current

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

/-- `HwKey::round_keys_512` split by `RoundKeys512::split`: `round_keys`' keys,
each broadcast to every lane. -/
def low.x86_64.aes.HwKey.round_keys_512 (key : low.x86_64.aes.HwKey) :
    Result (core.core_arch.x86.__m512i × List core.core_arch.x86.__m512i × core.core_arch.x86.__m512i) := do
  let (f, rks, l) := low.x86_64.aes.HwKey.round_keys key
  let f ← core.core_arch.x86.avx512f._mm512_broadcast_i32x4 f
  let rks ← rks.mapM core.core_arch.x86.avx512f._mm512_broadcast_i32x4
  let l ← core.core_arch.x86.avx512f._mm512_broadcast_i32x4 l
  ok (f, rks, l)

/-- `aes_gcm::COUNTER_512_4`: 4 in each lane's counter word. -/
def low.x86_64.aes_gcm.COUNTER_512_4 : Result core.core_arch.x86.__m512i :=
  ok 0x00000000000000040000000000000000000000000000000400000000000000000000000000000004000000000000000000000000000000040000000000000000#512

/-- `aes_gcm::BYTESWAP_512`. -/
def low.x86_64.aes_gcm.BYTESWAP_512 : Result core.core_arch.x86.__m512i :=
  ok 0x303132333435363738393a3b3c3d3e3f202122232425262728292a2b2c2d2e2f101112131415161718191a1b1c1d1e1f000102030405060708090a0b0c0d0e0f#512

/-- `aes_gcm::BYTESWAP_512_EPI64`. -/
def low.x86_64.aes_gcm.BYTESWAP_512_EPI64 : Result core.core_arch.x86.__m512i :=
  ok 0x38393a3b3c3d3e3f303132333435363728292a2b2c2d2e2f202122232425262718191a1b1c1d1e1f101112131415161708090a0b0c0d0e0f0001020304050607#512

/-- `Counter512::new`: the four counters after `bytes`, each as `Counter`
keeps it, lane 0 first. -/
def low.x86_64.aes_gcm.Counter512.new (bytes : Std.Array U8 16#usize) :
    Result core.core_arch.x86.__m512i := do
  let cnt ← low.x86_64.aes_gcm.Counter.new bytes
  let (a, cnt) ← low.x86_64.aes_gcm.Counter.next cnt
  let (b, cnt) ← low.x86_64.aes_gcm.Counter.next cnt
  let (c, cnt) ← low.x86_64.aes_gcm.Counter.next cnt
  let (d, _) ← low.x86_64.aes_gcm.Counter.next cnt
  let s ← low.x86_64.aes_gcm.BYTESWAP_EPI64
  let r ← core.core_arch.x86.avx512f._mm512_setzero_si512
  let a ← core.core_arch.x86.ssse3._mm_shuffle_epi8 a s
  let r ← core.core_arch.x86.avx512f._mm512_inserti32x4 0#i32 r a
  let b ← core.core_arch.x86.ssse3._mm_shuffle_epi8 b s
  let r ← core.core_arch.x86.avx512f._mm512_inserti32x4 1#i32 r b
  let c ← core.core_arch.x86.ssse3._mm_shuffle_epi8 c s
  let r ← core.core_arch.x86.avx512f._mm512_inserti32x4 2#i32 r c
  let d ← core.core_arch.x86.ssse3._mm_shuffle_epi8 d s
  core.core_arch.x86.avx512f._mm512_inserti32x4 3#i32 r d

/-- `Counter512::next4`: four counter blocks, and the counters after them. -/
def low.x86_64.aes_gcm.Counter512.next4 (self : core.core_arch.x86.__m512i) :
    Result (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i) := do
  let s ← low.x86_64.aes_gcm.BYTESWAP_512_EPI64
  let r ← core.core_arch.x86.avx512bw._mm512_shuffle_epi8 self s
  let four ← low.x86_64.aes_gcm.COUNTER_512_4
  let c ← core.core_arch.x86.avx512f._mm512_add_epi32 self four
  ok (r, c)

/-- `_cipher_avx512`'s AES of a vector before its last round: the first round
key XORed, then `VAESENC` with each of `rks`. -/
def low.x86_64.aes_gcm.rounds512 (c rk_first : core.core_arch.x86.__m512i)
    (rks : List core.core_arch.x86.__m512i) : Result core.core_arch.x86.__m512i := do
  let c ← core.core_arch.x86.avx512f._mm512_xor_epi32 c rk_first
  rks.foldlM core.core_arch.x86.vaes._mm512_aesenc_epi128 c

/-- `_cipher_avx512`'s AES of a vector: `rounds512`, then `VAESENCLAST`. -/
def low.x86_64.aes_gcm.encrypt512 (c rk_first : core.core_arch.x86.__m512i)
    (rks : List core.core_arch.x86.__m512i) (rk_last : core.core_arch.x86.__m512i) :
    Result core.core_arch.x86.__m512i := do
  let c ← low.x86_64.aes_gcm.rounds512 c rk_first rks
  core.core_arch.x86.vaes._mm512_aesenclast_epi128 c rk_last

/-- `_cipher_avx512`'s loop over the 256-byte chunks: the counter and hash
after them, and their output. -/
def low.x86_64.aes_gcm.by16_loop (ENC : Bool) (table : low.x86_64.ghash.GhashTableAvx512)
    (rk_first : core.core_arch.x86.__m512i) (rks : List core.core_arch.x86.__m512i)
    (rk_last : core.core_arch.x86.__m512i) :
    List (List U8) → core.core_arch.x86.__m512i → core.core_arch.x86.__m128i →
    Result (core.core_arch.x86.__m512i × core.core_arch.x86.__m128i × List U8)
  | [], counter, current => ok (counter, current, [])
  | blocks :: chunks, counter, current => do
    let (c0123, counter) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let (c4567, counter) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let (c89ab, counter) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let (ccdef, counter) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let k0123 ← low.x86_64.aes_gcm.encrypt512 c0123 rk_first rks rk_last
    let k4567 ← low.x86_64.aes_gcm.encrypt512 c4567 rk_first rks rk_last
    let k89ab ← low.x86_64.aes_gcm.encrypt512 c89ab rk_first rks rk_last
    let kcdef ← low.x86_64.aes_gcm.encrypt512 ccdef rk_first rks rk_last
    let ps := (chunksOf 64 blocks).map loadBytes512
    let c0123 ← core.core_arch.x86.avx512f._mm512_xor_epi32 k0123 ps[0]!
    let c4567 ← core.core_arch.x86.avx512f._mm512_xor_epi32 k4567 ps[1]!
    let c89ab ← core.core_arch.x86.avx512f._mm512_xor_epi32 k89ab ps[2]!
    let ccdef ← core.core_arch.x86.avx512f._mm512_xor_epi32 kcdef ps[3]!
    let cs := [c0123, c4567, c89ab, ccdef]
    let s ← low.x86_64.aes_gcm.BYTESWAP_512
    let current ← low.x86_64.ghash.hash16 table s (if ENC then cs else ps) current
    let (counter, current, out) ←
      low.x86_64.aes_gcm.by16_loop ENC table rk_first rks rk_last chunks counter current
    ok (counter, current, cs.flatMap bytes512 ++ out)

/-- `_cipher_avx512`'s loop over the tail's chunks of up to 64 bytes, each
zipped with its counters' AES before the last round: the vectors it hashes,
and its output. -/
def low.x86_64.aes_gcm.by16_tail_loop (ENC : Bool) (rk_last : core.core_arch.x86.__m512i) :
    List core.core_arch.x86.__m512i → List (List U8) → Result (List core.core_arch.x86.__m512i × List U8)
  | k :: ks, chunk :: chunks => do
    let mask : Std.U64 := ⟨BitVec.allOnes 64 >>> (64 - chunk.length)⟩
    let p := loadBytes512 (chunk ++ List.replicate (64 - chunk.length) 0#u8)
    let e ← core.core_arch.x86.vaes._mm512_aesenclast_epi128 k rk_last
    let e ← core.core_arch.x86.avx512bw._mm512_maskz_mov_epi8 mask e
    let c ← core.core_arch.x86.avx512f._mm512_xor_epi32 e p
    let s ← low.x86_64.aes_gcm.BYTESWAP_512
    let t ← core.core_arch.x86.avx512bw._mm512_shuffle_epi8 (if ENC then c else p) s
    let (ts, out) ← low.x86_64.aes_gcm.by16_tail_loop ENC rk_last ks chunks
    ok (t :: ts, (bytes512 c).take chunk.length ++ out)
  | _, _ => ok ([], [])

/-- `_cipher_avx512`. -/
def low.x86_64.aes_gcm._cipher_avx512 (ENC : Bool) (key : low.x86_64.aes.HwKey)
    (ghash : low.x86_64.ghash.Ghash) (initial_counter : Std.Array U8 16#usize) (aad cipher_inout : Slice U8)
    (_feature_token : low.x86_64.cpu.HaveAvx512ForAesGcm) : Result (low.x86_64.ghash.Ghash × Slice U8) := do
  let ghash ← low.x86_64.ghash.Ghash.addBytes ghash aad.val
  let (rk_first, rks, rk_last) ← low.x86_64.aes.HwKey.round_keys_512 key
  let counter ← low.x86_64.aes_gcm.Counter512.new initial_counter
  let table ← match ghash.table with
    | .Avx512 table => ok table
    | _ => fail .panic
  let (counter, current, head) ← low.x86_64.aes_gcm.by16_loop ENC table rk_first rks rk_last
    (chunksOf 256 cipher_inout.val) counter ghash.current
  let ghash := { ghash with current }
  let rest := chunksRest 256 cipher_inout.val
  let (ghash, out) ← if rest.isEmpty then ok (ghash, head) else do
    let (k0, counter) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let (k1, counter) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let (k2, counter) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let (k3, _) ← low.x86_64.aes_gcm.Counter512.next4 counter
    let ks ← [k0, k1, k2, k3].mapM fun k => low.x86_64.aes_gcm.rounds512 k rk_first rks
    let (ts, tail_out) ← low.x86_64.aes_gcm.by16_tail_loop ENC rk_last ks (chunksUpTo 64 rest)
    let current ← low.x86_64.ghash._mul_tail table ghash.current (ts ++ List.replicate (4 - ts.length) 0)
      rest.length
    ok ({ ghash with current }, head ++ tail_out)
  if h : out.length ≤ Usize.max then ok (ghash, Slice.from out h) else fail .panic

/-! The other AES-GCM kernels, which no theorem here is about. -/

opaque low.x86_64.aes_gcm.composed
  (ENC : Bool) :
  low.x86_64.aes.AesKey → low.x86_64.ghash.Ghash → Std.Array U8 16#usize → Slice U8 → Slice U8 →
    Result (low.x86_64.ghash.Ghash × Slice U8)


opaque low.x86_64.aes_gcm_vaes.VaesKernel.cipher
  (ENC : Bool) :
  low.x86_64.aes_gcm_vaes.VaesKernel → low.x86_64.aes.HwKey → Std.Array U8 16#usize →
    low.x86_64.ghash.Ghash → Slice U8 → Result (low.x86_64.ghash.Ghash × Slice U8)

end rind.x86_64
