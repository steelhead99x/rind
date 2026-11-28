import RindIsa.X86_64.PolyHashAd

/-!
# ChaCha20-Poly1305's AVX2 seal

rind's naked function `low::x86_64::chacha20poly1305::seal_avx2`, its
structured copy of the AVX2 half of aws-lc's `chacha20_poly1305_seal`
(`crypto/cipher_extra/asm/chacha20_poly1305_x86_64.pl`), in rind's model of
x86_64: `(out = rdi, in = rsi, len = rdx, aad = rcx, aad_len = r8, data =
r9)`, `data` the key, the counter, and the nonce. It interleaves AVX2
ChaCha20, two blocks to a `ymm` register, with scalar Poly1305 on `mulx`,
whose accumulator stays in `r10`–`r12` and whose clamped `r` stays on the
stack frame at `rbp`, and returns the tag in `rax` (its first eight bytes)
and `rdx`.

The copy keeps aws-lc's instructions but lays its control flow out as
`Code`'s `ite` and `loop`, so the program is one structured term. Where
aws-lc's text jumps into the middle of a loop or shares a tail between
paths, the copy re-tests a flag (`testq`, `cmpq`) or clears a count (`xorl
%ecx,%ecx`) so that each path takes the same instructions in the same
order; it inlines `poly_hash_ad_internal` (`PolyHashAd.prog`); it drops
`extra_in`, which rind never passes; it returns the tag in registers rather
than through `data`, so it no longer saves `r9`; and its last partial block
copies `xmm15` with `movdqa` rather than `movdqu`, the same move. ALGORITHMS.md
lists it as a deliberate change.

`admin/prove lean` checks that `function sealAvx2 repRet` is the function's
bytes and relocations as rind's build emits them, and that the static
`CONSTS` begins with `consts`' words.
-/

namespace Rind.X86_64.ChaCha20Poly1305

open VG VG.X86_64

/-- The name of the static of constants. -/
def constsName : String := "chacha20_consts"

/-- The static's words, little-endian: aws-lc's `chacha20_consts` (RFC
8439's ChaCha20 constant twice, the `pshufb` masks rotating each 32-bit lane
left by 8 and 16, the counter increments, and RFC 8439's Poly1305 clamp of
`r`), then its `and_masks`, which keep the first 1 to 16 bytes of a block. -/
