// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::ops::{Deref, DerefMut};

use crate::Error;
use crate::low;

#[derive(Clone, Debug)]
pub(crate) struct PosInt<const N: usize> {
    words: [u64; N],
    used: usize,
}

impl<const N: usize> PosInt<N> {
    /// Makes a minimum-width zero.
    pub(crate) fn zero() -> Self {
        Self {
            words: [0; N],
            used: 0,
        }
    }

    /// Makes a minimum-width, single-word value.
    pub(crate) fn word(w: u64) -> Self {
        let mut r = Self::zero();
        r.push_word(w).unwrap();
        r
    }

    /// Makes a minimum-width one.
    pub(crate) fn one() -> Self {
        let mut r = Self::zero();
        r.words[0] = 1;
        r.used = 1;
        r
    }

    /// Makes a one, but at the width of `self`.
    pub(crate) fn fixed_one(&self) -> Self {
        let mut one = Self::one();
        one.expand(self);
        one
    }

    /// Widen `self` to `other`.
    pub(crate) fn expand(&mut self, other: &Self) {
        // nb, self and other are both of type `Self`, so they have
        // the same size backing store, and `self` has zero words above
        // its used words. inductively that means this is safe.
        // compare this with `widen()`.
        self.used = other.used;
    }

    /// Replaces top word with `word` and increases `used`.
    ///
    /// This means `Self::zero().push_word(1)` == `Self::one()`,
    /// and notably that is not the same as `1 << 64`!
    fn push_word(&mut self, word: u64) -> Result<(), Error> {
        if self.used == N {
            return Err(Error::WrongLength);
        }

        self.words[self.used] = word;
        self.used += 1;
        Ok(())
    }

    /// Makes a value from little-endian `words`, `words.len()` wide.
    pub(crate) fn from_words(words: &[u64]) -> Result<Self, Error> {
        let mut r = Self::zero();
        r.words
            .get_mut(..words.len())
            .ok_or(Error::WrongLength)?
            .copy_from_slice(words);
        r.used = words.len();
        Ok(r)
    }

    pub(crate) fn from_bytes(bytes: &[u8]) -> Result<Self, Error> {
        let mut r = Self::zero();

        let bytes = trim_leading_zeroes(bytes);

        if bytes.len() > N * 8 {
            return Err(Error::WrongLength);
        }

        let mut words = bytes.rchunks_exact(8);

        for word_bytes in words.by_ref() {
            r.push_word(u64::from_be_bytes(word_bytes.try_into().unwrap()))?;
        }

        let remainder = words.remainder();
        let mut final_word = 0;
        for byte in remainder.iter() {
            final_word = (final_word << 8) | (*byte as u64);
        }

        if final_word != 0 {
            r.push_word(final_word)?;
        }

        Ok(r)
    }

    pub(crate) fn to_bytes<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let required_bytes = self.used * 8;
        let out = out.get_mut(..required_bytes).ok_or(Error::WrongLength)?;

        let (chunks, _) = out.as_chunks_mut::<8>();
        for (chunk, word) in chunks.iter_mut().rev().zip(self.as_words().iter()) {
            chunk.copy_from_slice(&word.to_be_bytes());
        }

        Ok(out)
    }

    /// Like `to_bytes`, but guarantees a zero byte prefix.
    ///
    /// This means, if the result is used in an ASN.1 encoded integer, the encoding
    /// is positive.
    pub(crate) fn to_bytes_asn1<'a>(&self, out: &'a mut [u8]) -> Result<&'a [u8], Error> {
        let required_bytes = self.used * 8 + 1;
        let out = out.get_mut(..required_bytes).ok_or(Error::WrongLength)?;

        out[0] = 0x00;
        {
            let (_, val) = out.split_at_mut(1);

            let (chunks, _) = val.as_chunks_mut::<8>();
            for (chunk, word) in chunks.iter_mut().rev().zip(self.as_words().iter()) {
                chunk.copy_from_slice(&word.to_be_bytes());
            }
        }

        Ok(out)
    }

    #[allow(dead_code)]
    pub(crate) fn debug(&self, why: &str) {
        let mut bytes = [0u8; 1024];
        let bytes = self.to_bytes(&mut bytes).unwrap();
        print!("{why} = 0x");
        for b in bytes {
            print!("{b:02x}");
        }
        println!();
    }

    pub(crate) fn len_bytes(&self) -> usize {
        self.len_bits().wrapping_add(7) / 8
    }

    pub(crate) fn len_bits(&self) -> usize {
        low::bignum_bitsize(self.as_words())
    }

    pub(crate) fn count_trailing_zeroes(&self) -> usize {
        low::bignum_ctz(self.as_words())
    }

    pub(crate) fn is_even(&self) -> bool {
        self.words[0] & 1 == 0
    }

    /// Return true if `gcd(self, other)` is one
    pub(crate) fn is_coprime(&self, other: &Self) -> bool {
        const { assert!(N <= MAX_SCRATCH_WORDS) };
        // On the stack, so nothing derived from a key outlives the call.
        let mut tmp = [0u64; 2 * MAX_SCRATCH_WORDS];
        low::bignum_coprime(self.as_words(), other.as_words(), &mut tmp[..N + N])
    }

    /// The significant words.
    pub(crate) fn as_words(&self) -> &[u64] {
        &self.words[..self.used]
    }

    fn as_mut_words(&mut self) -> &mut [u64] {
        &mut self.words[..self.used]
    }

    /// This is `as_words()`, but taking the length of `len`.
    ///
    /// This is safe assuming `len.used` is in range (a fundamental invariant in this type)
    /// because `len` and `self` share the same type.
    fn as_words_with_len_of(&self, len: &Self) -> &[u64] {
        &self.words[..len.used]
    }

    /// Constant-time equality
    pub(crate) fn equals(&self, other: &Self) -> bool {
        low::bignum_eq(self.as_words(), other.as_words())
    }

    #[cfg(test)]
    pub(crate) fn pub_equals(&self, other: &Self) -> bool {
        // eliminate trailing zero words, which we can do here
        // because this is a `pub_` function
        let mut s_used = self.used;
        while s_used != 0 {
            if self.words[s_used - 1] == 0 {
                s_used -= 1;
            } else {
                break;
            }
        }

        let mut o_used = other.used;
        while o_used != 0 {
            if other.words[o_used - 1] == 0 {
                o_used -= 1;
            } else {
                break;
            }
        }

        self.words[..s_used] == other.words[..o_used]
    }

    /// Returns `self` < `other`.
    pub(crate) fn less_than(&self, other: &Self) -> bool {
        low::bignum_cmp_lt(self.as_words(), other.as_words()) > 0
    }

    /// Returns the "montifier" for arithmetic mod `self`: M^2 mod self.
    #[must_use]
    pub(crate) fn montifier(&self) -> Self {
        let mut tmp = Self::zero();
        tmp.used = self.used;
        let mut montifier = Self::zero();
        montifier.used = self.used;
        low::bignum_montifier(
            montifier.as_mut_words(),
            self.as_words(),
            tmp.as_mut_words(),
        );
        montifier
    }

    /// Returns [`Self::montifier`] for a public `self` with a nonzero top
    /// word, faster: it runs in variable time. A zero top word gives zero.
    ///
    /// This divides as aws-lc does: from 2^(64 * (width - 1)), which is below
    /// `self`, each of width + 1 steps of long division multiplies by 2^64,
    /// ending at M^2 mod `self`.
    #[must_use]
    pub(crate) fn pub_montifier(&self) -> Self {
        let k = self.used;
        let Some(&top) = self.as_words().last().filter(|top| **top != 0) else {
            return Self::zero();
        };

        // Shift both so the divisor's top bit is set, as `mul_word_mod` needs.
        let shift = top.leading_zeros();
        let mut d = Self::zero();
        d.used = k;
        for i in 0..k {
            let below = i.checked_sub(1).map_or(0, |i| self.words[i]);
            d.words[i] = self.words[i] << shift | below.checked_shr(64 - shift).unwrap_or(0);
        }
        let mut r = Self::zero();
        r.used = k;
        r.words[k - 1] = 1 << shift;

        for _ in 0..=k {
            mul_word_mod(r.as_mut_words(), d.as_words());
        }

        for i in 0..k {
            let above = r.words.get(i + 1).copied().filter(|_| i + 1 < k);
            r.words[i] = r.words[i] >> shift
                | above.map_or(0, |above| above.checked_shl(64 - shift).unwrap_or(0));
        }
        r
    }

    /// Bring `self` into montgomery domain, self * M^2 * M^-1 mod n
    #[must_use]
    pub(crate) fn to_montgomery(&self, montifier: &Self, n: &Self) -> Self {
        self.mont_mul(montifier, n, n.mont_neg_inverse())
    }

    #[must_use]
    pub(crate) fn mont_neg_inverse(&self) -> u64 {
        // The inverse's low word depends only on the low word.
        let mut n0 = [0];
        low::bignum_negmodinv(&mut n0, &self.words[..1]);
        n0[0]
    }

    /// Return `self` ^ 2 in montgomery domain, self ^ 2 * M^-1 mod n.
    ///
    /// `n0` is `n.mont_neg_inverse()`.
    #[must_use]
    pub(crate) fn mont_sqr(&self, n: &Self, n0: u64) -> Self {
        let mut r = Self::zero();
        self.mont_sqr_into(&mut r, n, n0);
        r
    }

    /// Variant of `mont_sqr` that writes the result to `out`, so a loop can
    /// alternate between two values rather than copy each result.
    pub(crate) fn mont_sqr_into(&self, out: &mut Self, n: &Self, n0: u64) {
        out.used = n.used;
        low::mont_sqr(
            out.as_mut_words(),
            self.as_words_with_len_of(n),
            n.as_words(),
            n0,
        );
    }

    /// Return `self` * v in montgomery domain, self * v * M^-1 mod n.
    ///
    /// `n0` is `n.mont_neg_inverse()`.
    #[must_use]
    pub(crate) fn mont_mul(&self, v: &Self, n: &Self, n0: u64) -> Self {
        let mut r = Self::zero();
        self.mont_mul_into(v, &mut r, n, n0);
        r
    }

    /// Variant of `mont_mul` that writes the result to `out`, as
    /// `mont_sqr_into` does.
    pub(crate) fn mont_mul_into(&self, v: &Self, out: &mut Self, n: &Self, n0: u64) {
        out.used = n.used;
        low::mont_mul(
            out.as_mut_words(),
            self.as_words_with_len_of(n),
            v.as_words_with_len_of(n),
            n.as_words(),
            n0,
        );
    }

    #[must_use]
    fn mont_redc<const M: usize>(&self, n: &PosInt<M>) -> PosInt<M> {
        let mut tmp = PosInt::<M>::zero();
        tmp.used = n.used;
        low::bignum_montredc(
            tmp.as_mut_words(),
            self.as_words(),
            n.as_words(),
            n.as_words().len() as u64,
        );
        tmp
    }

    /// Reduce `self` mod `n`.
    ///
    /// `n` must be odd.
    /// `n_montifier` is `n.montifier()`.
    #[must_use]
    pub(crate) fn reduce<const M: usize>(
        &self,
        n: &PosInt<M>,
        n_montifier: &PosInt<M>,
    ) -> PosInt<M> {
        assert!(M < N);
        // do this by montgomery reduction (leaving one inverse-M term) then multiply out M
        self.mont_redc(n).to_montgomery(n_montifier, n)
    }

    /// Bring `self` out of montgomery domain, self * M^-1 mod n.
    #[must_use]
    #[allow(clippy::wrong_self_convention)]
    pub(crate) fn from_montgomery(self, n: &Self) -> Self {
        // On x86_64, `mont_mul` by one measured faster than s2n-bignum's
        // generic `bignum_demont`, and the portable `bignum_demont` takes
        // only group orders.
        #[cfg(not(rind_backend = "aarch64"))]
        return self.mont_mul(&n.fixed_one(), n, n.mont_neg_inverse());

        #[cfg(rind_backend = "aarch64")]
        {
            let mut demont = Self::zero();
            demont.used = n.used;
            low::bignum_demont(demont.as_mut_words(), self.as_words(), n.as_words());
            demont
        }
    }

    /// Returns a * b
    #[must_use]
    pub(crate) fn mul<const M: usize>(a: &Self, b: &Self) -> PosInt<M> {
        assert!(M >= N + N);
        let mut r = PosInt::<M>::zero();
        r.used = a.used + b.used;
        low::bignum_mul(r.as_mut_words(), a.as_words(), b.as_words());
        r
    }

    /// Computes each of `pair`, as [`Self::mod_exp`] does: two at once by
    /// aws-lc's dual RSAZ where it is the fastest, on x86_64 CPUs with
    /// AVX-512 IFMA, for moduli of 16, 24, or 32 words each, and exponents
    /// no wider.
    pub(crate) fn mod_exp_pair(pair: [ModExp<'_, N>; 2]) -> [Self; 2] {
        #[cfg(rind_backend = "x86_64")]
        if let Some(r) = Self::mod_exp_pair_rsaz(&pair) {
            return r;
        }

        pair.map(|x| x.base.mod_exp(x.e, x.n, x.n_montifier, x.n_0))
    }

    /// [`Self::mod_exp_pair`] by aws-lc's dual RSAZ, which takes every word
    /// of `e` to `n`'s width, so the trace depends on none of the values.
    #[cfg(rind_backend = "x86_64")]
    fn mod_exp_pair_rsaz(pair: &[ModExp<'_, N>; 2]) -> Option<[Self; 2]> {
        let k = pair[0].n.used;
        if pair.iter().any(|x| x.n.used != k || x.e.used > k) {
            return None;
        }
        let rsaz = low::RsazAvx512::check(k)?;
        // Each word above `used` is zero.
        let mut r = [Self::zero(), Self::zero()];
        let [r0, r1] = &mut r;
        r0.used = k;
        r1.used = k;
        rsaz.mod_exp(
            [&mut r0.words[..k], &mut r1.words[..k]],
            pair.each_ref().map(|x| low::Operands {
                x: &x.base.words[..k],
                e: &x.e.words[..k],
                m: &x.n.words[..k],
                rr: &x.n_montifier.words[..k],
                n0: x.n_0,
            }),
        );
        Some(r)
    }

    /// Computes `self` ^ `e` mod `n`.
    ///
    /// `self` is not in the montgomery domain, and neither is the result.
    ///
    /// `n_montifier` is `n.montifier()`.
    /// `n_0` is `n.mont_neg_inverse()`.
    ///
    /// This is done in a side-channel-free way, with respect to the values of `self`, `e`,
    /// `n` and `n_0`.  The instruction trace depends only on `e.used` and `n.used`.
    fn mod_exp(&self, e: &Self, n: &Self, n_montifier: &Self, n_0: u64) -> Self {
        #[cfg(rind_backend = "x86_64")]
        if let Some(r) = self.mod_exp_rsaz(e, n, n_montifier, n_0) {
            return r;
        }

        let one_mont = n.fixed_one().mont_mul(n_montifier, n, n_0);
        let self_mont = self.to_montgomery(n_montifier, n);

        self_mont.mont_exp(one_mont, e, n, n_0).from_montgomery(n)
    }

    /// [`Self::mod_exp`] by aws-lc's RSAZ, for a 16-word `n` and an `e` no
    /// wider, where it is the fastest: on x86_64 CPUs with AVX2 but without
    /// ADX. RSAZ takes every 1024 bits of `e`, so the trace depends on none
    /// of the values.
    #[cfg(rind_backend = "x86_64")]
    fn mod_exp_rsaz(&self, e: &Self, n: &Self, n_montifier: &Self, n_0: u64) -> Option<Self> {
        let rsaz = low::Rsaz::check()?;
        if n.used != 16 || e.used > 16 {
            return None;
        }
        // Each word above `used` is zero.
        let mut r = Self::zero();
        r.used = n.used;
        rsaz.mod_exp(
            r.words.first_chunk_mut()?,
            self.words.first_chunk()?,
            e.words.first_chunk()?,
            n.words.first_chunk()?,
            n_montifier.words.first_chunk()?,
            n_0,
        );
        Some(r)
    }

    /// Computes `self` ^ `e` mod `n`.
    ///
    /// `self` is in the montgomery domain, and so is the result.
    ///
    /// `one_mont` is the identity in the montgomery domain.
    /// `n_0` is `n.mont_neg_inverse()`.
    ///
    /// This is done in a side-channel-free way, with respect to the values of `self`, `e`,
    /// `n` and `n_0`.  The instruction trace depends only on `e.used` and `n.used`.
    #[cfg(rind_backend = "x86_64")]
    pub(crate) fn mont_exp(&self, one_mont: Self, e: &Self, n: &Self, n_0: u64) -> Self {
        let mut r = Self::zero();
        r.used = n.used;
        low::mont_exp(
            r.as_mut_words(),
            self.as_words_with_len_of(n),
            one_mont.as_words_with_len_of(n),
            e.as_words(),
            n.as_words(),
            n_0,
        );
        r
    }

    /// Computes `self` ^ `e` mod `n`, as the x86_64 `mont_exp` does, by a
    /// 5-bit window over `mont_mul` and `mont_sqr`.
    #[cfg(not(rind_backend = "x86_64"))]
    pub(crate) fn mont_exp(&self, one_mont: Self, e: &Self, n: &Self, n_0: u64) -> Self {
        const WINDOW: usize = 5;
        let k = n.used;
        let Some(top) = (e.used * 64).checked_sub(1) else {
            return one_mont;
        };

        // `table` holds `self^i` at row `i`: each even power squares its
        // half, and each odd one multiplies the power below it by `self`.
        let mut table = vec![0; k << WINDOW];
        table[..k].copy_from_slice(one_mont.as_words_with_len_of(n));
        table[k..2 * k].copy_from_slice(self.as_words_with_len_of(n));
        for i in 2..1 << WINDOW {
            let (done, rest) = table.split_at_mut(i * k);
            let row = |j: usize| &done[j * k..(j + 1) * k];
            match i % 2 {
                0 => low::mont_sqr(&mut rest[..k], row(i / 2), n.as_words(), n_0),
                _ => low::mont_mul(&mut rest[..k], row(i - 1), row(1), n.as_words(), n_0),
            }
        }
        // Reads every row, so the trace is the same whichever it takes.
        let select = |z: &mut Self, i: u64| {
            low::bignum_copy_row_from_table(z.as_mut_words(), &table, 1 << WINDOW, k as u64, i)
        };

        // Each product goes to the other of these, then they swap roles.
        let mut term = Self::zero();
        term.used = k;
        let (mut a, mut b) = (term.clone(), term.clone());
        let (mut accum, mut spare) = (&mut a, &mut b);

        // The top window takes what is left above whole windows, starting
        // `accum` at its power rather than squaring `one_mont`.
        let mut lsb = top - top % WINDOW;
        select(accum, window_bits(e.as_words(), lsb, top + 1 - lsb));
        while lsb > 0 {
            lsb -= WINDOW;
            for _ in 0..WINDOW {
                accum.mont_sqr_into(spare, n, n_0);
                core::mem::swap(&mut accum, &mut spare);
            }
            select(&mut term, window_bits(e.as_words(), lsb, WINDOW));
            accum.mont_mul_into(&term, spare, n, n_0);
            core::mem::swap(&mut accum, &mut spare);
        }

        // The powers of a secret base, on the heap.
        low::zeroise(&mut table);
        accum.clone()
    }

    /// Computes the multiplicative inverse of `self` mod `n`.
    ///
    /// For that, `self` and `n` must be coprime: check with `is_coprime()`
    /// first.
    #[must_use]
    pub(crate) fn mod_inverse(&self, n: &Self) -> Self {
        let mut r = Self::zero();
        r.used = n.used;
        const { assert!(N <= MAX_SCRATCH_WORDS) };
        // On the stack, as `is_coprime`'s.
        let mut temp = [0u64; 3 * MAX_SCRATCH_WORDS];
        low::bignum_modinv(
            r.as_mut_words(),
            self.as_words_with_len_of(n),
            n.as_words(),
            &mut temp[..N * 3],
        );
        r
    }

    /// Computes `self` mod `m`, where `m` may be even but its top word is
    /// nonzero.
    ///
    /// Use `reduce()` if `m` is odd; it will be faster.
    #[must_use]
    pub(crate) fn reduce_even<const M: usize>(&self, m: &PosInt<M>) -> PosInt<M> {
        assert!(M < N);

        let mut a = PosInt::<M>::zero();
        a.used = m.used;
        let mut b = a.clone();
        let mut addend = a.clone();

        // First, observe that any value of M-1 words cannot change
        // when reduced by m (M := |m|).  So we can copy these top words
        // in directly.
        let limit = a.used.saturating_sub(1);
        let i = self.used.saturating_sub(limit);
        let top = &self.words[i..self.used];
        a.words[..top.len()].copy_from_slice(top);

        // The remaining bits are shifted in by doubling, then added, a word
        // at a time where a word is below `m`, as it is when `m` is wider,
        // and a bit at a time otherwise. Each step writes to the other of
        // `a` and `b`, then they swap roles.
        let bits = if m.used > 1 { 64 } else { 1 };
        let (mut r, mut next) = (&mut a, &mut b);
        for j in (0..i).rev() {
            for piece in (0..64 / bits).rev() {
                for _ in 0..bits {
                    low::bignum_modadd(
                        next.as_mut_words(),
                        r.as_words(),
                        r.as_words(),
                        m.as_words(),
                    );
                    core::mem::swap(&mut r, &mut next);
                }

                addend.words[0] = self.words[j] >> (piece * bits) & u64::MAX >> (64 - bits);
                low::bignum_modadd(
                    next.as_mut_words(),
                    r.as_words(),
                    addend.as_words(),
                    m.as_words(),
                );
                core::mem::swap(&mut r, &mut next);
            }
        }
        r.clone()
    }

    /// Computes `self` + `b`
    #[must_use]
    pub(crate) fn add(&self, b: &Self) -> Self {
        let mut r = Self::zero();
        low::bignum_add(&mut r.words, self.as_words(), b.as_words());
        r.used = low::bignum_digitsize(&r.words);
        r
    }

    /// Computes `self` - `b`
    #[must_use]
    pub(crate) fn sub(&self, b: &Self) -> Self {
        let mut r = Self::zero();
        r.used = self.used;
        // TODO: could pull in bignum_sub for this.
        low::bignum_optsub(
            r.as_mut_words(),
            self.as_words(),
            b.as_words_with_len_of(self),
            1,
        );
        r
    }

    /// Computes `self` - `b` mod `p`
    #[must_use]
    pub(crate) fn sub_mod(&self, b: &Self, p: &Self) -> Self {
        let mut r = Self::zero();
        r.used = p.used;
        low::bignum_modsub(
            r.as_mut_words(),
            self.as_words(),
            b.as_words(),
            p.as_words(),
        );
        r
    }

    /// Zero extends `self` to have a larger representation.
    #[must_use]
    pub(crate) fn widen<const M: usize>(&self) -> PosInt<M> {
        assert!(M >= N);
        let mut r = PosInt::<M>::zero();
        r.words[..self.used].copy_from_slice(self.as_words());
        r.used = self.used;
        r
    }
}

// All-zero bytes are a valid zero.
impl<const N: usize> low::Zeroable for PosInt<N> {}

/// The widest operands of `is_coprime` and `mod_inverse`, an 8192-bit
/// modulus, whose scratch is sized for it on the stack.
const MAX_SCRATCH_WORDS: usize = 128;

/// `base` ^ `e` mod `n`, one of a pair for [`PosInt::mod_exp_pair`], where
/// `n_montifier` is `n.montifier()` and `n_0` is `n.mont_neg_inverse()`.
pub(crate) struct ModExp<'a, const N: usize> {
    pub(crate) base: &'a PosInt<N>,
    pub(crate) e: &'a PosInt<N>,
    pub(crate) n: &'a PosInt<N>,
    pub(crate) n_montifier: &'a PosInt<N>,
    pub(crate) n_0: u64,
}

/// A `SecretPosInt` is a `PosInt` containing long-term key material.
///
/// It is zeroed on drop.
pub(crate) struct SecretPosInt<const N: usize>(PosInt<N>);

impl<const N: usize> From<PosInt<N>> for SecretPosInt<N> {
    fn from(pi: PosInt<N>) -> Self {
        Self(PosInt {
            used: pi.used,
            words: low::ct::into_secret(pi.words),
        })
    }
}

impl<const N: usize> Deref for SecretPosInt<N> {
    type Target = PosInt<N>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<const N: usize> DerefMut for SecretPosInt<N> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<const N: usize> Drop for SecretPosInt<N> {
    fn drop(&mut self) {
        // The whole value, as 32-bit targets pad after `used`.
        low::zeroise_value(&mut self.0);
    }
}

/// The `width` bits of `e` from bit `lsb` up, which must lie within it. Only
/// the positions decide which words are read, so the bits may be secret.
#[cfg(not(rind_backend = "x86_64"))]
fn window_bits(e: &[u64], lsb: usize, width: usize) -> u64 {
    let (word, shift) = (lsb / 64, lsb % 64);
    let mut bits = e[word] >> shift;
    if shift + width > 64 {
        bits |= e[word + 1] << (64 - shift);
    }
    bits & ((1 << width) - 1)
}

fn trim_leading_zeroes(mut bytes: &[u8]) -> &[u8] {
    while let Some((first, rest)) = bytes.split_first() {
        if *first == 0x00 {
            bytes = rest;
        } else {
            return bytes;
        }
    }

    bytes
}

/// Replaces `u` with `u * 2^64 mod d`, in variable time.
///
/// This is one step of Knuth's algorithm D (TAOCP 4.3.1). `d`'s top bit must
/// be set, `u` must be below `d`, and both must be as wide.
// Out of line, so `admin/ct-vartime`'s list of public divisions names this
// function rather than its callers.
#[inline(never)]
fn mul_word_mod(u: &mut [u64], d: &[u64]) {
    let k = d.len();
    let (Some(&d1), Some(&u2)) = (d.last(), u.last()) else {
        return;
    };
    let d0 = k.checked_sub(2).map_or(0, |i| d[i]);
    let u1 = k.checked_sub(2).map_or(0, |i| u[i]);
    let u0 = k.checked_sub(3).map_or(0, |i| u[i]);
    u.copy_within(..k - 1, 1);
    u[0] = 0;

    // Estimate the quotient word from the top words, then refine it with
    // the next, after which it is at most one too large. `u` is below `d`,
    // so u2 <= d1.
    let num = u128::from(u2) << 64 | u128::from(u1);
    let mut q = match u2 < d1 {
        true => num / u128::from(d1),
        false => u128::from(u64::MAX),
    };
    let mut rem = num - q * u128::from(d1);
    while rem >> 64 == 0 && q * u128::from(d0) > (rem << 64 | u128::from(u0)) {
        q -= 1;
        rem += u128::from(d1);
    }

    // (u2, u) -= q * d, then add d back if that went negative.
    let mut carry = 0u64;
    let mut borrow = false;
    for (u, d) in u.iter_mut().zip(d) {
        let product = q * u128::from(*d) + u128::from(carry);
        carry = (product >> 64) as u64;
        let (diff, b1) = u.overflowing_sub(product as u64);
        let (diff, b2) = diff.overflowing_sub(u64::from(borrow));
        *u = diff;
        borrow = b1 | b2;
    }
    if u2 < carry || (u2 == carry && borrow) {
        let mut carry = false;
        for (u, d) in u.iter_mut().zip(d) {
            let (sum, c1) = u.overflowing_add(*d);
            let (sum, c2) = sum.overflowing_add(u64::from(carry));
            *u = sum;
            carry = c1 | c2;
        }
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::bignum::{div_r, mod_exp_vectors, mod_mul_vectors};

    // Through the products and exponentiation this CPU picks, on every
    // backend; the backends' own tests run each of their routines.
    #[test]
    fn aws_lc_mod_mul() {
        for v in mod_mul_vectors() {
            let int = |words: &[u64]| PosInt::<64>::from_words(words).unwrap();
            let n = int(&v.m);
            let got = int(&v.a).mont_mul(&int(&v.b), &n, n.mont_neg_inverse());
            assert_eq!(got.as_words(), div_r(&v.want, &v.m), "{}", v.at);
        }
    }

    #[test]
    fn aws_lc_mod_exp() {
        for v in mod_exp_vectors() {
            let int = |words: &[u64]| PosInt::<128>::from_words(words).unwrap();
            let n = int(&v.m);
            let got = int(&v.a).mod_exp(&int(&v.e), &n, &n.montifier(), n.mont_neg_inverse());
            assert_eq!(got.as_words(), v.want, "{}", v.at);
        }
    }

    /// Against the constant-time montifier, at the extremes of each width,
    /// including a top word of one.
    #[test]
    fn pub_montifier() {
        for bits in [1024usize, 1025, 2047, 2048, 2049, 3072, 4095, 8192] {
            let len = bits.div_ceil(64);
            let mut low = PosInt::<128>::zero();
            low.used = len;
            low.words[0] = 1;
            low.words[(bits - 1) / 64] |= 1 << ((bits - 1) % 64);
            let mut high = PosInt::<128>::zero();
            high.used = len;
            high.words[..len].fill(u64::MAX);
            high.words[len - 1] >>= 64 * len - bits;

            for n in [low, high] {
                assert!(n.pub_montifier().pub_equals(&n.montifier()), "{bits} bits");
            }
        }
    }

    /// Against square-and-multiply, at each width class aarch64's
    /// `bn_mul_mont` branches on, and exponents of one to five words, whose
    /// top windows take each width from one to five bits.
    #[cfg(not(rind_backend = "x86_64"))]
    #[test]
    fn mont_exp_matches_square_and_multiply() {
        let mut state = 0x6a09_e667_f3bc_c908u64;
        let mut word = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for k in [1, 2, 7, 8, 16, 17] {
            let mut n = PosInt::<32>::zero();
            n.used = k;
            n.words[..k].fill_with(&mut word);
            n.words[0] |= 1;
            n.words[k - 1] |= 1 << 63;
            let n_0 = n.mont_neg_inverse();
            let montifier = n.montifier();
            let one_mont = n.fixed_one().to_montgomery(&montifier, &n);

            // A base below `n`, with its extremes, zero and `n - 1`, and an
            // exponent of zero, of every bit set, and random.
            for case in 0..5 {
                let mut x = PosInt::<32>::zero();
                x.used = k;
                x.words[..k].fill_with(&mut word);
                x.words[k - 1] >>= 1;
                match case {
                    0 => x.words[..k].fill(0),
                    1 => {
                        x.words[..k].copy_from_slice(n.as_words());
                        x.words[0] -= 1;
                    }
                    _ => {}
                }
                let x = x.to_montgomery(&montifier, &n);

                for len in 1..=5 {
                    let mut e = PosInt::<32>::zero();
                    e.used = len;
                    match case {
                        2 => {}
                        3 => e.words[..len].fill(u64::MAX),
                        _ => e.words[..len].fill_with(&mut word),
                    }

                    let mut want = one_mont.clone();
                    for i in (0..len * 64).rev() {
                        want = want.mont_sqr(&n, n_0);
                        if e.words[i / 64] >> (i % 64) & 1 == 1 {
                            want = want.mont_mul(&x, &n, n_0);
                        }
                    }
                    let got = x.mont_exp(one_mont.clone(), &e, &n, n_0);
                    assert!(
                        got.equals(&want),
                        "{k} words, case {case}, {len}-word exponent"
                    );
                }
            }
        }
    }

    /// Dual RSAZ takes a pair of 16-word moduli wherever the CPU runs it, and
    /// leaves moduli of different widths, or an exponent wider than them, to
    /// the exponentiations one at a time.
    #[cfg(rind_backend = "x86_64")]
    #[test]
    fn mod_exp_pair_rsaz_takes_what_fits() {
        let mut state = 0x3c6e_f372_fe94_f82bu64;
        let mut random = |k: usize| {
            let mut x = PosInt::<32>::zero();
            x.used = k;
            for w in &mut x.words[..k] {
                state ^= state << 13;
                state ^= state >> 7;
                state ^= state << 17;
                *w = state;
            }
            x
        };
        let mut odd = |k: usize| {
            let mut n = random(k);
            n.words[0] |= 1;
            n.words[k - 1] |= 1 << 63;
            n
        };
        let moduli = [odd(16), odd(16), odd(15)];
        let montifiers = moduli.each_ref().map(PosInt::montifier);
        // Each below every modulus, as a 15-word value is.
        let base = random(15);
        // Exponents of 16 and 17 words.
        let exponents = [random(16), random(17)];
        let pair = |[i, j]: [usize; 2], [ei, ej]: [usize; 2]| {
            [(i, ei), (j, ej)].map(|(i, e)| ModExp {
                base: &base,
                e: &exponents[e],
                n: &moduli[i],
                n_montifier: &montifiers[i],
                n_0: moduli[i].mont_neg_inverse(),
            })
        };

        let rsaz = low::RsazAvx512::check(16).is_some();
        assert_eq!(
            PosInt::mod_exp_pair_rsaz(&pair([0, 1], [0, 0])).is_some(),
            rsaz
        );
        assert!(PosInt::mod_exp_pair_rsaz(&pair([0, 2], [0, 0])).is_none());
        assert!(PosInt::mod_exp_pair_rsaz(&pair([0, 1], [0, 1])).is_none());
    }

    /// The rare quotient estimates `pub_montifier`'s moduli never reach.
    #[test]
    fn mul_word_mod() {
        const TOP: u64 = 1 << 63;
        for (mut u, d, want, why) in [
            // 2^192 mod 2^191 + 1: the estimate 2 survives refinement, so
            // the remainder goes negative and d is added back.
            (
                [0, 0, 1],
                [1, 0, TOP],
                [u64::MAX, u64::MAX, TOP - 1],
                "added back",
            ),
            // 2^192 mod 2^191 + 2^128 - 2^64: the second word refines the
            // estimate 2 down to 1.
            ([0, 0, 1], [0, u64::MAX, TOP], [0, 1, TOP - 1], "refined"),
            // Adding d back carries between words.
            (
                [0, u64::MAX, 0],
                [1, 0, u64::MAX],
                [0, 0, u64::MAX],
                "carried back",
            ),
        ] {
            super::mul_word_mod(&mut u, &d);
            assert_eq!(u, want, "{why}");
        }
    }

    #[test]
    fn from_bytes() {
        // no bytes -> zero
        assert!(
            PosInt::<1>::from_bytes(&[])
                .unwrap()
                .pub_equals(&PosInt::<1>::zero())
        );

        // from single zero byte
        assert!(
            PosInt::<1>::from_bytes(&[0])
                .unwrap()
                .pub_equals(&PosInt::<1>::zero())
        );

        // can parse exactly 8N bytes
        assert!(
            PosInt::<1>::from_bytes(&[0; 8])
                .unwrap()
                .pub_equals(&PosInt::<1>::zero())
        );

        // cannot parse > 8N bytes (excluding leading zeroes)
        assert_eq!(
            PosInt::<1>::from_bytes(&[1; 9]).unwrap_err(),
            Error::WrongLength
        );
        PosInt::<1>::from_bytes(&[0; 9]).unwrap();

        // can parse both entire words and remaining bytes
        assert_eq!(
            PosInt::<2>::from_bytes(&[1, 0, 0, 0, 0, 0, 0, 0, 2])
                .unwrap()
                .as_words(),
            &[2, 1]
        );

        // and remaining bytes that require combining
        assert_eq!(
            PosInt::<1>::from_bytes(&[0x11, 0x22, 0x33, 0x44])
                .unwrap()
                .as_words(),
            &[0x11223344]
        );

        // multi-word PosInt with leading zeros
        let p = PosInt::<2>::from_bytes(&[0x00, 0x00, 0x00, 0x00, 0x00, 0x11, 0x22, 0x33, 0x44])
            .unwrap();
        let mut expected = PosInt::<2>::zero();
        assert!(expected.push_word(0x11223344).is_ok());
        assert!(p.pub_equals(&expected));
        assert!(expected.push_word(0).is_ok());
        assert!(p.pub_equals(&expected));
    }

    #[test]
    fn to_bytes() {
        let mut buf = [0xff; 8];
        assert!(PosInt::<2>::zero().to_bytes(&mut buf).unwrap().is_empty());

        let all_bits_set = PosInt::<2>::from_bytes(&[0xff; 16]).unwrap();
        assert_eq!(
            all_bits_set.to_bytes(&mut buf).unwrap_err(),
            Error::WrongLength
        );
        assert_eq!(
            all_bits_set.to_bytes_asn1(&mut buf).unwrap_err(),
            Error::WrongLength
        );

        let mut buf16 = [0; 16];
        all_bits_set.to_bytes(&mut buf16).unwrap();
        assert_eq!(buf16, [0xff; 16]);
        let mut buf_asn1 = [0; 17];
        all_bits_set.to_bytes_asn1(&mut buf_asn1).unwrap();
        assert_eq!(
            buf_asn1,
            [
                0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
                0xff, 0xff, 0xff
            ]
        );
    }

    #[test]
    fn mul() {
        // identities
        let zero_1 = PosInt::<1>::zero();
        let zero_2 = PosInt::<2>::zero();
        let one_1 = PosInt::<1>::one();
        let one_2 = PosInt::<2>::one();

        let r = PosInt::mul(&one_1, &one_1);
        r.debug("1 x 1");
        assert!(r.pub_equals(&one_2));

        let r = PosInt::mul(&zero_1, &one_1);
        r.debug("1 x 0");
        assert!(r.pub_equals(&zero_2));

        let r = PosInt::mul(&zero_1, &zero_1);
        r.debug("0 x 0");
        assert!(r.pub_equals(&zero_2));

        let x_4 = PosInt::<4>::from_bytes(b"\xed\x1f\xde\xb5\xc6\x39\x43\x8f\xea\x1d\x05\x9c\xba\xa8\xd3\x7c\x13\x96\xf4\x96\x1c\x8e\x5f\x52\x8f\x3c\x4c\x3c\x45\xe5\x75\xa2").unwrap();
        let y_4 = PosInt::<4>::from_bytes(b"\x38\x8f\xb5\xd8\xbd\xad\x46\xfd\xe2\x8e\x33\x11\xe4\xdd\xef\x79\x70\xfe\x4a\xb9\xef\x24\x85\xbe\x4f\xde\x81\x79\x36\x0c\x9c\x86").unwrap();
        let xy_8: PosInt<8> = PosInt::mul(&x_4, &y_4);
        println!("{xy_8:x?}");

        let expect_8 = PosInt::<8>::from_bytes(b"\x34\x64\x15\xf5\x75\xf1\xb7\x01\x8b\x1d\xc4\x68\xde\x4b\xf7\x6e\x6f\x62\x87\xa1\x44\x08\x6f\xb1\x85\x9c\xf3\x84\x41\x64\x48\x9d\x16\xe7\xb0\xd0\xd3\x56\x13\xba\xa2\xb9\xa6\x12\x1a\x6c\x2f\x93\xcd\xe4\x20\xfa\x41\xa4\xef\xa2\xab\xcd\x8b\x48\x19\x62\x4a\xcc").unwrap();
        assert!(xy_8.pub_equals(&expect_8));
    }

    #[test]
    fn basics() {
        let zero = PosInt::<1>::zero();
        let one = PosInt::<1>::one();
        let two = PosInt::<1>::word(2);
        let max_one_word = PosInt::<1>::word(u64::MAX);

        assert_eq!(zero.len_bits(), 0);
        assert!(zero.is_even());
        assert!(zero.equals(&zero));
        assert_eq!(zero.count_trailing_zeroes(), 0);
        assert!(zero.less_than(&one));
        assert!(!one.less_than(&zero));

        assert_eq!(one.len_bits(), 1);
        assert!(!one.is_even());
        assert_eq!(one.count_trailing_zeroes(), 0);
        assert!(one.equals(&one));

        assert_eq!(two.len_bits(), 2);
        assert!(two.is_even());
        assert_eq!(two.count_trailing_zeroes(), 1);
        assert!(two.equals(&two));

        assert_eq!(max_one_word.len_bits(), 64);
        assert!(!max_one_word.is_even());
        assert!(max_one_word.equals(&max_one_word));
        assert!(one.less_than(&max_one_word));

        let two_words = PosInt::<2>::from_bytes(&[0xff; 16]).unwrap();
        assert_eq!(two_words.len_bits(), 128);
        assert!(!two_words.is_even());
        assert!(two_words.equals(&two_words));
        assert!(two_words.fixed_one().less_than(&two_words));

        let mut two_words = PosInt::<2>::zero();
        const LOW_ORDER_WORD: u64 = 0xfedcba9876543210;
        const HIGH_ORDER_WORD: u64 = 0x1234;
        assert!(two_words.push_word(LOW_ORDER_WORD).is_ok());
        assert!(two_words.push_word(HIGH_ORDER_WORD).is_ok());
        assert!(two_words.push_word(0).is_err());
        let mut out = [0; 15];
        assert!(two_words.to_bytes(&mut out).is_err());
        let mut out = [0; 16];
        assert!(two_words.to_bytes(&mut out).is_ok());
        assert_eq!(
            u64::from_be_bytes(out[0..8].try_into().unwrap()),
            HIGH_ORDER_WORD
        );
        assert_eq!(
            u64::from_be_bytes(out[8..16].try_into().unwrap()),
            LOW_ORDER_WORD
        );
    }

    /// A narrower subtrahend's borrow runs through the wider value's words.
    #[test]
    fn sub_narrower() {
        let w = PosInt::<2>::from_words(&[1, 1]).unwrap();
        assert_eq!(w.sub(&PosInt::word(3)).as_words(), &[u64::MAX - 1, 0]);
    }

    #[test]
    fn is_coprime() {
        let (four, six, nine) = (PosInt::<1>::word(4), PosInt::word(6), PosInt::word(9));
        assert!(four.is_coprime(&nine));
        assert!(!four.is_coprime(&six));
    }

    // A one-word modulus, which the bits shift in one at a time.
    #[test]
    fn reduce_even_by_a_word() {
        let a =
            PosInt::<3>::from_words(&[0x0123_4567_89ab_cdef, 0xfedc_ba98_7654_3210, 7]).unwrap();
        let m = PosInt::<1>::word(0xffff_ffff_0000_0001);
        let want = ((7u128 << 64 | 0xfedc_ba98_7654_3210) % 0xffff_ffff_0000_0001) << 64
            | 0x0123_4567_89ab_cdef;
        assert_eq!(
            a.reduce_even(&m).as_words(),
            &[(want % 0xffff_ffff_0000_0001) as u64]
        );
    }

    #[test]
    fn test_reduce_even() {
        let mut a = PosInt::<32>::zero();
        for i in 0..32 {
            a.push_word(0x8000_1234_5678_0000 + i).unwrap();
        }
        let m = PosInt::<16> {
            used: 16,
            words: [0xff55_3322_ff55_3322; 16],
        };
        let c = a.reduce_even(&m);
        assert_eq!(
            c.as_words(),
            &[
                0x1e0a0609caf9e1b2,
                0x1e0a0609caf9e1b4,
                0x1e0a0609caf9e1b6,
                0x1e0a0609caf9e1b8,
                0x1e0a0609caf9e1ba,
                0x1e0a0609caf9e1bc,
                0x1e0a0609caf9e1be,
                0x1e0a0609caf9e1c0,
                0x1e0a0609caf9e1c2,
                0x1e0a0609caf9e1c4,
                0x1e0a0609caf9e1c6,
                0x1e0a0609caf9e1c8,
                0x1e0a0609caf9e1ca,
                0x1e0a0609caf9e1cc,
                0x1e0a0609caf9e1ce,
                0x1e0a0609caf9e1d0
            ]
        );
    }
}
