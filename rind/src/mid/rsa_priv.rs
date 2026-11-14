// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::rsa_pub::{MAX_PUBLIC_MODULUS_BYTES, RsaPublicKey};
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rng::RandomSource;
use crate::mid::rsa_key_size::RsaKeySize;

mod exponents;
mod generate;

pub(crate) struct RsaPrivateKey {
    public: RsaPublicKey,

    p: SecretRsaPosIntModP,
    q: SecretRsaPosIntModP,
    d: SecretRsaPosIntD,
    dp: SecretRsaPosIntModP,
    dq: SecretRsaPosIntModP,
    iqmp: SecretRsaPosIntModP,

    iqmp_mont: SecretRsaPosIntModP,
    p_montifier: SecretRsaPosIntModP,
    q_montifier: SecretRsaPosIntModP,
    p0: u64,
    q0: u64,
}

impl RsaPrivateKey {
    pub(crate) fn new(
        p: RsaPosIntModP,
        q: RsaPosIntModP,
        d: RsaPosIntD,
        dp: RsaPosIntModP,
        dq: RsaPosIntModP,
        iqmp: RsaPosIntModP,
        n: RsaPosIntModN,
        e: u64,
    ) -> Result<Self, Error> {
        Self::from_components(p, q, d, dp, dq, iqmp, RsaPublicKey::new(n, e)?)
    }

    /// Validates private components against an already validated public key.
    pub(crate) fn from_components(
        p: RsaPosIntModP,
        q: RsaPosIntModP,
        d: RsaPosIntD,
        dp: RsaPosIntModP,
        dq: RsaPosIntModP,
        iqmp: RsaPosIntModP,
        public: RsaPublicKey,
    ) -> Result<Self, Error> {
        if public.modulus_len_bits() < MIN_MODULUS_BITS {
            return Err(KeyFormatError::RsaModulus.into());
        }
        // The arithmetic needs nonzero top words. Only this format verdict
        // is public; the actual prime lengths and parity stay secret.
        let p_bytes = p.len_bytes();
        let valid = !p.is_even()
            & !q.is_even()
            & (q.len_bits() >= 2)
            & (p_bytes >= MIN_PRIVATE_MODULUS_BYTES)
            & (p.as_words().last().copied().unwrap_or(0) != 0)
            & (q.as_words().last().copied().unwrap_or(0) != 0);
        if !low::ct::into_public(valid) {
            return Err(KeyFormatError::RsaPrimes.into());
        }
        // Widths come from the encodings, not a scan of the secret primes.
        let (p_len, q_len) = (p.as_words().len(), q.as_words().len());
        let e = public.e;

        let mut p: SecretRsaPosIntModP = p.into();
        let mut q: SecretRsaPosIntModP = q.into();
        let d: SecretRsaPosIntD = d.into();
        let dp: SecretRsaPosIntModP = dp.into();
        let dq: SecretRsaPosIntModP = dq.into();
        let iqmp: SecretRsaPosIntModP = iqmp.into();

        // Each prime is still at its own width, as `reduce_even` needs.
        let e = low::PosInt::word(e);
        let exponents_agree = exponents_agree(&p, &d, &dp, &e) & exponents_agree(&q, &d, &dq, &e);

        // The CRT reduces `c` mod each prime by Montgomery reduction, which
        // needs `c` below 2^(64w) times the prime for a w-word prime. Working
        // at the wider prime's width meets that for unbalanced primes too.
        if p_len < q_len {
            p.expand(&q);
        } else {
            q.expand(&p);
        }

        let p_montifier: SecretRsaPosIntModP = p.montifier().into();
        let q_montifier = q.montifier().into();
        let iqmp_mont: SecretRsaPosIntModP = iqmp.to_montgomery(&p_montifier, &p).into();
        let p0 = p.mont_neg_inverse();
        let q0 = q.mont_neg_inverse();

        // As aws-lc's `RSA_check_key`, so a key that cannot sign is refused
        // here rather than by every signature's fault check. Each relation
        // is computed in full, and only the verdict is revealed.
        let pq: RsaPosIntModN = low::PosInt::mul(&p, &q);
        // q may be above p, and Montgomery multiplication takes operands
        // below the modulus.
        let q_wide: RsaPosIntModN = q.widen();
        let q_p = q_wide.reduce(&p, &p_montifier);
        let consistent = exponents_agree
            & pq.equals(&public.n)
            & iqmp.less_than(&p)
            // Out of Montgomery form: iqmp * R * q * R^-1 = iqmp * q (mod p).
            & iqmp_mont.mont_mul(&q_p, &p, p0).equals(&p.fixed_one());
        if !low::ct::into_public(consistent) {
            return Err(KeyFormatError::MismatchedRsaComponents.into());
        }

        Ok(Self {
            public,
            p,
            q,
            d,
            dp,
            dq,
            iqmp,
            iqmp_mont,
            p_montifier,
            q_montifier,
            p0,
            q0,
        })
    }

    pub(crate) fn generate(
        size: RsaKeySize,
        candidate_source: &mut dyn RandomSource,
        witness_source: &mut dyn RandomSource,
    ) -> Result<Self, Error> {
        generate::generate_key(size, candidate_source, witness_source)
    }

    /// Swaps `dp` and `dq`, as a fault in the CRT would corrupt them.
    #[cfg(test)]
    pub(crate) fn swap_crt_exponents(&mut self) {
        core::mem::swap(&mut self.dp, &mut self.dq);
    }

    pub(crate) fn public_key(&self) -> RsaPublicKey {
        self.public.clone()
    }

    pub(crate) fn modulus_len_bytes(&self) -> usize {
        self.public.modulus_len_bytes()
    }

    pub(crate) fn modulus_len_bits(&self) -> usize {
        self.public.modulus_len_bits()
    }

    pub(crate) fn encode_components<'a>(
        &self,
        buffer: &'a mut RsaComponentsBuffer,
    ) -> Result<RsaComponents<'a>, Error> {
        let (public_modulus, buffer) = buffer.0.split_at_mut(MAX_PUBLIC_MODULUS_BYTES + 1);
        let (public_exponent, buffer) = buffer.split_at_mut(8);
        let (p, buffer) = buffer.split_at_mut(MAX_PRIVATE_MODULUS_BYTES + 1);
        let (q, buffer) = buffer.split_at_mut(MAX_PRIVATE_MODULUS_BYTES + 1);
        let (d, buffer) = buffer.split_at_mut(MAX_PUBLIC_MODULUS_BYTES + 1);
        let (dp, buffer) = buffer.split_at_mut(MAX_PRIVATE_MODULUS_BYTES + 1);
        let (dq, buffer) = buffer.split_at_mut(MAX_PRIVATE_MODULUS_BYTES + 1);
        let (iqmp, _) = buffer.split_at_mut(MAX_PRIVATE_MODULUS_BYTES + 1);

        let public_modulus = self.public.n.to_bytes_asn1(public_modulus)?;
        public_exponent.copy_from_slice(&self.public.e.to_be_bytes());

        let p = self.p.to_bytes_asn1(p)?;
        let q = self.q.to_bytes_asn1(q)?;
        let d = self.d.to_bytes_asn1(d)?;
        let dp = self.dp.to_bytes_asn1(dp)?;
        let dq = self.dq.to_bytes_asn1(dq)?;
        let iqmp = self.iqmp.to_bytes_asn1(iqmp)?;

        // We are exporting this key; it is leaving the confines of this
        // library and becoming public data.
        low::ct::public_slice(p);
        low::ct::public_slice(q);
        low::ct::public_slice(d);
        low::ct::public_slice(dp);
        low::ct::public_slice(dq);
        low::ct::public_slice(iqmp);

        Ok(RsaComponents {
            public_modulus,
            public_exponent,
            p,
            q,
            d,
            dp,
            dq,
            iqmp,
        })
    }

    /// returns c ^ d mod n
    ///
    /// (albeit via CRT)
    ///
    /// The result is at the modulus's width and stays secret, as a decrypted
    /// message must: a signer declassifies it.
    pub(crate) fn private_op(&self, c: &RsaPosIntModN) -> Result<RsaPosIntModN, Error> {
        if !c.less_than(&self.public.n) {
            return Err(Error::WrongLength);
        }

        // A note about blinding:
        //
        // `c` is public, a message to sign or a ciphertext to decrypt, so
        // base blinding would hide nothing a timing channel could reveal.
        //
        // Exponent and modulus blinding are _also_ relatively unnecessary,
        // since our `PosInt::mod_exp_pair` is side-channel silent.
        // See the commentary there for why I think that is the case.

        // i.   Let m_1 = c^dP mod p and m_2 = c^dQ mod q.
        // (do reductions of c first, so the mod exp can be done at
        // width of p or q rather than pq.)
        let cmp = c.reduce(&self.p, &self.p_montifier);
        let cmq = c.reduce(&self.q, &self.q_montifier);
        let [m_1, m_2] = low::PosInt::mod_exp_pair([
            low::ModExp {
                base: &cmp,
                e: &self.dp,
                n: &self.p,
                n_montifier: &self.p_montifier,
                n_0: self.p0,
            },
            low::ModExp {
                base: &cmq,
                e: &self.dq,
                n: &self.q,
                n_montifier: &self.q_montifier,
                n_0: self.q0,
            },
        ]);

        // ii. If u > 2, let m_i = c^(d_i) mod r_i, i = 3, ..., u.
        // (we don't support multiprime rsa)

        // iii. Let h = (m_1 - m_2) * qInv mod p.
        // (m_2 < q may exceed p, so reduce it first.)
        let m_2_wide: RsaPosIntModN = m_2.widen();
        let m_2_p = m_2_wide.reduce(&self.p, &self.p_montifier);
        let h = m_1
            .sub_mod(&m_2_p, &self.p)
            .mont_mul(&self.iqmp_mont, &self.p, self.p0);

        // iv.  Let m = m_2 + q * h.
        // `add` narrows `m` to its nonzero words, a width that depends on
        // its value, so widen it back before anything reads that width.
        let mut m = m_2.widen().add(&low::PosInt::mul(&self.q, &h));
        m.expand(&self.public.n);

        // Check the result as a fault attack countermeasure: `new` checked
        // the key's components, so only a fault fails this, and the verdict
        // reveals nothing else.
        match self.public.public_op(m.clone()) {
            Ok(c2) if low::ct::into_public(c2.equals(c)) => Ok(m),
            _ => Err(Error::Fault),
        }
    }
}

impl Drop for RsaPrivateKey {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.p0);
        low::zeroise_value(&mut self.q0);
        // Not secret, but wiping it lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(&mut self.public);
    }
}

/// Whether `dp = d mod (p - 1)` and `dp * e = 1 (mod p - 1)`.
///
/// These accept the same keys as aws-lc's `d * e = 1 (mod p - 1)` and
/// `dp = d mod (p - 1)`, with one reduction of `d` rather than two. `p` must
/// be above one and at its own width, as `reduce_even` needs the top word of
/// `p - 1` nonzero.
fn exponents_agree(
    p: &RsaPosIntModP,
    d: &RsaPosIntD,
    dp: &RsaPosIntModP,
    e: &RsaPosIntModP,
) -> bool {
    let p_1 = p.sub(&low::PosInt::one());
    let d_p = d.reduce_even(&p_1);
    let d_p_e: RsaPosIntD = low::PosInt::mul(&d_p, e);
    d_p.equals(dp) & d_p_e.reduce_even(&p_1).equals(&p_1.fixed_one())
}

pub(crate) struct RsaComponents<'a> {
    pub(crate) public_modulus: &'a [u8],
    pub(crate) public_exponent: &'a [u8],
    pub(crate) p: &'a [u8],
    pub(crate) q: &'a [u8],
    pub(crate) d: &'a [u8],
    pub(crate) dp: &'a [u8],
    pub(crate) dq: &'a [u8],
    pub(crate) iqmp: &'a [u8],
}

pub(crate) struct RsaComponentsBuffer([u8; Self::LEN]);

impl RsaComponentsBuffer {
    pub(crate) const LEN: usize =
        // public modulus and private exponent
        (MAX_PUBLIC_MODULUS_BYTES + 1) * 2 +
            // public exponent
            8 +
            // private moduli and crt components
            (MAX_PRIVATE_MODULUS_BYTES + 1) * 5;
}

impl Default for RsaComponentsBuffer {
    fn default() -> Self {
        Self([0u8; Self::LEN])
    }
}

const MAX_PRIVATE_MODULUS_BITS: usize = 4096;
const MAX_PRIVATE_MODULUS_WORDS: usize = MAX_PRIVATE_MODULUS_BITS / 64;
pub(crate) const MAX_PRIVATE_MODULUS_BYTES: usize = MAX_PRIVATE_MODULUS_BITS / 8;

const MIN_PRIVATE_MODULUS_BITS: usize = 1024;
const MIN_PRIVATE_MODULUS_BYTES: usize = MIN_PRIVATE_MODULUS_BITS / 8;

// Signing keeps the 2048-bit floor that only legacy verification goes below.
const MIN_MODULUS_BITS: usize = 2048;

type SecretRsaPosIntModP = low::SecretPosInt<MAX_PRIVATE_MODULUS_WORDS>;
type SecretRsaPosIntD = low::SecretPosInt<{ MAX_PRIVATE_MODULUS_WORDS * 2 }>;
type RsaPosIntModP = low::PosInt<MAX_PRIVATE_MODULUS_WORDS>;
type RsaPosIntD = low::PosInt<{ MAX_PRIVATE_MODULUS_WORDS * 2 }>;
type RsaPosIntModN = low::PosInt<{ MAX_PRIVATE_MODULUS_WORDS * 2 }>;

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::test::{Acvp, acvp};

    /// Loads an ACVP test's key, deriving the CRT values a `standard` key
    /// lacks, or `None` for a public exponent above 33 bits, which rind
    /// refuses as aws-lc does.
    fn acvp_key(mode: &str, test: &serde_json::Value) -> Option<RsaPrivateKey> {
        let modp = |name| RsaPosIntModP::from_bytes(&test.hex(name)).unwrap();
        let (p, q) = (modp("p"), modp("q"));
        let d = RsaPosIntD::from_bytes(&test.hex("d")).unwrap();
        let n = RsaPosIntModN::from_bytes(&test.hex("n")).unwrap();
        let (dp, dq, iqmp) = match mode {
            "crt" => (modp("dmp1"), modp("dmq1"), modp("iqmp")),
            "standard" => {
                let one = low::PosInt::one();
                let q_mod_p: RsaPosIntModP = q
                    .widen::<{ MAX_PRIVATE_MODULUS_WORDS * 2 }>()
                    .reduce(&p, &p.montifier());
                (
                    d.reduce_even(&p.sub(&one)),
                    d.reduce_even(&q.sub(&one)),
                    q_mod_p.mod_inverse(&p),
                )
            }
            other => panic!("unexpected key mode {other}"),
        };
        let e = test.hex("e");
        let e_bits = e.len() * 8 - e[0].leading_zeros() as usize;
        let e = e.iter().fold(0, |e, byte| e << 8 | u64::from(*byte));
        let key = RsaPrivateKey::new(p, q, d, dp, dq, iqmp, n, e);
        if e_bits > 33 {
            assert_eq!(key.err(), Some(KeyFormatError::RsaExponent.into()));
            return None;
        }
        Some(key.unwrap())
    }

    /// The private operation on `input`, at the modulus's length, or `None`
    /// if `input` is not below the modulus.
    fn acvp_private_op(key: &RsaPrivateKey, input: &[u8]) -> Option<Vec<u8>> {
        let input: RsaPosIntModN = low::PosInt::from_bytes(input).ok()?;
        let output = key.private_op(&input).ok()?;
        let mut bytes = vec![0; key.modulus_len_bytes()];
        output.to_bytes(&mut bytes).unwrap();
        low::ct::public_slice(&bytes);
        Some(bytes)
    }

    #[test]
    fn acvp_decryption_primitive() {
        for group in acvp("RSA-DecryptionPrimitive-Sp800-56Br2") {
            for test in group.tests() {
                let Some(key) = acvp_key(group.str("keyMode"), test) else {
                    continue;
                };
                let ct = test.hex("ct");
                if test.flag("testPassed") {
                    assert_eq!(acvp_private_op(&key, &ct).unwrap(), test.hex("pt"));
                    continue;
                }
                // SP 800-56B's RSADP refuses a ciphertext outside 1 < c < n - 1
                // before its private operation; rind's OAEP leaves 0, 1, and
                // n - 1 to its padding check, which their outputs fail.
                let c: RsaPosIntModN = low::PosInt::from_bytes(&ct).unwrap();
                let n: RsaPosIntModN = low::PosInt::from_bytes(&test.hex("n")).unwrap();
                let n_1 = n.sub(&low::PosInt::one());
                let two: RsaPosIntModN = low::PosInt::word(2);
                assert!(c.less_than(&two) || !c.less_than(&n_1));
            }
        }
    }

    #[test]
    fn acvp_signature_primitive() {
        for group in acvp("RSA-SignaturePrimitive-2.0") {
            for test in group.tests() {
                let Some(key) = acvp_key(group.str("keyMode"), test) else {
                    continue;
                };
                let signature = acvp_private_op(&key, &test.hex("message"));
                match test.flag("testPassed") {
                    true => assert_eq!(signature.unwrap(), test.hex("signature")),
                    false => assert_eq!(signature, None),
                }
            }
        }
    }

    // A prime below 1024 bits is refused before anything is computed from
    // it, however wide the modulus.
    #[test]
    fn short_prime_refused() {
        fn int<const N: usize>(bytes: &[u8]) -> low::PosInt<N> {
            low::PosInt::from_bytes(bytes).unwrap()
        }
        let mut n = [0u8; 256];
        n[0] = 0x80;
        n[255] = 1;
        let mut p = [0u8; 127];
        p[0] = 0x80;
        p[126] = 1;
        let key = RsaPrivateKey::new(
            int(&p),
            int(&[3]),
            int(&[1]),
            int(&[1]),
            int(&[1]),
            int(&[1]),
            int(&n),
            65537,
        );
        assert_eq!(key.err(), Some(KeyFormatError::RsaPrimes.into()));
    }
}
