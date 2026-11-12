// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::marker::PhantomData;

use super::digest::Digest;
use super::hash::Hash;
use super::hmac::HmacKey;
use crate::Error;
use crate::mid::rng::RandomSource;

/// SP 800-90A Table 2: one HMAC_DRBG generate returns at most 2^19 bits.
pub(crate) const MAX_GENERATE_BYTES: usize = 1 << 16;

/// SP 800-90A Table 2: reseed after more than 2^48 generates.
const MAX_RESEED_INTERVAL: u64 = 1 << 48;

/// SP 800-90A HMAC_DRBG without a derivation function.
///
/// ECDSA's nonces use it with no additional input. The FIPS module's
/// [`crate::drbg::HmacDrbg`] is this construction over SHA-512, with reseeding.
pub(crate) struct HmacDrbg<H: Hash> {
    k: Digest,
    v: Digest,
    reseed_counter: u64,
    _h: PhantomData<H>,
}

impl<H: Hash> HmacDrbg<H> {
    pub(crate) fn new(entropy_input: &[u8], nonce: &[u8], personalization_string: &[u8]) -> Self {
        // 1. seed_material = entropy_input || nonce || personalization_string.
        let seed_material = &[entropy_input, nonce, personalization_string];

        // 2. Key = 0x00 00...00. Comment: outlen bits.
        let k = H::zeroed_output();
        // 3. V = 0x01 01...01. Comment: outlen bits.
        let mut v = H::zeroed_output();
        v.as_mut().fill(1u8);

        // 4. (Key, V) = HMAC_DRBG_Update (seed_material, Key, V).
        // 5. reseed_counter = 1.
        let mut r = Self {
            k,
            v,
            reseed_counter: 0,
            _h: PhantomData,
        };
        r.update(seed_material);
        r.reseed_counter = 1;
        r
    }

    /// Mixes new `entropy` into the state. `additional` of `None` is the
    /// standard's Null; an empty slice is still provided data.
    pub(crate) fn reseed(&mut self, entropy: &[u8], additional: Option<&[u8]>) {
        match additional {
            Some(extra) => self.update(&[entropy, extra]),
            None => self.update(&[entropy]),
        }
        self.reseed_counter = 1;
    }

    /// Writes one generate, at most [`MAX_GENERATE_BYTES`], into `out`.
    ///
    /// `additional` of `None` is Null. A generate past [`MAX_RESEED_INTERVAL`]
    /// returns [`Error::RngFailed`] and leaves the state unchanged, so the
    /// caller can reseed.
    pub(crate) fn generate(
        &mut self,
        out: &mut [u8],
        additional: Option<&[u8]>,
    ) -> Result<(), Error> {
        if self.reseed_counter > MAX_RESEED_INTERVAL {
            return Err(Error::RngFailed);
        }
        if out.len() > MAX_GENERATE_BYTES {
            return Err(Error::WrongLength);
        }

        // 2. If additional_input ≠ Null, then
        //    (Key, V) = HMAC_DRBG_Update (additional_input, Key, V).
        if let Some(extra) = additional {
            self.update(&[extra]);
        }

        // 3-5. V = HMAC(Key, V), repeated, and the output is the leading bytes.
        let hashlen = self.v.as_ref().len();
        for chunk in out.chunks_mut(hashlen) {
            self.generate_block();
            chunk.copy_from_slice(&self.v.as_ref()[..chunk.len()]);
        }

        // 6. (Key, V) = HMAC_DRBG_Update (additional_input, Key, V).
        // 7. reseed_counter = reseed_counter + 1.
        match additional {
            Some(extra) => self.update(&[extra]),
            None => self.update(&[]),
        }
        self.reseed_counter += 1;
        Ok(())
    }

    fn update(&mut self, additional_input: &[&[u8]]) {
        // 1. K = HMAC (K, V || 0x00 || provided_data).
        let mut ctx = HmacKey::<H>::new(self.k.as_ref()).start();
        ctx.update(self.v.as_ref());
        ctx.update([0u8]);

        for item in additional_input {
            ctx.update(item);
        }

        self.k = ctx.finish();

        // 2. V = HMAC (K, V).
        self.v = HmacKey::<H>::new(self.k.as_ref()).sign(self.v.as_ref());

        // 3. If (provided_data = Null), then return K and V.
        if additional_input.is_empty() {
            return;
        }

        // 4. K = HMAC (K, V || 0x01 || provided_data).
        let mut ctx = HmacKey::<H>::new(self.k.as_ref()).start();
        ctx.update(self.v.as_ref());
        ctx.update([1u8]);

        for item in additional_input {
            ctx.update(item);
        }

        self.k = ctx.finish();

        // 5. V = HMAC (K, V).
        self.v = HmacKey::<H>::new(self.k.as_ref()).sign(self.v.as_ref());
    }

    fn generate_block(&mut self) {
        // V = HMAC (Key, V).
        self.v = HmacKey::<H>::new(self.k.as_ref()).sign(self.v.as_ref());
    }
}

impl<H: Hash> RandomSource for HmacDrbg<H> {
    fn fill(&mut self, out: &mut [u8]) -> Result<(), Error> {
        // ECDSA and RSA key generation pass no additional input. A buffer
        // longer than one generate is several generates, each under the cap.
        let mut rest = &mut *out;
        if rest.is_empty() {
            return self.generate(rest, None);
        }
        while !rest.is_empty() {
            let n = rest.len().min(MAX_GENERATE_BYTES);
            let (head, tail) = rest.split_at_mut(n);
            self.generate(head, None)?;
            rest = tail;
        }
        Ok(())
    }
}

impl HmacDrbg<super::hash::Sha512> {
    pub(crate) fn from_parts(k: &[u8; 64], v: &[u8; 64], reseed_counter: u64) -> Self {
        Self {
            k: Digest::new(super::hash::Sha512::ALGORITHM, k),
            v: Digest::new(super::hash::Sha512::ALGORITHM, v),
            reseed_counter,
            _h: PhantomData,
        }
    }

    pub(crate) fn to_parts(&self) -> ([u8; 64], [u8; 64], u64) {
        let mut k = [0u8; 64];
        let mut v = [0u8; 64];
        k.copy_from_slice(self.k.as_ref());
        v.copy_from_slice(self.v.as_ref());
        (k, v, self.reseed_counter)
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::Error;
    use crate::high::hash::{Hash, Sha256};
    use crate::test::Acvp;

    fn provided(bytes: &[u8]) -> Option<&[u8]> {
        if bytes.is_empty() { None } else { Some(bytes) }
    }

    fn acvp_run<H: Hash>(
        test: &serde_json::Value,
        prediction_resistance: bool,
        bits: usize,
    ) -> Vec<u8> {
        let mut drbg = HmacDrbg::<H>::new(
            &test.hex("entropyInput"),
            &test.hex("nonce"),
            &test.hex("persoString"),
        );
        let steps = test["otherInput"].as_array().expect("otherInput");
        let mut out = vec![0u8; bits / 8];
        for step in steps {
            let additional = hex::decode(step["additionalInput"].as_str().unwrap()).unwrap();
            let entropy = hex::decode(step["entropyInput"].as_str().unwrap()).unwrap();
            let extra = provided(&additional);
            match step["intendedUse"].as_str() {
                Some("reSeed") => drbg.reseed(&entropy, extra),
                Some("generate") if prediction_resistance => {
                    drbg.reseed(&entropy, extra);
                    drbg.generate(&mut out, None).unwrap();
                }
                Some("generate") => drbg.generate(&mut out, extra).unwrap(),
                other => panic!("unexpected intendedUse {other:?}"),
            }
        }
        out
    }

    /// CAVP's HMAC_DRBG vectors for SHA-256, SHA-384, and SHA-512. Each count
    /// instantiates, reseeds, and generates twice; the file's empty additional
    /// input is the standard's Null. The second generate is the returned bits.
    #[test]
    fn cavp() {
        use crate::high::hash::{Sha384, Sha512};
        use crate::test::{CavpSink, Value, process_cavp};

        #[derive(Default)]
        struct State {
            hash: String,
            entropy: Vec<u8>,
            nonce: Vec<u8>,
            personalization: Vec<u8>,
            reseed: Vec<u8>,
            reseed_additional: Vec<u8>,
            additional: Vec<Vec<u8>>,
            tests: usize,
        }

        fn provided(bytes: &[u8]) -> Option<&[u8]> {
            if bytes.is_empty() { None } else { Some(bytes) }
        }

        fn second_output<H: Hash>(state: &State, len: usize) -> Vec<u8> {
            let mut drbg = HmacDrbg::<H>::new(&state.entropy, &state.nonce, &state.personalization);
            drbg.reseed(&state.reseed, provided(&state.reseed_additional));
            let mut out = vec![0; len];
            drbg.generate(&mut out, provided(&state.additional[0]))
                .unwrap();
            drbg.generate(&mut out, provided(&state.additional[1]))
                .unwrap();
            out
        }

        impl CavpSink for State {
            fn on_meta(&mut self, meta: &str) {
                if meta.split_once(" = ").is_none() {
                    self.hash = meta.to_string();
                }
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "COUNT" => self.additional.clear(),
                    "AdditionalInput" => self.additional.push(value.bytes()),
                    "AdditionalInputReseed" => self.reseed_additional = value.bytes(),
                    "EntropyInput" => self.entropy = value.bytes(),
                    "Nonce" => self.nonce = value.bytes(),
                    "PersonalizationString" => self.personalization = value.bytes(),
                    "EntropyInputReseed" => self.reseed = value.bytes(),
                    "ReturnedBits" => {
                        let expected = value.bytes();
                        let out = match self.hash.as_str() {
                            "SHA-256" => second_output::<Sha256>(self, expected.len()),
                            "SHA-384" => second_output::<Sha384>(self, expected.len()),
                            "SHA-512" => second_output::<Sha512>(self, expected.len()),
                            _ => return,
                        };
                        assert_eq!(out, expected);
                        self.tests += 1;
                    }
                    _ => panic!("unexpected value {name}"),
                }
            }
        }

        let mut state = State::default();
        process_cavp("../thirdparty/cavp/drbg/HMAC_DRBG.rsp", &mut state);
        // Sixteen groups of 15 for each of SHA-256, SHA-384, and SHA-512.
        assert_eq!(state.tests, 3 * 16 * 15);
    }

    /// ACVP's hmacDRBG samples, no derivation function, for the hashes this
    /// DRBG implements. Prediction resistance reseeds with that step's entropy
    /// and additional input, then generates with Null additional input.
    #[test]
    fn acvp() {
        use crate::high::hash::{Sha384, Sha512};
        use crate::test::Acvp;

        for name in ["hmacDRBG-1.0", "hmacDRBG-SP800-90Ar1"] {
            let mut tests = 0usize;
            for group in crate::test::acvp(name) {
                assert!(!group.flag("derFunc"));
                assert!(group.flag("reSeed"));
                let pr = group.flag("predResistance");
                let bits = group.int("returnedBitsLen");
                assert_eq!(bits % 8, 0, "returnedBitsLen is whole bytes");
                let mode = group.str("mode");
                for test in group.tests() {
                    let out = match mode {
                        "SHA2-256" => acvp_run::<Sha256>(test, pr, bits),
                        "SHA2-384" => acvp_run::<Sha384>(test, pr, bits),
                        "SHA2-512" => acvp_run::<Sha512>(test, pr, bits),
                        other => panic!("unexpected hmacDRBG mode {other}"),
                    };
                    assert_eq!(out, hex::decode(test.str("returnedBits")).unwrap());
                    tests += 1;
                }
            }
            let expected = match name {
                "hmacDRBG-1.0" => 90,
                "hmacDRBG-SP800-90Ar1" => 180,
                _ => unreachable!(),
            };
            assert_eq!(tests, expected, "{name}");
        }
    }

    #[test]
    fn reseed_interval_refuses_without_changing_state() {
        let mut drbg = HmacDrbg::<Sha256>::new(&[1, 2, 3, 4], &[5, 6], &[]);
        drbg.reseed_counter = MAX_RESEED_INTERVAL + 1;
        let mut out = [0u8; 16];
        assert_eq!(drbg.generate(&mut out, None), Err(Error::RngFailed));
        assert_eq!(out, [0u8; 16]);
        assert_eq!(drbg.reseed_counter, MAX_RESEED_INTERVAL + 1);

        drbg.reseed_counter = MAX_RESEED_INTERVAL;
        assert!(drbg.generate(&mut out, None).is_ok());
    }

    #[test]
    fn secret_generate() {
        // Under `admin/ctgrind`, entropy, the nonce, and additional input stay
        // secret through instantiate, reseed, and generate. The output is
        // declassified only for the comparison.
        let entropy = [0x11u8; 32];
        let nonce = [0x22u8; 16];
        let additional = [0x33, 0x44, 0x55, 0x66];
        let mut wanted = [0u8; 32];
        let mut drbg = HmacDrbg::<Sha256>::new(&entropy, &nonce, &[]);
        drbg.reseed(&entropy, Some(&additional));
        drbg.generate(&mut wanted, Some(&additional)).unwrap();

        crate::low::ct::secret_slice(&entropy);
        crate::low::ct::secret_slice(&nonce);
        crate::low::ct::secret_slice(&additional);
        let mut drbg = HmacDrbg::<Sha256>::new(&entropy, &nonce, &[]);
        drbg.reseed(&entropy, Some(&additional));
        let mut out = [0u8; 32];
        drbg.generate(&mut out, Some(&additional)).unwrap();
        crate::low::ct::public_slice(&out);
        assert_eq!(out, wanted);
    }

    #[test]
    fn rfc6979_example() {
        let x =
            b"\x00\x9A\x4D\x67\x92\x29\x5A\x7F\x73\x0F\xC3\xF2\xB4\x9C\xBC\x0F\x62\xE8\x62\x27\x2F";
        let h1 =
            b"\x01\x79\x5E\xDF\x0D\x54\xDB\x76\x0F\x15\x6D\x0D\xAC\x04\xC0\x32\x2B\x3A\x20\x42\x24";

        let mut ctx = HmacDrbg::<Sha256>::new(x, h1, &[]);
        let mut t1 = [0u8; 32];
        ctx.fill(&mut t1).unwrap();
        assert_eq!(&t1, b"\x93\x05\xA4\x6D\xE7\xFF\x8E\xB1\x07\x19\x4D\xEB\xD3\xFD\x48\xAA\x20\xD5\xE7\x65\x6C\xBE\x0E\xA6\x9D\x2A\x8D\x4E\x7C\x67\x31\x4A");

        let mut t2 = [0u8; 32];
        ctx.fill(&mut t2).unwrap();
        assert_eq!(&t2, b"\xC7\x0C\x78\x60\x8A\x3B\x5B\xE9\x28\x9B\xE9\x0E\xF6\xE8\x1A\x9E\x2C\x15\x16\xD5\x75\x1D\x2F\x75\xF5\x00\x33\xE4\x5F\x73\xBD\xEB");
    }
}
