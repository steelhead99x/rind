// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::marker::PhantomData;

use super::digest::Digest;
use super::hash::Hash;
use super::hmac::HmacKey;
use crate::Error;
#[cfg(any(test, rind_fips))]
use crate::low::zeroise;
use crate::mid::rng::RandomSource;

/// SP 800-90A's HMAC_DRBG: RFC 6979's ECDSA nonces, and the FIPS module's
/// random generator.
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
            reseed_counter: 1,
            _h: PhantomData,
        };
        r.update(seed_material);
        r
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

    /// SP 800-90A section 10.1.2.4's reseed.
    #[cfg(any(test, rind_fips))]
    pub(crate) fn reseed(&mut self, entropy_input: &[u8], additional_input: &[u8]) {
        // 1. seed_material = entropy_input || additional_input.
        // 2. (Key, V) = HMAC_DRBG_Update (seed_material, Key, V).
        self.update(&[entropy_input, additional_input]);
        // 3. reseed_counter = 1.
        self.reseed_counter = 1;
    }

    /// SP 800-90A section 10.1.2.5's generate, steps 2 to 7: the caller
    /// checks the reseed counter and bounds the request.
    pub(crate) fn generate(&mut self, out: &mut [u8], additional_input: &[u8]) {
        let hashlen = self.v.as_ref().len();
        let one = [additional_input];
        let provided: &[&[u8]] = if additional_input.is_empty() {
            &[]
        } else {
            &one
        };

        // 2. If additional_input ≠ Null, then (Key, V) =
        //    HMAC_DRBG_Update (additional_input, Key, V).
        if !provided.is_empty() {
            self.update(provided);
        }

        // 3. - 5. this is a different formulation, but
        // ends up with all `V` terms being written to `out`.
        for chunk in out.chunks_mut(hashlen) {
            // V = HMAC (Key, V).
            self.v = HmacKey::<H>::new(self.k.as_ref()).sign(self.v.as_ref());
            chunk.copy_from_slice(&self.v.as_ref()[..chunk.len()]);
        }

        // 6. (Key, V) = HMAC_DRBG_Update (additional_input, Key, V).
        self.update(provided);
        // 7. reseed_counter = reseed_counter + 1.
        self.reseed_counter += 1;
    }

    /// Wipes K and V, the secret state, under `wipe`.
    #[cfg(any(test, rind_fips))]
    pub(crate) fn zeroise(&mut self) {
        zeroise(self.k.as_mut());
        zeroise(self.v.as_mut());
    }
}

impl<H: Hash> RandomSource for HmacDrbg<H> {
    fn fill(&mut self, out: &mut [u8]) -> Result<(), Error> {
        // 1. If reseed_counter > reseed_interval, then
        //    return an indication that a reseed is required.
        // nb. in practice, does not happen in our uses
        assert!(self.reseed_counter < 0x1_0000_0000_0000);

        self.generate(out, &[]);
        Ok(())
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::high::hash::Sha256;

    /// CAVP's HMAC_DRBG vectors for the hashes ECDSA's nonces and the FIPS
    /// module use: each instantiates, reseeds, and generates twice, checking
    /// the second output.
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
            additional_reseed: Vec<u8>,
            additional: Vec<Vec<u8>>,
            tests: usize,
        }

        fn second_output<H: Hash>(state: &State, len: usize) -> Vec<u8> {
            let mut drbg = HmacDrbg::<H>::new(&state.entropy, &state.nonce, &state.personalization);
            drbg.reseed(&state.reseed, &state.additional_reseed);
            let mut out = vec![0; len];
            drbg.generate(&mut out, &state.additional[0]);
            drbg.generate(&mut out, &state.additional[1]);
            out
        }

        impl CavpSink for State {
            fn on_meta(&mut self, meta: &str) {
                if !meta.contains(" = ") {
                    self.hash = meta.to_string();
                }
            }

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "COUNT" => self.additional.clear(),
                    "EntropyInput" => self.entropy = value.bytes(),
                    "Nonce" => self.nonce = value.bytes(),
                    "PersonalizationString" => self.personalization = value.bytes(),
                    "EntropyInputReseed" => self.reseed = value.bytes(),
                    "AdditionalInputReseed" => self.additional_reseed = value.bytes(),
                    "AdditionalInput" => self.additional.push(value.bytes()),
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
        // Sixteen groups of 15 per hash.
        assert_eq!(state.tests, 3 * 16 * 15);
    }

    #[test]
    fn secret_entropy_and_state() {
        // Under `admin/ctgrind`, nothing may branch on or index by the
        // entropy or the state derived from it, through instantiate, reseed,
        // and a generate of a partial last block.
        use crate::high::hash::Sha512;

        fn draw(entropy: &[u8], reseed: &[u8]) -> [u8; 100] {
            let mut drbg = HmacDrbg::<Sha512>::new(entropy, &[0xa5; 16], b"");
            drbg.reseed(reseed, b"");
            let mut out = [0u8; 100];
            drbg.generate(&mut out, b"additional");
            out
        }

        let entropy = [0x5a; 32];
        let reseed = [0x3c; 32];
        let wanted = draw(&entropy, &reseed);
        crate::low::ct::secret_slice(&entropy);
        crate::low::ct::secret_slice(&reseed);
        assert_eq!(crate::low::ct::into_public(draw(&entropy, &reseed)), wanted);
    }

    #[test]
    fn zeroise_wipes_the_state_under_wipe() {
        let mut drbg = HmacDrbg::<Sha256>::new(&[1; 32], &[2; 16], b"");
        drbg.zeroise();
        let wiped = drbg
            .k
            .as_ref()
            .iter()
            .chain(drbg.v.as_ref())
            .all(|&b| b == 0);
        assert_eq!(wiped, cfg!(feature = "wipe"));
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
