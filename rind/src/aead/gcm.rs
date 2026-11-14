// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;
use core::mem::ManuallyDrop;

use super::{AES_128_GCM, AES_192_GCM, AES_256_GCM, Inner, Nonce};
use crate::Error;
use crate::cipher::Algorithm;
use crate::low::{Zeroable, zeroise_value};
use crate::mid::aes::check_gcm_iv;
use crate::mid::aes_gcm::AesGcm;

/// How long an AES-GCM tag is: one of NIST SP 800-38D's lengths, named in bits.
///
/// A forger's every try at a `t`-bit tag succeeds with probability 2^-t, and
/// each forgery against a short tag also helps recover the authentication key
/// (Ferguson, "Authentication weaknesses in GCM"). Keep [`TagLength::Full`]
/// unless a protocol fixes a shorter tag; SP 800-38D's Appendix C bounds how
/// much one key may open under 32- and 64-bit tags.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum TagLength {
    /// The whole 128-bit tag.
    Full,
    /// The first 120 bits of the tag.
    Truncated120,
    /// The first 112 bits of the tag.
    Truncated112,
    /// The first 104 bits of the tag.
    Truncated104,
    /// The first 96 bits of the tag.
    Truncated96,
    /// The first 64 bits of the tag.
    Truncated64,
    /// The first 32 bits of the tag.
    Truncated32,
}

impl TagLength {
    fn bytes(self) -> usize {
        match self {
            Self::Full => 16,
            Self::Truncated120 => 15,
            Self::Truncated112 => 14,
            Self::Truncated104 => 13,
            Self::Truncated96 => 12,
            Self::Truncated64 => 8,
            Self::Truncated32 => 4,
        }
    }
}

/// An AES-GCM IV of any length but zero, which the caller promises seals
/// only once under a key.
///
/// It is not `Clone`, so one value seals at most one message.
pub struct Iv<'a>(&'a [u8]);

impl<'a> Iv<'a> {
    /// Wraps `iv`, which the caller promises is never reused with the same
    /// key, failing with [`Error::WrongLength`] if it is empty or past GCM's
    /// limit of 2^61 - 1 bytes.
    pub fn assume_unique_for_key(iv: &'a [u8]) -> Result<Self, Error> {
        check_gcm_iv(iv)?;
        Ok(Self(iv))
    }
}

impl fmt::Debug for Iv<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Iv").finish_non_exhaustive()
    }
}

/// An AES-GCM key that takes an IV of any length and makes tags of one
/// [`TagLength`], as WebCrypto's AES-GCM does; wiped on drop under the `wipe` feature.
///
/// Prefer [`super::Key`], whose 96-bit nonces and full tags are what
/// protocols use; GCM hashes an IV of any other length into its counter,
/// which weakens its bounds. The caller owns IV uniqueness, as for a
/// [`super::Nonce`].
pub struct Key {
    // An `aead::Key`, so a 96-bit IV takes its path, compiled as when it had
    // no other caller.
    key: ManuallyDrop<super::Key>,
    tag_len: TagLength,
}

// All-zero is an `aead::Key` of zeroes and a full tag, as `Zeroable`
// requires. The key owns no memory beyond itself, so its own drop would only
// wipe what this one does; `ManuallyDrop` skips that second pass.
impl Drop for Key {
    fn drop(&mut self) {
        // Wipes the padding too, not only the key.
        zeroise_value(self);
    }
}

impl Zeroable for Key {}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Key")
            .field("algorithm", crate::cipher::aes(self.aes_gcm().key_len()))
            .finish_non_exhaustive()
    }
}

impl Key {
    /// Expands `key` for `algorithm`, to make tags of `tag_len`, failing with
    /// [`Error::WrongLength`] if it is not that algorithm's key length.
    pub fn new(
        algorithm: &'static Algorithm,
        key: &[u8],
        tag_len: TagLength,
    ) -> Result<Self, Error> {
        let aead = match algorithm.key_len {
            16 => &AES_128_GCM,
            24 => &AES_192_GCM,
            _ => &AES_256_GCM,
        };
        if key.len() != algorithm.key_len {
            return Err(Error::WrongLength);
        }
        Ok(Self {
            key: ManuallyDrop::new(super::Key::new(aead, key)?),
            tag_len,
        })
    }

    fn aes_gcm(&self) -> &AesGcm {
        match &self.key.0 {
            Inner::AesGcm(sealer) => &sealer.key,
            Inner::ChaCha20Poly1305(_) => unreachable!("`new` expands only AES"),
        }
    }

    /// The length of this key's tags, in bytes.
    pub fn tag_len(&self) -> usize {
        self.tag_len.bytes()
    }

    /// Encrypts `in_out` in place under `iv` and returns the tag.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `aad` or `in_out` is past GCM's limit: 2^61 - 1 and 2^36 - 32 bytes.
    pub fn seal_in_place_separate_tag(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        in_out: &mut [u8],
    ) -> Result<Tag, Error> {
        let mut tag = Tag {
            bytes: [0; 16],
            len: self.tag_len(),
        };
        match iv.0.try_into() {
            Ok(nonce) => {
                let nonce = Nonce::assume_unique_for_key(nonce);
                tag.bytes = self.key.seal_in_place_separate_tag(nonce, aad, in_out)?.0;
            }
            Err(_) => {
                self.aes_gcm()
                    .encrypt_any(iv.0, aad, in_out, &mut tag.bytes[..tag.len])?;
            }
        }
        Ok(tag)
    }

    /// Encrypts `in_out` in place under `iv` and appends the tag to it.
    ///
    /// Fails as [`Self::seal_in_place_separate_tag`] does.
    pub fn seal_in_place_append_tag<InOut>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        in_out: &mut InOut,
    ) -> Result<(), Error>
    where
        InOut: AsMut<[u8]> + for<'a> Extend<&'a u8>,
    {
        let tag = self.seal_in_place_separate_tag(iv, aad, in_out.as_mut())?;
        in_out.extend(tag.as_ref());
        Ok(())
    }

    /// Decrypts and verifies `in_out`, the ciphertext followed by its tag of
    /// [`Self::tag_len`] bytes, and returns the plaintext at its front.
    ///
    /// Fails with [`Error::DecryptFailed`] if `in_out` is shorter than a tag
    /// or does not verify, clearing the ciphertext in the latter case, and
    /// with [`Error::WrongLength`] past the sealing limits.
    pub fn open_in_place<'a>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        let at = in_out
            .len()
            .checked_sub(self.tag_len())
            .ok_or(Error::DecryptFailed)?;
        let (in_out, tag) = in_out.split_at_mut(at);
        self.open(iv, aad, tag, in_out)?;
        Ok(in_out)
    }

    /// Decrypts and verifies `in_out` against the separate `tag`, and returns
    /// the plaintext.
    ///
    /// Fails with [`Error::WrongLength`], leaving `in_out` unchanged, if
    /// `tag` is not [`Self::tag_len`] bytes or past the sealing limits, and
    /// with [`Error::DecryptFailed`], clearing `in_out`, if it does not
    /// verify.
    pub fn open_in_place_separate_tag<'a>(
        &self,
        iv: Iv<'_>,
        aad: &[u8],
        tag: &[u8],
        in_out: &'a mut [u8],
    ) -> Result<&'a mut [u8], Error> {
        if tag.len() != self.tag_len() {
            return Err(Error::WrongLength);
        }
        self.open(iv, aad, tag, in_out)?;
        Ok(in_out)
    }

    /// Opens `in_out` against `tag`, of this key's length.
    fn open(&self, iv: Iv<'_>, aad: &[u8], tag: &[u8], in_out: &mut [u8]) -> Result<(), Error> {
        match (iv.0.try_into(), tag.try_into()) {
            (Ok(nonce), Ok(tag)) => {
                let nonce = Nonce::assume_unique_for_key(nonce);
                self.key
                    .open_in_place_separate_tag(nonce, aad, super::Tag(tag), in_out)?;
            }
            _ => self.aes_gcm().decrypt_any(iv.0, aad, in_out, tag)?,
        }
        Ok(())
    }
}

/// A tag [`Key`] sealed, of its [`TagLength`].
#[derive(Clone, Copy)]
pub struct Tag {
    bytes: [u8; 16],
    len: usize,
}

impl fmt::Debug for Tag {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tag")
            .field("len", &self.len)
            .finish_non_exhaustive()
    }
}

impl AsRef<[u8]> for Tag {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::aead::{AES_128_GCM, Nonce};
    use crate::cipher::AES_128;
    use crate::test::*;

    fn iv(iv: &[u8]) -> Iv<'_> {
        Iv::assume_unique_for_key(iv).unwrap()
    }

    #[test]
    fn acvp() {
        for name in ["ACVP-AES-GCM-1.0", "ACVP-AES-GMAC-1.0"] {
            for group in crate::test::acvp(name) {
                assert_eq!(group.str("ivGen"), "external");
                let tag_len = match group.int("tagLen") {
                    128 => TagLength::Full,
                    32 => TagLength::Truncated32,
                    other => panic!("unexpected tag length {other}"),
                };
                for test in group.tests() {
                    let key = test.hex("key");
                    let key = Key::new(crate::cipher::aes(key.len()), &key, tag_len).unwrap();
                    let (iv_bytes, aad) = (test.hex("iv"), test.hex("aad"));
                    let (pt, ct, tag) = (test.hex("pt"), test.hex("ct"), test.hex("tag"));
                    match group.str("direction") {
                        "encrypt" => {
                            let mut text = pt;
                            let sealed = key
                                .seal_in_place_separate_tag(iv(&iv_bytes), &aad, &mut text)
                                .unwrap();
                            assert_eq!((text, sealed.as_ref()), (ct, &tag[..]));
                        }
                        "decrypt" => {
                            let mut text = ct;
                            let opened = key
                                .open_in_place_separate_tag(iv(&iv_bytes), &aad, &tag, &mut text)
                                .map(|pt| pt.to_vec());
                            match test.flag("testPassed") {
                                true => assert_eq!(opened.unwrap(), pt),
                                false => assert_eq!(opened, Err(Error::DecryptFailed)),
                            }
                        }
                        other => panic!("unexpected direction {other}"),
                    }
                }
            }
        }
    }

    const TAG_LENGTHS: [TagLength; 7] = [
        TagLength::Full,
        TagLength::Truncated120,
        TagLength::Truncated112,
        TagLength::Truncated104,
        TagLength::Truncated96,
        TagLength::Truncated64,
        TagLength::Truncated32,
    ];

    fn tag_length(bytes: usize) -> TagLength {
        *TAG_LENGTHS.iter().find(|t| t.bytes() == bytes).unwrap()
    }

    fn key(key: &[u8], tag_len: TagLength) -> Key {
        Key::new(crate::cipher::aes(key.len()), key, tag_len).unwrap()
    }

    // NIST's vectors: IVs of 1, 12, and 128 bytes, each tag length, and
    // forgeries under each.
    #[test]
    fn cavp() {
        #[derive(Default)]
        struct State {
            encrypt: bool,
            key: Vec<u8>,
            iv: Vec<u8>,
            ct: Vec<u8>,
            aad: Vec<u8>,
            pt: Vec<u8>,
            tag: Vec<u8>,
        }

        impl CavpSink for State {
            fn on_meta(&mut self, _meta: &str) {}

            fn on_value(&mut self, name: &str, value: Value<'_>) {
                match name {
                    "Count" => {}
                    "Key" => self.key = value.bytes(),
                    "IV" => self.iv = value.bytes(),
                    "CT" => self.ct = value.bytes(),
                    "AAD" => self.aad = value.bytes(),
                    "PT" if self.encrypt => self.pt = value.bytes(),
                    "Tag" if !self.encrypt => self.tag = value.bytes(),
                    "Tag" => {
                        let want = value.bytes();
                        let key = key(&self.key, tag_length(want.len()));
                        let tag = key
                            .seal_in_place_separate_tag(iv(&self.iv), &self.aad, &mut self.pt)
                            .unwrap();
                        assert_eq!(self.pt, self.ct);
                        assert_eq!(tag.as_ref(), want);
                    }
                    "FAIL" | "PT" => {
                        let key = key(&self.key, tag_length(self.tag.len()));
                        let result = key.open_in_place_separate_tag(
                            iv(&self.iv),
                            &self.aad,
                            &self.tag,
                            &mut self.ct,
                        );
                        match name {
                            "PT" => assert_eq!(result.unwrap(), value.bytes()),
                            _ => assert_eq!(result.unwrap_err(), Error::DecryptFailed),
                        }
                    }
                    _ => todo!("unhandled value {name} = {value:?}"),
                }
            }
        }

        for file in ["gcmDecrypt128", "gcmDecrypt192", "gcmDecrypt256"] {
            process_cavp(
                format!("../thirdparty/cavp/gcm/{file}.rsp"),
                &mut State::default(),
            );
        }
        for file in [
            "gcmEncryptExtIV128",
            "gcmEncryptExtIV192",
            "gcmEncryptExtIV256",
        ] {
            let mut state = State {
                encrypt: true,
                ..Default::default()
            };
            process_cavp(format!("../thirdparty/cavp/gcm/{file}.rsp"), &mut state);
        }
    }

    // A 96-bit IV and full tag are `aead::Key`'s, and each shorter tag is
    // their prefix, appended or separate.
    #[test]
    fn tags_are_prefixes() {
        let raw = [9u8; 16];
        let mut want = b"message".to_vec();
        crate::aead::Key::new(&AES_128_GCM, &raw)
            .unwrap()
            .seal_in_place_append_tag(Nonce::assume_unique_for_key([3; 12]), b"aad", &mut want)
            .unwrap();

        for tag_len in TAG_LENGTHS {
            let key = key(&raw, tag_len);
            let mut sealed = b"message".to_vec();
            key.seal_in_place_append_tag(iv(&[3; 12]), b"aad", &mut sealed)
                .unwrap();
            assert_eq!(sealed, want[..7 + key.tag_len()], "{tag_len:?}");

            let mut separate = b"message".to_vec();
            let tag = key
                .seal_in_place_separate_tag(iv(&[3; 12]), b"aad", &mut separate)
                .unwrap();
            assert_eq!([&separate[..], tag.as_ref()].concat(), sealed);

            let mut opened = sealed.clone();
            assert_eq!(
                key.open_in_place(iv(&[3; 12]), b"aad", &mut opened)
                    .unwrap(),
                b"message"
            );
        }
    }

    #[test]
    fn refuses_malformed_input() {
        assert_eq!(
            Key::new(&AES_128, &[0; 32], TagLength::Full).err(),
            Some(Error::WrongLength)
        );
        // An empty IV, for which GCM is undefined.
        assert_eq!(
            Iv::assume_unique_for_key(&[]).err(),
            Some(Error::WrongLength)
        );

        for tag_len in TAG_LENGTHS {
            let key = key(&[1; 32], tag_len);
            let len = key.tag_len();

            let mut msg = [5u8; 20];

            // A tag of another length than the key's, so a forger cannot
            // pick a shorter one.
            let tag = key
                .seal_in_place_separate_tag(iv(&[2; 7]), &[], &mut msg)
                .unwrap();
            for other in [len - 1, len + 1] {
                let mut copy = msg;
                assert_eq!(
                    key.open_in_place_separate_tag(iv(&[2; 7]), &[], &[0; 17][..other], &mut copy)
                        .err(),
                    Some(Error::WrongLength)
                );
                assert_eq!(copy, msg);
            }

            // Input shorter than a tag, and a tag wrong in its last byte.
            let mut short = vec![0xaa; len - 1];
            assert_eq!(
                key.open_in_place(iv(&[2; 7]), &[], &mut short).err(),
                Some(Error::DecryptFailed)
            );
            assert_eq!(short, vec![0xaa; len - 1]);
            let mut wrong = tag.as_ref().to_vec();
            wrong[len - 1] ^= 1;
            assert_eq!(
                key.open_in_place_separate_tag(iv(&[2; 7]), &[], &wrong, &mut msg)
                    .err(),
                Some(Error::DecryptFailed)
            );
            assert_eq!(msg, [0; 20]);
        }
    }
}
