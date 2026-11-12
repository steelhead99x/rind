//! Feeds rind-str0m what an SRTP peer controls, through the traits str0m
//! calls and in the shapes it calls them, and compares each answer with
//! str0m's own aws-lc-rs provider. str0m keeps its packet parsing private, so
//! this calls the ciphers as `SrtpContext::unprotect_rtp` and
//! `unprotect_rtcp` do: AES-CM's output padded to a whole block, and
//! AES-GCM's input at least a tag long, with its additional data whole or, for
//! unencrypted SRTCP, in two parts. Its DTLS runs through rind-dimpl, which
//! the `dimpl` target covers, and its key derivation reads no peer bytes.

#![no_main]

use std::sync::OnceLock;

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use str0m::crypto::CryptoProvider;

mod edit;
use edit::Edit;

fuzz_target!(|input: Input| match input {
    Input::Cm { key, iv, input } => cm(key, &iv, &input),
    Input::Gcm {
        aes256,
        key,
        iv,
        aad,
        split,
        plain,
        edit,
    } => gcm(aes256, key, &iv, &aad, split, &plain, &edit),
    Input::Hmac { key, payloads } => hmac(&key, &payloads),
});

#[derive(Arbitrary, Debug)]
enum Input {
    /// An AES_CM_128_HMAC_SHA1_80 payload, which str0m decrypts once its HMAC verifies.
    Cm {
        key: [u8; 16],
        iv: [u8; 16],
        input: Vec<u8>,
    },
    /// An AEAD_AES_128_GCM or AEAD_AES_256_GCM packet the peer sealed, then
    /// edited. Its additional data is at least the 12 bytes of an RTP header
    /// or SRTCP's prefix and index.
    Gcm {
        aes256: bool,
        key: [u8; 32],
        iv: [u8; 12],
        aad: ([u8; 12], Vec<u8>),
        split: Option<u8>,
        plain: Vec<u8>,
        edit: Edit,
    },
    /// The packet and index that AES_CM_128_HMAC_SHA1_80's tag covers, under
    /// the derived 20-byte key.
    Hmac {
        key: [u8; 20],
        payloads: Vec<Vec<u8>>,
    },
}

fn rind() -> &'static CryptoProvider {
    static PROVIDER: OnceLock<CryptoProvider> = OnceLock::new();
    PROVIDER.get_or_init(rind_str0m::default_provider)
}

fn baseline() -> &'static CryptoProvider {
    static PROVIDER: OnceLock<CryptoProvider> = OnceLock::new();
    PROVIDER.get_or_init(str0m_aws_lc_rs::default_provider)
}

/// str0m pads AES-CM's output by one block less a byte, as aws-lc-rs needs.
const CTR_PADDING: usize = 15;

const TAG_LEN: usize = 16;

fn cm(key: [u8; 16], iv: &[u8; 16], input: &[u8]) {
    let decrypt = |provider: &CryptoProvider| {
        let mut output = vec![0; input.len() + CTR_PADDING];
        provider
            .srtp_provider
            .aes_128_cm_sha1_80()
            .create_cipher(key, false)
            .decrypt(iv, input, &mut output)
            .map(|()| output[..input.len()].to_vec())
            .ok()
    };
    assert_eq!(decrypt(rind()), decrypt(baseline()));
}

fn gcm(
    aes256: bool,
    key: [u8; 32],
    iv: &[u8; 12],
    aad: &([u8; 12], Vec<u8>),
    split: Option<u8>,
    plain: &[u8],
    edit: &Edit,
) {
    let aad = [&aad.0[..], &aad.1].concat();
    let aads: Vec<&[u8]> = match split {
        None => vec![&aad],
        Some(at) => {
            let (a, b) = aad.split_at(usize::from(at) % (aad.len() + 1));
            vec![a, b]
        }
    };
    let cipher = |provider: &CryptoProvider| -> Box<dyn Gcm> {
        let srtp = provider.srtp_provider;
        match aes256 {
            false => Box::new(
                srtp.aead_aes_128_gcm()
                    .create_cipher(key[..16].try_into().unwrap(), false),
            ),
            true => Box::new(srtp.aead_aes_256_gcm().create_cipher(key, false)),
        }
    };

    let mut sealed = vec![0; plain.len() + TAG_LEN];
    cipher(baseline())
        .encrypt(iv, &aad, plain, &mut sealed)
        .unwrap();
    let edited = edit.apply(&mut sealed);
    if sealed.len() < TAG_LEN {
        // str0m refuses a packet shorter than its tag before decrypting.
        return;
    }

    let open = |provider: &CryptoProvider| {
        let mut output = vec![0; sealed.len() - TAG_LEN];
        let opened = cipher(provider).decrypt(iv, &aads, &sealed, &mut output);
        match opened {
            Ok(len) => Some(output[..len].to_vec()),
            Err(_) => {
                assert!(
                    output.iter().all(|b| *b == 0) || output == sealed[..output.len()],
                    "a failed open left plaintext"
                );
                None
            }
        }
    };
    let opened = open(rind());
    assert_eq!(opened, open(baseline()));
    if !edited {
        assert_eq!(opened.as_deref(), Some(plain), "an unedited packet opens");
    }
}

fn hmac(key: &[u8; 20], payloads: &[Vec<u8>]) {
    let payloads = payloads.iter().map(Vec::as_slice).collect::<Vec<_>>();
    let tag = |provider: &CryptoProvider| provider.sha1_hmac_provider.sha1_hmac(key, &payloads);
    assert_eq!(tag(rind()), tag(baseline()));
}

/// AES-GCM under either key length, as str0m's two traits share a shape.
trait Gcm {
    fn encrypt(
        &mut self,
        iv: &[u8; 12],
        aad: &[u8],
        input: &[u8],
        output: &mut [u8],
    ) -> Result<(), String>;
    fn decrypt(
        &mut self,
        iv: &[u8; 12],
        aads: &[&[u8]],
        input: &[u8],
        output: &mut [u8],
    ) -> Result<usize, String>;
}

macro_rules! gcm {
    ($trait:path) => {
        impl Gcm for Box<dyn $trait> {
            fn encrypt(
                &mut self,
                iv: &[u8; 12],
                aad: &[u8],
                input: &[u8],
                output: &mut [u8],
            ) -> Result<(), String> {
                (**self)
                    .encrypt(iv, aad, input, output)
                    .map_err(|e| e.to_string())
            }
            fn decrypt(
                &mut self,
                iv: &[u8; 12],
                aads: &[&[u8]],
                input: &[u8],
                output: &mut [u8],
            ) -> Result<usize, String> {
                (**self)
                    .decrypt(iv, aads, input, output)
                    .map_err(|e| e.to_string())
            }
        }
    };
}
gcm!(str0m::crypto::AeadAes128GcmCipher);
gcm!(str0m::crypto::AeadAes256GcmCipher);
