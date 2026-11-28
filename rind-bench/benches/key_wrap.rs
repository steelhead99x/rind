//! Wrapping and unwrapping a 16- and a 32-byte key, each from the KEK's
//! bytes, as pyca and JWE use a KEK: aws-lc-rs's `KeyWrap` consumes its key
//! anyway.

#[cfg(target_arch = "xtensa")]
fn main() {}

#[cfg(not(target_arch = "xtensa"))]
mod common;

#[cfg(not(target_arch = "xtensa"))]
use common::{Dit, Size};
#[cfg(not(target_arch = "xtensa"))]
use rind::key_wrap::Mode;

#[cfg(not(target_arch = "xtensa"))]
const KEYS: [Size; 2] = [Size::new(16, "16B"), Size::new(32, "32B")];

/// One row's KEK, the key it wraps, that key wrapped by rind, and the
/// buffer each call writes.
#[cfg(not(target_arch = "xtensa"))]
struct Wrap {
    kek: &'static [u8],
    key: &'static [u8],
    wrapped: Vec<u8>,
    out: Vec<u8>,
}

#[cfg(not(target_arch = "xtensa"))]
impl Wrap {
    fn new(mode: Mode, kek_len: usize, key: Size) -> Self {
        let kek = &[0x42u8; 32][..kek_len];
        let key = &[0x24u8; 32][..key.len];
        let mut wrapped = vec![0u8; key.len() + 8];
        rind_kek(kek).wrap_key(mode, key, &mut wrapped).unwrap();
        Self {
            kek,
            key,
            wrapped,
            // aws-lc-rs's padded wrap wants 15 bytes of room
            out: vec![0u8; key.len() + 15],
        }
    }
}

#[cfg(not(target_arch = "xtensa"))]
fn rind_kek(kek: &[u8]) -> rind::key_wrap::AesKek {
    let algorithm = if kek.len() == 16 {
        &rind::key_wrap::AES_128
    } else {
        &rind::key_wrap::AES_256
    };
    rind::key_wrap::AesKek::new(algorithm, kek).unwrap()
}

macro_rules! rows {
    ($kek_len:literal, $mode:ident, $padded:literal, $unwrap:literal) => {
        fn wrap(key: Size) -> Wrap {
            Wrap::new(Mode::$mode, $kek_len, key)
        }

        fn rind_wrap(key: Size) -> Dit<Wrap> {
            Dit::hold(wrap(key))
        }

        #[bench(args = KEYS, setup = wrap)]
        fn aws_lc_rs(w: &mut Wrap) {
            use aws_lc_rs::key_wrap::{AES_128, AES_256, AesKek, KeyWrap, KeyWrapPadded};
            let algorithm = if $kek_len == 16 { &AES_128 } else { &AES_256 };
            let kek = AesKek::new(algorithm, w.kek).unwrap();
            match ($padded, $unwrap) {
                (false, false) => kek.wrap(w.key, &mut w.out).unwrap(),
                (false, true) => kek.unwrap(&w.wrapped, &mut w.out).unwrap(),
                (true, false) => kek.wrap_with_padding(w.key, &mut w.out).unwrap(),
                (true, true) => kek.unwrap_with_padding(&w.wrapped, &mut w.out).unwrap(),
            };
        }

        #[bench(args = KEYS, setup = rind_wrap)]
        fn rind(w: &mut Dit<Wrap>) {
            let w = &mut **w;
            let kek = rind_kek(w.kek);
            let key_len = w.key.len();
            if $unwrap {
                kek.unwrap_key(Mode::$mode, &w.wrapped, &mut w.out[..key_len])
                    .unwrap();
            } else {
                kek.wrap_key(Mode::$mode, w.key, &mut w.out[..key_len + 8])
                    .unwrap();
            }
        }
    };
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_kw_wrap {
    use swole::bench;

    use super::*;
    rows!(16, Kw, false, false);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_kw_unwrap {
    use swole::bench;

    use super::*;
    rows!(16, Kw, false, true);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_kwp_wrap {
    use swole::bench;

    use super::*;
    rows!(16, Kwp, true, false);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes128_kwp_unwrap {
    use swole::bench;

    use super::*;
    rows!(16, Kwp, true, true);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_kw_wrap {
    use swole::bench;

    use super::*;
    rows!(32, Kw, false, false);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_kw_unwrap {
    use swole::bench;

    use super::*;
    rows!(32, Kw, false, true);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_kwp_wrap {
    use swole::bench;

    use super::*;
    rows!(32, Kwp, true, false);
}

#[cfg(not(target_arch = "xtensa"))]
mod aes256_kwp_unwrap {
    use swole::bench;

    use super::*;
    rows!(32, Kwp, true, true);
}

#[cfg(not(target_arch = "xtensa"))]
fn main() {
    swole::main();
}
