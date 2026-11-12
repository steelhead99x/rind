use core::sync::atomic::{AtomicUsize, Ordering};
use std::fmt;
use std::sync::Arc;

use rind::aead::{RandomNonce, RandomizedNonceKey};
use rind::rand;
use rustls::crypto::GetRandomFailed;
use rustls::server::ProducesTickets;
use rustls::{Error, TicketRotator};

/// A rustls session ticketer, sealing tickets with XChaCha20-Poly1305.
pub struct Ticketer {}

impl Ticketer {
    /// Makes a ticketer.
    ///
    /// Tickets are encrypted with XChaCha20Poly1305.
    /// Ticket keys are rotated every 6 hours.
    #[allow(clippy::new_ret_no_self)]
    pub fn new() -> Result<Arc<dyn ProducesTickets>, Error> {
        Ok(Arc::new(TicketRotator::new(
            ONE_TICKET_LIFETIME_SECS,
            make_ticket_generator,
        )?))
    }
}

fn make_ticket_generator() -> Result<Box<dyn ProducesTickets>, GetRandomFailed> {
    Ok(Box::new(XChaCha20Ticketer::new()?))
}

struct XChaCha20Ticketer {
    key: RandomizedNonceKey,
    key_name: [u8; 16],
    lifetime: u32,
    maximum_ciphertext_len: AtomicUsize,
}

impl XChaCha20Ticketer {
    fn new() -> Result<Self, GetRandomFailed> {
        let mut key = [0u8; 32];
        let mut key_name = [0u8; 16];

        rand::fill(&mut key).map_err(|_| GetRandomFailed)?;
        rand::fill(&mut key_name).map_err(|_| GetRandomFailed)?;

        let key = RandomizedNonceKey::new(&key);

        Ok(Self {
            key,
            key_name,
            lifetime: ONE_TICKET_LIFETIME_SECS,
            maximum_ciphertext_len: AtomicUsize::new(0),
        })
    }
}

impl ProducesTickets for XChaCha20Ticketer {
    fn enabled(&self) -> bool {
        true
    }

    fn lifetime(&self) -> u32 {
        self.lifetime
    }

    fn encrypt(&self, message: &[u8]) -> Option<Vec<u8>> {
        // wire format is:
        // - key_name [u8; 16]
        // - nonce [u8; 24]
        // - ciphertext [u8; n]
        // - tag [u8; 16]
        //
        // aad is key_name

        let mut sealed = message.to_vec();
        let nonce = self
            .key
            .seal_in_place_append_tag(&self.key_name, &mut sealed)
            .ok()?;

        let mut res = Vec::with_capacity(self.key_name.len() + NONCE_LEN + sealed.len());
        res.extend(&self.key_name);
        res.extend(nonce.as_ref());
        res.extend(sealed);

        self.maximum_ciphertext_len
            .fetch_max(res.len(), Ordering::SeqCst);

        Some(res)
    }

    fn decrypt(&self, ciphertext: &[u8]) -> Option<Vec<u8>> {
        if ciphertext.len() > self.maximum_ciphertext_len.load(Ordering::SeqCst) {
            return None;
        }

        let plain_len = ciphertext
            .len()
            .saturating_sub(self.key_name.len() + NONCE_LEN + TAG_LEN);

        if plain_len == 0 {
            return None;
        }

        let (alleged_key_name, rest) = ciphertext.split_at(self.key_name.len());

        // nb. key_name is public data
        if alleged_key_name != self.key_name {
            return None;
        }

        let (nonce, sealed) = rest.split_at(NONCE_LEN);
        let nonce = RandomNonce::from(<[u8; NONCE_LEN]>::try_from(nonce).unwrap());
        let mut plain = sealed.to_vec();

        self.key
            .open_in_place(nonce, alleged_key_name, &mut plain)
            .ok()?;
        plain.truncate(plain_len);
        Some(plain)
    }
}

impl fmt::Debug for XChaCha20Ticketer {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("XChaCha20Ticketer")
            .field("lifetime", &self.lifetime)
            .finish_non_exhaustive()
    }
}

const ONE_TICKET_LIFETIME_SECS: u32 = 6 * 60 * 60;
const NONCE_LEN: usize = 24;
const TAG_LEN: usize = 16;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn roundtrip() {
        let t = Ticketer::new().unwrap();
        let ehello = t.encrypt(b"hello").unwrap();
        assert_eq!(t.decrypt(&ehello).unwrap(), b"hello");

        assert!(t.enabled());
        assert_eq!(t.lifetime(), ONE_TICKET_LIFETIME_SECS * 2);
        let theirs = rustls::crypto::aws_lc_rs::Ticketer::new().unwrap();
        assert_eq!(t.lifetime(), theirs.lifetime());
    }

    #[test]
    fn make_generator() {
        let g = make_ticket_generator().unwrap();
        assert!(g.enabled());
        // aws-lc-rs's `Ticketer` is a rotator of two of these generators, so
        // one generator's lifetime is half of that rotator's. A change to
        // `ONE_TICKET_LIFETIME_SECS` no longer matches aws-lc-rs.
        let theirs = rustls::crypto::aws_lc_rs::Ticketer::new().unwrap();
        let one_ticket = theirs.lifetime() / 2;
        assert_eq!(g.lifetime(), one_ticket);
        let rendered = format!("{g:?}");
        assert!(rendered.contains("XChaCha20Ticketer"), "{rendered}");
        assert!(rendered.contains(&one_ticket.to_string()), "{rendered}");
    }

    #[test]
    fn shorter_ticket_decrypts_after_a_longer_one() {
        // `decrypt` refuses a ciphertext longer than any ticket this key has
        // sealed. Replacing that `>` with `<` refuses the shorter one instead.
        let t = XChaCha20Ticketer::new().unwrap();
        let long = t.encrypt(&[0xab; 48]).unwrap();
        let short = t.encrypt(b"hello").unwrap();
        assert!(long.len() > short.len());
        assert_eq!(t.decrypt(&short).as_deref(), Some(&b"hello"[..]));
        assert_eq!(t.decrypt(&long).unwrap().len(), 48);
    }

    #[test]
    fn length_checks() {
        let t = Ticketer::new().unwrap();
        assert_eq!(t.decrypt(b""), None);
        assert_eq!(t.decrypt(b"a"), None);

        let e = t.encrypt(b"a").unwrap();
        assert_eq!(t.decrypt(&e).unwrap(), b"a");
        assert_eq!(t.decrypt(&e[..e.len() - 1]), None);
    }

    #[test]
    fn non_malleable() {
        let t = Ticketer::new().unwrap();
        let ehello = t.encrypt(b"hello").unwrap();

        for i in 0..ehello.len() {
            let mut ehello_tmp = ehello.clone();
            ehello_tmp[i] ^= 1;
            assert_eq!(None, t.decrypt(&ehello_tmp));
        }
    }
}
