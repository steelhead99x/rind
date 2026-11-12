// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The FIPS module's SP 800-90A HMAC_DRBG.
//!
//! One generator per thread, seeded from a process-wide generator, seeded
//! from the operating system. rind's own key generation does not call this.

use std::cell::RefCell;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, Once};

use rind::Error;
use rind::drbg::HmacDrbg;

/// aws-lc's `kCtrDrbgReseedInterval`: generate calls before a reseed
/// (`crypto/fipsmodule/rand/internal.h`). SP 800-90A allows up to 2^48.
const RESEED_EVERY: u64 = 4096;

/// Entropy per seed or reseed. 64 bytes is SHA-512's output length and covers
/// a 256-bit strength. The nonce is 32 bytes, above the standard's
/// security_strength/2 minimum when no derivation function is used.
const ENTROPY: usize = 64;
const NONCE: usize = 32;

struct Node {
    drbg: HmacDrbg,
    pid: u32,
    generates: u64,
}

trait Entropy {
    fn fill(&mut self, out: &mut [u8]) -> Result<(), Error>;
}

struct OsEntropy;

impl Entropy for OsEntropy {
    fn fill(&mut self, out: &mut [u8]) -> Result<(), Error> {
        getrandom::fill(out).map_err(|_| Error::RngFailed)
    }
}

fn instantiate(entropy: &mut impl Entropy, pid: u32) -> Result<Node, Error> {
    let mut seed = [0u8; ENTROPY];
    let mut nonce = [0u8; NONCE];
    entropy.fill(&mut seed)?;
    entropy.fill(&mut nonce)?;
    Ok(Node {
        drbg: HmacDrbg::new(&seed, &nonce, &[]),
        pid,
        generates: 0,
    })
}

fn reseed(node: &mut Node, entropy: &mut impl Entropy) -> Result<(), Error> {
    let mut seed = [0u8; ENTROPY];
    entropy.fill(&mut seed)?;
    node.drbg.reseed(&seed, None);
    node.generates = 0;
    Ok(())
}

/// One generate from `parent`, reseeding it from `entropy` first when its
/// call count has reached `interval`.
fn parent_generate(
    parent: &mut Node,
    entropy: &mut impl Entropy,
    interval: u64,
    out: &mut [u8],
) -> Result<(), Error> {
    if parent.generates >= interval {
        reseed(parent, entropy)?;
    }
    parent.drbg.generate(out, None)?;
    parent.generates += 1;
    Ok(())
}

fn spawn_child(
    parent: &mut Node,
    entropy: &mut impl Entropy,
    interval: u64,
    pid: u32,
) -> Result<Node, Error> {
    let mut seed = [0u8; ENTROPY];
    let mut nonce = [0u8; NONCE];
    parent_generate(parent, entropy, interval, &mut seed)?;
    parent_generate(parent, entropy, interval, &mut nonce)?;
    Ok(Node {
        drbg: HmacDrbg::new(&seed, &nonce, &[]),
        pid,
        generates: 0,
    })
}

fn child_generate(
    parent: &mut Node,
    child: &mut Node,
    entropy: &mut impl Entropy,
    interval: u64,
    out: &mut [u8],
) -> Result<(), Error> {
    let mut rest = out;
    loop {
        if child.generates >= interval {
            let mut seed = [0u8; ENTROPY];
            parent_generate(parent, entropy, interval, &mut seed)?;
            child.drbg.reseed(&seed, None);
            child.generates = 0;
        }
        let n = rest.len().min(1 << 16);
        let (head, tail) = rest.split_at_mut(n);
        child.drbg.generate(head, None)?;
        child.generates += 1;
        if tail.is_empty() {
            return Ok(());
        }
        rest = tail;
    }
}

fn draw(
    parent: &mut Option<Node>,
    child: &mut Option<Node>,
    entropy: &mut impl Entropy,
    interval: u64,
    pid: u32,
    out: &mut [u8],
) -> Result<(), Error> {
    // A changed pid is a fork: the other process holds the copied state, so
    // both generators are replaced rather than reseeded from it.
    if parent.as_ref().is_none_or(|node| node.pid != pid) {
        *parent = Some(instantiate(entropy, pid)?);
    }
    let parent = parent
        .as_mut()
        .expect("the process generator was just seeded");
    if child.as_ref().is_none_or(|node| node.pid != pid) {
        *child = Some(spawn_child(parent, entropy, interval, pid)?);
    }
    let child = child
        .as_mut()
        .expect("the thread generator was just seeded");
    child_generate(parent, child, entropy, interval, out)
}

static PARENT: Mutex<Option<Node>> = Mutex::new(None);

thread_local! {
    static CHILD: RefCell<Option<Node>> = const { RefCell::new(None) };
}

fn clear_parent() {
    if let Ok(mut parent) = PARENT.try_lock() {
        *parent = None;
    }
}

fn ensure_health() -> Result<(), Error> {
    static ONCE: Once = Once::new();
    static PASSED: AtomicBool = AtomicBool::new(false);
    ONCE.call_once(|| {
        PASSED.store(rind::drbg::health_test().is_ok(), Ordering::Relaxed);
    });
    if PASSED.load(Ordering::Relaxed) {
        Ok(())
    } else {
        Err(Error::Fault)
    }
}

fn register_exit_wipe() {
    static ONCE: Once = Once::new();
    ONCE.call_once(|| {
        #[cfg(unix)]
        {
            // SAFETY: `wipe_at_exit` is a C callback that only drops the
            // process generator, and `atexit` runs it once at process exit.
            let rc = unsafe { atexit(wipe_at_exit) };
            debug_assert_eq!(rc, 0);
        }
    });
}

#[cfg(unix)]
unsafe extern "C" fn wipe_at_exit() {
    clear_parent();
}

#[cfg(unix)]
unsafe extern "C" {
    fn atexit(func: unsafe extern "C" fn()) -> i32;
}

/// Fills `out` from this thread's HMAC-SHA-512 DRBG.
///
/// The first call in the process runs [`rind::drbg::health_test`]. A failure
/// is [`Error::Fault`] and this returns no bytes. The first call on a thread
/// seeds the process generator from the operating system, then seeds the
/// thread's generator from that. A failed read returns [`Error::RngFailed`]
/// and tries no other source. After a fork, the next call replaces both
/// generators.
pub fn fill(out: &mut [u8]) -> Result<(), Error> {
    ensure_health()?;
    register_exit_wipe();
    let mut parent = PARENT.lock().map_err(|_| Error::RngFailed)?;
    CHILD.with(|child| {
        draw(
            &mut parent,
            &mut child.borrow_mut(),
            &mut OsEntropy,
            RESEED_EVERY,
            std::process::id(),
            out,
        )
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Script<'a> {
        rest: &'a [u8],
    }

    impl Entropy for Script<'_> {
        fn fill(&mut self, out: &mut [u8]) -> Result<(), Error> {
            if out.len() > self.rest.len() {
                return Err(Error::RngFailed);
            }
            let (head, tail) = self.rest.split_at(out.len());
            out.copy_from_slice(head);
            self.rest = tail;
            Ok(())
        }
    }

    fn bytes(seed: u8, n: usize) -> Vec<u8> {
        vec![seed; n]
    }

    /// Parent entropy `0x11` * 64 and nonce `0x22` * 32. The child is seeded
    /// from the parent's next 64 and 32 bytes, then generates 32. The expected
    /// bytes are that sequence run with Python's `hmac`.
    #[test]
    fn scripted_tree_matches_hmac() {
        let mut seed = bytes(0x11, ENTROPY);
        seed.extend(bytes(0x22, NONCE));
        let mut script = Script { rest: &seed };
        let mut parent = None;
        let mut child = None;
        let mut out = [0u8; 32];
        draw(
            &mut parent,
            &mut child,
            &mut script,
            RESEED_EVERY,
            1,
            &mut out,
        )
        .unwrap();
        assert!(script.rest.is_empty());
        assert_eq!(
            out,
            [
                0x12, 0x60, 0x7a, 0x16, 0xb4, 0x74, 0xf6, 0x26, 0xc1, 0x98, 0xbf, 0x41, 0xe1, 0xa6,
                0xa5, 0x3e, 0xb0, 0x68, 0x24, 0x40, 0xc2, 0xe1, 0x0e, 0x80, 0x5e, 0x5d, 0x93, 0x83,
                0xb9, 0xbd, 0x84, 0x12,
            ]
        );

        let mut again = [0u8; 32];
        draw(
            &mut parent,
            &mut child,
            &mut script,
            RESEED_EVERY,
            1,
            &mut again,
        )
        .unwrap();
        assert!(
            script.rest.is_empty(),
            "a later generate reads no more entropy"
        );
        assert_ne!(again, out);
    }

    #[test]
    fn short_entropy_is_an_error_and_keeps_no_generator() {
        let seed = [0u8; 10];
        let mut script = Script { rest: &seed };
        let mut parent = None;
        let mut child = None;
        let mut out = [0u8; 32];
        assert_eq!(
            draw(
                &mut parent,
                &mut child,
                &mut script,
                RESEED_EVERY,
                1,
                &mut out
            ),
            Err(Error::RngFailed)
        );
        assert!(parent.is_none());
        assert!(child.is_none());
        assert_eq!(out, [0u8; 32]);
    }

    #[test]
    fn fork_replaces_both_generators() {
        let mut seed = bytes(0x11, ENTROPY);
        seed.extend(bytes(0x22, NONCE));
        seed.extend(bytes(0x11, ENTROPY));
        seed.extend(bytes(0x22, NONCE));
        let mut script = Script { rest: &seed };
        let mut parent = None;
        let mut child = None;
        let mut out = [0u8; 8];
        draw(
            &mut parent,
            &mut child,
            &mut script,
            RESEED_EVERY,
            1,
            &mut out,
        )
        .unwrap();
        assert_eq!(script.rest.len(), ENTROPY + NONCE);
        draw(
            &mut parent,
            &mut child,
            &mut script,
            RESEED_EVERY,
            2,
            &mut out,
        )
        .unwrap();
        assert!(script.rest.is_empty());
    }

    #[test]
    fn interval_reseeds_from_the_script() {
        // First fill: parent instantiate (96) and, because the second half of
        // the child's seed is the parent's second generate, a parent reseed
        // (64). Second fill: the child is due, and the parent is due again, so
        // one more parent reseed (64).
        let seed = bytes(0x5a, 96 + 64 + 64);
        let mut script = Script { rest: &seed };
        let mut parent = None;
        let mut child = None;
        let mut out = [0u8; 8];
        draw(&mut parent, &mut child, &mut script, 1, 7, &mut out).unwrap();
        assert_eq!(script.rest.len(), 64);
        draw(&mut parent, &mut child, &mut script, 1, 7, &mut out).unwrap();
        assert!(script.rest.is_empty());
    }

    #[test]
    fn threads_do_not_share_a_generator() {
        let mut joins = Vec::new();
        for _ in 0..4 {
            joins.push(std::thread::spawn(|| {
                let mut out = [0u8; 32];
                fill(&mut out).unwrap();
                out
            }));
        }
        let outs: Vec<_> = joins.into_iter().map(|join| join.join().unwrap()).collect();
        assert!(outs.iter().any(|out| out.iter().any(|&byte| byte != 0)));
    }

    #[test]
    fn os_fill_covers_its_buffer() {
        let mut first = [0u8; 32];
        let mut second = [0u8; 32];
        fill(&mut first).unwrap();
        fill(&mut second).unwrap();
        assert!(first.iter().any(|&byte| byte != 0));
        assert_ne!(first, second);
    }
}
