// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! A child forked without libc's `fork`, as a raw `clone` system call forks
//! it, runs none of the module's fork handlers, so it inherits its parent's
//! DRBG instance as it stood. Every draw reseeds from the OS first, so the
//! child still never repeats its parent's output. Its own test binary, so no
//! other thread is inside a draw when it forks.
#![cfg(all(rind_fips_module, any(target_arch = "x86_64", target_arch = "aarch64")))]

use core::ffi::c_long;
use std::thread;
use std::time::{Duration, Instant};

unsafe extern "C" {
    fn syscall(number: c_long, ...) -> c_long;
    fn pipe(fds: *mut i32) -> i32;
    fn read(fd: i32, buf: *mut u8, count: usize) -> isize;
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
    fn close(fd: i32) -> i32;
    fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    fn kill(pid: i32, signal: i32) -> i32;
    fn _exit(status: i32) -> !;
}

#[cfg(target_arch = "x86_64")]
const SYS_CLONE: c_long = 56;
#[cfg(target_arch = "aarch64")]
const SYS_CLONE: c_long = 220;
const SIGCHLD: c_long = 17;
const WNOHANG: i32 = 1;
const SIGKILL: i32 = 9;

#[test]
fn a_raw_fork_child_never_repeats_its_parent() {
    // The parent's instance exists before the fork, so the child copies it.
    rind_fips::rand::fill(&mut [0; 32]).unwrap();
    let mut fds = [0; 2];
    // SAFETY: `fds` holds the two descriptors `pipe` writes.
    assert_eq!(unsafe { pipe(fds.as_mut_ptr()) }, 0);
    let [from_child, to_parent] = fds;

    // `clone`'s other arguments, the new stack, thread IDs, and TLS, come in
    // a different order on x86_64 and aarch64; all zero, they agree.
    let none: c_long = 0;
    // SAFETY: `clone` with only SIGCHLD forks as `fork` does, without libc's
    // handlers. The child only draws, writes, and leaves through `_exit`.
    let pid = unsafe { syscall(SYS_CLONE, SIGCHLD, none, none, none, none) };
    assert!(pid >= 0, "clone failed");
    let pid = pid as i32;
    if pid == 0 {
        let mut out = [0; 32];
        let ok = rind_fips::rand::fill(&mut out).is_ok()
            // SAFETY: `out` is readable for its length.
            && unsafe { write(to_parent, out.as_ptr(), out.len()) } == out.len() as isize;
        // SAFETY: ends the child without running the parent's destructors.
        unsafe { _exit(if ok { 0 } else { 1 }) };
    }
    // SAFETY: the parent's copy of the write end, which it never uses, so
    // the read below ends once the child's copy closes.
    unsafe { close(to_parent) };

    let mut ours = [0; 32];
    rind_fips::rand::fill(&mut ours).unwrap();

    // The child's 32 bytes fit the pipe's buffer, so it exits without
    // waiting for the read; one that hangs fails the test.
    let deadline = Instant::now() + Duration::from_secs(10);
    let mut status = 0;
    loop {
        // SAFETY: `pid` is our child, and `status` writable.
        match unsafe { waitpid(pid, &mut status, WNOHANG) } {
            0 if Instant::now() < deadline => thread::sleep(Duration::from_millis(1)),
            0 => {
                // SAFETY: `pid` is our child, and `status` writable.
                unsafe {
                    kill(pid, SIGKILL);
                    waitpid(pid, &mut status, 0);
                }
                panic!("the child hung");
            }
            reaped => {
                assert_eq!(reaped, pid, "waitpid failed");
                break;
            }
        }
    }
    assert_eq!(status, 0, "the child failed to draw");

    let mut theirs = [0; 32];
    let mut filled = 0;
    while filled < theirs.len() {
        // SAFETY: `theirs` is writable past `filled` for the rest.
        let n = unsafe {
            read(
                from_child,
                theirs[filled..].as_mut_ptr(),
                theirs.len() - filled,
            )
        };
        assert!(n > 0, "the child wrote no draw");
        filled += n as usize;
    }
    assert_ne!(ours, theirs);
}
