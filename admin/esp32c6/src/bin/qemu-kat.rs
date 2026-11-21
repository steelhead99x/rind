// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Runs rind's known-answer checks on riscv32imac under `qemu-riscv32` (user
//! mode), and reports each one's peak stack and heap use.
//!
//! The binary has no libc and no startup code: `_start` sets the stack and
//! the program talks to the kernel through `ecall`. Stack use is the deepest
//! byte an algorithm touched in a painted region, and heap use the peak of
//! live bytes through a counting allocator, so both are properties of the code
//! and not of the emulator. Time is not reported: qemu's is not a board's.
//!
//! The randomness source below is a fixed xorshift stream so a run repeats. It
//! is NOT secure and exists only so the round-trip checks can generate keys.

#![no_std]
#![no_main]

extern crate alloc;

use alloc::format;
use core::alloc::{GlobalAlloc, Layout};
use core::arch::{asm, global_asm};
use core::cell::UnsafeCell;
use core::sync::atomic::{AtomicUsize, Ordering::Relaxed};

const STACK_BYTES: usize = 512 * 1024;
const HEAP_BYTES: usize = 512 * 1024;
const PAINT: u8 = 0xA5;
/// Bytes below the caller's sp left unpainted for the painting call itself.
const GUARD: usize = 256;

#[repr(C, align(16))]
struct Stack(UnsafeCell<[u8; STACK_BYTES]>);
// SAFETY: one thread.
unsafe impl Sync for Stack {}
static STACK: Stack = Stack(UnsafeCell::new([0; STACK_BYTES]));
static mut HEAP_MEM: [u8; HEAP_BYTES] = [0; HEAP_BYTES];

global_asm!(
    ".section .text.init,\"ax\"",
    ".globl _start",
    "_start:",
    "la sp, {stack}",
    "li t0, {size}",
    "add sp, sp, t0",
    "call {main}",
    stack = sym STACK,
    size = const STACK_BYTES,
    main = sym rust_main,
);

struct Counting {
    heap: linked_list_allocator::LockedHeap,
    live: AtomicUsize,
    peak: AtomicUsize,
}

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        let p = unsafe { self.heap.alloc(l) };
        if !p.is_null() {
            let now = self.live.fetch_add(l.size(), Relaxed) + l.size();
            self.peak.fetch_max(now, Relaxed);
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        self.live.fetch_sub(l.size(), Relaxed);
        unsafe { self.heap.dealloc(p, l) }
    }
}

#[global_allocator]
static ALLOC: Counting = Counting {
    heap: linked_list_allocator::LockedHeap::empty(),
    live: AtomicUsize::new(0),
    peak: AtomicUsize::new(0),
};

static RNG: AtomicUsize = AtomicUsize::new(0x2545_F491);

/// getrandom's custom backend: a repeatable, insecure stream for the checks.
///
/// # Safety
/// `dest` points to `len` writable bytes, as getrandom promises.
#[unsafe(no_mangle)]
unsafe extern "Rust" fn __getrandom_v03_custom(
    dest: *mut u8,
    len: usize,
) -> Result<(), getrandom::Error> {
    for i in 0..len {
        let mut x = RNG.load(Relaxed);
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        RNG.store(x, Relaxed);
        unsafe { dest.add(i).write(x as u8) };
    }
    Ok(())
}

fn syscall(n: usize, a0: usize, a1: usize, a2: usize) -> usize {
    let r;
    unsafe {
        asm!("ecall", in("a7") n, inlateout("a0") a0 => r, in("a1") a1, in("a2") a2);
    }
    r
}

fn print(s: &str) {
    syscall(64, 1, s.as_ptr() as usize, s.len());
}

fn exit(code: usize) -> ! {
    syscall(93, code, 0, 0);
    loop {}
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    print(&format!("RIND-KAT v1 panic {info}\n"));
    exit(2)
}

fn sp() -> usize {
    let s;
    unsafe { asm!("mv {}, sp", out(reg) s) };
    s
}

extern "C" fn rust_main() -> ! {
    // SAFETY: the arena is used only by the allocator.
    unsafe {
        let p = core::ptr::addr_of_mut!(HEAP_MEM) as *mut u8;
        ALLOC.heap.lock().init(p, HEAP_BYTES);
    }
    let lo = STACK.0.get() as usize;
    let mut failed = 0;
    print("RIND-KAT v1 target=riscv32imac emulator=qemu-user\n");
    for kat in rind_esp32c6::all() {
        // Paint everything below this frame, run, find the lowest dirty byte.
        // `origin` is the caller's true sp: depth is measured from it. The
        // painted region stops `GUARD` bytes lower, because the painting call
        // itself needs stack. A run that dirties nothing painted therefore
        // reports `GUARD`, an upper bound for it, and never less than the
        // truth.
        let origin = sp();
        let here = origin - GUARD;
        unsafe { core::ptr::write_bytes(lo as *mut u8, PAINT, here - lo) };
        ALLOC.peak.store(ALLOC.live.load(Relaxed), Relaxed);
        let base = ALLOC.live.load(Relaxed);
        let ok = (kat.run)();
        let used = {
            let mut i = lo;
            while i < here && unsafe { *(i as *const u8) } == PAINT {
                i += 1;
            }
            origin - i
        };
        let heap = ALLOC.peak.load(Relaxed) - base;
        if !ok {
            failed += 1;
        }
        print(&format!(
            "RIND-KAT v1 {} {} stack={} heap_peak={}\n",
            kat.name,
            if ok { "ok" } else { "FAIL" },
            used,
            heap
        ));
    }
    print(&format!("RIND-KAT v1 done failed={failed}\n"));
    exit(failed)
}
