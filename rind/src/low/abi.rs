// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Calls an assembly routine through a trampoline that loads canaries into
//! the registers its ABI says it must preserve, and panics naming each one
//! that comes back changed, the stack pointer if it moved, and on x86_64 the
//! direction flag if it is left set. BoringSSL's `abi_test` is the model.
//!
//! Every assembly routine gets one [`call!`] in a test beside it, and
//! `every_routine_has_a_harness_call` fails on one that has none.
//!
//! The trampoline keeps what it needs after the call in a static rather than
//! on the stack or in a register, so a routine that breaks either is still
//! reported; a lock serializes the tests that share it.
//!
//! A Rust-ABI wrapper is called as C would call a function taking the same
//! words: rustc passes each pointer, reference, and integer in one register
//! or stack slot, and each slice as its pointer and length in two. An
//! argument rustc passed differently would reach the routine wrong and fail
//! its test, and `rust_abi_arguments_arrive` checks this directly.

use core::cell::UnsafeCell;
use core::mem::offset_of;
use std::sync::{Mutex, PoisonError};

type Word = usize;

/// More words than any routine takes. x86_64 passes those past its argument
/// registers on the stack; aarch64 and armv7 routines need none there.
const MAX_WORDS: usize = 20;

/// The words of a call's arguments, in order.
pub(crate) struct Words {
    words: [Word; MAX_WORDS],
    len: usize,
}

impl Words {
    fn push(&mut self, word: Word) {
        assert!(self.len < MAX_WORDS, "more than {MAX_WORDS} argument words");
        self.words[self.len] = word;
        self.len += 1;
    }
}

/// An argument the trampoline can pass.
pub(crate) trait Arg {
    /// Appends the words this argument is passed in.
    fn pass(self, words: &mut Words);
}

impl<T> Arg for &T {
    fn pass(self, words: &mut Words) {
        words.push(core::ptr::from_ref(self).expose_provenance());
    }
}

impl<T> Arg for &mut T {
    fn pass(self, words: &mut Words) {
        words.push(core::ptr::from_mut(self).expose_provenance());
    }
}

impl<T> Arg for &[T] {
    fn pass(self, words: &mut Words) {
        words.push(self.as_ptr().expose_provenance());
        words.push(self.len());
    }
}

impl<T> Arg for &mut [T] {
    fn pass(self, words: &mut Words) {
        words.push(self.as_mut_ptr().expose_provenance());
        words.push(self.len());
    }
}

impl<T> Arg for *const T {
    fn pass(self, words: &mut Words) {
        words.push(self.expose_provenance());
    }
}

impl<T> Arg for *mut T {
    fn pass(self, words: &mut Words) {
        words.push(self.expose_provenance());
    }
}

impl Arg for usize {
    fn pass(self, words: &mut Words) {
        words.push(self);
    }
}

macro_rules! narrow_args {
    ($($ty:ty)*) => {$(
        impl Arg for $ty {
            fn pass(self, words: &mut Words) {
                words.push(self as Word);
            }
        }
    )*};
}

narrow_args!(bool u8 u32 i32);

/// Eight bytes, which the Rust ABI passes in one register, as an integer.
impl Arg for [u8; 8] {
    fn pass(self, words: &mut Words) {
        words.push(u64::from_ne_bytes(self) as Word);
    }
}

/// A CPU feature token, which is zero-sized, so the Rust ABI passes nothing.
#[cfg(target_arch = "x86_64")]
impl Arg for crate::low::x86_64::cpu::HaveSha256 {
    fn pass(self, _: &mut Words) {}
}

#[cfg(target_pointer_width = "64")]
narrow_args!(u64);

/// A return value the trampoline can hand back.
pub(crate) trait Ret {
    /// Calls the routine through `call` with `words`, its arguments, and
    /// returns what it returned.
    fn returned(words: Words, call: impl FnOnce(&Words) -> Word) -> Self;
}

/// A return value the routine leaves in the return register.
trait InRegister {
    /// The value a routine returning `Self` leaves in the return register.
    fn from_word(word: Word) -> Self;
}

impl<T: InRegister> Ret for T {
    fn returned(words: Words, call: impl FnOnce(&Words) -> Word) -> Self {
        T::from_word(call(&words))
    }
}

/// A SHA-256 digest, which the Rust ABI returns through a hidden pointer
/// passed before the arguments.
#[cfg(target_arch = "x86_64")]
impl Ret for [u8; 32] {
    fn returned(words: Words, call: impl FnOnce(&Words) -> Word) -> Self {
        let mut out = [0; 32];
        let mut all = Words {
            words: [0; MAX_WORDS],
            len: 0,
        };
        all.push(out.as_mut_ptr().expose_provenance());
        for &word in &words.words[..words.len] {
            all.push(word);
        }
        call(&all);
        out
    }
}

impl InRegister for () {
    fn from_word(_: Word) -> Self {}
}

impl InRegister for bool {
    fn from_word(word: Word) -> Self {
        word as u8 != 0
    }
}

impl InRegister for usize {
    fn from_word(word: Word) -> Self {
        word
    }
}

macro_rules! narrow_rets {
    ($($ty:ty)*) => {$(
        impl InRegister for $ty {
            fn from_word(word: Word) -> Self {
                word as Self
            }
        }
    )*};
}

narrow_rets!(u8 u32 i32);

#[cfg(target_pointer_width = "64")]
narrow_rets!(u64);

/// A function pointer the trampoline can call.
pub(crate) trait Routine: Copy {
    /// Its parameters.
    type Args;
    /// `fn(Self's parameters) -> Self::Args`, through which `call!` passes
    /// its arguments so they coerce as in a direct call.
    type Params;
    /// What it returns.
    type Output;

    /// Returns `Self::Params`.
    fn params(self) -> Self::Params;

    /// Calls the routine, named `name` in a failure, with `args`.
    ///
    /// # Safety
    ///
    /// Calling the routine with `args` must be sound.
    unsafe fn call(self, name: &str, args: Self::Args) -> Self::Output;
}

macro_rules! routine {
    ($conv:expr, $fty:ty; $($ty:ident $arg:ident)*) => {
        impl<$($ty: Arg,)* R: Ret> Routine for $fty {
            type Args = ($($ty,)*);
            type Params = fn($($ty),*) -> ($($ty,)*);
            type Output = R;

            fn params(self) -> Self::Params {
                |$($arg),*| ($($arg,)*)
            }

            unsafe fn call(self, name: &str, ($($arg,)*): Self::Args) -> R {
                let mut _words = Words { words: [0; MAX_WORDS], len: 0 };
                $($arg.pass(&mut _words);)*
                R::returned(_words, |words| run($conv, self as Word, words, name))
            }
        }
    };
}

macro_rules! routines {
    ($($ty:ident $arg:ident)*) => {
        routine!(NATIVE, fn($($ty),*) -> R; $($ty $arg)*);
        routine!(NATIVE, unsafe fn($($ty),*) -> R; $($ty $arg)*);
        routine!(NATIVE, unsafe extern "C" fn($($ty),*) -> R; $($ty $arg)*);
        #[cfg(target_arch = "x86_64")]
        routine!(Convention::SysV, unsafe extern "sysv64" fn($($ty),*) -> R; $($ty $arg)*);
        #[cfg(target_arch = "x86_64")]
        routine!(Convention::Win64, unsafe extern "win64" fn($($ty),*) -> R; $($ty $arg)*);
    };
}

routines!();
routines!(A a);
routines!(A a B b);
routines!(A a B b C c);
routines!(A a B b C c D d);
routines!(A a B b C c D d E e);
routines!(A a B b C c D d E e F f);
routines!(A a B b C c D d E e F f G g);
routines!(A a B b C c D d E e F f G g H h);
routines!(A a B b C c D d E e F f G g H h I i);
routines!(A a B b C c D d E e F f G g H h I i J j);
routines!(A a B b C c D d E e F f G g H h I i J j K k);
routines!(A a B b C c D d E e F f G g H h I i J j K k L l);
routines!(A a B b C c D d E e F f G g H h I i J j K k L l M m);
routines!(A a B b C c D d E e F f G g H h I i J j K k L l M m N n);
routines!(A a B b C c D d E e F f G g H h I i J j K k L l M m N n O o);
routines!(A a B b C c D d E e F f G g H h I i J j K k L l M m N n O o P p);
routines!(A a B b C c D d E e F f G g H h I i J j K k L l M m N n O o P p Q q);

/// Calls `f` with the arguments after it through the trampoline, and panics
/// if it breaks its ABI. Prefix `unsafe` for an `unsafe fn` or one with
/// `#[target_feature]`, and `unsafe extern "C"` and the like for those.
macro_rules! call {
    (unsafe extern $abi:tt $f:expr $(, $arg:expr)* $(,)?) => {
        $crate::low::abi::call!(@call
            unsafe extern $abi fn($($crate::low::abi::hole!($arg)),*) -> _, $f $(, $arg)*)
    };
    (unsafe $f:expr $(, $arg:expr)* $(,)?) => {
        $crate::low::abi::call!(@call unsafe fn($($crate::low::abi::hole!($arg)),*) -> _, $f $(, $arg)*)
    };
    (@call $fty:ty, $f:expr $(, $arg:expr)*) => {{
        // `asm_call!` passes a function pointer field in parentheses.
        #[allow(unused_parens)]
        let f: $fty = $f;
        $crate::low::abi::Routine::call(
            f,
            stringify!($f),
            $crate::low::abi::Routine::params(f)($($arg),*),
        )
    }};
    ($f:expr $(, $arg:expr)* $(,)?) => {{
        let f: fn($($crate::low::abi::hole!($arg)),*) -> _ = $f;
        // SAFETY: `$f` is a safe function, and these are its arguments.
        unsafe {
            $crate::low::abi::Routine::call(
                f,
                stringify!($f),
                $crate::low::abi::Routine::params(f)($($arg),*),
            )
        }
    }};
}

macro_rules! hole {
    ($arg:expr) => {
        _
    };
}

pub(crate) use {call, hole};

/// A harness call's argument, aligned as a routine loading whole vectors
/// from it may need.
#[cfg(any(target_arch = "x86_64", target_arch = "aarch64"))]
#[repr(C, align(64))]
pub(crate) struct Aligned<T>(pub(crate) T);

/// A value of all zero bits, for a harness call's vector arguments.
#[cfg(target_arch = "aarch64")]
pub(crate) fn zeroed<T: Plain>() -> T {
    // SAFETY: all zero bits is a valid `T`, as `Plain` promises.
    unsafe { core::mem::zeroed() }
}

/// # Safety
///
/// All zero bits must be a valid value of the type.
#[cfg(target_arch = "aarch64")]
pub(crate) unsafe trait Plain {}

// SAFETY: vector registers hold any bits.
#[cfg(target_arch = "aarch64")]
unsafe impl Plain for core::arch::aarch64::uint8x16_t {}
// SAFETY: vector registers hold any bits.
#[cfg(target_arch = "aarch64")]
unsafe impl Plain for core::arch::aarch64::uint64x2_t {}

static LOCK: Mutex<()> = Mutex::new(());

struct Shared(UnsafeCell<State>);

// SAFETY: `LOCK` serializes every access.
unsafe impl Sync for Shared {}

static STATE: Shared = Shared(UnsafeCell::new(State::CANARIES));

fn run(conv: Convention, f: Word, words: &Words, name: &str) -> Word {
    let (ret, after) = {
        let _held = LOCK.lock().unwrap_or_else(PoisonError::into_inner);
        // SAFETY: `_held` gives this thread sole use of `STATE`, which the
        // trampoline reads and writes; `f` is a routine taking `words`, and
        // `words.words` holds at least as many as the trampoline reads.
        unsafe {
            STATE.0.get().write(State::canaries());
            let ret = trampoline(conv)(f, words.words.as_ptr(), words.len);
            (ret, STATE.0.get().read())
        }
    };

    let mut broken = State::canaries().changed(&after, conv);
    if after.sp_after != after.sp_before {
        broken.push(format!(
            "the stack pointer: {:#x} before, {:#x} after",
            after.sp_before, after.sp_after
        ));
    }
    assert!(
        broken.is_empty(),
        "{name} broke its ABI: {}",
        broken.join("; ")
    );
    ret
}

/// One canary per register, distinct from each other and from values a
/// routine would leave by accident.
const fn canary(i: usize) -> u64 {
    0x5a5a_0000_0000_a5a5 ^ (i as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

fn compare(broken: &mut Vec<String>, names: &[&str], canaries: &[u64], after: &[u64]) {
    for ((name, canary), after) in names.iter().zip(canaries).zip(after) {
        if canary != after {
            broken.push(format!("{name}: canary {canary:#x}, got {after:#x}"));
        }
    }
}

#[derive(Clone, Copy)]
enum Convention {
    #[cfg(target_arch = "x86_64")]
    SysV,
    #[cfg(target_arch = "x86_64")]
    Win64,
    #[cfg(not(target_arch = "x86_64"))]
    C,
}

/// Rust's ABI and `extern "C"` on this target.
#[cfg(all(target_arch = "x86_64", windows))]
const NATIVE: Convention = Convention::Win64;
#[cfg(all(target_arch = "x86_64", not(windows)))]
const NATIVE: Convention = Convention::SysV;
#[cfg(not(target_arch = "x86_64"))]
const NATIVE: Convention = Convention::C;

use arch::{State, trampoline};

#[cfg(target_arch = "x86_64")]
mod arch {
    use super::{Convention, STATE, Word, canary, compare, offset_of};

    #[repr(C)]
    #[derive(Clone, Copy)]
    pub(super) struct State {
        /// rbx, rbp, r12-r15, then rdi and rsi, which only Windows preserves.
        gpr: [u64; 8],
        /// The halves of xmm6-xmm15, which only Windows preserves.
        xmm: [u64; 20],
        frame: u64,
        pub(super) sp_before: u64,
        pub(super) sp_after: u64,
        flags: u64,
    }

    const GPR: [&str; 8] = ["rbx", "rbp", "r12", "r13", "r14", "r15", "rdi", "rsi"];
    const XMM: [&str; 20] = [
        "xmm6 low",
        "xmm6 high",
        "xmm7 low",
        "xmm7 high",
        "xmm8 low",
        "xmm8 high",
        "xmm9 low",
        "xmm9 high",
        "xmm10 low",
        "xmm10 high",
        "xmm11 low",
        "xmm11 high",
        "xmm12 low",
        "xmm12 high",
        "xmm13 low",
        "xmm13 high",
        "xmm14 low",
        "xmm14 high",
        "xmm15 low",
        "xmm15 high",
    ];
    const DIRECTION_FLAG: u64 = 1 << 10;

    impl State {
        pub(super) fn canaries() -> Self {
            Self::CANARIES
        }

        pub(super) const CANARIES: Self = {
            let mut s = Self {
                gpr: [0; 8],
                xmm: [0; 20],
                frame: 0,
                sp_before: 0,
                sp_after: 0,
                flags: 0,
            };
            let mut i = 0;
            while i < 8 {
                s.gpr[i] = canary(i);
                i += 1;
            }
            while i < 28 {
                s.xmm[i - 8] = canary(i);
                i += 1;
            }
            s
        };

        pub(super) fn changed(&self, after: &Self, conv: Convention) -> Vec<String> {
            let mut broken = Vec::new();
            match conv {
                Convention::SysV => compare(&mut broken, &GPR[..6], &self.gpr, &after.gpr),
                Convention::Win64 => {
                    compare(&mut broken, &GPR, &self.gpr, &after.gpr);
                    compare(&mut broken, &XMM, &self.xmm, &after.xmm);
                }
            }
            // `pushfq` mixes the direction flag with arithmetic flags the
            // routine may have computed from secrets, so memcheck taints the
            // whole word; only the direction flag is checked, and it is public.
            if crate::low::ct::into_public(after.flags) & DIRECTION_FLAG != 0 {
                broken.push("the direction flag: left set".into());
            }
            broken
        }
    }

    /// The trampolines' own convention is the same on every OS, unlike
    /// `extern "C"`, which on Windows also preserves what they canary.
    pub(super) type Trampoline = unsafe extern "sysv64" fn(Word, *const Word, Word) -> Word;

    pub(super) fn trampoline(conv: Convention) -> Trampoline {
        match conv {
            Convention::SysV => sysv,
            Convention::Win64 => win64,
        }
    }

    // Both save what their own convention preserves, record the stack
    // pointer, copy the arguments past the registers onto the stack, load
    // the arguments and canaries, call, record the registers and stack
    // pointer, restore the stack pointer from `STATE`, record and clear the
    // flags, and return what the routine did.

    #[unsafe(naked)]
    unsafe extern "sysv64" fn sysv(f: Word, args: *const Word, len: Word) -> Word {
        core::arch::naked_asm!(
            "push rbp",
            "push rbx",
            "push r12",
            "push r13",
            "push r14",
            "push r15",
            "sub rsp, 8",
            "mov [rip + {state} + {frame}], rsp",
            "mov r10, rdi",
            "mov r11, rsi",
            "sub rdx, 6",
            "jbe 2f",
            "lea rax, [rdx * 8 + 15]",
            "and rax, -16",
            "sub rsp, rax",
            "xor eax, eax",
            "3:",
            "mov rcx, [r11 + rax * 8 + 48]",
            "mov [rsp + rax * 8], rcx",
            "inc rax",
            "cmp rax, rdx",
            "jb 3b",
            "2:",
            "mov [rip + {state} + {sp_before}], rsp",
            "mov rdi, [r11]",
            "mov rsi, [r11 + 8]",
            "mov rdx, [r11 + 16]",
            "mov rcx, [r11 + 24]",
            "mov r8, [r11 + 32]",
            "mov r9, [r11 + 40]",
            "mov rbx, [rip + {state} + {gpr}]",
            "mov rbp, [rip + {state} + {gpr} + 8]",
            "mov r12, [rip + {state} + {gpr} + 16]",
            "mov r13, [rip + {state} + {gpr} + 24]",
            "mov r14, [rip + {state} + {gpr} + 32]",
            "mov r15, [rip + {state} + {gpr} + 40]",
            "call r10",
            "mov [rip + {state} + {gpr}], rbx",
            "mov [rip + {state} + {gpr} + 8], rbp",
            "mov [rip + {state} + {gpr} + 16], r12",
            "mov [rip + {state} + {gpr} + 24], r13",
            "mov [rip + {state} + {gpr} + 32], r14",
            "mov [rip + {state} + {gpr} + 40], r15",
            "mov [rip + {state} + {sp_after}], rsp",
            "mov rsp, [rip + {state} + {frame}]",
            "pushfq",
            "pop rcx",
            "mov [rip + {state} + {flags}], rcx",
            "cld",
            "add rsp, 8",
            "pop r15",
            "pop r14",
            "pop r13",
            "pop r12",
            "pop rbx",
            "pop rbp",
            "ret",
            state = sym STATE,
            gpr = const offset_of!(State, gpr),
            frame = const offset_of!(State, frame),
            sp_before = const offset_of!(State, sp_before),
            sp_after = const offset_of!(State, sp_after),
            flags = const offset_of!(State, flags),
        )
    }

    #[unsafe(naked)]
    unsafe extern "sysv64" fn win64(f: Word, args: *const Word, len: Word) -> Word {
        core::arch::naked_asm!(
            "push rbp",
            "push rbx",
            "push r12",
            "push r13",
            "push r14",
            "push r15",
            "sub rsp, 8",
            "mov [rip + {state} + {frame}], rsp",
            "mov r10, rdi",
            "mov r11, rsi",
            // Four registers, then 32 bytes of shadow space before the rest.
            "xor ecx, ecx",
            "sub rdx, 4",
            "cmovbe rdx, rcx",
            "lea rax, [rdx * 8 + 32 + 15]",
            "and rax, -16",
            "sub rsp, rax",
            "xor eax, eax",
            "test rdx, rdx",
            "jz 2f",
            "3:",
            "mov rcx, [r11 + rax * 8 + 32]",
            "mov [rsp + rax * 8 + 32], rcx",
            "inc rax",
            "cmp rax, rdx",
            "jb 3b",
            "2:",
            "mov [rip + {state} + {sp_before}], rsp",
            "mov rcx, [r11]",
            "mov rdx, [r11 + 8]",
            "mov r8, [r11 + 16]",
            "mov r9, [r11 + 24]",
            "mov rbx, [rip + {state} + {gpr}]",
            "mov rbp, [rip + {state} + {gpr} + 8]",
            "mov r12, [rip + {state} + {gpr} + 16]",
            "mov r13, [rip + {state} + {gpr} + 24]",
            "mov r14, [rip + {state} + {gpr} + 32]",
            "mov r15, [rip + {state} + {gpr} + 40]",
            "mov rdi, [rip + {state} + {gpr} + 48]",
            "mov rsi, [rip + {state} + {gpr} + 56]",
            "movdqu xmm6, [rip + {state} + {xmm}]",
            "movdqu xmm7, [rip + {state} + {xmm} + 16]",
            "movdqu xmm8, [rip + {state} + {xmm} + 32]",
            "movdqu xmm9, [rip + {state} + {xmm} + 48]",
            "movdqu xmm10, [rip + {state} + {xmm} + 64]",
            "movdqu xmm11, [rip + {state} + {xmm} + 80]",
            "movdqu xmm12, [rip + {state} + {xmm} + 96]",
            "movdqu xmm13, [rip + {state} + {xmm} + 112]",
            "movdqu xmm14, [rip + {state} + {xmm} + 128]",
            "movdqu xmm15, [rip + {state} + {xmm} + 144]",
            "call r10",
            "mov [rip + {state} + {gpr}], rbx",
            "mov [rip + {state} + {gpr} + 8], rbp",
            "mov [rip + {state} + {gpr} + 16], r12",
            "mov [rip + {state} + {gpr} + 24], r13",
            "mov [rip + {state} + {gpr} + 32], r14",
            "mov [rip + {state} + {gpr} + 40], r15",
            "mov [rip + {state} + {gpr} + 48], rdi",
            "mov [rip + {state} + {gpr} + 56], rsi",
            "movdqu [rip + {state} + {xmm}], xmm6",
            "movdqu [rip + {state} + {xmm} + 16], xmm7",
            "movdqu [rip + {state} + {xmm} + 32], xmm8",
            "movdqu [rip + {state} + {xmm} + 48], xmm9",
            "movdqu [rip + {state} + {xmm} + 64], xmm10",
            "movdqu [rip + {state} + {xmm} + 80], xmm11",
            "movdqu [rip + {state} + {xmm} + 96], xmm12",
            "movdqu [rip + {state} + {xmm} + 112], xmm13",
            "movdqu [rip + {state} + {xmm} + 128], xmm14",
            "movdqu [rip + {state} + {xmm} + 144], xmm15",
            "mov [rip + {state} + {sp_after}], rsp",
            "mov rsp, [rip + {state} + {frame}]",
            "pushfq",
            "pop rcx",
            "mov [rip + {state} + {flags}], rcx",
            "cld",
            "add rsp, 8",
            "pop r15",
            "pop r14",
            "pop r13",
            "pop r12",
            "pop rbx",
            "pop rbp",
            "ret",
            state = sym STATE,
            gpr = const offset_of!(State, gpr),
            xmm = const offset_of!(State, xmm),
            frame = const offset_of!(State, frame),
            sp_before = const offset_of!(State, sp_before),
            sp_after = const offset_of!(State, sp_after),
            flags = const offset_of!(State, flags),
        )
    }
}

#[cfg(target_arch = "aarch64")]
mod arch {
    use super::{Convention, STATE, Word, canary, compare, offset_of};

    #[repr(C)]
    #[derive(Clone, Copy)]
    pub(super) struct State {
        /// x19-x29.
        x: [u64; 11],
        /// Which Linux lets a routine use but Apple, Windows, and Android
        /// reserve, so rind's routines must leave it alone everywhere.
        x18: u64,
        /// The low halves of v8-v15, which are all the ABI preserves.
        d: [u64; 8],
        frame: u64,
        pub(super) sp_before: u64,
        pub(super) sp_after: u64,
    }

    const X: [&str; 11] = [
        "x19", "x20", "x21", "x22", "x23", "x24", "x25", "x26", "x27", "x28", "x29",
    ];
    const D: [&str; 8] = ["d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"];

    impl State {
        pub(super) fn canaries() -> Self {
            Self::CANARIES
        }

        pub(super) const CANARIES: Self = {
            let mut s = Self {
                x: [0; 11],
                x18: canary(11),
                d: [0; 8],
                frame: 0,
                sp_before: 0,
                sp_after: 0,
            };
            let mut i = 0;
            while i < 11 {
                s.x[i] = canary(i);
                i += 1;
            }
            let mut i = 0;
            while i < 8 {
                s.d[i] = canary(12 + i);
                i += 1;
            }
            s
        };

        pub(super) fn changed(&self, after: &Self, _: Convention) -> Vec<String> {
            let mut broken = Vec::new();
            compare(&mut broken, &X, &self.x, &after.x);
            if X18_CANARY {
                compare(&mut broken, &["x18"], &[self.x18], &[after.x18]);
            }
            compare(&mut broken, &D, &self.d, &after.d);
            broken
        }
    }

    /// Only Linux lets the trampoline write x18; elsewhere it holds the
    /// thread's TEB, the shadow call stack, or what the kernel puts there.
    const X18_CANARY: bool = cfg!(target_os = "linux");

    pub(super) type Trampoline = unsafe extern "C" fn(Word, *const Word, Word) -> Word;

    pub(super) fn trampoline(_: Convention) -> Trampoline {
        c
    }

    #[cfg(target_vendor = "apple")]
    macro_rules! state_address {
        () => {
            "adrp x16, {state}@PAGE\nadd x16, x16, {state}@PAGEOFF"
        };
    }

    #[cfg(not(target_vendor = "apple"))]
    macro_rules! state_address {
        () => {
            "adrp x16, {state}\nadd x16, x16, :lo12:{state}"
        };
    }

    #[cfg(target_os = "linux")]
    macro_rules! x18 {
        ($($line:literal)*) => { concat!($($line, "\n"),*) };
    }

    #[cfg(not(target_os = "linux"))]
    macro_rules! x18 {
        ($($line:literal)*) => {
            ""
        };
    }

    // Saves what the ABI preserves, records the stack pointer, loads the
    // arguments, which all fit in registers, and the canaries, calls,
    // records the registers and stack pointer, restores the stack pointer
    // from `STATE`, and returns what the routine did.
    #[unsafe(naked)]
    unsafe extern "C" fn c(f: Word, args: *const Word, len: Word) -> Word {
        core::arch::naked_asm!(
            "cmp x2, #8",
            "b.hi 9f",
            "stp x29, x30, [sp, #-176]!",
            "mov x29, sp",
            "stp x19, x20, [sp, #16]",
            "stp x21, x22, [sp, #32]",
            "stp x23, x24, [sp, #48]",
            "stp x25, x26, [sp, #64]",
            "stp x27, x28, [sp, #80]",
            "stp d8, d9, [sp, #96]",
            "stp d10, d11, [sp, #112]",
            "stp d12, d13, [sp, #128]",
            "stp d14, d15, [sp, #144]",
            x18!("str x18, [sp, #160]"),
            state_address!(),
            "mov x9, sp",
            "str x9, [x16, #{frame}]",
            "str x9, [x16, #{sp_before}]",
            "mov x10, x0",
            "mov x11, x1",
            "ldp x19, x20, [x16, #({x} + 0)]",
            "ldp x21, x22, [x16, #({x} + 16)]",
            "ldp x23, x24, [x16, #({x} + 32)]",
            "ldp x25, x26, [x16, #({x} + 48)]",
            "ldp x27, x28, [x16, #({x} + 64)]",
            "ldr x29, [x16, #({x} + 80)]",
            "ldp d8, d9, [x16, #({d} + 0)]",
            "ldp d10, d11, [x16, #({d} + 16)]",
            "ldp d12, d13, [x16, #({d} + 32)]",
            "ldp d14, d15, [x16, #({d} + 48)]",
            x18!("ldr x18, [x16, #{x18}]"),
            "ldp x0, x1, [x11]",
            "ldp x2, x3, [x11, #16]",
            "ldp x4, x5, [x11, #32]",
            "ldp x6, x7, [x11, #48]",
            "blr x10",
            state_address!(),
            "stp x19, x20, [x16, #({x} + 0)]",
            "stp x21, x22, [x16, #({x} + 16)]",
            "stp x23, x24, [x16, #({x} + 32)]",
            "stp x25, x26, [x16, #({x} + 48)]",
            "stp x27, x28, [x16, #({x} + 64)]",
            "str x29, [x16, #({x} + 80)]",
            "stp d8, d9, [x16, #({d} + 0)]",
            "stp d10, d11, [x16, #({d} + 16)]",
            "stp d12, d13, [x16, #({d} + 32)]",
            "stp d14, d15, [x16, #({d} + 48)]",
            "str x18, [x16, #{x18}]",
            "mov x9, sp",
            "str x9, [x16, #{sp_after}]",
            "ldr x9, [x16, #{frame}]",
            "mov sp, x9",
            x18!("ldr x18, [sp, #160]"),
            "ldp d14, d15, [sp, #144]",
            "ldp d12, d13, [sp, #128]",
            "ldp d10, d11, [sp, #112]",
            "ldp d8, d9, [sp, #96]",
            "ldp x27, x28, [sp, #80]",
            "ldp x25, x26, [sp, #64]",
            "ldp x23, x24, [sp, #48]",
            "ldp x21, x22, [sp, #32]",
            "ldp x19, x20, [sp, #16]",
            "ldp x29, x30, [sp], #176",
            "ret",
            // More than eight words would go on the stack, which no routine
            // needs and Apple lays out differently.
            "9:",
            "brk #1",
            state = sym STATE,
            x = const offset_of!(State, x),
            x18 = const offset_of!(State, x18),
            d = const offset_of!(State, d),
            frame = const offset_of!(State, frame),
            sp_before = const offset_of!(State, sp_before),
            sp_after = const offset_of!(State, sp_after),
        )
    }
}

#[cfg(target_arch = "arm")]
mod arch {
    use super::{Convention, STATE, Word, canary, compare, offset_of};
    use crate::low::arm::cpu::HaveNeon;

    #[repr(C)]
    #[derive(Clone, Copy)]
    pub(super) struct State {
        /// r4-r11.
        r: [u32; 8],
        /// d8-d15, checked only when `vfp` is set.
        d: [u64; 8],
        /// Whether the CPU has NEON. Only NEON routines write d8-d15, and an
        /// ARMv7 core may have no VFP registers at all, so the trampoline
        /// touches them only when this is set.
        vfp: u32,
        frame: u32,
        pub(super) sp_before: u32,
        pub(super) sp_after: u32,
    }

    // `ldm` and `stm` take the registers from `STATE` itself.
    const _: () = assert!(offset_of!(State, r) == 0);

    const R: [&str; 8] = ["r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11"];
    const D: [&str; 8] = ["d8", "d9", "d10", "d11", "d12", "d13", "d14", "d15"];

    impl State {
        pub(super) const CANARIES: Self = {
            let mut s = Self {
                r: [0; 8],
                d: [0; 8],
                vfp: 0,
                frame: 0,
                sp_before: 0,
                sp_after: 0,
            };
            let mut i = 0;
            while i < 8 {
                s.r[i] = canary(i) as u32;
                s.d[i] = canary(8 + i);
                i += 1;
            }
            s
        };

        pub(super) fn canaries() -> Self {
            Self {
                vfp: u32::from(HaveNeon::check().is_some()),
                ..Self::CANARIES
            }
        }

        pub(super) fn changed(&self, after: &Self, _: Convention) -> Vec<String> {
            let mut broken = Vec::new();
            let widen = |r: [u32; 8]| r.map(u64::from);
            compare(&mut broken, &R, &widen(self.r), &widen(after.r));
            if self.vfp != 0 {
                compare(&mut broken, &D, &self.d, &after.d);
            }
            broken
        }
    }

    pub(super) type Trampoline = unsafe extern "C" fn(Word, *const Word, Word) -> Word;

    pub(super) fn trampoline(_: Convention) -> Trampoline {
        c
    }

    // Saves what the ABI preserves, records the stack pointer, copies the
    // arguments past r0-r3 onto the stack, loads the arguments and canaries,
    // calls, records the registers and stack pointer, restores the stack
    // pointer from `STATE`, and returns what the routine did. It touches
    // d8-d15 only when `STATE.vfp` is set, and `.fpu vfpv3` lets it name them
    // on a soft-float target, leaving `.fpu` as `curve25519` and `sha_armv4`
    // do.
    //
    // It finds `STATE` from a literal's own address, which `adr` gives in
    // both A32 and Thumb, rather than from `pc`, which reads 8 ahead in one
    // and 4 in the other. Rustc builds this in Thumb on Android, and stable
    // rustc tells neither `cfg` nor `instruction_set` which it is.
    #[unsafe(naked)]
    unsafe extern "C" fn c(f: Word, args: *const Word, len: Word) -> Word {
        core::arch::naked_asm!(
            ".fpu vfpv3",
            "push {{r4-r11, lr}}",
            "adr r3, 5f",
            "ldr r12, [r3]",
            "add r12, r12, r3",
            "ldr r5, [r12, #{vfp}]",
            "cmp r5, #0",
            "beq 1f",
            "vpush {{d8-d15}}",
            "1:",
            "sub sp, sp, #4",
            "str sp, [r12, #{frame}]",
            "mov lr, r0",
            "mov r4, r1",
            "subs r5, r2, #4",
            "ble 2f",
            "lsl r6, r5, #2",
            "add r6, r6, #7",
            "bic r6, r6, #7",
            "sub sp, sp, r6",
            "mov r6, #0",
            "3:",
            "add r7, r6, #4",
            "ldr r7, [r4, r7, lsl #2]",
            "str r7, [sp, r6, lsl #2]",
            "add r6, r6, #1",
            "cmp r6, r5",
            "blt 3b",
            "2:",
            "str sp, [r12, #{sp_before}]",
            "ldr r0, [r4]",
            "ldr r1, [r4, #4]",
            "ldr r2, [r4, #8]",
            "ldr r3, [r4, #12]",
            "ldr r5, [r12, #{vfp}]",
            "cmp r5, #0",
            "beq 8f",
            "add r4, r12, #{d}",
            "vldm r4, {{d8-d15}}",
            "8:",
            "ldm r12, {{r4-r11}}",
            "mov r12, lr",
            "blx r12",
            "adr r3, 6f",
            "ldr r12, [r3]",
            "add r12, r12, r3",
            "stm r12, {{r4-r11}}",
            "str sp, [r12, #{sp_after}]",
            "ldr r2, [r12, #{vfp}]",
            "cmp r2, #0",
            "beq 9f",
            "add r3, r12, #{d}",
            "vstm r3, {{d8-d15}}",
            "9:",
            "ldr r3, [r12, #{frame}]",
            "mov sp, r3",
            "add sp, sp, #4",
            "cmp r2, #0",
            "beq 10f",
            "vpop {{d8-d15}}",
            "10:",
            "pop {{r4-r11, pc}}",
            ".p2align 2",
            "5: .word {state} - 5b",
            "6: .word {state} - 6b",
            state = sym STATE,
            d = const offset_of!(State, d),
            vfp = const offset_of!(State, vfp),
            frame = const offset_of!(State, frame),
            sp_before = const offset_of!(State, sp_before),
            sp_after = const offset_of!(State, sp_after),
        )
    }
}

#[cfg(test)]
mod tests {

    /// Runs `f` and returns its panic message, failing if it did not panic.
    fn broken(f: impl FnOnce() + core::panic::UnwindSafe) -> String {
        let payload = std::panic::catch_unwind(f).expect_err("no ABI break reported");
        payload
            .downcast_ref::<String>()
            .cloned()
            .unwrap_or_default()
    }

    #[allow(clippy::too_many_arguments)]
    extern "C" fn c_words(
        a: usize,
        b: usize,
        c: usize,
        d: usize,
        e: usize,
        f: usize,
        g: usize,
        h: usize,
    ) -> usize {
        [a, b, c, d, e, f, g, h]
            .iter()
            .enumerate()
            .fold(0, |acc, (i, w)| acc ^ w.rotate_left(i as u32 * 7))
    }

    // Eight words, the most an aarch64 routine takes, with the last slice
    // straddling x86_64's argument registers and the stack.
    #[inline(never)]
    fn rust_words(z: &mut [usize; 2], p: usize, x: &[u32], y: &[u32], m: &[u32]) -> bool {
        z[0] = p + x.iter().chain(y).chain(m).sum::<u32>() as usize;
        z[1] = x.len() * 100 + y.len() * 10 + m.len();
        x.len() == 1
    }

    #[test]
    fn c_abi_arguments_arrive() {
        let words = [1, 2, 3, 4, 5, 6, 7, 8].map(|w: usize| w.wrapping_mul(0x0101_0101));
        let [a, b, c, d, e, f, g, h] = words;
        // SAFETY: `c_words` is safe to call.
        let called = unsafe { call!(unsafe extern "C" c_words, a, b, c, d, e, f, g, h) };
        assert_eq!(called, c_words(a, b, c, d, e, f, g, h));
    }

    #[test]
    fn rust_abi_arguments_arrive() {
        let mut z = [0; 2];
        assert!(call!(rust_words, &mut z, 1000, &[1], &[2, 3], &[4, 5, 6]));
        assert_eq!(z, [1021, 123]);
    }

    /// Routines that need no harness call of their own, with why.
    const EXEMPT: &[(&str, &str, &str)] = &[
        ("x86_64/aes_gcm_avx.rs", "gcm128_encrypt_opt", DISPATCHED),
        ("x86_64/aes_gcm_avx.rs", "gcm128_decrypt_opt", DISPATCHED),
        ("x86_64/aes_gcm_avx.rs", "gcm256_encrypt_opt", DISPATCHED),
        ("x86_64/aes_gcm_avx.rs", "gcm256_decrypt_opt", DISPATCHED),
        (
            "x86_64/rsaz_avx512.rs",
            "rsaz_amm52x20_x2_ifma256",
            DISPATCHED,
        ),
        (
            "x86_64/rsaz_avx512.rs",
            "rsaz_amm52x30_x2_ifma256",
            DISPATCHED,
        ),
        (
            "x86_64/rsaz_avx512.rs",
            "rsaz_amm52x40_x2_ifma256",
            DISPATCHED,
        ),
        (
            "x86_64/rsaz_avx512.rs",
            "extract_multiplier_2x20_win5",
            DISPATCHED,
        ),
        (
            "x86_64/rsaz_avx512.rs",
            "extract_multiplier_2x30_win5",
            DISPATCHED,
        ),
        (
            "x86_64/rsaz_avx512.rs",
            "extract_multiplier_2x40_win5",
            DISPATCHED,
        ),
        (
            "aarch64/cpu.rs",
            "reads_dit",
            "a test, whose assembly only reads DIT",
        ),
        (
            "aarch64/aes_cbc.rs",
            "hw_encrypt",
            "one `aese` on registers the compiler allocates, which no ABI governs",
        ),
        (
            "arm/ct_qemu.rs",
            "traced",
            "test-only hints, which touch no register",
        ),
    ];

    const DISPATCHED: &str = "picked into a function pointer that `asm_call!` calls";

    /// The name of each assembly routine in `text` that Rust calls: each
    /// function holding `asm!` or `naked_asm!`, directly or through a macro
    /// in `text`, and each declared in an `extern` block over `global_asm!`.
    /// An internal entry, which only other assembly reaches through a `sym`
    /// operand, is left out: its callers' harness calls cover it.
    fn routines(text: &str) -> Vec<String> {
        let mut names = Vec::new();
        for (at, _) in text.match_indices("asm!(") {
            if !text[..at].ends_with("global_") {
                let fn_at = text[..at]
                    .rfind("fn ")
                    .expect("assembly outside a function");
                names.push(ident(&text[fn_at + 3..]));
            }
        }
        for (at, _) in text.match_indices("extern \"C\" {") {
            let block = &text[at..at + text[at..].find("\n}").unwrap()];
            for (fn_at, _) in block.match_indices("fn ") {
                names.push(ident(&block[fn_at + 3..]));
            }
        }

        // Each macro holding assembly defines the routine its invocations
        // name first; one invoking such a macro, each it lists.
        let macros: Vec<(String, &str)> = text
            .match_indices("macro_rules! ")
            .map(|(at, _)| {
                let rest = &text[at + 13..];
                (ident(rest), braced(rest))
            })
            .collect();
        let mut defining: Vec<(&str, bool)> = macros
            .iter()
            .filter(|(_, body)| body.contains("asm!("))
            .map(|(name, _)| (name.as_str(), false))
            .collect();
        for (name, body) in &macros {
            if !defining.iter().any(|(d, _)| d == name)
                && defining
                    .iter()
                    .any(|(d, _)| body.contains(&format!("{d}!")))
            {
                defining.push((name, true));
            }
        }
        for (name, lists) in defining {
            for (at, _) in text.match_indices(&format!("{name}!")) {
                if text[..at].ends_with("macro_rules! ") {
                    continue;
                }
                let args = text[at + name.len() + 1..].trim_start();
                let args = args[1..].trim_start();
                if lists {
                    let list = &args[..args.find(')').unwrap()];
                    names.extend(list.split(',').map(ident));
                } else {
                    names.push(ident(args.strip_prefix("fn ").unwrap_or(args)));
                }
            }
        }

        names.retain(|name| {
            !name.is_empty()
                && !text.contains(&format!("sym {name}"))
                && !text.contains(&format!("{name} = {name}"))
        });
        names.sort();
        names.dedup();
        names
    }

    /// The name of each routine `text` passes to `call!` or `asm_call!`.
    fn harness_calls(text: &str) -> Vec<String> {
        text.match_indices("call!(")
            .map(|(at, _)| {
                let mut rest = text[at + 6..].trim_start();
                for prefix in ["unsafe ", "extern "] {
                    rest = rest.strip_prefix(prefix).unwrap_or(rest).trim_start();
                }
                if let Some(abi) = rest.strip_prefix('"') {
                    rest = abi.split_once('"').unwrap().1.trim_start();
                }
                let path = rest.split([',', '(', ')']).next().unwrap();
                let path = path.split("::<").next().unwrap();
                ident(path.rsplit("::").next().unwrap())
            })
            .collect()
    }

    // `options(nostack)` promises rustc the block leaves the stack alone, so
    // rustc may keep data below the stack pointer, in the red zone, across
    // it. The harness cannot see a block clobber that, so this fails on a
    // `nostack` block naming the stack pointer or an instruction that moves
    // it.
    #[test]
    fn nostack_blocks_leave_the_stack_alone() {
        const STACK: [&str; 11] = [
            "push", "pop", "call", "bl", "blx", "vpush", "vpop", "rsp", "esp", "sp", "wsp",
        ];
        fn visit(dir: &std::path::Path, blocks: &mut usize) {
            for entry in std::fs::read_dir(dir).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    visit(&path, blocks);
                    continue;
                }
                // This file names `asm!(` in its scans.
                if path.extension().is_none_or(|e| e != "rs") || path.ends_with("abi.rs") {
                    continue;
                }
                let text = std::fs::read_to_string(&path).unwrap();
                for (at, _) in text.match_indices("asm!(") {
                    let block = parenthesized(&text[at + 4..]);
                    if !block.contains("nostack") {
                        continue;
                    }
                    *blocks += 1;
                    let words = block.split(|c: char| !c.is_alphanumeric() && c != '_');
                    for word in words {
                        assert!(
                            !STACK.contains(&word),
                            "{}: a nostack block names {word}",
                            path.display()
                        );
                    }
                }
            }
        }

        let mut blocks = 0;
        visit(
            &std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/low"),
            &mut blocks,
        );
        assert!(blocks >= 10, "found only {blocks} nostack blocks");
    }

    /// `text` up to the parenthesis closing its first, skipping those in
    /// strings and line comments.
    fn parenthesized(text: &str) -> &str {
        let (mut depth, mut string, mut comment, mut escaped) = (0, false, false, false);
        let mut chars = text.char_indices().peekable();
        while let Some((at, c)) = chars.next() {
            if comment {
                comment = c != '\n';
            } else if string {
                string = escaped || c != '"';
                escaped = !escaped && c == '\\';
            } else {
                match c {
                    '"' => string = true,
                    '/' if chars.peek().is_some_and(|&(_, n)| n == '/') => comment = true,
                    '(' => depth += 1,
                    ')' if depth == 1 => return &text[..at],
                    ')' => depth -= 1,
                    _ => {}
                }
            }
        }
        panic!("unclosed parenthesis")
    }

    /// `text` up to the brace closing its first.
    fn braced(text: &str) -> &str {
        let mut depth = 0;
        for (at, c) in text.char_indices() {
            match c {
                '{' => depth += 1,
                '}' if depth == 1 => return &text[..at],
                '}' => depth -= 1,
                _ => {}
            }
        }
        panic!("unclosed brace")
    }

    fn ident(text: &str) -> String {
        text.trim_start()
            .chars()
            .take_while(|c| c.is_alphanumeric() || *c == '_')
            .collect()
    }

    // Scans every backend's sources, wherever it runs, so a routine added
    // for another target fails here too.
    #[test]
    fn every_routine_has_a_harness_call() {
        let low = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/low");
        let mut missing = Vec::new();
        let mut found = 0;
        for arch in ["x86_64", "aarch64", "arm"] {
            for entry in std::fs::read_dir(low.join(arch)).unwrap() {
                let path = entry.unwrap().path();
                if path.extension().is_none_or(|e| e != "rs") {
                    continue;
                }
                let file = format!("{arch}/{}", path.file_name().unwrap().to_str().unwrap());
                let text = std::fs::read_to_string(&path).unwrap();
                let calls = harness_calls(&text);
                for name in routines(&text) {
                    found += 1;
                    let exempt = EXEMPT.iter().any(|(f, n, _)| *f == file && *n == name);
                    if !exempt && !calls.contains(&name) {
                        missing.push(format!("{file}: {name}"));
                    }
                }
            }
        }
        assert!(found > 200, "found only {found} routines");
        assert!(
            missing.is_empty(),
            "no harness call:\n{}",
            missing.join("\n")
        );
    }

    #[cfg(target_arch = "x86_64")]
    mod x86_64 {
        use super::broken;

        macro_rules! planted {
            ($name:ident, $abi:tt, $($line:literal),*) => {
                #[unsafe(naked)]
                unsafe extern $abi fn $name() {
                    core::arch::naked_asm!($($line),*)
                }
            };
        }

        planted!(clean, "sysv64", "ret");
        planted!(clean_win64, "win64", "ret");
        planted!(rbx, "sysv64", "xor ebx, ebx", "ret");
        planted!(rbp, "sysv64", "inc rbp", "ret");
        planted!(r15, "sysv64", "not r15", "ret");
        planted!(sp, "sysv64", "pop rax", "add rsp, 8", "jmp rax");
        planted!(direction, "sysv64", "std", "ret");
        planted!(rdi, "win64", "xor edi, edi", "ret");
        planted!(xmm15, "win64", "pxor xmm15, xmm15", "ret");
        // What SysV lets a routine change.
        planted!(
            scratch,
            "sysv64",
            "xor edi, edi",
            "pxor xmm15, xmm15",
            "ret"
        );

        #[test]
        fn planted_clobbers_fail() {
            // SAFETY: each planted routine takes nothing and returns.
            unsafe {
                call!(unsafe extern "sysv64" clean);
                call!(unsafe extern "sysv64" scratch);
                call!(unsafe extern "win64" clean_win64);
                for (expect, message) in [
                    ("rbx", broken(|| call!(unsafe extern "sysv64" rbx))),
                    ("rbp", broken(|| call!(unsafe extern "sysv64" rbp))),
                    ("r15", broken(|| call!(unsafe extern "sysv64" r15))),
                    ("stack pointer", broken(|| call!(unsafe extern "sysv64" sp))),
                    (
                        "direction flag",
                        broken(|| call!(unsafe extern "sysv64" direction)),
                    ),
                    ("rdi", broken(|| call!(unsafe extern "win64" rdi))),
                    ("xmm15", broken(|| call!(unsafe extern "win64" xmm15))),
                ] {
                    assert!(message.contains(expect), "{expect}: {message}");
                }
            }
        }
    }

    #[cfg(target_arch = "aarch64")]
    mod aarch64 {
        use super::broken;

        macro_rules! planted {
            ($name:ident, $($line:literal),*) => {
                #[unsafe(naked)]
                unsafe extern "C" fn $name() {
                    core::arch::naked_asm!($($line),*)
                }
            };
        }

        planted!(clean, "ret");
        planted!(x19, "mov x19, xzr", "ret");
        planted!(x29, "add x29, x29, #16", "ret");
        planted!(d8, "movi d8, #0", "ret");
        // Lowered rather than raised: raising it would free the trampoline's
        // saved frame, which memcheck, with no red zone on ARM, then reports
        // undefined when the trampoline restores it.
        planted!(sp, "sub sp, sp, #16", "ret");
        // The upper half of v8 is the caller's to save.
        planted!(scratch, "mov x9, xzr", "mov v8.d[1], xzr", "ret");
        #[cfg(target_os = "linux")]
        planted!(x18, "mov x18, xzr", "ret");

        #[test]
        fn planted_clobbers_fail() {
            // SAFETY: each planted routine takes nothing and returns.
            unsafe {
                call!(unsafe extern "C" clean);
                call!(unsafe extern "C" scratch);
                for (expect, message) in [
                    ("x19", broken(|| call!(unsafe extern "C" x19))),
                    ("x29", broken(|| call!(unsafe extern "C" x29))),
                    ("d8", broken(|| call!(unsafe extern "C" d8))),
                    ("stack pointer", broken(|| call!(unsafe extern "C" sp))),
                    #[cfg(target_os = "linux")]
                    ("x18", broken(|| call!(unsafe extern "C" x18))),
                ] {
                    assert!(message.contains(expect), "{expect}: {message}");
                }
            }
        }
    }

    #[cfg(target_arch = "arm")]
    mod arm {
        use super::broken;
        use crate::low::arm::cpu::HaveNeon;

        macro_rules! planted {
            ($name:ident, $($line:literal),*) => {
                #[unsafe(naked)]
                unsafe extern "C" fn $name() {
                    core::arch::naked_asm!($($line),*)
                }
            };
        }

        planted!(clean, "bx lr");
        planted!(r4, "mov r4, #0", "bx lr");
        planted!(r11, "add r11, r11, #4", "bx lr");
        planted!(d8, ".fpu vfpv3", "vmov.f64 d8, #1.0", "bx lr");
        // Lowered rather than raised, as on aarch64.
        planted!(sp, "sub sp, sp, #8", "bx lr");
        planted!(
            scratch,
            ".fpu vfpv3",
            "mov r12, #0",
            "vmov.f64 d0, #1.0",
            "bx lr"
        );

        #[test]
        fn planted_clobbers_fail() {
            // SAFETY: each planted routine takes nothing and returns.
            unsafe {
                call!(unsafe extern "C" clean);
                for (expect, message) in [
                    ("r4", broken(|| call!(unsafe extern "C" r4))),
                    ("r11", broken(|| call!(unsafe extern "C" r11))),
                    ("stack pointer", broken(|| call!(unsafe extern "C" sp))),
                ] {
                    assert!(message.contains(expect), "{expect}: {message}");
                }
                // The trampoline checks d8-d15 only where NEON, which every
                // routine writing them needs, is present.
                if HaveNeon::check().is_some() {
                    call!(unsafe extern "C" scratch);
                    let message = broken(|| call!(unsafe extern "C" d8));
                    assert!(message.contains("d8"), "d8: {message}");
                }
            }
        }
    }
}
