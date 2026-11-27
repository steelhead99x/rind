// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! `abi`'s armv7 registers and trampoline, in a file of their own so that
//! `.cargo/mutants.toml` can exclude them: no mutation campaign runs armv7.

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

    pub(super) fn changed(&self, after: &Self, _: Convention, _: &str) -> Vec<String> {
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
