//! Runs each instruction of pyca/verified-garbage's (VG's) code on this CPU from
//! the start states `vg-cosim` (`proofs/verified-garbage/Cosim/`) writes, and
//! compares the state it leaves with the one VG's model says it does.
//!
//! `vg-cosim-runner --features` prints the CPU features this CPU has, by their
//! Rust `target_feature` names, comma-separated. `vg-cosim-runner [<stream>...]`
//! reads each stream of cases, or stdin, and fails if any case differs,
//! printing the first three of each instruction. `vg-cosim-runner --fault-test`
//! runs one case that faults, which must print its instruction and exit 1.
//!
//! The instruction's machine code runs at a fixed address, `INSN`, in a page of
//! its own, between a prologue that loads every register the model has from
//! `IN`, and an epilogue that stores them to `OUT`, both in `global_asm!`
//! below. A branch case's target and a call's `ret` are at `TARGET`. The data
//! the model may access is a page at `DATA`, which the case gives in full and
//! is compared in full.

use std::io::{BufReader, Read, Write};

const CODE: usize = 0x10_0000_0000;
const INSN: usize = CODE + 0x1000;
const TARGET: usize = INSN + 0x100;
const DATA: usize = 0x20_0000_0000;
const DATA_LEN: usize = 2048;

/// glibc's `struct sigaction` on Linux, the same on x86_64 and aarch64.
#[repr(C)]
struct SigAction {
    handler: usize,
    mask: [u64; 16],
    flags: i32,
    restorer: usize,
}

/// `stack_t`.
#[repr(C)]
struct StackT {
    sp: *mut u8,
    flags: i32,
    size: usize,
}

const SA_ONSTACK: i32 = 0x0800_0000;

unsafe extern "C" {
    fn mmap(addr: *mut u8, len: usize, prot: i32, flags: i32, fd: i32, off: i64) -> *mut u8;
    fn sigaction(sig: i32, act: *const SigAction, old: *mut SigAction) -> i32;
    fn sigaltstack(ss: *const StackT, old: *mut StackT) -> i32;
    fn write(fd: i32, buf: *const u8, len: usize) -> isize;
    fn _exit(code: i32) -> !;
}

const PROT_RWX: i32 = 7;
const PROT_RW: i32 = 3;
const MAP_PRIVATE_ANON_FIXED_NOREPLACE: i32 = 0x02 | 0x20 | 0x100000;

/// The text of the block running, for a fault to print.
static mut RUNNING: [u8; 512] = [0; 512];
static mut RUNNING_LEN: usize = 0;

extern "C" fn fault(sig: i32) {
    let msg = b"vg-cosim-runner: the CPU faulted (signal ";
    let digits = [
        b'0' + (sig / 10) as u8,
        b'0' + (sig % 10) as u8,
        b')',
        b' ',
        b'i',
        b'n',
        b' ',
    ];
    // SAFETY: `RUNNING` is only written between cases, and this exits.
    unsafe {
        write(2, msg.as_ptr(), msg.len());
        write(2, digits.as_ptr(), digits.len());
        write(2, (&raw const RUNNING).cast(), RUNNING_LEN);
        write(2, b"\n".as_ptr(), 1);
        _exit(1);
    }
}

fn map(addr: usize, len: usize, prot: i32) {
    // SAFETY: a fixed mapping at an address nothing else uses, which
    // `MAP_FIXED_NOREPLACE` refuses rather than replaces.
    let p = unsafe {
        mmap(
            addr as *mut u8,
            len,
            prot,
            MAP_PRIVATE_ANON_FIXED_NOREPLACE,
            -1,
            0,
        )
    };
    assert_eq!(p as usize, addr, "vg-cosim-runner: cannot map {addr:#x}");
}

fn read_u8(r: &mut impl Read) -> u8 {
    let mut b = [0; 1];
    r.read_exact(&mut b)
        .expect("vg-cosim-runner: truncated stream");
    b[0]
}

fn read_u16(r: &mut impl Read) -> usize {
    let mut b = [0; 2];
    r.read_exact(&mut b)
        .expect("vg-cosim-runner: truncated stream");
    u16::from_le_bytes(b) as usize
}

fn read_u32(r: &mut impl Read) -> usize {
    let mut b = [0; 4];
    r.read_exact(&mut b)
        .expect("vg-cosim-runner: truncated stream");
    u32::from_le_bytes(b) as usize
}

fn read_vec(r: &mut impl Read, n: usize) -> Vec<u8> {
    let mut v = vec![0; n];
    r.read_exact(&mut v)
        .expect("vg-cosim-runner: truncated stream");
    v
}

/// A block's kind: falls through, a branch reporting whether it is taken, or a
/// call that returns.
const INSN_KIND: u8 = 0;
const BRANCH_KIND: u8 = 1;
const CALL_KIND: u8 = 2;

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

#[cfg(target_arch = "x86_64")]
mod arch {
    //! x86-64: `rax`–`r15` in the model's order (`rax rcx rdx rbx rsp rbp rsi
    //! rdi r8`–`r15`, the encoding's), CF, ZF, SF and OF in a word, MXCSR, and
    //! `zmm0`–`zmm31`, or as much of them as the CPU has.

    pub const ARCH: u8 = 0;
    /// `mov rax, QWORD PTR [rbx]`, which faults with every register zero.
    pub const FAULT: (&str, &[u8]) = ("mov rax, QWORD PTR [rbx]", &[0x48, 0x8b, 0x03]);
    pub const REGS_LEN: usize = 16 * 8 + 4 + 4 + 32 * 64;
    /// The general-purpose registers, flags and MXCSR, which a mismatch
    /// prints.
    pub const START_SHOWN: usize = 136;
    const FLAGS: usize = 128;
    const MXCSR: usize = 132;
    const VEC: usize = 136;

    #[repr(C, align(64))]
    pub struct Regs(pub [u8; REGS_LEN]);

    #[unsafe(no_mangle)]
    pub static mut VG_IN: Regs = Regs([0; REGS_LEN]);
    #[unsafe(no_mangle)]
    pub static mut VG_OUT: Regs = Regs([0; REGS_LEN]);
    /// RFLAGS to load: CF, ZF, SF and OF from `VG_IN`, at bits 0, 6, 7 and 11,
    /// with bit 1, which is always set.
    #[unsafe(no_mangle)]
    pub static mut VG_RFLAGS: u64 = 0;
    /// What `lahf` and `seto` leave in `ax` at the end.
    #[unsafe(no_mangle)]
    pub static mut VG_AX: u64 = 0;
    #[unsafe(no_mangle)]
    pub static mut VG_MARKER: u64 = 0;
    #[unsafe(no_mangle)]
    pub static mut VG_HOST_RSP: u64 = 0;
    #[unsafe(no_mangle)]
    pub static mut VG_HOST_MXCSR: u32 = 0;
    #[unsafe(no_mangle)]
    pub static mut VG_INSN_PTR: u64 = super::INSN as u64;

    // Each variant loads and stores the vector registers the CPU has: with
    // AVX-512 all 512 bits of 32, with AVX 256 of 16, else 128 of 16. The
    // registers but `rax` load from `VG_IN` with `rax` as base, then `rsp`,
    // then `rax` itself; RFLAGS by `popfq` while `rsp` is still the host's.
    // Nothing after `popfq` changes the flags.
    macro_rules! trampoline {
        ($enter:literal, $leave0:literal, $leave1:literal, $load:literal, $store:literal) => {
            core::arch::global_asm!(
                concat!(".globl ", $enter),
                concat!($enter, ":"),
                "push rbx",
                "push rbp",
                "push r12",
                "push r13",
                "push r14",
                "push r15",
                "sub rsp, 8",
                "stmxcsr [rip + VG_HOST_MXCSR]",
                "mov [rip + VG_HOST_RSP], rsp",
                "lea rax, [rip + VG_IN]",
                $load,
                "ldmxcsr [rax + 132]",
                "push qword ptr [rip + VG_RFLAGS]",
                "popfq",
                "mov rcx, [rax + 8]",
                "mov rdx, [rax + 16]",
                "mov rbx, [rax + 24]",
                "mov rbp, [rax + 40]",
                "mov rsi, [rax + 48]",
                "mov rdi, [rax + 56]",
                "mov r8, [rax + 64]",
                "mov r9, [rax + 72]",
                "mov r10, [rax + 80]",
                "mov r11, [rax + 88]",
                "mov r12, [rax + 96]",
                "mov r13, [rax + 104]",
                "mov r14, [rax + 112]",
                "mov r15, [rax + 120]",
                "mov rsp, [rax + 32]",
                "mov rax, [rax]",
                "jmp qword ptr [rip + VG_INSN_PTR]",
                // Fallthrough, or a branch not taken.
                concat!(".globl ", $leave0),
                concat!($leave0, ":"),
                "mov [rip + VG_OUT], rax",
                "mov rax, 0",
                "mov [rip + VG_MARKER], rax",
                concat!("jmp 2f"),
                concat!(".globl ", $leave1),
                concat!($leave1, ":"),
                "mov [rip + VG_OUT], rax",
                "mov rax, 1",
                "mov [rip + VG_MARKER], rax",
                "2:",
                "lahf",
                "seto al",
                "mov [rip + VG_AX], rax",
                "lea rax, [rip + VG_OUT]",
                "mov [rax + 8], rcx",
                "mov [rax + 16], rdx",
                "mov [rax + 24], rbx",
                "mov [rax + 32], rsp",
                "mov [rax + 40], rbp",
                "mov [rax + 48], rsi",
                "mov [rax + 56], rdi",
                "mov [rax + 64], r8",
                "mov [rax + 72], r9",
                "mov [rax + 80], r10",
                "mov [rax + 88], r11",
                "mov [rax + 96], r12",
                "mov [rax + 104], r13",
                "mov [rax + 112], r14",
                "mov [rax + 120], r15",
                "stmxcsr [rax + 132]",
                $store,
                "mov rsp, [rip + VG_HOST_RSP]",
                "ldmxcsr [rip + VG_HOST_MXCSR]",
                "add rsp, 8",
                "pop r15",
                "pop r14",
                "pop r13",
                "pop r12",
                "pop rbp",
                "pop rbx",
                "ret",
            );
        };
    }

    // `.irp` repeats its body for each register, `\i` its number.
    trampoline!(
        "vg_enter_zmm",
        "vg_leave0_zmm",
        "vg_leave1_zmm",
        ".irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\nvmovdqu64 zmm\\i, [rax + 136 + \\i * 64]\n.endr",
        ".irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\nvmovdqu64 [rax + 136 + \\i * 64], zmm\\i\n.endr"
    );
    trampoline!(
        "vg_enter_ymm",
        "vg_leave0_ymm",
        "vg_leave1_ymm",
        ".irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15\nvmovdqu ymm\\i, [rax + 136 + \\i * 64]\n.endr",
        ".irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15\nvmovdqu [rax + 136 + \\i * 64], ymm\\i\n.endr"
    );
    trampoline!(
        "vg_enter_xmm",
        "vg_leave0_xmm",
        "vg_leave1_xmm",
        ".irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15\nmovdqu xmm\\i, [rax + 136 + \\i * 64]\n.endr",
        ".irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15\nmovdqu [rax + 136 + \\i * 64], xmm\\i\n.endr"
    );

    unsafe extern "C" {
        fn vg_enter_zmm();
        fn vg_leave0_zmm();
        fn vg_leave1_zmm();
        fn vg_enter_ymm();
        fn vg_leave0_ymm();
        fn vg_leave1_ymm();
        fn vg_enter_xmm();
        fn vg_leave0_xmm();
        fn vg_leave1_xmm();
    }

    /// The trampoline for the vector registers this CPU has, and how many bytes
    /// of each and how many of them it compares.
    pub struct Tramp {
        enter: unsafe extern "C" fn(),
        pub leave0: usize,
        pub leave1: usize,
        width: usize,
        count: usize,
    }

    pub fn tramp() -> Tramp {
        if std::arch::is_x86_feature_detected!("avx512f") {
            Tramp {
                enter: vg_enter_zmm,
                leave0: vg_leave0_zmm as *const () as usize,
                leave1: vg_leave1_zmm as *const () as usize,
                width: 64,
                count: 32,
            }
        } else if std::arch::is_x86_feature_detected!("avx") {
            Tramp {
                enter: vg_enter_ymm,
                leave0: vg_leave0_ymm as *const () as usize,
                leave1: vg_leave1_ymm as *const () as usize,
                width: 32,
                count: 16,
            }
        } else {
            Tramp {
                enter: vg_enter_xmm,
                leave0: vg_leave0_xmm as *const () as usize,
                leave1: vg_leave1_xmm as *const () as usize,
                width: 16,
                count: 16,
            }
        }
    }

    pub fn features() -> Vec<&'static str> {
        macro_rules! has {
            ($($f:tt),*) => { [$(($f, std::arch::is_x86_feature_detected!($f))),*] };
        }
        has!(
            "ssse3",
            "sse4.1",
            "sha",
            "aes",
            "pclmulqdq",
            "avx",
            "avx2",
            "vaes",
            "vpclmulqdq",
            "bmi1",
            "bmi2",
            "adx",
            "avx512f",
            "avx512vl",
            "avx512bw",
            "avx512ifma",
            "sha512"
        )
        .into_iter()
        .filter(|(_, on)| *on)
        .map(|(f, _)| f)
        .collect()
    }

    /// `jmp qword ptr [rip]` and the address: to `to`, from anywhere.
    pub fn jump(_from: usize, to: usize) -> Vec<u8> {
        let mut v = vec![0xFF, 0x25, 0, 0, 0, 0];
        v.extend_from_slice(&(to as u64).to_le_bytes());
        v
    }

    /// `ret`.
    pub const RET: &[u8] = &[0xC3];

    /// x86-64 keeps instruction fetch coherent with stores (SDM Vol. 3,
    /// 11.6, "Self-Modifying Code"), and the jump to the code serializes.
    pub fn sync(_addr: usize, _len: usize) {}

    /// Runs the code at `INSN` from `regs`, giving the registers it leaves and
    /// the branch marker.
    pub fn run(t: &Tramp, regs: &[u8]) -> (Vec<u8>, u8) {
        // SAFETY: the trampolines read and write these only while they run,
        // and this thread is the only one.
        unsafe {
            let inp = &mut *(&raw mut VG_IN);
            inp.0.copy_from_slice(regs);
            let fl = u32::from_le_bytes(regs[FLAGS..FLAGS + 4].try_into().unwrap()) as u64;
            VG_RFLAGS =
                2 | (fl & 1) | ((fl >> 1) & 1) << 6 | ((fl >> 2) & 1) << 7 | ((fl >> 3) & 1) << 11;
            let out = &mut *(&raw mut VG_OUT);
            out.0.fill(0);
            (t.enter)();
            // `lahf` gives SF:ZF:0:AF:0:PF:1:CF in AH; `seto` OF in AL.
            let ax = VG_AX;
            let ah = (ax >> 8) & 0xFF;
            let fl = (ah & 1) | ((ah >> 6) & 1) << 1 | ((ah >> 7) & 1) << 2 | (ax & 1) << 3;
            out.0[FLAGS..FLAGS + 4].copy_from_slice(&(fl as u32).to_le_bytes());
            (out.0.to_vec(), VG_MARKER as u8)
        }
    }

    /// The fields of the register state in which `got` differs from `want`,
    /// comparing the flags `mask` says are defined, and only the vector
    /// registers the trampoline loaded.
    pub fn diff(t: &Tramp, got: &[u8], want: &[u8], mask: u8) -> Vec<String> {
        const NAMES: [&str; 16] = [
            "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi", "r8", "r9", "r10", "r11",
            "r12", "r13", "r14", "r15",
        ];
        let mut d = vec![];
        for (i, n) in NAMES.iter().enumerate() {
            let (g, w) = (&got[8 * i..8 * i + 8], &want[8 * i..8 * i + 8]);
            if g != w {
                d.push(format!(
                    "{n}: {} (model {})",
                    super::hex(&rev(g)),
                    super::hex(&rev(w))
                ));
            }
        }
        let (g, w) = (got[FLAGS] & mask, want[FLAGS] & mask);
        if g != w {
            d.push(format!(
                "flags (CF ZF SF OF, defined {mask:04b}): {g:04b} (model {w:04b})"
            ));
        }
        if got[MXCSR..MXCSR + 4] != want[MXCSR..MXCSR + 4] {
            d.push(format!(
                "mxcsr: {} (model {})",
                super::hex(&rev(&got[MXCSR..MXCSR + 4])),
                super::hex(&rev(&want[MXCSR..MXCSR + 4]))
            ));
        }
        for i in 0..t.count {
            let o = VEC + 64 * i;
            if got[o..o + t.width] != want[o..o + t.width] {
                d.push(format!(
                    "zmm{i}[{}:0]: {} (model {})",
                    8 * t.width - 1,
                    super::hex(&rev(&got[o..o + t.width])),
                    super::hex(&rev(&want[o..o + t.width]))
                ));
            }
        }
        d
    }

    fn rev(b: &[u8]) -> Vec<u8> {
        b.iter().rev().copied().collect()
    }
}

#[cfg(target_arch = "aarch64")]
mod arch {
    //! AArch64: `x0`–`x30` by number (`x18` and `x29`, which the model does
    //! not have, are compared with what they were), `sp`, NZCV (bit 3 N, 2 Z, 1
    //! C, 0 V: the register's bits 31–28), PSTATE.DIT, and `v0`–`v31`.
    //!
    //! No register is free here: the model has every one but `x18` and `x29`,
    //! and a branch needs one unless it is PC-relative, which reaches only
    //! ±128 MB. So the trampoline is copied into the code page, before `INSN`,
    //! where `b` reaches the instruction and the instruction's exits reach the
    //! trampoline's; it finds its data with `movz`/`movk`, at `VARS`, also in
    //! that page. Its exit has no register to put that address in, so it
    //! first moves `sp`, which the cases keep 16-byte aligned (AAPCS64; Linux
    //! sets SCTLR_EL1.SA0, which checks it at each access through `sp`), 4096
    //! bytes down, into `SCRATCH` below the data, which no case compares, and
    //! stores `x0` and `x1` there. `sub sp, sp, #imm` leaves NZCV as it is.

    pub const ARCH: u8 = 1;
    /// `ldr x0, [x1]`, which faults with every register zero.
    pub const FAULT: (&str, &[u8]) = ("ldr x0, [x1]", &[0x20, 0x00, 0x40, 0xf9]);
    pub const REGS_LEN: usize = 31 * 8 + 8 + 4 + 4 + 32 * 16;
    /// The general-purpose registers, `sp`, NZCV and DIT, which a mismatch
    /// prints.
    pub const START_SHOWN: usize = VEC;
    const SP: usize = 248;
    const NZCV: usize = 256;
    const DIT: usize = 260;
    const VEC: usize = 264;
    /// The trampoline's data: the registers to load (`IN`), those it stores
    /// (`OUT`), the host's `sp` and the branch marker.
    const VARS: usize = super::CODE + 0x8000;
    const IN: usize = VARS;
    const OUT: usize = VARS + 0x400;
    const MARKER: usize = VARS + 0x808;
    /// Below the data. `vg-cosim` leaves `sp` at most 4096 bytes below the
    /// window, its start 512 bytes into the data, at the end of a case (an
    /// `alloc` moves it at most 4095 bytes down, and an access through it is
    /// at most 3824 bytes above it, VG's largest offset), so the exit's
    /// stores, 4096 bytes below that, land in it. 64 KiB, so its start is
    /// page-aligned under 64-KiB pages too, as a fixed mapping needs.
    const SCRATCH: usize = 0x10000;

    // `DIT` is
    // `S3_3_C4_C2_5` (DDI 0601, "DIT, Data Independent Timing"), which needs
    // FEAT_DIT, so only one variant loads and stores it.
    macro_rules! trampoline {
        ($enter:literal, $go:literal, $leave0:literal, $leave1:literal, $end:literal,
         $load_dit:literal, $store_dit:literal) => {
            core::arch::global_asm!(
                ".p2align 4",
                concat!(".globl ", $enter),
                concat!($enter, ":"),
                "stp x29, x30, [sp, #-16]!",
                "stp x27, x28, [sp, #-16]!", "stp x25, x26, [sp, #-16]!", "stp x23, x24, [sp, #-16]!",
                "stp x21, x22, [sp, #-16]!", "stp x19, x20, [sp, #-16]!", "stp x17, x18, [sp, #-16]!",
                "stp d14, d15, [sp, #-16]!", "stp d12, d13, [sp, #-16]!", "stp d10, d11, [sp, #-16]!",
                "stp d8, d9, [sp, #-16]!",
                "mov x1, sp",
                "movz x0, #({vars} & 0xffff)",
                "movk x0, #(({vars} >> 16) & 0xffff), lsl #16",
                "movk x0, #(({vars} >> 32) & 0xffff), lsl #32",
                "str x1, [x0, #2048]",
                "add x1, x0, #264",
                "ldp q0, q1, [x1, #0]", "ldp q2, q3, [x1, #32]", "ldp q4, q5, [x1, #64]", "ldp q6, q7, [x1, #96]",
                "ldp q8, q9, [x1, #128]", "ldp q10, q11, [x1, #160]", "ldp q12, q13, [x1, #192]", "ldp q14, q15, [x1, #224]",
                "ldp q16, q17, [x1, #256]", "ldp q18, q19, [x1, #288]", "ldp q20, q21, [x1, #320]", "ldp q22, q23, [x1, #352]",
                "ldp q24, q25, [x1, #384]", "ldp q26, q27, [x1, #416]", "ldp q28, q29, [x1, #448]", "ldp q30, q31, [x1, #480]",
                "ldr w2, [x0, #256]",
                "lsl x2, x2, #28",
                "msr nzcv, x2",
                $load_dit,
                "ldr x1, [x0, #248]",
                "mov sp, x1",
                "ldp x2, x3, [x0, #16]", "ldp x4, x5, [x0, #32]", "ldp x6, x7, [x0, #48]", "ldp x8, x9, [x0, #64]",
                "ldp x10, x11, [x0, #80]", "ldp x12, x13, [x0, #96]", "ldp x14, x15, [x0, #112]", "ldp x16, x17, [x0, #128]",
                "ldp x18, x19, [x0, #144]", "ldp x20, x21, [x0, #160]", "ldp x22, x23, [x0, #176]", "ldp x24, x25, [x0, #192]",
                "ldp x26, x27, [x0, #208]", "ldp x28, x29, [x0, #224]",
                "ldr x30, [x0, #240]",
                "ldp x0, x1, [x0]",
                // `b INSN`, which the runner writes once the code is in place.
                concat!(".globl ", $go),
                concat!($go, ":"),
                ".inst 0",
                // Fallthrough, or a branch not taken.
                concat!(".globl ", $leave0),
                concat!($leave0, ":"),
                "sub sp, sp, #4096",
                "stp x0, x1, [sp]",
                "movz x0, #0",
                "b 1f",
                concat!(".globl ", $leave1),
                concat!($leave1, ":"),
                "sub sp, sp, #4096",
                "stp x0, x1, [sp]",
                "movz x0, #1",
                "1:",
                "movz x1, #(({vars} + 0x400) & 0xffff)",
                "movk x1, #((({vars} + 0x400) >> 16) & 0xffff), lsl #16",
                "movk x1, #((({vars} + 0x400) >> 32) & 0xffff), lsl #32",
                "str x0, [x1, #1032]",
                "stp x2, x3, [x1, #16]", "stp x4, x5, [x1, #32]", "stp x6, x7, [x1, #48]", "stp x8, x9, [x1, #64]",
                "stp x10, x11, [x1, #80]", "stp x12, x13, [x1, #96]", "stp x14, x15, [x1, #112]", "stp x16, x17, [x1, #128]",
                "stp x18, x19, [x1, #144]", "stp x20, x21, [x1, #160]", "stp x22, x23, [x1, #176]", "stp x24, x25, [x1, #192]",
                "stp x26, x27, [x1, #208]", "stp x28, x29, [x1, #224]",
                "str x30, [x1, #240]",
                "ldp x2, x3, [sp]",
                "stp x2, x3, [x1]",
                "add sp, sp, #4096",
                "mov x2, sp",
                "str x2, [x1, #248]",
                "mrs x2, nzcv",
                "lsr x2, x2, #28",
                "str w2, [x1, #256]",
                $store_dit,
                "add x3, x1, #264",
                "stp q0, q1, [x3, #0]", "stp q2, q3, [x3, #32]", "stp q4, q5, [x3, #64]", "stp q6, q7, [x3, #96]",
                "stp q8, q9, [x3, #128]", "stp q10, q11, [x3, #160]", "stp q12, q13, [x3, #192]", "stp q14, q15, [x3, #224]",
                "stp q16, q17, [x3, #256]", "stp q18, q19, [x3, #288]", "stp q20, q21, [x3, #320]", "stp q22, q23, [x3, #352]",
                "stp q24, q25, [x3, #384]", "stp q26, q27, [x3, #416]", "stp q28, q29, [x3, #448]", "stp q30, q31, [x3, #480]",
                "movz x0, #({vars} & 0xffff)",
                "movk x0, #(({vars} >> 16) & 0xffff), lsl #16",
                "movk x0, #(({vars} >> 32) & 0xffff), lsl #32",
                "ldr x1, [x0, #2048]",
                "mov sp, x1",
                "ldp d8, d9, [sp], #16", "ldp d10, d11, [sp], #16", "ldp d12, d13, [sp], #16",
                "ldp d14, d15, [sp], #16",
                "ldp x17, x18, [sp], #16", "ldp x19, x20, [sp], #16", "ldp x21, x22, [sp], #16",
                "ldp x23, x24, [sp], #16", "ldp x25, x26, [sp], #16", "ldp x27, x28, [sp], #16",
                "ldp x29, x30, [sp], #16",
                "ret",
                concat!(".globl ", $end),
                concat!($end, ":"),
                vars = const VARS,
            );
        };
    }

    trampoline!(
        "vg_enter_dit",
        "vg_go_dit",
        "vg_leave0_dit",
        "vg_leave1_dit",
        "vg_end_dit",
        "ldr w2, [x0, #260]\nlsl x2, x2, #24\nmsr S3_3_C4_C2_5, x2",
        "mrs x2, S3_3_C4_C2_5\nlsr x2, x2, #24\nstr w2, [x1, #260]\nmsr S3_3_C4_C2_5, xzr"
    );
    trampoline!(
        "vg_enter",
        "vg_go",
        "vg_leave0",
        "vg_leave1",
        "vg_end",
        "",
        ""
    );

    unsafe extern "C" {
        fn vg_enter_dit();
        fn vg_go_dit();
        fn vg_leave0_dit();
        fn vg_leave1_dit();
        fn vg_end_dit();
        fn vg_enter();
        fn vg_go();
        fn vg_leave0();
        fn vg_leave1();
        fn vg_end();
    }

    /// The trampoline, in the code page: its exits, and whether it loads and
    /// stores DIT.
    pub struct Tramp {
        pub leave0: usize,
        pub leave1: usize,
        dit: bool,
    }

    /// Copies the trampoline for this CPU into the code page, at `CODE`, and
    /// maps the scratch below the data.
    pub fn tramp() -> Tramp {
        let dit = std::arch::is_aarch64_feature_detected!("dit");
        let [enter, go, leave0, leave1, end] = if dit {
            [
                vg_enter_dit as *const (),
                vg_go_dit as *const (),
                vg_leave0_dit as *const (),
                vg_leave1_dit as *const (),
                vg_end_dit as *const (),
            ]
        } else {
            [
                vg_enter as *const (),
                vg_go as *const (),
                vg_leave0 as *const (),
                vg_leave1 as *const (),
                vg_end as *const (),
            ]
        }
        .map(|p| p as usize);
        let len = end - enter;
        assert!(
            len <= super::INSN - super::CODE,
            "vg-cosim-runner: the trampoline does not fit"
        );
        let at = |p: usize| super::CODE + (p - enter);
        // SAFETY: the code page is mapped, and the trampoline's bytes are
        // this program's text.
        unsafe {
            std::ptr::copy_nonoverlapping(enter as *const u8, super::CODE as *mut u8, len);
            let b = jump(at(go), super::INSN);
            std::ptr::copy_nonoverlapping(b.as_ptr(), at(go) as *mut u8, 4);
        }
        sync(super::CODE, len);
        super::map(super::DATA - SCRATCH, SCRATCH, super::PROT_RW);
        Tramp {
            leave0: at(leave0),
            leave1: at(leave1),
            dit,
        }
    }

    pub fn features() -> Vec<&'static str> {
        macro_rules! has {
            ($($f:tt),*) => { [$(($f, std::arch::is_aarch64_feature_detected!($f))),*] };
        }
        has!("aes", "sha2", "sha3", "sm4", "sve2", "dit", "sb")
            .into_iter()
            .filter(|(_, on)| *on)
            .map(|(f, _)| f)
            .collect()
    }

    /// `b to` at `from` (DDI 0487 C6.2, "B": `0 00101 imm26`, the offset
    /// `imm26 * 4`, ±128 MB).
    pub fn jump(from: usize, to: usize) -> Vec<u8> {
        let off = (to as isize - from as isize) / 4;
        assert!(
            (-(1 << 25)..1 << 25).contains(&off),
            "vg-cosim-runner: {to:#x} is out of reach of {from:#x}"
        );
        (0x1400_0000u32 | (off as u32 & 0x03FF_FFFF))
            .to_le_bytes()
            .to_vec()
    }

    /// `ret`.
    pub const RET: &[u8] = &0xD65F_03C0u32.to_le_bytes();

    /// Makes instruction fetch see the code written at `addr`: each data cache
    /// line cleaned to the point of unification, each instruction cache line
    /// invalidated, by the line sizes CTR_EL0 gives (DDI 0487 B2.4.4, the
    /// sequence for self-modifying code).
    pub fn sync(addr: usize, len: usize) {
        // SAFETY: cache maintenance by address on this program's own mapped
        // code, which EL0 may do (SCTLR_EL1.UCI, which Linux sets).
        unsafe {
            let ctr: u64;
            core::arch::asm!("mrs {}, ctr_el0", out(reg) ctr);
            let dline = 4usize << ((ctr >> 16) & 0xF);
            let iline = 4usize << (ctr & 0xF);
            let mut a = addr & !(dline - 1);
            while a < addr + len {
                core::arch::asm!("dc cvau, {}", in(reg) a);
                a += dline;
            }
            core::arch::asm!("dsb ish");
            let mut a = addr & !(iline - 1);
            while a < addr + len {
                core::arch::asm!("ic ivau, {}", in(reg) a);
                a += iline;
            }
            core::arch::asm!("dsb ish", "isb");
        }
    }

    /// Runs the code at `INSN` from `regs`, giving the registers it leaves and
    /// the branch marker.
    pub fn run(_t: &Tramp, regs: &[u8]) -> (Vec<u8>, u8) {
        // SAFETY: the trampoline in the code page reads `IN` and writes `OUT`
        // and `MARKER` only while it runs, and this thread is the only one;
        // it saves and restores every callee-saved register and the host's
        // `sp`, as a call to an `extern "C" fn()` may assume.
        unsafe {
            std::ptr::copy_nonoverlapping(regs.as_ptr(), IN as *mut u8, REGS_LEN);
            std::ptr::write_bytes(OUT as *mut u8, 0, REGS_LEN);
            let enter: extern "C" fn() = std::mem::transmute(super::CODE);
            enter();
            let out = std::slice::from_raw_parts(OUT as *const u8, REGS_LEN).to_vec();
            (out, *(MARKER as *const u64) as u8)
        }
    }

    /// The fields of the register state in which `got` differs from `want`,
    /// comparing the flags `mask` says are defined, and DIT only where the
    /// trampoline loads it.
    pub fn diff(t: &Tramp, got: &[u8], want: &[u8], mask: u8) -> Vec<String> {
        let mut d = vec![];
        for i in 0..31 {
            let (g, w) = (&got[8 * i..8 * i + 8], &want[8 * i..8 * i + 8]);
            if g != w {
                d.push(format!(
                    "x{i}: {} (model {})",
                    super::hex(&rev(g)),
                    super::hex(&rev(w))
                ));
            }
        }
        if got[SP..SP + 8] != want[SP..SP + 8] {
            d.push(format!(
                "sp: {} (model {})",
                super::hex(&rev(&got[SP..SP + 8])),
                super::hex(&rev(&want[SP..SP + 8]))
            ));
        }
        let (g, w) = (got[NZCV] & mask, want[NZCV] & mask);
        if g != w {
            d.push(format!(
                "nzcv (defined {mask:04b}): {g:04b} (model {w:04b})"
            ));
        }
        if t.dit && got[DIT] != want[DIT] {
            d.push(format!("dit: {} (model {})", got[DIT], want[DIT]));
        }
        for i in 0..32 {
            let o = VEC + 16 * i;
            if got[o..o + 16] != want[o..o + 16] {
                d.push(format!(
                    "v{i}: {} (model {})",
                    super::hex(&rev(&got[o..o + 16])),
                    super::hex(&rev(&want[o..o + 16]))
                ));
            }
        }
        d
    }

    fn rev(b: &[u8]) -> Vec<u8> {
        b.iter().rev().copied().collect()
    }
}

fn main() {
    if std::env::args().nth(1).as_deref() == Some("--features") {
        println!("{}", arch::features().join(","));
        return;
    }
    map(CODE, 0x10000, PROT_RWX);
    map(DATA, DATA_LEN, PROT_RW);
    let t = arch::tramp();
    // A case runs on the model's stack pointer, inside the data, where the
    // kernel cannot write a signal frame, so `fault` runs on a stack of its
    // own, which lives as long as the program.
    let alt: &'static mut [u8] = Box::leak(vec![0u8; 1 << 16].into_boxed_slice());
    let ss = StackT {
        sp: alt.as_mut_ptr(),
        flags: 0,
        size: alt.len(),
    };
    // SAFETY: the stack is leaked, so valid for the rest of the program.
    assert_eq!(
        unsafe { sigaltstack(&ss, std::ptr::null_mut()) },
        0,
        "vg-cosim-runner: sigaltstack"
    );
    let act = SigAction {
        handler: fault as *const () as usize,
        mask: [0; 16],
        flags: SA_ONSTACK,
        restorer: 0,
    };
    for sig in [4, 5, 7, 8, 11] {
        // SAFETY: `fault` only writes to stderr and exits.
        assert_eq!(
            unsafe { sigaction(sig, &act, std::ptr::null_mut()) },
            0,
            "vg-cosim-runner: sigaction"
        );
    }
    if std::env::args().nth(1).as_deref() == Some("--fault-test") {
        // One case that faults, every register zero, so `admin/prove vg` can
        // check that a fault names its instruction and fails the run.
        let (text, code) = arch::FAULT;
        let n = arch::REGS_LEN + DATA_LEN;
        let mut s = b"VGCS".to_vec();
        s.push(arch::ARCH);
        s.extend((n as u32).to_le_bytes());
        s.push(1);
        s.extend((text.len() as u16).to_le_bytes());
        s.extend(text.as_bytes());
        s.push(INSN_KIND);
        s.extend((code.len() as u16).to_le_bytes());
        s.extend(code);
        s.extend(1u32.to_le_bytes());
        s.extend(vec![0; 2 * n + 2]);
        s.push(0);
        let (mut b, mut c, mut f) = (0, 0, 0);
        run_stream(&s[..], &t, &mut b, &mut c, &mut f);
        eprintln!("vg-cosim-runner: {text} ran without faulting");
        std::process::exit(2);
    }
    let paths: Vec<String> = std::env::args().skip(1).collect();
    let (mut blocks, mut cases, mut failed) = (0usize, 0usize, 0usize);
    let mut streams: Vec<Box<dyn Read>> = Vec::new();
    if paths.is_empty() {
        streams.push(Box::new(std::io::stdin().lock()));
    }
    for p in &paths {
        streams.push(Box::new(
            std::fs::File::open(p).unwrap_or_else(|e| panic!("vg-cosim-runner: {p}: {e}")),
        ));
    }
    for s in streams {
        run_stream(
            BufReader::with_capacity(1 << 20, s),
            &t,
            &mut blocks,
            &mut cases,
            &mut failed,
        );
    }
    eprintln!(
        "vg-cosim-runner: {blocks} instructions, {cases} cases, {failed} differ from the model"
    );
    if failed > 0 {
        std::process::exit(1);
    }
}

/// Runs the cases of one stream, adding to the counts.
fn run_stream(
    mut r: impl Read,
    t: &arch::Tramp,
    blocks: &mut usize,
    cases: &mut usize,
    failed: &mut usize,
) {
    let magic = read_vec(&mut r, 4);
    assert_eq!(magic, b"VGCS", "vg-cosim-runner: not a stream of cases");
    assert_eq!(
        read_u8(&mut r),
        arch::ARCH,
        "vg-cosim-runner: the cases are for another target"
    );
    let state_len = read_u32(&mut r);
    assert_eq!(
        state_len,
        arch::REGS_LEN + DATA_LEN,
        "vg-cosim-runner: the cases' states differ from this runner's"
    );
    let stderr = std::io::stderr();
    loop {
        match read_u8(&mut r) {
            0 => break,
            1 => {}
            tag => panic!("vg-cosim-runner: a block's tag is {tag}, not 0 or 1"),
        }
        let len = read_u16(&mut r);
        let text = read_vec(&mut r, len);
        let kind = read_u8(&mut r);
        let len = read_u16(&mut r);
        let code = read_vec(&mut r, len);
        let n = read_u32(&mut r);
        // SAFETY: the code page is this program's, mapped above, and nothing
        // runs from it while it is written.
        unsafe {
            let len = text.len().min(512);
            (&mut *(&raw mut RUNNING))[..len].copy_from_slice(&text[..len]);
            RUNNING_LEN = len;
            let page = std::slice::from_raw_parts_mut(INSN as *mut u8, 0x1000);
            page.fill(0xCC);
            page[..code.len()].copy_from_slice(&code);
            let after = arch::jump(INSN + code.len(), t.leave0);
            page[code.len()..code.len() + after.len()].copy_from_slice(&after);
            let target: &[u8] = match kind {
                BRANCH_KIND => &arch::jump(TARGET, t.leave1),
                CALL_KIND => arch::RET,
                INSN_KIND => &[],
                _ => panic!("vg-cosim-runner: unknown kind {kind}"),
            };
            page[TARGET - INSN..TARGET - INSN + target.len()].copy_from_slice(target);
            arch::sync(INSN, 0x1000);
        }
        let mut shown = 0;
        for c in 0..n {
            let start = read_vec(&mut r, state_len);
            let want = read_vec(&mut r, state_len);
            let marker = read_u8(&mut r);
            let mask = read_u8(&mut r);
            // SAFETY: the data page is this program's, mapped above.
            let data = unsafe { std::slice::from_raw_parts_mut(DATA as *mut u8, DATA_LEN) };
            data.copy_from_slice(&start[arch::REGS_LEN..]);
            let (got, got_marker) = arch::run(t, &start[..arch::REGS_LEN]);
            let mut d = arch::diff(t, &got, &want[..arch::REGS_LEN], mask);
            if kind == BRANCH_KIND && got_marker != marker {
                d.push(format!(
                    "branch: {} (model {})",
                    if got_marker == 1 {
                        "taken"
                    } else {
                        "not taken"
                    },
                    if marker == 1 { "taken" } else { "not taken" }
                ));
            }
            for (o, (g, w)) in data.iter().zip(&want[arch::REGS_LEN..]).enumerate() {
                if g != w {
                    d.push(format!("data[{o}]: {g:02x} (model {w:02x})"));
                }
            }
            *cases += 1;
            if !d.is_empty() {
                *failed += 1;
                if shown < 3 {
                    shown += 1;
                    let mut e = stderr.lock();
                    writeln!(
                        e,
                        "vg-cosim-runner: {} ({}), case {c}:",
                        String::from_utf8_lossy(&text),
                        hex(&code)
                    )
                    .unwrap();
                    writeln!(e, "  start: {}", hex(&start[..arch::START_SHOWN])).unwrap();
                    for l in d.iter().take(12) {
                        writeln!(e, "  {l}").unwrap();
                    }
                }
            }
        }
        *blocks += 1;
    }
    let mut rest = [0u8; 1];
    assert_eq!(
        r.read(&mut rest).unwrap(),
        0,
        "vg-cosim-runner: bytes follow the stream's end"
    );
}
