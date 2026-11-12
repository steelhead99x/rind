//! Runs each aarch64 intrinsic `proofs/Rind/Aarch64/Neon.lean` models on this
//! CPU and prints a Lean file of `#guard`s that each model computes what the
//! instruction did: every immediate the instruction reads, zero and all-ones
//! lanes, and random inputs from a fixed seed. Its output is committed as
//! `proofs/Rind/Aarch64/NeonVectors.lean`, which `admin/prove` checks on any
//! host, and the `prove` workflow's `neon` job reruns this on an aarch64 CPU
//! and fails if the output differs.
//!
//! Usage: rustc --edition 2024 -O admin/neon-vectors.rs && ./neon-vectors

#[cfg(not(target_arch = "aarch64"))]
compile_error!("the aarch64 intrinsics run only on aarch64");

use std::arch::aarch64::*;
use std::fmt::Write;
use std::mem::transmute;

/// SplitMix64, from a fixed seed.
struct Rng(u64);

impl Rng {
    fn u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let z = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    fn u128(&mut self) -> u128 {
        (u128::from(self.u64()) << 64) | u128::from(self.u64())
    }
}

fn v(x: u128) -> uint8x16_t {
    unsafe { transmute(x) }
}

fn q(x: uint8x16_t) -> String {
    format!("0x{:032x}#128", unsafe { transmute::<uint8x16_t, u128>(x) })
}

type Unary = unsafe fn(uint8x16_t) -> uint8x16_t;
type Binary = unsafe fn(uint8x16_t, uint8x16_t) -> uint8x16_t;

#[target_feature(enable = "neon")]
fn ext<const N: i32>(a: uint8x16_t, b: uint8x16_t) -> uint8x16_t {
    vextq_u8::<N>(a, b)
}

#[target_feature(enable = "neon")]
fn dup_lane<const N: i32>(a: uint8x16_t) -> uint8x16_t {
    vreinterpretq_u8_u32(vdupq_laneq_u32::<N>(vreinterpretq_u32_u8(a)))
}

const ARM: &str = "core.core_arch.arm_shared.neon.generated";
const AARCH64: &str = "core.core_arch.aarch64.neon.generated";
const RANDOM: usize = 16;

fn main() {
    if !std::arch::is_aarch64_feature_detected!("aes") {
        eprintln!("admin/neon-vectors: this CPU lacks aes");
        std::process::exit(1);
    }
    let mut rng = Rng(0x7269_6e64);
    let mut inputs = vec![0, u128::MAX, 0x8080_8080_8080_8080_8080_8080_8080_8080];
    inputs.extend((0..RANDOM).map(|_| rng.u128()));
    let pairs: Vec<(u128, u128)> = inputs
        .iter()
        .flat_map(|&a| [(a, 0), (a, u128::MAX), (a, rng.u128())])
        .collect();
    let mut out = String::from("import Rind.Aarch64.Neon\nopen Aeneas Aeneas.Std Result\n\n");
    let mut guard = |call: String, result: String| {
        writeln!(out, "#guard reducesTo (R := BitVec _) ( {call} ) {result}").unwrap()
    };

    // `TBL`'s indices past 15 select zero: each pair's random second vector
    // has some, and these some at and around the edge.
    let tbl_edges = [0x0f10_1f20_7f80_ff00_0102_0304_0506_0708, 0x1011_1213_0f0e_0d0c_8000_7fff_4020_1008];
    let binary: [(String, Binary); 5] = [
        (format!("{ARM}.veorq_u8"), |a, b| unsafe { veorq_u8(a, b) }),
        (format!("{AARCH64}.vqtbl1q_u8"), |a, b| unsafe {
            vqtbl1q_u8(a, b)
        }),
        (format!("{AARCH64}.vzip1q_u64"), |a, b| unsafe {
            vreinterpretq_u8_u64(vzip1q_u64(
                vreinterpretq_u64_u8(a),
                vreinterpretq_u64_u8(b),
            ))
        }),
        (format!("{ARM}.vaeseq_u8"), |a, b| unsafe { vaeseq_u8(a, b) }),
        (format!("{ARM}.vaesdq_u8"), |a, b| unsafe { vaesdq_u8(a, b) }),
    ];
    for (name, f) in binary {
        let edges = tbl_edges.iter().map(|&b| (inputs[3], b));
        for (a, b) in pairs.iter().copied().chain(edges) {
            let r = unsafe { f(v(a), v(b)) };
            guard(format!("{name} {} {}", q(v(a)), q(v(b))), q(r));
        }
    }

    let unary: [(&str, Unary); 6] = [
        ("vaesmcq_u8", |a| unsafe { vaesmcq_u8(a) }),
        ("vaesimcq_u8", |a| unsafe { vaesimcq_u8(a) }),
        ("vreinterpretq_u32_u8", |a| unsafe {
            transmute(vreinterpretq_u32_u8(a))
        }),
        ("vreinterpretq_u8_u32", |a| unsafe {
            vreinterpretq_u8_u32(transmute(a))
        }),
        ("vreinterpretq_u64_u8", |a| unsafe {
            transmute(vreinterpretq_u64_u8(a))
        }),
        ("vreinterpretq_u8_u64", |a| unsafe {
            vreinterpretq_u8_u64(transmute(a))
        }),
    ];
    for (name, f) in unary {
        for &a in &inputs {
            let r = unsafe { f(v(a)) };
            guard(format!("{ARM}.{name} {}", q(v(a))), q(r));
        }
    }

    let exts: [Binary; 16] = [
        ext::<0>, ext::<1>, ext::<2>, ext::<3>, ext::<4>, ext::<5>, ext::<6>, ext::<7>,
        ext::<8>, ext::<9>, ext::<10>, ext::<11>, ext::<12>, ext::<13>, ext::<14>, ext::<15>,
    ];
    for (imm, f) in exts.iter().enumerate() {
        for (a, b) in [(inputs[1], 0), (rng.u128(), rng.u128())] {
            let r = unsafe { f(v(a), v(b)) };
            guard(
                format!("{ARM}.vextq_u8 ⟨{imm}#32⟩ {} {}", q(v(a)), q(v(b))),
                q(r),
            );
        }
    }
    let lanes: [Unary; 4] = [dup_lane::<0>, dup_lane::<1>, dup_lane::<2>, dup_lane::<3>];
    for (imm, f) in lanes.iter().enumerate() {
        let a = rng.u128();
        let r = unsafe { f(v(a)) };
        guard(format!("{ARM}.vdupq_laneq_u32 ⟨{imm}#32⟩ {}", q(v(a))), q(r));
    }

    for &a in &inputs {
        let (b, w) = (a as u8, a as u32);
        guard(format!("{ARM}.vdupq_n_u8 ⟨{b}#8⟩"), q(unsafe { vdupq_n_u8(b) }));
        let r = unsafe { vreinterpretq_u8_u32(vdupq_n_u32(w)) };
        guard(format!("{ARM}.vdupq_n_u32 ⟨{w}#32⟩"), q(r));
        let r = unsafe { vreinterpretq_u8_p128(a) };
        guard(format!("{ARM}.vreinterpretq_u8_p128 ⟨{a:#x}#128⟩"), q(r));
        let r = unsafe { vreinterpretq_p128_u8(v(a)) };
        guard(
            format!("((·.bv) <$> {ARM}.vreinterpretq_p128_u8 {})", q(v(a))),
            format!("{r:#x}#128"),
        );
    }
    print!("{out}");
}
