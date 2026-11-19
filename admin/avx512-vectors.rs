//! Runs each AVX-512, VAES, and VPCLMULQDQ intrinsic
//! `proofs/Rind/X86_64/Simd.lean` models on this CPU and prints a Lean file
//! of `#guard`s that each model computes what the instruction did: every
//! immediate the instruction reads, zero and all-ones lanes, and random
//! inputs from a fixed seed. Its output is committed as
//! `proofs/Rind/X86_64/Avx512Vectors.lean`, which `admin/prove` checks on any
//! host, and reruns, failing if the output differs, on a CPU with these
//! instructions.
//!
//! Usage: rustc --edition 2024 -O admin/avx512-vectors.rs && ./avx512-vectors

#[cfg(not(target_arch = "x86_64"))]
compile_error!("the x86_64 intrinsics run only on x86_64");

use std::arch::x86_64::*;
use std::fmt::Write;
use std::mem::transmute;

type Binary = unsafe fn(__m512i, __m512i) -> __m512i;
type Unary = unsafe fn(__m512i) -> __m512i;
type Ternary = unsafe fn(__m512i, __m512i, __m512i) -> __m512i;
type Ternary128 = unsafe fn(__m128i, __m128i, __m128i) -> __m128i;

macro_rules! imm8 {
    ($f:ident) => {
        [
            $f::<0>, $f::<1>, $f::<2>, $f::<3>, $f::<4>, $f::<5>, $f::<6>, $f::<7>, $f::<8>,
            $f::<9>, $f::<10>, $f::<11>, $f::<12>, $f::<13>, $f::<14>, $f::<15>, $f::<16>,
            $f::<17>, $f::<18>, $f::<19>, $f::<20>, $f::<21>, $f::<22>, $f::<23>, $f::<24>,
            $f::<25>, $f::<26>, $f::<27>, $f::<28>, $f::<29>, $f::<30>, $f::<31>, $f::<32>,
            $f::<33>, $f::<34>, $f::<35>, $f::<36>, $f::<37>, $f::<38>, $f::<39>, $f::<40>,
            $f::<41>, $f::<42>, $f::<43>, $f::<44>, $f::<45>, $f::<46>, $f::<47>, $f::<48>,
            $f::<49>, $f::<50>, $f::<51>, $f::<52>, $f::<53>, $f::<54>, $f::<55>, $f::<56>,
            $f::<57>, $f::<58>, $f::<59>, $f::<60>, $f::<61>, $f::<62>, $f::<63>, $f::<64>,
            $f::<65>, $f::<66>, $f::<67>, $f::<68>, $f::<69>, $f::<70>, $f::<71>, $f::<72>,
            $f::<73>, $f::<74>, $f::<75>, $f::<76>, $f::<77>, $f::<78>, $f::<79>, $f::<80>,
            $f::<81>, $f::<82>, $f::<83>, $f::<84>, $f::<85>, $f::<86>, $f::<87>, $f::<88>,
            $f::<89>, $f::<90>, $f::<91>, $f::<92>, $f::<93>, $f::<94>, $f::<95>, $f::<96>,
            $f::<97>, $f::<98>, $f::<99>, $f::<100>, $f::<101>, $f::<102>, $f::<103>, $f::<104>,
            $f::<105>, $f::<106>, $f::<107>, $f::<108>, $f::<109>, $f::<110>, $f::<111>, $f::<112>,
            $f::<113>, $f::<114>, $f::<115>, $f::<116>, $f::<117>, $f::<118>, $f::<119>, $f::<120>,
            $f::<121>, $f::<122>, $f::<123>, $f::<124>, $f::<125>, $f::<126>, $f::<127>, $f::<128>,
            $f::<129>, $f::<130>, $f::<131>, $f::<132>, $f::<133>, $f::<134>, $f::<135>, $f::<136>,
            $f::<137>, $f::<138>, $f::<139>, $f::<140>, $f::<141>, $f::<142>, $f::<143>, $f::<144>,
            $f::<145>, $f::<146>, $f::<147>, $f::<148>, $f::<149>, $f::<150>, $f::<151>, $f::<152>,
            $f::<153>, $f::<154>, $f::<155>, $f::<156>, $f::<157>, $f::<158>, $f::<159>, $f::<160>,
            $f::<161>, $f::<162>, $f::<163>, $f::<164>, $f::<165>, $f::<166>, $f::<167>, $f::<168>,
            $f::<169>, $f::<170>, $f::<171>, $f::<172>, $f::<173>, $f::<174>, $f::<175>, $f::<176>,
            $f::<177>, $f::<178>, $f::<179>, $f::<180>, $f::<181>, $f::<182>, $f::<183>, $f::<184>,
            $f::<185>, $f::<186>, $f::<187>, $f::<188>, $f::<189>, $f::<190>, $f::<191>, $f::<192>,
            $f::<193>, $f::<194>, $f::<195>, $f::<196>, $f::<197>, $f::<198>, $f::<199>, $f::<200>,
            $f::<201>, $f::<202>, $f::<203>, $f::<204>, $f::<205>, $f::<206>, $f::<207>, $f::<208>,
            $f::<209>, $f::<210>, $f::<211>, $f::<212>, $f::<213>, $f::<214>, $f::<215>, $f::<216>,
            $f::<217>, $f::<218>, $f::<219>, $f::<220>, $f::<221>, $f::<222>, $f::<223>, $f::<224>,
            $f::<225>, $f::<226>, $f::<227>, $f::<228>, $f::<229>, $f::<230>, $f::<231>, $f::<232>,
            $f::<233>, $f::<234>, $f::<235>, $f::<236>, $f::<237>, $f::<238>, $f::<239>, $f::<240>,
            $f::<241>, $f::<242>, $f::<243>, $f::<244>, $f::<245>, $f::<246>, $f::<247>, $f::<248>,
            $f::<249>, $f::<250>, $f::<251>, $f::<252>, $f::<253>, $f::<254>, $f::<255>,
        ]
    };
}

#[target_feature(enable = "avx512f")]
fn shuffle<const I: i32>(a: __m512i) -> __m512i {
    _mm512_shuffle_epi32::<I>(a)
}

#[target_feature(enable = "avx512f")]
fn ternary32<const I: i32>(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
    _mm512_ternarylogic_epi32::<I>(a, b, c)
}

#[target_feature(enable = "avx512f")]
fn ternary64<const I: i32>(a: __m512i, b: __m512i, c: __m512i) -> __m512i {
    _mm512_ternarylogic_epi64::<I>(a, b, c)
}

#[target_feature(enable = "avx512f,avx512vl")]
fn ternary128<const I: i32>(a: __m128i, b: __m128i, c: __m128i) -> __m128i {
    _mm_ternarylogic_epi32::<I>(a, b, c)
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn clmul<const I: i32>(a: __m512i, b: __m512i) -> __m512i {
    _mm512_clmulepi64_epi128::<I>(a, b)
}

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

    fn u512(&mut self) -> [u128; 4] {
        [self.u128(), self.u128(), self.u128(), self.u128()]
    }
}

/// A 512-bit vector of four 128-bit lanes, lane 0 first.
fn v(x: [u128; 4]) -> __m512i {
    unsafe { transmute(x) }
}

fn q(x: __m512i) -> String {
    let [a, b, c, d] = unsafe { transmute::<__m512i, [u128; 4]>(x) };
    format!("0x{d:032x}{c:032x}{b:032x}{a:032x}#512")
}

fn v128(x: u128) -> __m128i {
    unsafe { transmute(x) }
}

fn q128(x: __m128i) -> String {
    format!("0x{:032x}#128", unsafe { transmute::<__m128i, u128>(x) })
}

const F: &str = "core.core_arch.x86.avx512f";
const RANDOM: usize = 8;

fn main() {
    for feature in ["avx512f", "avx512bw", "avx512vl", "vaes", "vpclmulqdq"] {
        let present = match feature {
            "avx512f" => std::arch::is_x86_feature_detected!("avx512f"),
            "avx512bw" => std::arch::is_x86_feature_detected!("avx512bw"),
            "avx512vl" => std::arch::is_x86_feature_detected!("avx512vl"),
            "vaes" => std::arch::is_x86_feature_detected!("vaes"),
            _ => std::arch::is_x86_feature_detected!("vpclmulqdq"),
        };
        if !present {
            eprintln!("admin/avx512-vectors: this CPU lacks {feature}");
            std::process::exit(1);
        }
    }
    let mut rng = Rng(0x7269_6e64);
    let mut inputs = vec![[0; 4], [u128::MAX; 4], [0x8000_0000_8000_0000_8000_0000_8000_0000; 4]];
    inputs.extend((0..RANDOM).map(|_| rng.u512()));
    let pairs: Vec<([u128; 4], [u128; 4])> = inputs
        .iter()
        .flat_map(|&a| [(a, [0; 4]), (a, [u128::MAX; 4]), (a, rng.u512())])
        .collect();
    let mut out = String::from("import Rind.X86_64.Simd\nopen Aeneas Aeneas.Std Result\n\n");
    let mut guard = |call: String, result: String| {
        writeln!(out, "#guard reducesTo (R := BitVec _) ( {call} ) {result}").unwrap()
    };

    let binary: [(&str, Binary); 6] = [
        ("avx512f._mm512_xor_epi32", |a, b| unsafe { _mm512_xor_epi32(a, b) }),
        ("avx512f._mm512_xor_epi64", |a, b| unsafe { _mm512_xor_epi64(a, b) }),
        ("avx512f._mm512_add_epi32", |a, b| unsafe { _mm512_add_epi32(a, b) }),
        ("avx512bw._mm512_shuffle_epi8", |a, b| unsafe {
            _mm512_shuffle_epi8(a, b)
        }),
        ("vaes._mm512_aesenc_epi128", |a, b| unsafe {
            _mm512_aesenc_epi128(a, b)
        }),
        ("vaes._mm512_aesenclast_epi128", |a, b| unsafe {
            _mm512_aesenclast_epi128(a, b)
        }),
    ];
    for (name, f) in binary {
        for &(a, b) in &pairs {
            let r = unsafe { f(v(a), v(b)) };
            guard(format!("core.core_arch.x86.{name} {} {}", q(v(a)), q(v(b))), q(r));
        }
    }

    guard(format!("{F}._mm512_setzero_si512"), q(unsafe { _mm512_setzero_si512() }));
    for &a in &inputs {
        let lane = a[0] ^ a[3];
        guard(
            format!("{F}._mm512_broadcast_i32x4 {}", q128(v128(lane))),
            q(unsafe { _mm512_broadcast_i32x4(v128(lane)) }),
        );
        let b = v128(a[1]);
        let inserts = unsafe {
            [
                _mm512_inserti32x4::<0>(v(a), b),
                _mm512_inserti32x4::<1>(v(a), b),
                _mm512_inserti32x4::<2>(v(a), b),
                _mm512_inserti32x4::<3>(v(a), b),
            ]
        };
        let extracts = unsafe {
            [
                _mm512_extracti32x4_epi32::<0>(v(a)),
                _mm512_extracti32x4_epi32::<1>(v(a)),
                _mm512_extracti32x4_epi32::<2>(v(a)),
                _mm512_extracti32x4_epi32::<3>(v(a)),
            ]
        };
        for imm in 0..4 {
            guard(
                format!("{F}._mm512_inserti32x4 ⟨{imm}#32⟩ {} {}", q(v(a)), q128(b)),
                q(inserts[imm]),
            );
            guard(
                format!("{F}._mm512_extracti32x4_epi32 ⟨{imm}#32⟩ {}", q(v(a))),
                q128(extracts[imm]),
            );
        }
        for k in [0, u64::MAX, rng.u64(), u64::MAX >> (rng.u64() % 64)] {
            guard(
                format!("core.core_arch.x86.avx512bw._mm512_maskz_mov_epi8 ⟨{k}#64⟩ {}", q(v(a))),
                q(unsafe { _mm512_maskz_mov_epi8(k, v(a)) }),
            );
        }
    }

    // The immediates' sweeps run on one set of random inputs, named once:
    // random lanes hold every combination of bits each immediate selects.
    let (x, y, z) = (rng.u512(), rng.u512(), rng.u512());
    let (x1, y1, z1) = (rng.u128(), rng.u128(), rng.u128());
    for (name, a) in [("x", q(v(x))), ("y", q(v(y))), ("z", q(v(z)))] {
        writeln!(out, "private def {name} : BitVec 512 := {a}").unwrap();
    }
    for (name, a) in [("x1", q128(v128(x1))), ("y1", q128(v128(y1))), ("z1", q128(v128(z1)))] {
        writeln!(out, "private def {name} : BitVec 128 := {a}").unwrap();
    }
    let mut guard = |call: String, result: String| {
        writeln!(out, "#guard reducesTo (R := BitVec _) ( {call} ) {result}").unwrap()
    };
    let shuffles: [Unary; 256] = imm8!(shuffle);
    let clmuls: [Binary; 256] = imm8!(clmul);
    let ternary: [(&str, [Ternary; 256]); 2] = [
        ("_mm512_ternarylogic_epi32", imm8!(ternary32)),
        ("_mm512_ternarylogic_epi64", imm8!(ternary64)),
    ];
    let ternary128: [Ternary128; 256] = imm8!(ternary128);
    for imm in 0..256 {
        let r = unsafe { shuffles[imm](v(x)) };
        guard(format!("{F}._mm512_shuffle_epi32 ⟨{imm}#32⟩ x"), q(r));
        let r = unsafe { clmuls[imm](v(x), v(y)) };
        guard(format!("core.core_arch.x86.vpclmulqdq._mm512_clmulepi64_epi128 ⟨{imm}#32⟩ x y"), q(r));
        for (name, fs) in &ternary {
            let r = unsafe { fs[imm](v(x), v(y), v(z)) };
            guard(format!("{F}.{name} ⟨{imm}#32⟩ x y z"), q(r));
        }
        let r = unsafe { ternary128[imm](v128(x1), v128(y1), v128(z1)) };
        guard(format!("{F}._mm_ternarylogic_epi32 ⟨{imm}#32⟩ x1 y1 z1"), q128(r));
    }
    print!("{out}");
}
