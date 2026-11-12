//! Runs each x86_64 intrinsic `proofs/Rind/X86_64/Simd.lean` models on this
//! CPU and prints a Lean file of `#guard`s that each model computes what the
//! instruction did: every immediate the instruction reads, zero and all-ones
//! lanes, and random inputs from a fixed seed. `admin/prove` builds and
//! checks it, so the instructions run on the machine that checks the models.
//!
//! Usage: rustc --edition 2024 -O admin/simd-vectors.rs && ./simd-vectors

#[cfg(not(target_arch = "x86_64"))]
compile_error!("the x86_64 intrinsics run only on x86_64");

use std::arch::x86_64::*;
use std::fmt::Write;
use std::mem::transmute;

type Unary = unsafe fn(__m128i) -> __m128i;
type Binary = unsafe fn(__m128i, __m128i) -> __m128i;

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

#[target_feature(enable = "sse2")]
fn srai<const I: i32>(a: __m128i) -> __m128i {
    _mm_srai_epi32::<I>(a)
}

#[target_feature(enable = "sse2")]
fn shuffle<const I: i32>(a: __m128i) -> __m128i {
    _mm_shuffle_epi32::<I>(a)
}

#[target_feature(enable = "sse2")]
fn slli<const I: i32>(a: __m128i) -> __m128i {
    _mm_slli_si128::<I>(a)
}

#[target_feature(enable = "pclmulqdq")]
fn clmul<const I: i32>(a: __m128i, b: __m128i) -> __m128i {
    _mm_clmulepi64_si128::<I>(a, b)
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
}

fn v(x: u128) -> __m128i {
    unsafe { transmute(x) }
}

fn q(x: __m128i) -> String {
    format!("0x{:032x}#128", unsafe { transmute::<__m128i, u128>(x) })
}

const SSE2: &str = "core.core_arch.x86.sse2";
const RANDOM: usize = 64;

fn main() {
    let features = [
        ("sse2", std::arch::is_x86_feature_detected!("sse2")),
        ("ssse3", std::arch::is_x86_feature_detected!("ssse3")),
        (
            "pclmulqdq",
            std::arch::is_x86_feature_detected!("pclmulqdq"),
        ),
        ("aes", std::arch::is_x86_feature_detected!("aes")),
    ];
    for (feature, present) in features {
        if !present {
            eprintln!("admin/simd-vectors: this CPU lacks {feature}");
            std::process::exit(1);
        }
    }
    let mut rng = Rng(0x7269_6e64);
    let mut inputs = vec![0, u128::MAX, 0x8000_0000_8000_0000_8000_0000_8000_0000];
    inputs.extend((0..RANDOM).map(|_| rng.u128()));
    let pairs: Vec<(u128, u128)> = inputs
        .iter()
        .flat_map(|&a| [(a, 0), (a, u128::MAX), (a, rng.u128())])
        .collect();
    let mut out = String::from("import Rind.X86_64.Simd\nopen Aeneas Aeneas.Std Result\n\n");
    let mut guard = |call: String, result: String| {
        writeln!(out, "#guard reducesTo (R := BitVec _) ( {call} ) {result}").unwrap()
    };

    let binary: [(&str, Binary); 7] = [
        ("sse2._mm_xor_si128", |a, b| unsafe { _mm_xor_si128(a, b) }),
        ("sse2._mm_and_si128", |a, b| unsafe { _mm_and_si128(a, b) }),
        ("sse2._mm_add_epi64", |a, b| unsafe { _mm_add_epi64(a, b) }),
        ("sse2._mm_unpackhi_epi64", |a, b| unsafe {
            _mm_unpackhi_epi64(a, b)
        }),
        ("ssse3._mm_shuffle_epi8", |a, b| unsafe {
            _mm_shuffle_epi8(a, b)
        }),
        ("aes._mm_aesenc_si128", |a, b| unsafe {
            _mm_aesenc_si128(a, b)
        }),
        ("aes._mm_aesenclast_si128", |a, b| unsafe {
            _mm_aesenclast_si128(a, b)
        }),
    ];
    for (name, f) in binary {
        for &(a, b) in &pairs {
            let r = unsafe { f(v(a), v(b)) };
            guard(
                format!("core.core_arch.x86.{name} {} {}", q(v(a)), q(v(b))),
                q(r),
            );
        }
    }

    let unary: [(&str, [Unary; 256]); 3] = [
        ("_mm_srai_epi32", imm8!(srai)),
        ("_mm_shuffle_epi32", imm8!(shuffle)),
        ("_mm_slli_si128", imm8!(slli)),
    ];
    for (name, fs) in unary {
        for (imm, f) in fs.iter().enumerate() {
            for a in [inputs[1], inputs[2], rng.u128()] {
                let r = unsafe { f(v(a)) };
                guard(format!("{SSE2}.{name} ⟨{imm}#32⟩ {}", q(v(a))), q(r));
            }
        }
    }
    let clmuls: [Binary; 256] = imm8!(clmul);
    for (imm, f) in clmuls.iter().enumerate() {
        for (a, b) in [(inputs[1], inputs[1]), (rng.u128(), rng.u128())] {
            let r = unsafe { f(v(a), v(b)) };
            guard(
                format!(
                    "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 ⟨{imm}#32⟩ {} {}",
                    q(v(a)),
                    q(v(b))
                ),
                q(r),
            );
        }
    }

    guard(
        format!("{SSE2}._mm_setzero_si128"),
        q(unsafe { _mm_setzero_si128() }),
    );
    for &a in &inputs {
        let b: [i8; 16] = unsafe { transmute(a) };
        let r = unsafe {
            _mm_setr_epi8(
                b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9], b[10], b[11], b[12],
                b[13], b[14], b[15],
            )
        };
        let args: Vec<String> = b.iter().map(|x| format!("⟨{}#8⟩", *x as u8)).collect();
        guard(format!("{SSE2}._mm_setr_epi8 {}", args.join(" ")), q(r));
        let (hi, lo) = ((a >> 64) as i64, a as i64);
        let r = unsafe { _mm_set_epi64x(hi, lo) };
        guard(
            format!(
                "{SSE2}._mm_set_epi64x ⟨{}#64⟩ ⟨{}#64⟩",
                hi as u64, lo as u64
            ),
            q(r),
        );
        let w = a as i32;
        guard(
            format!("{SSE2}._mm_set1_epi32 ⟨{}#32⟩", w as u32),
            q(unsafe { _mm_set1_epi32(w) }),
        );
        let r = unsafe { _mm_cvtsi128_si64(v(a)) };
        guard(
            format!(
                "((·.bv) <$> core.core_arch.x86_64.sse2._mm_cvtsi128_si64 {})",
                q(v(a))
            ),
            format!("{}#64", r as u64),
        );
    }
    print!("{out}");
}
