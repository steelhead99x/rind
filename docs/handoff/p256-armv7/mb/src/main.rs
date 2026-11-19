use std::hint::black_box;
use std::time::Instant;

pub mod p256 {
    pub const P: [u64; 4] = [0xffff_ffff_ffff_ffff, 0x0000_0000_ffff_ffff, 0, 0xffff_ffff_0000_0001];
    pub const N: [u64; 4] = [0xf3b9_cac2_fc63_2551, 0xbce6_faad_a717_9e84, 0xffff_ffff_ffff_ffff, 0xffff_ffff_0000_0000];
    #[derive(Clone, Copy)]
    pub struct Fe(pub [u32; 8]);
    #[derive(Clone, Copy)]
    pub struct Fs(pub [u32; 8]);
    pub fn opaque<T>(x: T) -> T { core::hint::black_box(x) }
    pub fn select_words(flag: u8, z: &[u32; 8], nz: &[u32; 8]) -> [u32; 8] {
        let m = 0u32.wrapping_sub(flag as u32);
        core::array::from_fn(|i| (nz[i] & m) | (z[i] & !m))
    }
    pub fn split(x: &[u64; 4]) -> [u32; 8] {
        core::array::from_fn(|i| (x[i / 2] >> (32 * (i % 2))) as u32)
    }
    pub fn sub(x: &[u32; 8], y: &[u32; 8]) -> ([u32; 8], u8) {
        let mut d = [0; 8];
        let mut b = 0u64;
        for i in 0..8 {
            let t = (x[i] as u64).wrapping_sub(y[i] as u64).wrapping_sub(b);
            d[i] = t as u32;
            b = t >> 63;
        }
        (d, b as u8)
    }
}
mod p256_mul32;
use p256::Fe;

std::arch::global_asm!(include_str!("field.s"), options(raw));

unsafe extern "C" {
    fn ecp_nistz256_mul_mont(r: *mut u32, a: *const u32, b: *const u32);
    fn ecp_nistz256_sqr_mont(r: *mut u32, a: *const u32);
    fn ecp_nistz256_add(r: *mut u32, a: *const u32, b: *const u32);
    fn ecp_nistz256_sub(r: *mut u32, a: *const u32, b: *const u32);
}

fn rnd(s: &mut u64) -> u32 { *s ^= *s << 13; *s ^= *s >> 7; *s ^= *s << 17; (*s >> 16) as u32 }

fn bench(name: &str, mut f: impl FnMut()) {
    let n = 200_000;
    for _ in 0..n { f(); }
    let mut v = vec![];
    for _ in 0..15 {
        let t = Instant::now();
        for _ in 0..n { f(); }
        v.push(t.elapsed().as_nanos() as f64 / n as f64);
    }
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    println!("{name} median_ns {:.2} min_ns {:.2} p90_ns {:.2}", v[7], v[0], v[13]);
}

fn main() {
    let mut s = 0x1234_5678_9abc_def1u64;
    // Agreement on random reduced inputs.
    let mut bad = 0;
    for _ in 0..20000 {
        let mut a: [u32; 8] = core::array::from_fn(|_| rnd(&mut s));
        let mut b: [u32; 8] = core::array::from_fn(|_| rnd(&mut s));
        a[7] &= 0x7fff_ffff; b[7] &= 0x7fff_ffff; // below p
        let mine = p256_mul32::fe_mul(&Fe(a), &Fe(b)).0;
        let mut r = [0u32; 8];
        unsafe { ecp_nistz256_mul_mont(r.as_mut_ptr(), a.as_ptr(), b.as_ptr()) };
        let msq = p256_mul32::fe_sqr(&Fe(a)).0;
        let mut r2 = [0u32; 8];
        unsafe { ecp_nistz256_sqr_mont(r2.as_mut_ptr(), a.as_ptr()) };
        if mine != r || msq != r2 { bad += 1; }
    }
    println!("mismatches {bad}/20000");
    let which = std::env::args().nth(1).unwrap_or_default();
    let mut x: [u32; 8] = core::array::from_fn(|_| rnd(&mut s)); x[7] &= 0x7fff_ffff;
    let mut y: [u32; 8] = core::array::from_fn(|_| rnd(&mut s)); y[7] &= 0x7fff_ffff;
    // Dependent chains: the product feeds the next.
    let reps = if which.is_empty() { 3 } else { 1 };
    for _ in 0..reps {
        let mut a = Fe(x);
        let yy = Fe(y);
        bench("rind fe_mul chain", || { a = p256_mul32::fe_mul(black_box(&a), &yy); });
        black_box(a);
        let mut r = x;
        bench("nistz mul_mont chain", || unsafe { let t = r; ecp_nistz256_mul_mont(r.as_mut_ptr(), t.as_ptr(), y.as_ptr()); });
        black_box(r);
        let mut a = Fe(x);
        bench("rind fe_sqr chain", || { a = p256_mul32::fe_sqr(black_box(&a)); });
        black_box(a);
        let mut r = x;
        bench("nistz sqr_mont chain", || unsafe { let t = r; ecp_nistz256_sqr_mont(r.as_mut_ptr(), t.as_ptr()); });
        black_box(r);
        {
            use fiat_crypto::p256_32 as fp;
            let mut a = fp::fiat_p256_montgomery_domain_field_element(x);
            let yy = fp::fiat_p256_montgomery_domain_field_element(y);
            bench("fiat add chain", || { let t = a; fp::fiat_p256_add(&mut a, black_box(&t), &yy); });
            black_box(a);
            let mut a = fp::fiat_p256_montgomery_domain_field_element(x);
            bench("fiat sub chain", || { let t = a; fp::fiat_p256_sub(&mut a, black_box(&t), &yy); });
            black_box(a);
            let mut a = fp::fiat_p256_montgomery_domain_field_element(x);
            bench("fiat opp chain", || { let t = a; fp::fiat_p256_opp(&mut a, black_box(&t)); });
            black_box(a);
        }
        let mut r = x;
        bench("nistz add chain", || unsafe { let t = r; ecp_nistz256_add(r.as_mut_ptr(), t.as_ptr(), y.as_ptr()); });
        black_box(r);
        let mut r = x;
        bench("nistz sub chain", || unsafe { let t = r; ecp_nistz256_sub(r.as_mut_ptr(), t.as_ptr(), y.as_ptr()); });
        black_box(r);
    }
}
