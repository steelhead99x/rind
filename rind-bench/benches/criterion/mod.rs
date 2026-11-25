#[cfg(feature = "__bench_codspeed")]
pub use codspeed_criterion_compat::*;
#[cfg(not(feature = "__bench_codspeed"))]
pub use criterion::*;

/// Message sizes for ciphers and AEADs: a short token, QUIC datagrams at and
/// near the common 1200- and 1350-byte MTUs, and a full TLS record.
#[allow(dead_code)]
pub const SIZES: [(usize, &str); 4] = [
    (32, "32B"),
    (1200, "1200B"),
    (1350, "1350B"),
    (16384, "16KB"),
];

/// Lengths between the 64 B and 1200 B that the other rows time, where rind's
/// AEADs switch kernels, so a threshold set wrong for a CPU shows only here.
#[allow(dead_code)]
const KERNEL_SIZES: [(usize, &str); 3] =
    [(128, "quic-128B"), (256, "quic-256B"), (512, "quic-512B")];

/// The AEAD benches' rows: each of [`SIZES`] under a 32 B AAD, then
/// [`KERNEL_SIZES`] under QUIC's 13 B short-header AAD.
#[allow(dead_code)]
pub fn aead_rows() -> impl Iterator<Item = (usize, &'static str, &'static [u8])> {
    let sized = SIZES.map(|(size, name)| (size, name, &[0u8; 32][..]));
    let kernel = KERNEL_SIZES.map(|(size, name)| (size, name, &[0u8; 13][..]));
    sized.into_iter().chain(kernel)
}

/// [`SIZES`], plus one hash block and a file-sized input, for hashes and MACs.
#[allow(dead_code)]
pub const HASH_SIZES: [(usize, &str); 6] = [
    (32, "32B"),
    (64, "64B"),
    (1200, "1200B"),
    (1350, "1350B"),
    (8192, "8KB"),
    (16384, "16KB"),
];

/// A [`rind::cpu::Dit`] guard for rind's rows to hold while they are timed:
/// on a CPU with DIT, the report times rind as a caller holding it across its
/// calls, as MoQ does. Elsewhere the guard does nothing.
#[allow(dead_code)]
pub fn rind_dit() -> rind::cpu::Dit {
    rind::cpu::Dit::hold()
}

/// A group for rind's rows timed again without [`rind_dit`], named
/// `dit-per-call/{name}`, so the report shows what a caller holding no guard
/// pays for rind setting DIT around each call. On every aarch64 target, the
/// one architecture with DIT; where the OS reports none, as on GitHub's
/// arm64 runners, they match the held rows. Elsewhere they could only ever
/// repeat the held ones.
#[allow(dead_code)]
pub fn dit_per_call<'a>(
    c: &'a mut Criterion,
    name: &str,
) -> Option<BenchmarkGroup<'a, measurement::WallTime>> {
    cfg!(target_arch = "aarch64").then(|| c.benchmark_group(format!("dit-per-call/{name}")))
}

/// The [`aead_rows`] that [`dit_per_call`] times: a short token and a QUIC
/// packet, where the toggle is the largest and a typical share of a call.
#[allow(dead_code)]
pub fn dit_per_call_aead_rows() -> impl Iterator<Item = (usize, &'static str, &'static [u8])> {
    aead_rows().filter(|(size, ..)| [32, 1350].contains(size))
}
