//! A criterion stand-in for running rind-bench's bench files inside an app.
//!
//! Row IDs are built exactly as criterion builds them (`group/function/param`),
//! so they match bench-report's OPERATIONS. Nothing is timed unless the
//! current [`Plan`] selects the row; in list mode only the IDs are recorded.
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::Display;
use std::time::{Duration, Instant};

pub use std::hint::black_box;

pub mod measurement {
    pub trait Measurement {}
    pub struct WallTime;
    impl Measurement for WallTime {}
}
use measurement::{Measurement, WallTime};

#[derive(Clone, Copy, Debug)]
pub enum Throughput {
    Bytes(u64),
    BytesDecimal(u64),
    Elements(u64),
    ElementsAndBytes { elements: u64, bytes: u64 },
}

#[derive(Clone, Copy, Debug)]
pub enum BatchSize {
    SmallInput,
    LargeInput,
    PerIteration,
    NumBatches(u64),
    NumIterations(u64),
}

#[derive(Clone, Copy, Debug)]
pub enum SamplingMode {
    Auto,
    Linear,
    Flat,
}

#[derive(Clone, Debug)]
pub struct BenchmarkId(String);
impl BenchmarkId {
    pub fn new<S: Into<String>, P: Display>(function_name: S, parameter: P) -> Self {
        BenchmarkId(format!("{}/{}", function_name.into(), parameter))
    }
    pub fn from_parameter<P: Display>(parameter: P) -> Self {
        BenchmarkId(format!("{parameter}"))
    }
}
pub trait IntoBenchmarkId {
    fn into_benchmark_id(self) -> String;
}
impl IntoBenchmarkId for BenchmarkId {
    fn into_benchmark_id(self) -> String {
        self.0
    }
}
impl IntoBenchmarkId for &str {
    fn into_benchmark_id(self) -> String {
        self.to_string()
    }
}
impl IntoBenchmarkId for String {
    fn into_benchmark_id(self) -> String {
        self
    }
}
impl IntoBenchmarkId for &String {
    fn into_benchmark_id(self) -> String {
        self.clone()
    }
}

/// One timed row.
#[derive(Clone, Debug)]
pub struct Sample {
    pub id: String,
    /// ns per iteration of each sample, in the order taken.
    pub samples_ns: Vec<f64>,
    pub iters_per_sample: u64,
    pub throughput: Option<Throughput>,
    pub error: Option<String>,
}

/// What the next pass over the bench functions does.
pub enum Mode {
    /// Record every row ID, time nothing.
    List,
    /// Time the rows in `select` (all rows when `None`).
    Run { select: Option<HashSet<String>>, warm_ms: u64, sample_ms: u64, samples: usize },
}

pub struct Plan {
    pub mode: Mode,
    pub listed: Vec<(String, Option<Throughput>)>,
    pub results: Vec<Sample>,
    /// Called before and after each timed row: (id, finished sample or None).
    pub on_row: Option<Box<dyn FnMut(&str, Option<&Sample>)>>,
    pub stop: Option<fn() -> bool>,
}

thread_local! {
    static PLAN: RefCell<Option<Plan>> = const { RefCell::new(None) };
}

/// Runs `f` (which calls bench files' `main`s) under `plan` and returns the plan.
pub fn with_plan<F: FnOnce()>(plan: Plan, f: F) -> Plan {
    PLAN.with(|p| *p.borrow_mut() = Some(plan));
    f();
    PLAN.with(|p| p.borrow_mut().take()).unwrap()
}

fn stopping() -> bool {
    PLAN.with(|p| p.borrow().as_ref().and_then(|p| p.stop).is_some_and(|s| s()))
}

fn run_row(id: String, throughput: Option<Throughput>, f: &mut dyn FnMut(&mut Bencher<'_, WallTime>)) {
    let action = PLAN.with(|p| {
        let mut p = p.borrow_mut();
        let Some(plan) = p.as_mut() else { return None };
        match &plan.mode {
            Mode::List => {
                plan.listed.push((id.clone(), throughput));
                None
            }
            Mode::Run { select, warm_ms, sample_ms, samples } => {
                if select.as_ref().is_some_and(|s| !s.contains(&id)) {
                    None
                } else {
                    Some((*warm_ms, *sample_ms, *samples))
                }
            }
        }
    });
    let Some((warm_ms, sample_ms, samples)) = action else { return };
    if stopping() {
        return;
    }
    // Notify start (without holding the borrow while the callback runs).
    let mut cb = PLAN.with(|p| p.borrow_mut().as_mut().and_then(|p| p.on_row.take()));
    if let Some(cb) = cb.as_mut() {
        cb(&id, None);
    }
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| measure(f, warm_ms, sample_ms, samples)));
    let sample = match r {
        Ok(Ok((samples_ns, iters))) => Sample { id: id.clone(), samples_ns, iters_per_sample: iters, throughput, error: None },
        Ok(Err(e)) => Sample { id: id.clone(), samples_ns: vec![], iters_per_sample: 0, throughput, error: Some(e) },
        Err(e) => {
            let msg = e
                .downcast_ref::<String>()
                .cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_else(|| "panic".into());
            Sample { id: id.clone(), samples_ns: vec![], iters_per_sample: 0, throughput, error: Some(format!("panicked: {msg}")) }
        }
    };
    if let Some(cb) = cb.as_mut() {
        cb(&id, Some(&sample));
    }
    PLAN.with(|p| {
        if let Some(plan) = p.borrow_mut().as_mut() {
            plan.results.push(sample);
            if plan.on_row.is_none() {
                plan.on_row = cb;
            }
        }
    });
}

/// Warm up for `warm_ms` (doubling the iteration count), then take `samples`
/// samples of a fixed iteration count sized to about `sample_ms` each.
fn measure(f: &mut dyn FnMut(&mut Bencher<'_, WallTime>), warm_ms: u64, sample_ms: u64, samples: usize) -> Result<(Vec<f64>, u64), String> {
    let mut iters = 1u64;
    let warm_start = Instant::now();
    let mut per_iter;
    loop {
        let mut b = Bencher { iters, elapsed: Duration::ZERO, ran: false, _m: std::marker::PhantomData };
        f(&mut b);
        if !b.ran {
            return Err("bench closure never called iter".into());
        }
        per_iter = b.elapsed.as_nanos() as f64 / iters as f64;
        if warm_start.elapsed() >= Duration::from_millis(warm_ms) {
            break;
        }
        if stopping() {
            return Err("stopped".into());
        }
        iters = iters.saturating_mul(2);
    }
    let target = (sample_ms as f64 * 1e6 / per_iter.max(1.0)).max(1.0) as u64;
    let mut out = Vec::with_capacity(samples);
    for _ in 0..samples {
        if stopping() {
            return Err("stopped".into());
        }
        let mut b = Bencher { iters: target, elapsed: Duration::ZERO, ran: false, _m: std::marker::PhantomData };
        f(&mut b);
        out.push(b.elapsed.as_nanos() as f64 / target as f64);
    }
    Ok((out, target))
}

pub struct Bencher<'a, M: Measurement = WallTime> {
    iters: u64,
    elapsed: Duration,
    ran: bool,
    _m: std::marker::PhantomData<&'a M>,
}

impl<M: Measurement> Bencher<'_, M> {
    pub fn iter<O, R: FnMut() -> O>(&mut self, mut routine: R) {
        self.ran = true;
        let t = Instant::now();
        for _ in 0..self.iters {
            black_box(routine());
        }
        self.elapsed = t.elapsed();
    }
    pub fn iter_with_large_drop<O, R: FnMut() -> O>(&mut self, routine: R) {
        self.iter(routine)
    }
    pub fn iter_custom<R: FnMut(u64) -> Duration>(&mut self, mut routine: R) {
        self.ran = true;
        self.elapsed = routine(self.iters);
    }
    pub fn iter_batched<I, O, S: FnMut() -> I, R: FnMut(I) -> O>(&mut self, mut setup: S, mut routine: R, _size: BatchSize) {
        self.ran = true;
        let mut total = Duration::ZERO;
        // Batches of up to 64 inputs, set up untimed, as criterion's SmallInput does.
        let mut left = self.iters;
        while left > 0 {
            let n = left.min(64);
            let inputs: Vec<I> = (0..n).map(|_| setup()).collect();
            let mut outs = Vec::with_capacity(n as usize);
            let t = Instant::now();
            for i in inputs {
                outs.push(black_box(routine(i)));
            }
            total += t.elapsed();
            drop(outs);
            left -= n;
        }
        self.elapsed = total;
    }
    pub fn iter_batched_ref<I, O, S: FnMut() -> I, R: FnMut(&mut I) -> O>(&mut self, mut setup: S, mut routine: R, _size: BatchSize) {
        self.ran = true;
        let mut total = Duration::ZERO;
        let mut left = self.iters;
        while left > 0 {
            let n = left.min(64);
            let mut inputs: Vec<I> = (0..n).map(|_| setup()).collect();
            let mut outs = Vec::with_capacity(n as usize);
            let t = Instant::now();
            for i in inputs.iter_mut() {
                outs.push(black_box(routine(i)));
            }
            total += t.elapsed();
            drop(outs);
            left -= n;
        }
        self.elapsed = total;
    }
}

#[derive(Default)]
pub struct Criterion {
    _p: (),
}

impl Criterion {
    pub fn benchmark_group<S: Into<String>>(&mut self, name: S) -> BenchmarkGroup<'_, WallTime> {
        BenchmarkGroup { _c: self, name: name.into(), throughput: None, _m: std::marker::PhantomData }
    }
    pub fn bench_function<ID: IntoBenchmarkId, F: FnMut(&mut Bencher<'_, WallTime>)>(&mut self, id: ID, mut f: F) -> &mut Self {
        run_row(id.into_benchmark_id(), None, &mut f);
        self
    }
    pub fn bench_with_input<ID: IntoBenchmarkId, I: ?Sized, F: FnMut(&mut Bencher<'_, WallTime>, &I)>(&mut self, id: ID, input: &I, mut f: F) -> &mut Self {
        run_row(id.into_benchmark_id(), None, &mut |b| f(b, input));
        self
    }
    pub fn sample_size(self, _n: usize) -> Self {
        self
    }
    pub fn measurement_time(self, _d: Duration) -> Self {
        self
    }
    pub fn warm_up_time(self, _d: Duration) -> Self {
        self
    }
    pub fn configure_from_args(self) -> Self {
        self
    }
    pub fn final_summary(&mut self) {}
}

pub struct BenchmarkGroup<'a, M: Measurement = WallTime> {
    _c: &'a mut Criterion,
    name: String,
    throughput: Option<Throughput>,
    _m: std::marker::PhantomData<M>,
}

impl<M: Measurement> BenchmarkGroup<'_, M> {
    pub fn throughput(&mut self, t: Throughput) -> &mut Self {
        self.throughput = Some(t);
        self
    }
    pub fn sample_size(&mut self, _n: usize) -> &mut Self {
        self
    }
    pub fn measurement_time(&mut self, _d: Duration) -> &mut Self {
        self
    }
    pub fn warm_up_time(&mut self, _d: Duration) -> &mut Self {
        self
    }
    pub fn sampling_mode(&mut self, _m: SamplingMode) -> &mut Self {
        self
    }
    pub fn noise_threshold(&mut self, _t: f64) -> &mut Self {
        self
    }
    pub fn bench_function<ID: IntoBenchmarkId, F: FnMut(&mut Bencher<'_, WallTime>)>(&mut self, id: ID, mut f: F) -> &mut Self {
        run_row(format!("{}/{}", self.name, id.into_benchmark_id()), self.throughput, &mut f);
        self
    }
    pub fn bench_with_input<ID: IntoBenchmarkId, I: ?Sized, F: FnMut(&mut Bencher<'_, WallTime>, &I)>(&mut self, id: ID, input: &I, mut f: F) -> &mut Self {
        run_row(format!("{}/{}", self.name, id.into_benchmark_id()), self.throughput, &mut |b| f(b, input));
        self
    }
    pub fn finish(self) {}
}

/// `criterion_group!(name, f1, f2, ...)` (and the `name = ...; config = ...;
/// targets = ...` form): a `pub fn name()` that runs each target once.
#[macro_export]
macro_rules! criterion_group {
    (name = $name:ident; config = $config:expr; targets = $( $target:path ),+ $(,)*) => {
        pub fn $name() {
            let mut c: $crate::Criterion = $config;
            $( $target(&mut c); )+
        }
    };
    ($name:ident, $( $target:path ),+ $(,)*) => {
        pub fn $name() {
            let mut c = $crate::Criterion::default();
            $( $target(&mut c); )+
        }
    };
}

/// `criterion_main!(g1, g2)`: a `pub fn main()` the app calls per pass.
#[macro_export]
macro_rules! criterion_main {
    ( $( $group:path ),+ $(,)* ) => {
        pub fn main() {
            $( $group(); )+
        }
    };
}
