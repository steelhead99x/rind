// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ESP32-C6 status and benchmark firmware for rind.
//!
//! Shows its state on the board's LED (blue running, green every check passed,
//! red a check failed or a panic), runs the known-answer checks, then rind's
//! operations for a few rounds, and prints every result over USB-Serial-JTAG,
//! repeating the summary every five seconds so a monitor opened later sees it.
//!
//! The LED is tried two ways, because the board is not identified: a WS2812 on
//! GPIO8 (ESP32-C6-DevKitC-1) and a plain active-low LED on GPIO15 (XIAO
//! ESP32-C6), which blinks fast while running, stays on when all passed, and
//! blinks slowly on failure. Which one lit is for the person at the board.

#![no_std]
#![no_main]

extern crate alloc;

use alloc::string::String;
use core::fmt::Write as _;
use core::num::NonZeroU32;
use esp_hal::{
    clock::CpuClock,
    gpio::{Level, Output, OutputConfig},
    main,
    rmt::{PulseCode, Rmt, TxChannelConfig, TxChannelCreator},
    rng::Rng,
    time::{Duration, Instant, Rate},
};
use esp_println::println;
#[cfg(feature = "bench")]
use rind_esp32c6::bench::{self, Clock};

esp_bootloader_esp_idf::esp_app_desc!();

const ROUNDS: NonZeroU32 = NonZeroU32::new(7).unwrap();

#[unsafe(no_mangle)]
unsafe extern "Rust" fn __getrandom_v03_custom(
    dest: *mut u8,
    len: usize,
) -> Result<(), getrandom::Error> {
    // The hardware RNG is a true random source only while the radio or the SAR
    // ADC is on, which this firmware does not turn on: these bytes are for the
    // round-trip checks and the benchmark, not for keys.
    let rng = Rng::new();
    for i in 0..len {
        unsafe { dest.add(i).write(rng.random() as u8) };
    }
    Ok(())
}

unsafe extern "C" {
    /// The end of .bss, where the heap array ends and the stack's room begins.
    static _stack_end: u8;
}

#[cfg(feature = "bench")]
struct Timer;
#[cfg(feature = "bench")]
impl Clock for Timer {
    fn now_ns(&mut self) -> u64 {
        Instant::now().duration_since_epoch().as_micros() * 1000
    }

    fn free(&mut self) -> (usize, usize) {
        let marker = 0u8;
        let sp = core::ptr::addr_of!(marker) as usize;
        let floor = core::ptr::addr_of!(_stack_end) as usize;
        (esp_alloc::HEAP.free(), sp.saturating_sub(floor))
    }
}

#[panic_handler]
fn panic(info: &core::panic::PanicInfo) -> ! {
    println!("RIND-FW v1 panic {info}");
    // Reset after a short wait so the message is read and the board retries.
    let t = Instant::now();
    while t.elapsed() < Duration::from_millis(3000) {}
    esp_hal::system::software_reset()
}

fn wait_ms(ms: u64) {
    let t = Instant::now();
    while t.elapsed() < Duration::from_millis(ms) {}
}

#[derive(Clone, Copy, PartialEq)]
enum State {
    Running,
    Passed,
    Failed,
}

struct Leds<'a> {
    rgb: Option<esp_hal::rmt::Channel<'a, esp_hal::Blocking, esp_hal::rmt::Tx>>,
    plain: Output<'a>,
}

impl Leds<'_> {
    fn show(&mut self, s: State) {
        // WS2812 order is green, red, blue.
        let (g, r, b) = match s {
            State::Running => (0, 0, 24),
            State::Passed => (24, 0, 0),
            State::Failed => (0, 24, 0),
        };
        let bit = |v: bool| {
            if v {
                PulseCode::new(Level::High, 64, Level::Low, 36)
            } else {
                PulseCode::new(Level::High, 32, Level::Low, 68)
            }
        };
        let mut data = [PulseCode::end_marker(); 25];
        for (i, byte) in [g, r, b].into_iter().enumerate() {
            for k in 0..8u8 {
                data[i * 8 + usize::from(k)] = bit(byte & (0x80 >> k) != 0);
            }
        }
        if let Some(ch) = self.rgb.take() {
            self.rgb = match ch.transmit(&data) {
                Ok(t) => t.wait().ok(),
                Err((_, ch)) => Some(ch),
            };
        }
        // Active low: Passed is on, Running and Failed blink in `blink`.
        if s == State::Passed {
            self.plain.set_low();
        }
    }

    fn blink(&mut self, s: State, ms: u64) {
        match s {
            State::Passed => self.plain.set_low(),
            _ => self.plain.toggle(),
        }
        wait_ms(ms);
    }
}

#[main]
fn main() -> ! {
    let p = esp_hal::init(esp_hal::Config::default().with_cpu_clock(CpuClock::max()));
    esp_alloc::heap_allocator!(size: 140 * 1024);

    let rmt = Rmt::new(p.RMT, Rate::from_mhz(80)).ok();
    let rgb = rmt.and_then(|r| {
        r.channel0
            .configure_tx(&TxChannelConfig::default().with_clk_divider(1))
            .ok()
            .map(|c| c.with_pin(p.GPIO8))
    });
    let mut leds = Leds {
        rgb,
        plain: Output::new(p.GPIO15, Level::High, OutputConfig::default()),
    };

    leds.show(State::Running);
    println!("RIND-FW v1 start target=esp32c6 cpu_mhz=160 rind=0.3.2");

    let mut failed = 0u32;
    let mut kats = 0u32;
    let mut summary = String::new();
    for kat in rind_esp32c6::all() {
        leds.blink(State::Running, 10);
        let ok = (kat.run)();
        kats += 1;
        if !ok {
            failed += 1;
        }
        let _ = writeln!(
            summary,
            "RIND-KAT v1 {} {}",
            kat.name,
            if ok { "ok" } else { "FAIL" }
        );
    }
    println!("{summary}");

    #[allow(unused_mut)]
    let mut rows = String::new();
    #[allow(unused_mut)]
    let mut row_count = 0u32;
    #[cfg(feature = "bench")]
    {
        let mut timer = Timer;
        bench::run_all(&mut timer, ROUNDS, 1, |r| {
            let _ = writeln!(rows, "{}", r.line());
            row_count += 1;
            leds.blink(State::Running, 1);
        });
        rind_esp32c6::vendors::run_all(&mut timer, ROUNDS, 1, |r| {
            let _ = writeln!(rows, "{}", r.line());
            row_count += 1;
            leds.blink(State::Running, 1);
        });
    }
    let state = if failed == 0 {
        State::Passed
    } else {
        State::Failed
    };
    leds.show(state);
    loop {
        // The counts let the ingest tell a whole copy from one cut off.
        println!(
            "RIND-FW v1 done failed={failed} cpu_mhz=160 rounds={ROUNDS} kats={kats} rows={row_count}"
        );
        println!("{summary}{rows}");
        for _ in 0..10 {
            leds.blink(state, if state == State::Failed { 250 } else { 500 });
        }
    }
}
