//! Statistical timing tests of rind's secret operations, on the hardware it
//! runs on. `admin/timing` runs them; see it for how.

mod cases;
mod dudect;
mod marvin;
mod rsa_keys;

use std::process::ExitCode;

const USAGE: &str = "usage:
  rind-timing dudect [--seconds S] [--list] [FILTER...]
      times each case whose name contains a FILTER (every case without one),
      after the planted leak, for at least S seconds each (default 10) and
      until its second-order test has 10,000 measurements
  rind-timing marvin KEY CIPHERTEXTS OUT
      times the RSA-OAEP decryption of each ciphertext the Marvin toolkit wrote";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.first().map(String::as_str) {
        Some("dudect") => dudect(&args[1..]),
        Some("marvin") => match &args[1..] {
            [key, ciphertexts, out] => marvin::run(key, ciphertexts, out),
            _ => Err(USAGE.into()),
        },
        _ => Err(USAGE.into()),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("rind-timing: {e}");
            ExitCode::FAILURE
        }
    }
}

fn dudect(mut args: &[String]) -> Result<(), String> {
    let mut seconds = 10.0;
    let mut list = false;
    let mut filters = Vec::new();
    while let [arg, rest @ ..] = args {
        args = rest;
        match arg.as_str() {
            "--list" => list = true,
            "--seconds" => {
                let [value, rest @ ..] = args else {
                    return Err(USAGE.into());
                };
                args = rest;
                seconds = value
                    .parse()
                    .ok()
                    .filter(|s: &f64| s.is_finite() && *s >= 0.0)
                    .ok_or_else(|| format!("--seconds: not a duration: {value}"))?;
            }
            _ if arg.starts_with('-') => return Err(USAGE.into()),
            _ => filters.push(arg.as_str()),
        }
    }

    let mut all = cases::all().into_iter();
    let planted = all.next().unwrap();
    let cases: Vec<_> = all
        .filter(|case| filters.is_empty() || filters.iter().any(|f| case.name.contains(f)))
        .collect();
    if cases.is_empty() {
        return Err(format!("no case matches {filters:?}"));
    }
    if list {
        for case in &cases {
            println!("{}", case.name);
        }
        return Ok(());
    }

    let config = dudect::Config {
        seconds,
        ticks_per_second: dudect::ticks_per_second(),
    };
    println!(
        "counter: {:.1} MHz; a case leaks when |t| > {}",
        config.ticks_per_second as f64 / 1e6,
        dudect::THRESHOLD
    );
    println!(
        "{:<44} {:>11} {:>5} {:>9} {:>11}  test",
        "case", "measured", "reps", "t", "ticks/call"
    );
    let mut failed = Vec::new();
    for (i, case) in std::iter::once(planted).chain(cases).enumerate() {
        let report = (case.run)(&config);
        // The planted leak must be found, and nothing else may leak.
        let ok = report.leaks() == (i == 0);
        println!(
            "{:<44} {:>11} {:>5} {:>+9.2} {:>+11.3}  {}{}",
            case.name,
            report.measurements,
            report.reps,
            report.t,
            report.delta,
            report.test,
            match (ok, i) {
                (true, _) => "",
                (false, 0) => "  MISSED",
                (false, _) => "  LEAK",
            }
        );
        if !ok {
            failed.push(case.name);
        }
    }
    if failed.is_empty() {
        Ok(())
    } else {
        Err(format!("failed: {}", failed.join(", ")))
    }
}
