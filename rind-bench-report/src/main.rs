//! The `rind-bench-report` command. `admin/bench-report` stays the public entry point.

use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use rind_bench_report::{Paths, gate, render_check, render_write};

#[derive(Parser)]
#[command(
    name = "bench-report",
    about = "Times rind and the libraries it is compared with on the report's hosts."
)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Write BENCHMARKS.md and its SVGs from benchmarks/data.
    Render {
        /// First import a collection's measured hosts.
        #[arg(long = "from", value_name = "DIR")]
        from: Option<PathBuf>,
        /// Fail if BENCHMARKS.md or its SVGs are out of date.
        #[arg(long)]
        check: bool,
    },
    /// Fail on a nightly run's gap without a decision.
    Gate {
        /// The run's downloaded bench-* artifacts.
        dir: PathBuf,
        /// The previous run's, to fail only on a gap both show.
        #[arg(long, value_name = "DIR")]
        previous: Option<PathBuf>,
    },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let paths = Paths::discover();
    let result = match cli.command {
        Command::Render { from, check } => {
            if check {
                render_check(&paths)
            } else {
                render_write(&paths, from.as_deref())
            }
        }
        Command::Gate { dir, previous } => match gate(&dir, previous.as_deref(), &paths) {
            Ok(report) => {
                print!("{}", report.stdout);
                if let Some(message) = report.error {
                    Err(rind_bench_report::Error::new(message))
                } else {
                    Ok(())
                }
            }
            Err(err) => Err(err),
        },
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(err) => {
            eprintln!("bench-report: {err}");
            ExitCode::from(1)
        }
    }
}
