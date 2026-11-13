// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Checks that every Rust source under `rind/src/` carries an SPDX license
//! identifier, and that `rind-python/LICENSE` is a byte-for-byte copy of
//! `rind/LICENSE`.
//!
//! Usage, from the workspace root: `cargo run -p rind-admin --bin scan-license --locked`

use std::io::{self, Write};
use std::process::ExitCode;

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(err) => {
            let _ = writeln!(io::stderr(), "scan-license: {err}");
            ExitCode::from(2)
        }
    }
}

fn run() -> io::Result<ExitCode> {
    let cwd = std::env::current_dir()?;
    let mut bad = false;

    for path in rind_admin::missing_spdx(&cwd.join("rind/src"), &cwd)? {
        println!("{} requires a SPDX-License-Identifier", path.display());
        bad = true;
    }

    let license = cwd.join("rind/LICENSE");
    let python_license = cwd.join("rind-python/LICENSE");
    if !rind_admin::files_identical(&license, &python_license)? {
        println!("rind-python/LICENSE must be a copy of rind/LICENSE");
        bad = true;
    }

    Ok(if bad {
        ExitCode::from(1)
    } else {
        ExitCode::SUCCESS
    })
}
