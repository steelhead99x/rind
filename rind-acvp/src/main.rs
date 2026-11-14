// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

fn main() {
    if let Err(err) = rind_acvp::serve() {
        eprintln!("rind-acvp: {err}");
        std::process::exit(1);
    }
}
