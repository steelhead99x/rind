// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Points the binary at the module `rind-fips` built, so `acvptool` can run
//! it outside cargo, which otherwise finds the module for its own runs only.

fn main() {
    if let Some(lib) = std::env::var_os("DEP_RIND_FIPS_MODULE_LIB") {
        println!(
            "cargo::rustc-link-arg-bins=-Wl,-rpath,{}",
            lib.to_string_lossy()
        );
    }
}
