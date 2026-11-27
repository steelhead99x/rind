// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

fn main() {
    embuild::espidf::sysenv::output();
    println!("cargo::rerun-if-env-changed=RIND_FW_LABEL");
    println!("cargo::rerun-if-env-changed=RIND_FW_MHZ");
}
