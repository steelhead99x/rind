//! Times rind's RSA-OAEP decryption on the hardware it runs on, for the Marvin
//! toolkit. `admin/timing` runs it; see it for how.

mod clock;
mod marvin;

use std::process::ExitCode;

const USAGE: &str = "usage: rind-timing marvin KEY CIPHERTEXTS OUT
  times the RSA-OAEP decryption of each ciphertext the Marvin toolkit wrote";

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let result = match args.iter().map(String::as_str).collect::<Vec<_>>()[..] {
        ["marvin", key, ciphertexts, out] => marvin::run(key, ciphertexts, out),
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
