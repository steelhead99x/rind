//! Replace a file by renaming a complete temporary file over it.
//!
//! A reader sees the old file or the new one, never a partial write. On
//! Windows, rename fails while another test still has the destination open,
//! so this retries briefly.

use std::thread;
use std::time::Duration;

pub fn replace_file(path: &str, bytes: &[u8]) {
    let temporary = format!("{path}.{}.tmp", std::process::id());
    if let Err(err) = std::fs::write(&temporary, bytes) {
        panic!("cannot write {temporary}: {err}");
    }
    let mut last_err = None;
    for _ in 0..16 {
        match std::fs::rename(&temporary, path) {
            Ok(()) => return,
            Err(err) => {
                last_err = Some(err);
                thread::sleep(Duration::from_millis(10));
            }
        }
    }
    let _ = std::fs::remove_file(&temporary);
    let err = last_err.expect("rename failed");
    panic!("cannot replace {path}: {err}");
}
