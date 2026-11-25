#![no_main]

//! pyrind's native module, `_rind`, called from CPython embedded in this
//! target, as `python.py` directs from the fuzzer's bytes: every export,
//! with arguments of every type and buffer shape. CPython allocates through
//! `malloc` (`PYTHONMALLOC=malloc`), so AddressSanitizer sees the bytes
//! objects pyrind writes into as well as rind's own memory.
//!
//! Only under cargo fuzz, on 64-bit glibc Linux, does this target link
//! CPython; elsewhere it does nothing, so a workspace build needs no
//! libpython.

use libfuzzer_sys::fuzz_target;

// Unused where the target does nothing.
#[allow(dead_code)]
mod edit;
mod fixtures;

#[cfg(all(
    fuzzing,
    target_os = "linux",
    target_env = "gnu",
    target_pointer_width = "64"
))]
mod embedded {
    use std::ffi::CString;
    use std::sync::Once;

    use _rind::pyrind;
    use pyo3::prelude::*;
    use pyo3::types::{PyBytes, PyList};

    static INIT: Once = Once::new();

    pub fn run(data: &[u8]) {
        INIT.call_once(|| {
            // SAFETY: before CPython starts, on the only thread.
            unsafe { std::env::set_var("PYTHONMALLOC", "malloc") };
            pyo3::append_to_inittab!(pyrind);
        });
        Python::attach(|py| {
            let harness = harness(py);
            let fixtures = PyList::new(
                py,
                crate::fixtures::FILES.iter().map(|f| PyBytes::new(py, f)),
            )
            .unwrap();
            if let Err(error) = harness.call1(py, (PyBytes::new(py, data), fixtures)) {
                error.print(py);
                panic!("pyrind raised {error}");
            }
        });
    }

    /// `python.py`'s `fuzz`, loaded once.
    fn harness(py: Python<'_>) -> Py<PyAny> {
        static HARNESS: pyo3::sync::PyOnceLock<Py<PyAny>> = pyo3::sync::PyOnceLock::new();
        HARNESS
            .get_or_init(py, || {
                let code = CString::new(include_str!("python.py")).unwrap();
                let module = PyModule::from_code(py, &code, c"python.py", c"harness").unwrap();
                module.getattr("fuzz").unwrap().unbind()
            })
            .clone_ref(py)
    }
}

#[cfg(not(all(
    fuzzing,
    target_os = "linux",
    target_env = "gnu",
    target_pointer_width = "64"
)))]
mod embedded {
    pub fn run(_data: &[u8]) {}
}

fuzz_target!(|data: &[u8]| embedded::run(data));
