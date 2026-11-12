// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! pyrind: rind's API for Python.
//!
//! Each rind module becomes a Python submodule of the same name, importable
//! as `pyrind.<name>`. Keys and contexts are classes; algorithms are module
//! constants of a class per module, so passing one module's algorithm to
//! another's key is a `TypeError`. Every rind error raises a subclass of
//! `pyrind.Error`.
//!
//! Every class holds its rind value in a `Box`. pyo3 places a class's
//! contents inside the Python object, which CPython's allocator aligns to
//! only 16 bytes (8 on 32-bit targets), while some rind types need 32, such
//! as ML-KEM's coefficients that AVX2 loads aligned
//! (<https://github.com/PyO3/pyo3/issues/6526>).

use std::borrow::Cow;
use std::mem::MaybeUninit;

use pyo3::create_exception;
use pyo3::exceptions::{PyException, PyImportError, PyMemoryError};
use pyo3::ffi;
use pyo3::prelude::*;
use pyo3::types::{PyBytes, PyDict};

mod aead;
mod agreement;
mod cipher;
mod digest;
mod hkdf;
mod hmac;
mod kem;
mod pbkdf2;
mod rsa;
mod signature;

create_exception!(pyrind, Error, PyException, "A rind call failed.");
create_exception!(
    pyrind,
    WrongLength,
    Error,
    "An input or output of fixed length, such as a key, a nonce, or a derived key, was another length."
);
create_exception!(
    pyrind,
    KeyRejected,
    Error,
    "A private, public, or peer's key was refused; the message says why."
);
create_exception!(
    pyrind,
    BadSignature,
    Error,
    "A signature, MAC tag, or PBKDF2 output did not verify."
);
create_exception!(
    pyrind,
    DecryptFailed,
    Error,
    "An AEAD ciphertext, its tag, or its associated data did not authenticate, or an RSA-OAEP ciphertext did not decrypt."
);
create_exception!(pyrind, RngFailed, Error, "The system random source failed.");
create_exception!(
    pyrind,
    Unsupported,
    Error,
    "A call was given an algorithm it does not take."
);
create_exception!(
    pyrind,
    Fault,
    Error,
    "An internal consistency check failed, from a hardware fault or a rind bug."
);

/// Raises the `pyrind` exception for a rind error.
pub(crate) fn error(e: rind::Error) -> PyErr {
    match e {
        rind::Error::WrongLength => WrongLength::new_err(()),
        rind::Error::KeyRejected(why) => KeyRejected::new_err(why.to_string()),
        rind::Error::BadSignature => BadSignature::new_err(()),
        rind::Error::DecryptFailed => DecryptFailed::new_err(()),
        rind::Error::RngFailed => RngFailed::new_err(()),
        rind::Error::Unsupported => Unsupported::new_err(()),
        rind::Error::Fault => Fault::new_err(()),
        // `NotEqual` comes only from `constant_time`, which pyrind leaves to
        // `hmac.compare_digest`; the rest are variants rind adds later.
        other => Error::new_err(format!("{other:?}")),
    }
}

/// A bytes-like argument: borrowed from `bytes`, which is immutable, and
/// copied from any other buffer, such as a `bytearray`, `memoryview`, or
/// `array`, so no other thread can change it while rind reads it, even with
/// the GIL released. Like `hashlib`, it takes a buffer's raw bytes whatever
/// its item format or layout.
pub(crate) struct Bytes<'a>(Cow<'a, [u8]>);

impl<'a, 'py> FromPyObject<'a, 'py> for Bytes<'a> {
    type Error = PyErr;

    fn extract(obj: Borrowed<'a, 'py, PyAny>) -> PyResult<Self> {
        if let Ok(bytes) = <&'a [u8]>::extract(obj) {
            return Ok(Self(Cow::Borrowed(bytes)));
        }
        Ok(Self(Cow::Owned(copy_buffer(&obj)?)))
    }
}

/// Copies the raw bytes of any buffer, in C order, through CPython's own
/// copy, so no Rust reference ever covers memory another thread may write,
/// as a `bytearray` can be on free-threaded CPython.
fn copy_buffer(obj: &Bound<'_, PyAny>) -> PyResult<Vec<u8>> {
    let py = obj.py();
    let mut view = MaybeUninit::<ffi::Py_buffer>::uninit();
    // SAFETY: `obj` is a live object and `view` has room for a `Py_buffer`,
    // which this initializes on success.
    if unsafe { ffi::PyObject_GetBuffer(obj.as_ptr(), view.as_mut_ptr(), ffi::PyBUF_FULL_RO) } == -1
    {
        return Err(PyErr::fetch(py));
    }
    // SAFETY: `PyObject_GetBuffer` succeeded, so `view` is initialized and
    // must be released, which happens below in place, never moved.
    let view = unsafe { view.assume_init_mut() };
    let len = usize::try_from(view.len).expect("a buffer's length is non-negative");
    let mut out = Vec::<u8>::with_capacity(len);
    // SAFETY: `out` has room for `view.len` bytes, which this copies; the
    // view describes its own layout.
    let copied =
        unsafe { ffi::PyBuffer_ToContiguous(out.as_mut_ptr().cast(), view, view.len, b'C' as _) };
    // SAFETY: `view` came from `PyObject_GetBuffer` and is released once.
    unsafe { ffi::PyBuffer_Release(view) };
    if copied == -1 {
        return Err(PyErr::fetch(py));
    }
    // SAFETY: `PyBuffer_ToContiguous` wrote all `len` bytes.
    unsafe { out.set_len(len) };
    Ok(out)
}

impl core::ops::Deref for Bytes<'_> {
    type Target = [u8];

    fn deref(&self) -> &[u8] {
        &self.0
    }
}

/// Declares the Python class of a module's algorithm constants, each
/// wrapping a rind algorithm, with any further methods.
macro_rules! algorithm {
    ($(#[$doc:meta])* $ty:ident($inner:ty) as $module:literal . $name:literal { $($methods:tt)* }) => {
        $(#[$doc])*
        #[pyclass(frozen, module = $module, name = $name)]
        pub(crate) struct $ty {
            pub(crate) inner: &'static $inner,
            pub(crate) path: &'static str,
        }

        #[pymethods]
        impl $ty {
            fn __repr__(&self) -> &'static str {
                self.path
            }

            $($methods)*
        }
    };
}
pub(crate) use algorithm;

/// Adds each algorithm constant to the module `m`, whose path is `$module`.
macro_rules! constants {
    ($m:expr, $ty:ident, $module:literal, { $($constant:ident => $value:expr),* $(,)? }) => {{
        $($m.add(
            stringify!($constant),
            $ty {
                inner: $value,
                path: concat!($module, ".", stringify!($constant)),
            },
        )?;)*
    }};
}
pub(crate) use constants;

/// Returns a new `bytes` of `len` bytes that begins with `prefix`, the rest
/// zeroed, after `fill` has written it in place.
///
/// Unlike `PyBytes::new_with`, this writes each byte once before `fill`
/// rather than zeroing the whole buffer and then copying `prefix` over it,
/// which for an AEAD's plaintext is a pass over every byte saved.
pub(crate) fn bytes_with<'py>(
    py: Python<'py>,
    prefix: &[u8],
    len: usize,
    fill: impl FnOnce(&mut [u8]) -> PyResult<()>,
) -> PyResult<Bound<'py, PyBytes>> {
    assert!(prefix.len() <= len);
    let size = isize::try_from(len).map_err(|_| PyMemoryError::new_err(()))?;
    // SAFETY: `PyBytes_FromStringAndSize` with a null pointer returns a new
    // object, owned here and referenced nowhere else, whose `len` bytes are
    // uninitialized, or null with an exception set. Its buffer is copied and
    // zeroed into whole before any slice of it exists, and Python sees the
    // object only once it is returned.
    unsafe {
        let object = pyo3::ffi::PyBytes_FromStringAndSize(core::ptr::null(), size);
        let bytes = Bound::from_owned_ptr_or_err(py, object)?.cast_into_unchecked::<PyBytes>();
        let buffer = pyo3::ffi::PyBytes_AsString(object).cast::<u8>();
        core::ptr::copy_nonoverlapping(prefix.as_ptr(), buffer, prefix.len());
        core::ptr::write_bytes(buffer.add(prefix.len()), 0, len - prefix.len());
        fill(core::slice::from_raw_parts_mut(buffer, len))?;
        Ok(bytes)
    }
}

/// Returns `bytes` holding `value`.
pub(crate) fn bytes<'py>(py: Python<'py>, value: impl AsRef<[u8]>) -> Bound<'py, PyBytes> {
    PyBytes::new(py, value.as_ref())
}

/// Adds the submodule `path`, such as `pyrind.signature.verify`, to
/// `parent` under its last component, and to `sys.modules`, so that
/// `import pyrind.signature.verify` finds it.
pub(crate) fn submodule<'py>(
    parent: &Bound<'py, PyModule>,
    path: &str,
    build: impl FnOnce(&Bound<'py, PyModule>) -> PyResult<()>,
) -> PyResult<()> {
    let py = parent.py();
    let module = PyModule::new(py, path)?;
    build(&module)?;
    let name = path.rsplit('.').next().unwrap_or(path);
    parent.add(name, &module)?;
    py.import("sys")?
        .getattr("modules")?
        .cast_into::<PyDict>()?
        .set_item(path, module)
}

/// Whether this CPU runs AES and GHASH (or ARM's PMULL) in hardware; where it
/// does not, prefer ChaCha20-Poly1305.
#[pyfunction]
fn has_aes_hardware() -> bool {
    rind::cpu::has_aes_hardware()
}

#[pymodule]
#[pyo3(name = "_rind")]
fn pyrind(m: &Bound<'_, PyModule>) -> PyResult<()> {
    let py = m.py();
    m.add("Error", py.get_type::<Error>())?;
    m.add("WrongLength", py.get_type::<WrongLength>())?;
    m.add("KeyRejected", py.get_type::<KeyRejected>())?;
    m.add("BadSignature", py.get_type::<BadSignature>())?;
    m.add("DecryptFailed", py.get_type::<DecryptFailed>())?;
    m.add("RngFailed", py.get_type::<RngFailed>())?;
    m.add("Unsupported", py.get_type::<Unsupported>())?;
    m.add("Fault", py.get_type::<Fault>())?;

    submodule(m, "pyrind.aead", aead::register)?;
    submodule(m, "pyrind.agreement", agreement::register)?;
    submodule(m, "pyrind.cipher", cipher::register)?;
    submodule(m, "pyrind.cpu", |cpu| {
        cpu.add_function(wrap_pyfunction!(has_aes_hardware, cpu)?)
    })?;
    submodule(m, "pyrind.digest", digest::register)?;
    submodule(m, "pyrind.hkdf", hkdf::register)?;
    submodule(m, "pyrind.hmac", hmac::register)?;
    submodule(m, "pyrind.kem", kem::register)?;
    submodule(m, "pyrind.key_wrap", cipher::register_key_wrap)?;
    submodule(m, "pyrind.pbkdf2", pbkdf2::register)?;
    submodule(m, "pyrind.rsa", rsa::register)?;
    submodule(m, "pyrind.signature", signature::register)?;
    Ok(())
}
