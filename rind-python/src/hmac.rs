// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::hmac;

use crate::{Bytes, algorithm, bytes, constants, error, submodule};

algorithm!(
    /// An HMAC algorithm.
    Algorithm(hmac::Algorithm) as "pyrind.hmac"."Algorithm" {
    /// The tag's length in bytes.
    #[getter]
    fn tag_len(&self) -> usize {
        self.inner.tag_len()
    }
    }
);

/// An HMAC key, whose keyed hash states are computed once.
#[pyclass(frozen, module = "pyrind.hmac")]
pub(crate) struct Key(pub(crate) Box<hmac::Key>);

#[pymethods]
impl Key {
    /// Makes a key for `algorithm` from `key`, of any length.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, key: Bytes<'_>) -> Self {
        Self(Box::new(hmac::Key::new(algorithm.get().inner, &key)))
    }
}

/// Returns the tag of `data` under `key`.
#[pyfunction]
fn sign<'py>(py: Python<'py>, key: &Bound<'_, Key>, data: Bytes<'_>) -> Bound<'py, PyBytes> {
    bytes(py, hmac::sign(&key.get().0, &data))
}

/// Checks in constant time that `tag` is the whole tag of `data` under `key`;
/// raises `BadSignature` otherwise, including for a truncated tag.
#[pyfunction]
fn verify(key: &Bound<'_, Key>, data: Bytes<'_>, tag: Bytes<'_>) -> PyResult<()> {
    hmac::verify(&key.get().0, &data, &tag).map_err(error)
}

/// A tag of a message given in pieces, which signs once.
#[pyclass(module = "pyrind.hmac")]
struct Context(Option<Box<hmac::Context>>);

fn signed() -> PyErr {
    PyValueError::new_err("the context has already signed")
}

#[pymethods]
impl Context {
    /// Starts a tag under `key`.
    #[new]
    fn new(key: &Bound<'_, Key>) -> Self {
        Self(Some(Box::new(hmac::Context::with_key(&key.get().0))))
    }

    /// Adds `data` to the message.
    fn update(&mut self, data: Bytes<'_>) -> PyResult<()> {
        self.0.as_mut().ok_or_else(signed)?.update(&data);
        Ok(())
    }

    /// Returns a context that continues from this one's message, which this
    /// one keeps.
    fn copy(&self) -> PyResult<Self> {
        Ok(Self(Some(self.0.as_ref().ok_or_else(signed)?.clone())))
    }

    /// Returns the tag of the message; the context takes no more data.
    fn sign<'py>(&mut self, py: Python<'py>) -> PyResult<Bound<'py, PyBytes>> {
        Ok(bytes(py, self.0.take().ok_or_else(signed)?.sign()))
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Algorithm>()?;
    m.add_class::<Key>()?;
    m.add_class::<Context>()?;
    m.add_function(wrap_pyfunction!(sign, m)?)?;
    m.add_function(wrap_pyfunction!(verify, m)?)?;
    constants!(m, Algorithm, "pyrind.hmac", {
        HMAC_SHA256 => &hmac::HMAC_SHA256,
        HMAC_SHA384 => &hmac::HMAC_SHA384,
        HMAC_SHA512 => &hmac::HMAC_SHA512,
    });
    submodule(m, "pyrind.hmac.legacy", |legacy| {
        constants!(legacy, Algorithm, "pyrind.hmac.legacy", {
            HMAC_SHA1 => &hmac::legacy::HMAC_SHA1,
        });
        Ok(())
    })
}
