// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::hkdf;

use crate::{Bytes, aead, algorithm, constants, error, hmac, submodule};

algorithm!(
    /// An HKDF algorithm.
    Algorithm(hkdf::Algorithm) as "pyrind.hkdf"."Algorithm" {}
);

/// An HKDF salt, which extracts pseudorandom keys from secrets.
#[pyclass(frozen, module = "pyrind.hkdf")]
struct Salt(Box<hkdf::Salt>);

#[pymethods]
impl Salt {
    /// Makes a salt for `algorithm` from `value`, of any length.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, value: Bytes<'_>) -> Self {
        Self(Box::new(hkdf::Salt::new(algorithm.get().inner, &value)))
    }

    /// Extracts a pseudorandom key from `secret`.
    fn extract(&self, secret: Bytes<'_>) -> PyResult<Prk> {
        let prk = self.0.extract(&secret).map_err(error)?;
        Ok(Prk(Box::new(prk)))
    }
}

/// What `Prk.expand` derives: bytes of a length, or a key for an algorithm.
#[derive(FromPyObject)]
enum KeyType<'py> {
    Len(usize),
    Aead(Bound<'py, aead::Algorithm>),
    Hmac(Bound<'py, hmac::Algorithm>),
}

/// A pseudorandom key, which expands into any number of keys.
#[pyclass(frozen, module = "pyrind.hkdf")]
struct Prk(Box<hkdf::Prk>);

#[pymethods]
impl Prk {
    /// Expands the key with `info` into `key_type`: that many bytes for an
    /// `int`, or an `aead.Key` or `hmac.Key` for their algorithms, whose key
    /// bytes never leave rind.
    ///
    /// Raises `WrongLength` for more than 255 times the hash's length.
    fn expand<'py>(
        &self,
        py: Python<'py>,
        info: Bytes<'_>,
        key_type: KeyType<'py>,
    ) -> PyResult<Bound<'py, PyAny>> {
        let info: [&[u8]; 1] = [&info];
        Ok(match key_type {
            // Expanding first refuses a length too long before allocating it.
            KeyType::Len(len) => {
                let okm = self.0.expand(&info, len).map_err(error)?;
                PyBytes::new_with(py, len, |out| okm.fill(out).map_err(error))?.into_any()
            }
            KeyType::Aead(algorithm) => {
                let okm = self.0.expand(&info, algorithm.get().inner);
                let key = rind::aead::Key::from(okm.map_err(error)?);
                Bound::new(py, aead::Key(Box::new(key)))?.into_any()
            }
            KeyType::Hmac(algorithm) => {
                let okm = self.0.expand(&info, algorithm.get().inner);
                let key = rind::hmac::Key::from(okm.map_err(error)?);
                Bound::new(py, hmac::Key(Box::new(key)))?.into_any()
            }
        })
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Algorithm>()?;
    m.add_class::<Salt>()?;
    m.add_class::<Prk>()?;
    constants!(m, Algorithm, "pyrind.hkdf", {
        HKDF_SHA256 => &hkdf::HKDF_SHA256,
        HKDF_SHA384 => &hkdf::HKDF_SHA384,
        HKDF_SHA512 => &hkdf::HKDF_SHA512,
    });
    submodule(m, "pyrind.hkdf.legacy", |legacy| {
        constants!(legacy, Algorithm, "pyrind.hkdf.legacy", {
            HKDF_SHA1 => &hkdf::legacy::HKDF_SHA1,
        });
        Ok(())
    })
}
