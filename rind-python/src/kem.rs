// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::kem::{self, MlKem768};

use crate::{Bytes, PublicKeyCell, algorithm, bytes, constants, error};

/// The parameter sets these bindings offer.
#[derive(Debug)]
pub(crate) enum ParameterSet {
    MlKem768,
}

algorithm!(
    /// A key encapsulation mechanism.
    Algorithm(ParameterSet) as "pyrind.kem"."Algorithm" {}
);

/// The recipient's private key, which decapsulates.
#[pyclass(frozen, module = "pyrind.kem")]
struct DecapsulationKey {
    inner: Box<kem::DecapsulationKey<MlKem768>>,
    public_key: PublicKeyCell<EncapsulationKey>,
}

#[pymethods]
impl DecapsulationKey {
    /// Generates a key for `algorithm`.
    #[staticmethod]
    fn generate(algorithm: &Bound<'_, Algorithm>) -> PyResult<Self> {
        let ParameterSet::MlKem768 = algorithm.get().inner;
        Ok(Self {
            inner: Box::new(kem::DecapsulationKey::generate().map_err(error)?),
            public_key: PublicKeyCell::new(),
        })
    }

    /// The public key to send the sender, the same object each call.
    fn public_key(&self, py: Python<'_>) -> PyResult<Py<EncapsulationKey>> {
        self.public_key.get(py, || {
            EncapsulationKey(Box::new(self.inner.public_key().clone()))
        })
    }

    /// Recovers the shared secret from the sender's `ciphertext`.
    fn decapsulate<'py>(
        &self,
        py: Python<'py>,
        ciphertext: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let ciphertext = kem::Ciphertext::new(&ciphertext).map_err(error)?;
        Ok(bytes(py, self.inner.decapsulate(&ciphertext)))
    }
}

/// The recipient's public key, which encapsulates, and whose `bytes` are its
/// encoding.
#[pyclass(frozen, module = "pyrind.kem")]
struct EncapsulationKey(Box<kem::EncapsulationKey<MlKem768>>);

#[pymethods]
impl EncapsulationKey {
    /// Parses a public key for `algorithm`.
    #[new]
    fn new(algorithm: &Bound<'_, Algorithm>, data: Bytes<'_>) -> PyResult<Self> {
        let ParameterSet::MlKem768 = algorithm.get().inner;
        kem::EncapsulationKey::new(&data)
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// Encapsulates a fresh shared secret, returning the ciphertext to send
    /// the recipient and the secret.
    fn encapsulate<'py>(
        &self,
        py: Python<'py>,
    ) -> PyResult<(Bound<'py, PyBytes>, Bound<'py, PyBytes>)> {
        let (ciphertext, secret) = self.0.encapsulate().map_err(error)?;
        Ok((bytes(py, ciphertext), bytes(py, secret)))
    }

    fn __bytes__<'py>(&self, py: Python<'py>) -> Bound<'py, PyBytes> {
        bytes(py, &*self.0)
    }
}

pub(crate) fn register(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<Algorithm>()?;
    m.add_class::<DecapsulationKey>()?;
    m.add_class::<EncapsulationKey>()?;
    constants!(m, Algorithm, "pyrind.kem", {
        ML_KEM_768 => &ParameterSet::MlKem768,
    });
    Ok(())
}
