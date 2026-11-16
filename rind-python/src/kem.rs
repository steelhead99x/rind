// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
use pyo3::prelude::*;
use pyo3::types::PyBytes;
use rind::kem::{self, MlKem768};

use crate::{Bytes, algorithm, bytes, constants, error};

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
struct DecapsulationKey(Box<kem::DecapsulationKey<MlKem768>>);

#[pymethods]
impl DecapsulationKey {
    /// Generates a key for `algorithm`.
    #[staticmethod]
    fn generate(algorithm: &Bound<'_, Algorithm>) -> PyResult<Self> {
        let ParameterSet::MlKem768 = algorithm.get().inner;
        kem::DecapsulationKey::generate()
            .map(Box::new)
            .map(Self)
            .map_err(error)
    }

    /// The public key to send the sender.
    fn public_key(&self) -> EncapsulationKey {
        EncapsulationKey(Box::new(self.0.public_key()))
    }

    /// Recovers the shared secret from the sender's `ciphertext`.
    fn decapsulate<'py>(
        &self,
        py: Python<'py>,
        ciphertext: Bytes<'_>,
    ) -> PyResult<Bound<'py, PyBytes>> {
        let ciphertext = kem::Ciphertext::new(&ciphertext).map_err(error)?;
        Ok(bytes(py, self.0.decapsulate(&ciphertext)))
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
