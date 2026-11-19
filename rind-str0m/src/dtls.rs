use std::sync::Arc;
use std::time::Instant;

use rcgen::{
    CertificateParams, DistinguishedName, DnType, KeyIdMethod, PublicKeyData, SerialNumber,
};
use rind::digest::{SHA256, digest};
use str0m::crypto::CryptoError;
use str0m::crypto::dtls::{
    DtlsCert, DtlsImplError, DtlsInstance, DtlsOutput, DtlsProvider, DtlsVersion, ProtocolVersion,
};
use time::{Duration, OffsetDateTime};

pub(crate) static DTLS: RindDtls = RindDtls;

#[derive(Debug)]
pub(crate) struct RindDtls;

impl DtlsProvider for RindDtls {
    fn generate_certificate(&self) -> Option<DtlsCert> {
        generate_certificate()
    }

    fn new_dtls(
        &self,
        cert: &DtlsCert,
        now: Instant,
        dtls_version: DtlsVersion,
        mtu: Option<usize>,
    ) -> Result<Box<dyn DtlsInstance>, CryptoError> {
        let provider = rind_dimpl::default_provider();

        // dimpl panics on an empty certificate or a key it cannot load, and
        // `RtcConfig::set_dtls_cert` takes both from the caller.
        if cert.certificate.is_empty() {
            return Err(CryptoError::Other("empty DTLS certificate".into()));
        }
        provider
            .key_provider
            .load_private_key(&cert.private_key)
            .map_err(|e| CryptoError::Other(format!("DTLS private key: {e}")))?;

        // ICE checks return routability before DTLS starts, so a server cookie
        // adds a round trip without protecting anything.
        let mut builder = dimpl::Config::builder()
            .with_crypto_provider(provider)
            .use_server_cookie(false);
        if let Some(mtu) = mtu {
            builder = builder.mtu(mtu);
        }
        let config = Arc::new(
            builder
                .build()
                .map_err(|e| CryptoError::Other(e.to_string()))?,
        );

        let cert = cert.clone();
        let dtls = match dtls_version {
            DtlsVersion::Dtls12 => dimpl::Dtls::new_12(config, cert, now),
            DtlsVersion::Dtls13 => dimpl::Dtls::new_13(config, cert, now),
            DtlsVersion::Auto => dimpl::Dtls::new_auto(config, cert, now),
            other => {
                return Err(CryptoError::Other(format!(
                    "unsupported DTLS version: {other}"
                )));
            }
        };
        Ok(Box::new(Dtls(dtls)))
    }
}

/// A self-signed ECDSA P-256 certificate, valid for a year, as dimpl's own generator makes.
///
/// Only a failing system random source fails it, on which str0m panics.
fn generate_certificate() -> Option<DtlsCert> {
    let key = rind_rcgen::KeyPair::generate().ok()?;

    let mut name = DistinguishedName::new();
    name.push(DnType::OrganizationName, "DTLS");
    name.push(DnType::CommonName, "DTLS Peer");

    let mut params = CertificateParams::default();
    params.distinguished_name = name;
    // Firefox rejects a peer reusing another certificate's issuer and serial,
    // so the serial must be unique across processes, not only within one.
    let mut serial = [0u8; 20];
    rind::rand::fill(&mut serial).ok()?;
    let serial = clear_serial_high_bit(serial);
    params.serial_number = Some(SerialNumber::from_slice(&serial));
    // rcgen's `KeyIdMethod::Sha256`, which needs its `crypto` feature: the first
    // 20 bytes of the SubjectPublicKeyInfo's SHA-256 (RFC 7093 method 1).
    let hash = digest(&SHA256, &key.subject_public_key_info());
    params.key_identifier_method = KeyIdMethod::PreSpecified(hash.as_ref()[..20].to_vec());
    params.not_before = OffsetDateTime::now_utc();
    params.not_after = params.not_before + Duration::days(365);

    let certificate = params.self_signed(&key).ok()?;
    Some(DtlsCert {
        certificate: certificate.der().to_vec(),
        private_key: key.serialize_der(),
    })
}

/// Clears the top bit so the serial is a positive INTEGER of at most 20 octets (RFC 5280).
fn clear_serial_high_bit(mut serial: [u8; 20]) -> [u8; 20] {
    serial[0] &= 0x7f;
    serial
}

/// A dimpl connection, forwarded as is.
struct Dtls(dimpl::Dtls);

impl std::fmt::Debug for Dtls {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Dtls").finish_non_exhaustive()
    }
}

impl DtlsInstance for Dtls {
    fn set_active(&mut self, active: bool) {
        self.0.set_active(active);
    }

    fn handle_packet(&mut self, packet: &[u8]) -> Result<(), DtlsImplError> {
        self.0.handle_packet(packet)
    }

    fn poll_output<'a>(&mut self, buf: &'a mut [u8]) -> DtlsOutput<'a> {
        self.0.poll_output(buf)
    }

    fn handle_timeout(&mut self, now: Instant) -> Result<(), DtlsImplError> {
        self.0.handle_timeout(now)
    }

    fn send_application_data(&mut self, data: &[u8]) -> Result<usize, DtlsImplError> {
        self.0.send_application_data(data)
    }

    fn is_active(&self) -> bool {
        self.0.is_active()
    }

    fn protocol_version(&self) -> Option<ProtocolVersion> {
        self.0.protocol_version()
    }

    fn is_closing(&self) -> bool {
        self.0.is_closing()
    }

    fn is_closed(&self) -> bool {
        self.0.is_closed()
    }

    fn close(&mut self) -> Result<(), DtlsImplError> {
        self.0.close()
    }
}

#[cfg(test)]
mod tests {
    use super::clear_serial_high_bit;

    /// A fixed `0xff` octet, not a draw from `rind::rand`. Branching on a
    /// random serial is a secret-dependent branch, which `admin/ctgrind` would
    /// reject in this crate's unit tests.
    #[test]
    fn clear_serial_high_bit_forces_a_positive_integer() {
        let serial = clear_serial_high_bit([0xff; 20]);
        assert_eq!(serial[0], 0x7f);
        assert_eq!(&serial[1..], &[0xff; 19]);
    }
}
