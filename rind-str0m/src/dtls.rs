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
    // The top bit clear keeps it a positive integer of at most 20 octets (RFC 5280).
    serial[0] &= 0x7f;
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
    use str0m::crypto::dtls::{DtlsProvider, DtlsVersion};

    use super::{DTLS, generate_certificate};

    #[test]
    fn certificate_serial_stays_positive_and_the_span_is_a_year() {
        // `serial[0] |= 0x7f` forces the low seven bits on. A few certificates
        // must include one that does not. `not_after - 365 days` reverses the
        // validity span.
        let mut saw_unforced_low_bits = false;
        for _ in 0..8 {
            let cert = generate_certificate().unwrap();
            let serial = serial_integer(&cert.certificate);
            assert!(serial.len() <= 20 && serial[0] & 0x80 == 0, "{serial:?}");
            if serial[0] & 0x7f != 0x7f {
                saw_unforced_low_bits = true;
            }
            let (before, after) = validity(&cert.certificate);
            assert!(after > before, "{before} .. {after}");
        }
        assert!(saw_unforced_low_bits);
    }

    #[test]
    fn fresh_connection_reports_dimpl_state() {
        let cert = generate_certificate().unwrap();
        let mut dtls = DTLS
            .new_dtls(&cert, std::time::Instant::now(), DtlsVersion::Dtls12, None)
            .unwrap();
        let rendered = format!("{dtls:?}");
        assert!(rendered.contains("Dtls"), "{rendered}");
        assert!(!dtls.is_active());
        assert_eq!(format!("{:?}", dtls.protocol_version()), "Some(DTLS1_2)");
        let dtls13 = DTLS
            .new_dtls(&cert, std::time::Instant::now(), DtlsVersion::Dtls13, None)
            .unwrap();
        assert_eq!(format!("{:?}", dtls13.protocol_version()), "Some(DTLS1_3)");
        assert!(!dtls.is_closing());
        assert!(!dtls.is_closed());
        dtls.set_active(true);
        assert!(dtls.is_active());
        assert_eq!(dtls.send_application_data(&[0x11; 8]).unwrap(), 8);
        dtls.close().unwrap();
        assert!(dtls.is_closing() || dtls.is_closed());
    }

    fn serial_integer(cert: &[u8]) -> Vec<u8> {
        let body = sequence(cert);
        let tbs = sequence(body);
        let after_version = if tbs.first() == Some(&0xa0) {
            let (_, rest) = tlv(tbs);
            rest
        } else {
            tbs
        };
        let (serial, _) = tlv(after_version);
        assert_eq!(after_version[0], 0x02);
        serial.to_vec()
    }

    fn validity(cert: &[u8]) -> (String, String) {
        let body = sequence(cert);
        let tbs = sequence(body);
        let mut rest = tbs;
        // version, serial, signature, issuer, then validity.
        for _ in 0..4 {
            let (_, next) = tlv(rest);
            rest = next;
        }
        let (span, _) = tlv(rest);
        assert_eq!(rest[0], 0x30);
        let (before, after_bytes) = tlv(span);
        let (after, _) = tlv(after_bytes);
        (
            String::from_utf8(before.to_vec()).unwrap(),
            String::from_utf8(after.to_vec()).unwrap(),
        )
    }

    fn sequence(input: &[u8]) -> &[u8] {
        let (body, _) = tlv(input);
        assert_eq!(input[0], 0x30);
        body
    }

    fn tlv(input: &[u8]) -> (&[u8], &[u8]) {
        assert!(input.len() >= 2, "{input:?}");
        let (len, header) = match input[1] {
            len @ 0..=0x7f => (len as usize, 2),
            0x81 => (input[2] as usize, 3),
            0x82 => (u16::from_be_bytes([input[2], input[3]]) as usize, 4),
            other => panic!("DER length {other:#x}"),
        };
        let rest = &input[header..];
        (&rest[..len], &rest[len..])
    }
}
