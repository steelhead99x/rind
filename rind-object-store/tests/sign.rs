//! Drives object_store's own S3, Azure, and GCS signing through a provider
//! that runs every operation on rind and aws-lc-rs and asserts they agree.
//! Comparing per operation keeps the tests independent of the signing time,
//! which object_store reads from the clock.

use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::time::Duration;

use aws_lc_rs::{digest, hmac, rand, signature};
use http::Method;
use object_store::ClientOptions;
use object_store::aws::{AmazonS3Builder, AwsAuthorizer, AwsCredential};
use object_store::azure::MicrosoftAzureBuilder;
use object_store::client::{
    CryptoProvider, DigestAlgorithm, DigestContext, HmacContext, HttpClient, HttpConnector,
    HttpError, HttpRequest, HttpRequestBody, HttpResponse, HttpService, Signer, SigningAlgorithm,
};
use object_store::gcp::GoogleCloudStorageBuilder;
use object_store::path::Path;
use object_store::signer::Signer as _;
use rustls_pki_types::PrivateKeyDer;
use rustls_pki_types::pem::PemObject;

const PKCS8: &[u8] = include_bytes!("data/rsa2048.pkcs8.pem");
const PKCS1: &[u8] = include_bytes!("data/rsa2048.pkcs1.pem");
const SEC1: &[u8] = include_bytes!("data/p256.sec1.pem");

/// Counts the operations [`Tee`] has checked.
#[derive(Debug, Default)]
struct Checked {
    digests: AtomicUsize,
    hmacs: AtomicUsize,
    signatures: AtomicUsize,
}

impl Checked {
    fn count(&self) -> [usize; 3] {
        [&self.digests, &self.hmacs, &self.signatures].map(|n| n.load(Ordering::Relaxed))
    }
}

#[derive(Debug)]
struct Tee {
    rind: Arc<dyn CryptoProvider>,
    checked: Arc<Checked>,
}

impl Tee {
    fn new() -> Arc<Self> {
        Arc::new(Self {
            rind: rind_object_store::default_provider(),
            checked: Arc::default(),
        })
    }
}

impl CryptoProvider for Tee {
    fn digest(&self, algorithm: DigestAlgorithm) -> object_store::Result<Box<dyn DigestContext>> {
        assert_eq!(algorithm, DigestAlgorithm::Sha256);
        Ok(Box::new(TeeDigest {
            rind: self.rind.digest(DigestAlgorithm::Sha256)?,
            aws: digest::Context::new(&digest::SHA256),
            checked: self.checked.clone(),
        }))
    }

    fn hmac(
        &self,
        algorithm: DigestAlgorithm,
        secret: &[u8],
    ) -> object_store::Result<Box<dyn HmacContext>> {
        assert_eq!(algorithm, DigestAlgorithm::Sha256);
        Ok(Box::new(TeeHmac {
            rind: self.rind.hmac(DigestAlgorithm::Sha256, secret)?,
            aws: hmac::Context::with_key(&hmac::Key::new(hmac::HMAC_SHA256, secret)),
            checked: self.checked.clone(),
        }))
    }

    fn sign(
        &self,
        algorithm: SigningAlgorithm,
        pem: &[u8],
    ) -> object_store::Result<Box<dyn Signer>> {
        assert_eq!(algorithm, SigningAlgorithm::RS256);
        Ok(Box::new(TeeSigner {
            rind: self.rind.sign(SigningAlgorithm::RS256, pem)?,
            aws: aws_rsa_key(pem),
            checked: self.checked.clone(),
        }))
    }
}

struct TeeDigest {
    rind: Box<dyn DigestContext>,
    aws: digest::Context,
    checked: Arc<Checked>,
}

impl DigestContext for TeeDigest {
    fn update(&mut self, data: &[u8]) {
        self.rind.update(data);
        self.aws.update(data);
    }

    fn finish(&mut self) -> object_store::Result<&[u8]> {
        let expected = self.aws.clone().finish();
        let got = self.rind.finish()?;
        assert_eq!(got, expected.as_ref());
        self.checked.digests.fetch_add(1, Ordering::Relaxed);
        Ok(got)
    }
}

struct TeeHmac {
    rind: Box<dyn HmacContext>,
    aws: hmac::Context,
    checked: Arc<Checked>,
}

impl HmacContext for TeeHmac {
    fn update(&mut self, data: &[u8]) {
        self.rind.update(data);
        self.aws.update(data);
    }

    fn finish(&mut self) -> object_store::Result<&[u8]> {
        let expected = self.aws.clone().sign();
        let got = self.rind.finish()?;
        assert_eq!(got, expected.as_ref());
        self.checked.hmacs.fetch_add(1, Ordering::Relaxed);
        Ok(got)
    }
}

struct TeeSigner {
    rind: Box<dyn Signer>,
    aws: signature::RsaKeyPair,
    checked: Arc<Checked>,
}

impl Signer for TeeSigner {
    fn sign(&self, message: &[u8]) -> object_store::Result<Vec<u8>> {
        // RSASSA-PKCS1-v1_5 is deterministic, so the signatures must match exactly.
        let mut expected = vec![0; self.aws.public_modulus_len()];
        self.aws
            .sign(
                &signature::RSA_PKCS1_SHA256,
                &rand::SystemRandom::new(),
                message,
                &mut expected,
            )
            .unwrap();
        let got = self.rind.sign(message)?;
        assert_eq!(got, expected);
        self.checked.signatures.fetch_add(1, Ordering::Relaxed);
        Ok(got)
    }
}

fn aws_rsa_key(pem: &[u8]) -> signature::RsaKeyPair {
    match PrivateKeyDer::from_pem_slice(pem).unwrap() {
        PrivateKeyDer::Pkcs8(key) => {
            signature::RsaKeyPair::from_pkcs8(key.secret_pkcs8_der()).unwrap()
        }
        PrivateKeyDer::Pkcs1(key) => {
            signature::RsaKeyPair::from_der(key.secret_pkcs1_der()).unwrap()
        }
        _ => panic!("not an RSA key"),
    }
}

/// Builds stores without an HTTP client; signing must never reach the network.
#[derive(Debug)]
struct Offline;

impl HttpConnector for Offline {
    fn connect(&self, _: &ClientOptions) -> object_store::Result<HttpClient> {
        Ok(HttpClient::new(Offline))
    }
}

#[async_trait::async_trait]
impl HttpService for Offline {
    async fn call(&self, request: HttpRequest) -> Result<HttpResponse, HttpError> {
        panic!("signing sent {} {}", request.method(), request.uri())
    }
}

fn path() -> Path {
    Path::from("broadcast/segment.m4s")
}

const EXPIRES_IN: Duration = Duration::from_secs(3600);

#[tokio::test]
async fn s3_presigned_url() {
    let tee = Tee::new();
    let store = AmazonS3Builder::new()
        .with_bucket_name("bucket")
        .with_region("us-east-1")
        .with_access_key_id("AKIDEXAMPLE")
        .with_secret_access_key("wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY")
        .with_crypto_provider(tee.clone())
        .with_http_connector(Offline)
        .build()
        .unwrap();

    store
        .signed_url(Method::PUT, &path(), EXPIRES_IN)
        .await
        .unwrap();

    // The canonical request's digest, four HMACs deriving the signing key,
    // and the HMAC that signs.
    assert_eq!(tee.checked.count(), [1, 5, 0]);
}

#[test]
fn s3_authorizes_signed_payload() {
    let tee = Tee::new();
    let credential = AwsCredential {
        key_id: "AKIDEXAMPLE".to_string(),
        secret_key: "wJalrXUtnFEMI/K7MDENG+bPxRfiCYEXAMPLEKEY".to_string(),
        token: None,
    };

    let mut request = HttpRequest::new(HttpRequestBody::from(vec![0x5a; 100_000]));
    *request.method_mut() = Method::PUT;
    *request.uri_mut() = "https://bucket.s3.us-east-1.amazonaws.com/broadcast/segment.m4s"
        .parse()
        .unwrap();

    AwsAuthorizer::new(&credential, "s3", "us-east-1")
        .with_crypto(tee.as_ref())
        .try_authorize(&mut request, None)
        .unwrap();

    // The payload's digest joins the canonical request's.
    assert_eq!(tee.checked.count(), [2, 5, 0]);
}

#[tokio::test]
async fn azure_sas_url() {
    let tee = Tee::new();
    let store = MicrosoftAzureBuilder::new()
        .with_account("account")
        .with_container_name("container")
        .with_access_key("ZXhhbXBsZSBhenVyZSBzdG9yYWdlIGFjY291bnQga2V5IGZvciByaW5k")
        .with_crypto_provider(tee.clone())
        .with_http_connector(Offline)
        .build()
        .unwrap();

    store
        .signed_url(Method::GET, &path(), EXPIRES_IN)
        .await
        .unwrap();

    assert_eq!(tee.checked.count(), [0, 1, 0]);
}

async fn gcs_signed_url(pem: &[u8]) {
    let tee = Tee::new();
    let key = format!(
        r#"{{"private_key": {:?}, "private_key_id": "id", "client_email": "rind@example.iam.gserviceaccount.com"}}"#,
        std::str::from_utf8(pem).unwrap()
    );
    let store = GoogleCloudStorageBuilder::new()
        .with_bucket_name("bucket")
        .with_service_account_key(key)
        .with_crypto_provider(tee.clone())
        .with_http_connector(Offline)
        .build()
        .unwrap();

    store
        .signed_url(Method::GET, &path(), EXPIRES_IN)
        .await
        .unwrap();

    assert_eq!(tee.checked.count(), [1, 0, 1]);
}

#[tokio::test]
async fn gcs_signed_url_pkcs8() {
    gcs_signed_url(PKCS8).await;
}

#[tokio::test]
async fn gcs_signed_url_pkcs1() {
    gcs_signed_url(PKCS1).await;
}

#[test]
fn sign_refuses_non_rsa_keys() {
    let provider = rind_object_store::default_provider();
    // A PKCS#8 label around a PKCS#1 body, so the DER does not parse as PKCS#8.
    let mislabelled = std::str::from_utf8(PKCS1)
        .unwrap()
        .replace("RSA PRIVATE KEY", "PRIVATE KEY");
    let not_rsa: [&[u8]; 4] = [
        SEC1,
        b"",
        b"-----BEGIN PRIVATE KEY-----\nnot base64\n-----END PRIVATE KEY-----\n",
        mislabelled.as_bytes(),
    ];

    for pem in not_rsa {
        assert!(provider.sign(SigningAlgorithm::RS256, pem).is_err());
    }
}
