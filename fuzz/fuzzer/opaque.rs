#![no_main]

//! OPAQUE's server in both suites, the side that takes hostile input
//! without knowing the password, under a setup, account, and session the
//! fuzzer writes, with the setup, registration request, record, KE1, and
//! KE3 tampered with.
//!
//! No reference implements RFC 9807 on aws-lc, so this checks rind against
//! opaque-ke, which shares no code with it: both load or refuse the same
//! setups, requests, records, and KE1s, but for the P-256 elements in SEC1's
//! compact form that only opaque-ke decodes, and evaluate a request to the
//! same response. An opaque-ke client stretching with the identity function, as
//! the server never sees the stretch, registers and logs in to rind's
//! server. An untampered login agrees on the session key; a tampered one,
//! or one to an account with no record, fails rather than panicking or
//! agreeing, on the client if its KE2 was wrong and on the server if only
//! its KE3 was.

use libfuzzer_sys::{arbitrary, arbitrary::Arbitrary, fuzz_target};
use opaque_ke::ksf::Identity;
use opaque_ke::{
    CipherSuite, ClientLoginFinishParameters, ClientRegistrationFinishParameters,
    CredentialRequest, CredentialResponse, Identifiers, RegistrationRequest as TheirRequest,
    RegistrationResponse as TheirResponse, Ristretto255, ServerLoginParameters, ServerRegistration,
    TripleDh,
};
use p256_voprf::NistP256;
use rind::Error;
use rind::opaque::*;

mod edit;

struct Ristretto255Sha512;
impl CipherSuite for Ristretto255Sha512 {
    type OprfCs = Ristretto255;
    type KeyExchange = TripleDh<Ristretto255, sha2_opaque::Sha512>;
    type Ksf = Identity;
}

struct P256Sha256;
impl CipherSuite for P256Sha256 {
    type OprfCs = NistP256;
    type KeyExchange = TripleDh<NistP256, sha2_opaque::Sha256>;
    type Ksf = Identity;
}

#[derive(Arbitrary, Debug)]
struct Input {
    p256: bool,
    /// Seeds opaque-ke's setup and client.
    seed: [u8; 32],
    setup: edit::Edit,
    credential_identifier: Vec<u8>,
    password: Vec<u8>,
    context: Vec<u8>,
    client_identity: Option<Vec<u8>>,
    server_identity: Option<Vec<u8>>,
    request: edit::Edit,
    /// Whether the account has a record, or gets the fake one.
    registered: bool,
    record: edit::Edit,
    ke1: edit::Edit,
    ke3: edit::Edit,
}

fuzz_target!(|input: Input| {
    match input.p256 {
        false => run!(Ristretto255Sha512, &RISTRETTO255_SHA512_ARGON2ID, input),
        true => run!(P256Sha256, &P256_SHA256_ARGON2ID, input),
    }
});

/// Runs `input` against rind's server in `$suite` and opaque-ke's in `$cs`.
macro_rules! run {
    ($cs:ty, $suite:expr, $input:expr) => {{
        type Cs = $cs;
        let suite: &'static Suite = $suite;
        let input: Input = $input;
        let mut rng = Rng::new(&input.seed);

        // Both load the same setups.
        let mut setup = opaque_ke::ServerSetup::<Cs>::new(&mut rng)
            .serialize()
            .to_vec();
        input.setup.apply(&mut setup);
        let theirs = opaque_ke::ServerSetup::<Cs>::deserialize(&setup);
        let ours = ServerSetup::from_bytes(suite, &setup);
        assert_eq!(
            ours.is_ok(),
            theirs.is_ok() && !compact(suite, &setup, &[64])
        );
        let (Ok(theirs), Ok(ours)) = (theirs, ours) else {
            return;
        };
        assert_eq!(ours.to_bytes().as_ref(), &setup[..]);
        assert_eq!(
            ours.public_key(),
            &theirs.keypair().public().serialize()[..]
        );

        let session = Session {
            context: &input.context,
            client_identity: input.client_identity.as_deref(),
            server_identity: input.server_identity.as_deref(),
        };
        let identifiers = Identifiers {
            client: session.client_identity,
            server: session.server_identity,
        };
        let context = (!input.context.is_empty()).then_some(&input.context[..]);
        let password = &input.password[..];
        // opaque-ke's blinding refuses a password longer than a `u16`.
        if password.len() > usize::from(u16::MAX) {
            return;
        }
        let identifier = &input.credential_identifier[..];

        // An opaque-ke client registers, through a request both load or
        // refuse alike and evaluate to the same response.
        let start = opaque_ke::ClientRegistration::<Cs>::start(&mut rng, password).unwrap();
        let mut request = start.message.serialize().to_vec();
        let mut tampered = input.request.apply(&mut request);
        let theirs_request = TheirRequest::<Cs>::deserialize(&request);
        let ours_request = RegistrationRequest::new(suite, &request);
        assert_eq!(
            ours_request.is_ok(),
            theirs_request.is_ok() && !compact(suite, &request, &[0])
        );
        let (Ok(theirs_request), Ok(ours_request)) = (theirs_request, ours_request) else {
            return;
        };
        let response = ours.register(&ours_request, identifier).unwrap();
        let theirs_response =
            ServerRegistration::<Cs>::start(&theirs, theirs_request, identifier).unwrap();
        assert_eq!(response.as_ref(), &theirs_response.message.serialize()[..]);
        let Ok(finish) = start.state.finish(
            &mut rng,
            password,
            TheirResponse::deserialize(response.as_ref()).unwrap(),
            ClientRegistrationFinishParameters::new(identifiers, Some(&Identity)),
        ) else {
            // opaque-ke refuses a reflected element, or the identities its
            // envelope cannot encode, which rind's session refuses too.
            assert!(tampered || session_refused(&session));
            return;
        };
        let mut record = finish.message.serialize().to_vec();
        tampered |= input.record.apply(&mut record);
        let theirs_record = ServerRegistration::<Cs>::deserialize(&record);
        let ours_record = RegistrationRecord::new(suite, &record);
        assert_eq!(
            ours_record.is_ok(),
            theirs_record.is_ok() && !compact(suite, &record, &[0])
        );
        let (Ok(theirs_record), Ok(ours_record)) = (theirs_record, ours_record) else {
            return;
        };

        // The client logs in, through a KE1 both load or refuse alike.
        let start = opaque_ke::ClientLogin::<Cs>::start(&mut rng, password).unwrap();
        let mut ke1 = start.message.serialize().to_vec();
        tampered |= input.ke1.apply(&mut ke1);
        let theirs_ke1 = CredentialRequest::<Cs>::deserialize(&ke1);
        let ours_ke1 = Ke1::new(suite, &ke1);
        assert_eq!(
            ours_ke1.is_ok(),
            theirs_ke1.is_ok() && !compact(suite, &ke1, &[0, 33 + 32])
        );
        let (Ok(theirs_ke1), Ok(ours_ke1)) = (theirs_ke1, ours_ke1) else {
            return;
        };
        let credential = Credential {
            identifier,
            record: input.registered.then_some(&ours_record),
        };
        let ours_login = ours.login(&ours_ke1, &credential, &session);
        if session_refused(&session) {
            assert_eq!(ours_login.err(), Some(Error::WrongLength));
            return;
        }
        let (server, ke2) = ours_login.unwrap();
        // opaque-ke's server answers the same KE1 and record.
        opaque_ke::ServerLogin::<Cs>::start(
            &mut rng,
            &theirs,
            input.registered.then_some(theirs_record),
            theirs_ke1,
            identifier,
            ServerLoginParameters {
                context,
                identifiers,
            },
        )
        .unwrap();

        let finish = start.state.finish(
            &mut rng,
            password,
            CredentialResponse::deserialize(ke2.as_ref()).unwrap(),
            ClientLoginFinishParameters::new(context, identifiers, Some(&Identity)),
        );
        let Ok(finish) = finish else {
            assert!(tampered || !input.registered);
            return;
        };
        assert!(
            input.registered && !tampered,
            "a client logged in to a tampered account"
        );
        let mut ke3 = finish.message.serialize().to_vec();
        let tampered = input.ke3.apply(&mut ke3);
        match Ke3::new(suite, &ke3) {
            Ok(ke3) => match server.finish(&ke3) {
                Ok(key) => {
                    assert!(!tampered, "the server accepted a tampered KE3");
                    assert_eq!(key.as_ref(), &finish.session_key[..]);
                }
                Err(e) => {
                    assert!(tampered);
                    assert_eq!(e, Error::BadSignature);
                }
            },
            Err(e) => {
                assert!(tampered);
                assert!(matches!(e, Error::KeyRejected(_)));
            }
        }
    }};
}
use run;

/// Whether a P-256 element at one of `at` in `bytes` takes SEC1's compact
/// form, tag 5, which opaque-ke's P-256 decodes but RFC 9497's
/// `DeserializeElement`, and so rind, refuses.
fn compact(suite: &'static Suite, bytes: &[u8], at: &[usize]) -> bool {
    core::ptr::eq(suite, &P256_SHA256_ARGON2ID) && at.iter().any(|&i| bytes.get(i) == Some(&5))
}

/// Whether rind refuses `session`: an empty identity, which RFC 9807's
/// `<1..2^16-1>` excludes, or a field too long for its two-byte length.
fn session_refused(session: &Session<'_>) -> bool {
    let long = |field: &[u8]| field.len() > usize::from(u16::MAX);
    let bad = |id: Option<&[u8]>| id.is_some_and(|id| id.is_empty() || long(id));
    long(session.context) || bad(session.client_identity) || bad(session.server_identity)
}

/// SHA-256 of a seed and a counter, so opaque-ke's draws replay from the
/// input.
struct Rng {
    seed: [u8; 32],
    counter: u64,
}

impl Rng {
    fn new(seed: &[u8; 32]) -> Self {
        Self {
            seed: *seed,
            counter: 0,
        }
    }
}

impl rand_core_voprf::RngCore for Rng {
    fn next_u32(&mut self) -> u32 {
        rand_core_voprf::impls::next_u32_via_fill(self)
    }

    fn next_u64(&mut self) -> u64 {
        rand_core_voprf::impls::next_u64_via_fill(self)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        use sha2::Digest;
        for chunk in dest.chunks_mut(32) {
            let block = sha2::Sha256::new()
                .chain_update(self.seed)
                .chain_update(self.counter.to_le_bytes())
                .finalize();
            self.counter += 1;
            chunk.copy_from_slice(&block[..chunk.len()]);
        }
    }

    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core_voprf::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

// Seeded from the fuzzer's input, as a reference's test only needs.
impl rand_core_voprf::CryptoRng for Rng {}
