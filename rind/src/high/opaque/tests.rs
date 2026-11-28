// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use serde_json::Value;

use super::*;
use crate::mid::rng::SliceRandomSource;

/// RFC 9807's test vectors' configurations, which stretch with the identity.
static RISTRETTO255_IDENTITY: Suite = Suite {
    group: GroupId::Ristretto255,
    stretch: Stretch::Identity,
    name: "OPAQUE-3DH(ristretto255-SHA512, Identity)",
};

static P256_IDENTITY: Suite = Suite {
    group: GroupId::P256,
    stretch: Stretch::Identity,
    name: "OPAQUE-3DH(P256-SHA256, Identity)",
};

/// RFC 9807's Argon2id shape, one pass over four lanes, in 256 KiB rather
/// than 2 GiB, so the tests reach the stretch the shipped suites run.
const SMALL_ARGON2ID: Cost = Cost {
    memory_kib: 256,
    passes: 1,
    lanes: 4,
};

static RISTRETTO255_SMALL: Suite = Suite {
    group: GroupId::Ristretto255,
    stretch: Stretch::Argon2id(SMALL_ARGON2ID),
    name: "OPAQUE-3DH(ristretto255-SHA512, small Argon2id)",
};

static P256_SMALL: Suite = Suite {
    group: GroupId::P256,
    stretch: Stretch::Argon2id(SMALL_ARGON2ID),
    name: "OPAQUE-3DH(P256-SHA256, small Argon2id)",
};

const SUITES: [&Suite; 4] = [
    &RISTRETTO255_IDENTITY,
    &P256_IDENTITY,
    &RISTRETTO255_SMALL,
    &P256_SMALL,
];

fn h(hex: &str) -> Vec<u8> {
    hex::decode(hex).unwrap()
}

fn field(v: &Value, section: &str, name: &str) -> Vec<u8> {
    h(v[section][name].as_str().unwrap())
}

fn optional(v: &Value, name: &str) -> Option<Vec<u8>> {
    v["inputs"][name].as_str().map(h)
}

/// RFC 9807 Appendix C's vectors for ristretto255 and P-256.
fn vectors() -> Vec<Value> {
    let path = format!(
        "{}/../thirdparty/vectors/rfc9807/vectors.json",
        env!("CARGO_MANIFEST_DIR")
    );
    serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap()
}

fn identity_suite(v: &Value) -> &'static Suite {
    assert_eq!(v["config"]["KSF"], "Identity");
    match v["config"]["Group"].as_str().unwrap() {
        "ristretto255" => &RISTRETTO255_IDENTITY,
        "P256_XMD:SHA-256_SSWU_RO_" => &P256_IDENTITY,
        group => unreachable!("{group}"),
    }
}

fn scalar<G: Ake>(bytes: &[u8]) -> G::Scalar {
    G::scalar_from_bytes(bytes).unwrap()
}

/// Builds a setup from its parts, as the vectors give them.
fn setup<G: Ake>(suite: &'static Suite, v: &Value, fake_public_key: &[u8]) -> ServerSetup {
    let setup = ServerSetup::new::<G>(
        suite,
        concat(&[
            &field(v, "inputs", "oprf_seed"),
            &field(v, "inputs", "server_private_key"),
            fake_public_key,
        ]),
    )
    .unwrap();
    assert_eq!(setup.public_key(), field(v, "inputs", "server_public_key"));
    setup
}

fn real_vector<G: Ake>(suite: &'static Suite, v: &Value)
where
    RegistrationInner: From<ClientState<G>>,
    LoginInner: From<LoginState<G>>,
{
    let _entry = Entry::new_secret();
    let input = |name| field(v, "inputs", name);
    let output = |name| field(v, "outputs", name);
    let context = h(v["config"]["Context"].as_str().unwrap());
    let client_identity = optional(v, "client_identity");
    let server_identity = optional(v, "server_identity");
    let session = Session {
        context: &context,
        client_identity: client_identity.as_deref(),
        server_identity: server_identity.as_deref(),
    };
    let password = input("password");
    let identifier = input("credential_identifier");
    let server = setup::<G>(suite, v, &input("server_public_key"));

    let (client, request) = ClientRegistration::start_with::<G>(
        suite,
        &password,
        scalar::<G>(&input("blind_registration")),
    )
    .unwrap();
    assert_eq!(request.as_ref(), output("registration_request"));
    let response = server.register(&request, &identifier).unwrap();
    assert_eq!(response.as_ref(), output("registration_response"));
    let (record, export_key) = client
        .finish_with(
            &response,
            &session,
            &mut SliceRandomSource(&input("envelope_nonce")),
        )
        .unwrap();
    assert_eq!(record.as_ref(), output("registration_upload"));
    assert_eq!(export_key.as_ref(), output("export_key"));

    let randomness = [input("client_nonce"), input("client_keyshare_seed")].concat();
    let (client, ke1) = ClientLogin::start_with::<G>(
        suite,
        &password,
        scalar::<G>(&input("blind_login")),
        &mut SliceRandomSource(&randomness),
    )
    .unwrap();
    assert_eq!(ke1.as_ref(), output("KE1"));

    // The first bytes are the fake masking key, which a registered account's
    // login draws and discards.
    let randomness = [
        vec![0xff; G::LENS.nh],
        input("masking_nonce"),
        input("server_nonce"),
        input("server_keyshare_seed"),
    ]
    .concat();
    let credential = Credential {
        identifier: &identifier,
        record: Some(&record),
    };
    let (server_login, ke2) = server
        .login_with(
            &ke1,
            &credential,
            &session,
            &mut SliceRandomSource(&randomness),
        )
        .unwrap();
    assert_eq!(ke2.as_ref(), output("KE2"));

    let (ke3, session_key, export_key) = client.finish(&ke2, &session).unwrap();
    assert_eq!(ke3.as_ref(), output("KE3"));
    ct::public_slice(session_key.as_ref());
    ct::public_slice(export_key.as_ref());
    assert_eq!(session_key.as_ref(), output("session_key"));
    assert_eq!(export_key.as_ref(), output("export_key"));
    let server_key = server_login.finish(&ke3).unwrap();
    ct::public_slice(server_key.as_ref());
    assert_eq!(server_key.as_ref(), output("session_key"));
}

fn fake_vector<G: Ake>(suite: &'static Suite, v: &Value) {
    let _entry = Entry::new_secret();
    let input = |name| field(v, "inputs", name);
    let context = h(v["config"]["Context"].as_str().unwrap());
    let client_identity = input("client_identity");
    let server_identity = input("server_identity");
    let session = Session {
        context: &context,
        client_identity: Some(&client_identity),
        server_identity: Some(&server_identity),
    };
    let server = setup::<G>(suite, v, &input("client_public_key"));
    // The setup's fake public key is the vector's fake record's.
    let (_, public) = derive_dh_from_private::<G>(&input("client_private_key"));
    assert_eq!(public.as_ref(), input("client_public_key"));

    let randomness = [
        input("masking_key"),
        input("masking_nonce"),
        input("server_nonce"),
        input("server_keyshare_seed"),
    ]
    .concat();
    let ke1 = Ke1::new(suite, &input("KE1")).unwrap();
    let credential = Credential {
        identifier: &input("credential_identifier"),
        record: None,
    };
    let (_, ke2) = server
        .login_with(
            &ke1,
            &credential,
            &session,
            &mut SliceRandomSource(&randomness),
        )
        .unwrap();
    assert_eq!(ke2.as_ref(), field(v, "outputs", "KE2"));
}

fn derive_dh_from_private<G: Ake>(private: &[u8]) -> (G::Scalar, Bytes<MAX_ELEMENT>) {
    let private = scalar::<G>(private);
    let public = encode::<G>(&G::mul_base(&private));
    (private, public)
}

#[test]
fn rfc9807_vectors() {
    let vectors = vectors();
    assert_eq!(vectors.len(), 6);
    for v in &vectors {
        let suite = identity_suite(v);
        match v["config"]["Fake"].as_str().unwrap() {
            "False" => with_ake!(suite, G => real_vector::<G>(suite, v)),
            "True" => with_ake!(suite, G => fake_vector::<G>(suite, v)),
            fake => unreachable!("{fake}"),
        }
    }
}

#[test]
fn lengths() {
    // RFC 9807 Appendix C's lengths, and the longest of each.
    let suites = [
        (
            <Ristretto255 as Ake>::LENS,
            (32, 64),
            192,
            128,
            96,
            320,
            128,
        ),
        (<P256 as Ake>::LENS, (33, 32), 129, 97, 98, 259, 97),
    ];
    for (l, (npk, nh), record, masked, ke1, ke2, setup) in suites {
        assert_eq!((l.npk, l.nh), (npk, nh));
        assert_eq!(
            (l.record(), l.masked(), l.ke1(), l.ke2(), l.setup()),
            (record, masked, ke1, ke2, setup)
        );
    }
    let longest = |f: fn(Lens) -> usize| suites.iter().map(|s| f(s.0)).max().unwrap();
    assert_eq!(MAX_PK, longest(|l| l.npk));
    assert_eq!(MAX_HASH, longest(|l| l.nh));
    assert_eq!(MAX_RECORD, longest(Lens::record));
    assert_eq!(MAX_MASKED, longest(Lens::masked));
    assert_eq!(MAX_KE1, longest(Lens::ke1));
    assert_eq!(MAX_KE2, longest(Lens::ke2));
    assert_eq!(MAX_SETUP, longest(Lens::setup));
}

/// A registration and a login with `password` at registration and `guess`
/// at login, under `registered` and `login` sessions, returning the
/// client's and the server's results.
struct Run<'a> {
    suite: &'static Suite,
    password: &'a [u8],
    guess: &'a [u8],
    registered: Session<'a>,
    login: Session<'a>,
}

impl Run<'_> {
    fn new(suite: &'static Suite) -> Self {
        Run {
            suite,
            password: b"password",
            guess: b"password",
            registered: Session::default(),
            login: Session::default(),
        }
    }

    fn register(&self, server: &ServerSetup) -> (RegistrationRecord, ExportKey) {
        let (client, request) = ClientRegistration::start(self.suite, self.password).unwrap();
        let response = server.register(&request, b"alice").unwrap();
        client.finish(&response, &self.registered).unwrap()
    }

    /// The client's export key, and whether both sides agreed on a session
    /// key.
    fn run(&self) -> Result<ExportKey, Error> {
        let server = ServerSetup::generate(self.suite).unwrap();
        let (record, registered_export_key) = self.register(&server);
        let (client, ke1) = ClientLogin::start(self.suite, self.guess)?;
        let credential = Credential {
            identifier: b"alice",
            record: Some(&record),
        };
        let (server_login, ke2) = server.login(&ke1, &credential, &self.login)?;
        let (ke3, client_key, export_key) = client.finish(&ke2, &self.login)?;
        // A client that accepted the server's MAC shares the server's keys, so
        // a wrong password or session must fail above, not here.
        let server_key = server_login.finish(&ke3).unwrap();
        for key in [client_key.as_ref(), server_key.as_ref()] {
            ct::public_slice(key);
        }
        for key in [export_key.as_ref(), registered_export_key.as_ref()] {
            ct::public_slice(key);
        }
        assert_eq!(client_key.as_ref(), server_key.as_ref());
        assert_eq!(export_key.as_ref(), registered_export_key.as_ref());
        Ok(export_key)
    }
}

#[test]
fn round_trip() {
    for suite in SUITES {
        Run::new(suite).run().unwrap();
        let session = Session {
            context: b"app v1",
            client_identity: Some(b"alice@example.com"),
            server_identity: Some(b"example.com"),
        };
        Run {
            registered: session,
            login: session,
            ..Run::new(suite)
        }
        .run()
        .unwrap();
        // Registration binds only the identities.
        Run {
            registered: Session {
                context: b"other",
                ..session
            },
            login: session,
            ..Run::new(suite)
        }
        .run()
        .unwrap();
        // The empty password, and the longest.
        Run {
            password: b"",
            guess: b"",
            ..Run::new(suite)
        }
        .run()
        .unwrap();
        let longest = vec![0x5a; usize::from(u16::MAX) - 1];
        Run {
            password: &longest,
            guess: &longest,
            ..Run::new(suite)
        }
        .run()
        .unwrap();
    }
}

#[test]
fn refuses_wrong_password_and_sessions() {
    let session = Session {
        context: b"app v1",
        client_identity: Some(b"alice"),
        server_identity: Some(b"example.com"),
    };
    for suite in SUITES {
        let base = Run {
            registered: session,
            login: session,
            ..Run::new(suite)
        };
        let wrong = [
            Run {
                guess: b"passwore",
                ..base
            },
            Run {
                login: Session {
                    client_identity: Some(b"bob"),
                    ..session
                },
                ..base
            },
            Run {
                login: Session {
                    server_identity: None,
                    ..session
                },
                ..base
            },
            Run {
                login: Session {
                    client_identity: None,
                    ..session
                },
                ..base
            },
        ];
        for run in wrong {
            assert_eq!(run.run().err(), Some(Error::BadSignature));
        }
    }
}

#[test]
fn context_mismatch_fails_both_sides() {
    for suite in SUITES {
        let server = ServerSetup::generate(suite).unwrap();
        let run = Run::new(suite);
        let (record, _) = run.register(&server);
        let credential = Credential {
            identifier: b"alice",
            record: Some(&record),
        };
        let client_session = Session {
            context: b"client",
            ..Session::default()
        };
        let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
        let (_, ke2) = server
            .login(&ke1, &credential, &Session::default())
            .unwrap();
        assert_eq!(
            client.finish(&ke2, &client_session).err(),
            Some(Error::BadSignature)
        );
    }
}

#[test]
fn unknown_account_is_refused() {
    for suite in SUITES {
        let server = ServerSetup::generate(suite).unwrap();
        let session = Session::default();
        let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
        let credential = Credential {
            identifier: b"nobody",
            record: None,
        };
        let (server_login, ke2) = server.login(&ke1, &credential, &session).unwrap();
        assert_eq!(ke2.as_ref().len(), with_ake!(suite, G => G::LENS.ke2()));
        assert_eq!(
            client.finish(&ke2, &session).err(),
            Some(Error::BadSignature)
        );
        let nh = with_ake!(suite, G => G::LENS.nh);
        let ke3 = Ke3::new(suite, &vec![0; nh]).unwrap();
        assert_eq!(server_login.finish(&ke3).err(), Some(Error::BadSignature));
    }
}

/// A setup imported with a fake public key whose private part is known lets
/// a client compute the MAC, which the server must still refuse.
#[test]
fn unknown_account_never_gets_a_session_key() {
    for suite in SUITES {
        let server = ServerSetup::generate(suite).unwrap();
        let (_, ke1) = ClientLogin::start(suite, b"password").unwrap();
        let credential = Credential {
            identifier: b"nobody",
            record: None,
        };
        let (server_login, _) = server
            .login(&ke1, &credential, &Session::default())
            .unwrap();
        let forged = Ke3::new(suite, server_login.expected_client_mac.as_ref()).unwrap();
        assert_eq!(
            server_login.finish(&forged).err(),
            Some(Error::BadSignature)
        );
    }
}

#[test]
fn refuses_tampered_messages() {
    for suite in [&RISTRETTO255_IDENTITY, &P256_IDENTITY] {
        let server = ServerSetup::generate(suite).unwrap();
        let session = Session::default();
        let (record, _) = Run::new(suite).register(&server);
        let credential = Credential {
            identifier: b"alice",
            record: Some(&record),
        };

        // Every byte of KE2 is bound into the client's checks.
        let (_, ke1) = ClientLogin::start(suite, b"password").unwrap();
        let (_, ke2) = server.login(&ke1, &credential, &session).unwrap();
        for i in 0..ke2.as_ref().len() {
            let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
            let (_, ke2) = server.login(&ke1, &credential, &session).unwrap();
            let mut bytes = ke2.as_ref().to_vec();
            bytes[i] ^= 1;
            match Ke2::new(suite, &bytes) {
                Ok(ke2) => assert_eq!(
                    client.finish(&ke2, &session).err(),
                    Some(Error::BadSignature),
                    "byte {i}"
                ),
                Err(e) => {
                    // Only a byte of the evaluated element or the key share
                    // can fail to load; the rest is nonces, masked bytes, and
                    // the MAC.
                    let (npk, nh) = with_ake!(suite, G => (G::LENS.npk, G::LENS.nh));
                    let share = bytes.len() - nh - npk;
                    assert!(i < npk || (share..share + npk).contains(&i), "byte {i}");
                    assert!(matches!(e, Error::KeyRejected(_)), "byte {i}");
                }
            }
        }

        // As is every byte of KE1 and KE3 into the server's.
        for i in 0..ke1.as_ref().len() {
            let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
            let mut bytes = ke1.as_ref().to_vec();
            bytes[i] ^= 1;
            let Ok(tampered) = Ke1::new(suite, &bytes) else {
                // Only a byte of an encoded element can fail to load.
                let npk = with_ake!(suite, G => G::LENS.npk);
                assert!(!(npk..npk + NN).contains(&i), "byte {i}");
                continue;
            };
            let (server_login, ke2) = server.login(&tampered, &credential, &session).unwrap();
            // A tampered nonce or key share leaves the server's MAC for the
            // client to refuse; a tampered blinded element, the envelope.
            assert_eq!(
                client.finish(&ke2, &session).err(),
                Some(Error::BadSignature),
                "byte {i}"
            );
            let nh = with_ake!(suite, G => G::LENS.nh);
            let forged = Ke3::new(suite, &vec![0; nh]).unwrap();
            assert_eq!(
                server_login.finish(&forged).err(),
                Some(Error::BadSignature)
            );
        }

        let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
        let (server_login, ke2) = server.login(&ke1, &credential, &session).unwrap();
        let (ke3, _, _) = client.finish(&ke2, &session).unwrap();
        for i in 0..ke3.as_ref().len() {
            let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
            let (server_login, ke2) = server.login(&ke1, &credential, &session).unwrap();
            let (ke3, _, _) = client.finish(&ke2, &session).unwrap();
            let mut bytes = ke3.as_ref().to_vec();
            bytes[i] ^= 1;
            assert_eq!(
                server_login.finish(&Ke3::new(suite, &bytes).unwrap()).err(),
                Some(Error::BadSignature),
                "byte {i}"
            );
        }
        server_login.finish(&ke3).unwrap();
    }
}

#[test]
fn refuses_other_suites() {
    let server = ServerSetup::generate(&RISTRETTO255_IDENTITY).unwrap();
    let other = ServerSetup::generate(&RISTRETTO255_SMALL).unwrap();
    let session = Session::default();
    let (client, request) = ClientRegistration::start(&RISTRETTO255_SMALL, b"password").unwrap();
    assert_eq!(
        server.register(&request, b"alice").err(),
        Some(Error::Unsupported)
    );
    let response = other.register(&request, b"alice").unwrap();
    let (identity_client, _) =
        ClientRegistration::start(&RISTRETTO255_IDENTITY, b"password").unwrap();
    assert_eq!(
        identity_client.finish(&response, &session).err(),
        Some(Error::Unsupported)
    );
    let (record, _) = client.finish(&response, &session).unwrap();

    let (client, ke1) = ClientLogin::start(&RISTRETTO255_IDENTITY, b"password").unwrap();
    let credential = Credential {
        identifier: b"alice",
        record: Some(&record),
    };
    assert_eq!(
        server.login(&ke1, &credential, &session).err(),
        Some(Error::Unsupported)
    );
    let no_record = Credential {
        identifier: b"alice",
        record: None,
    };
    assert_eq!(
        other.login(&ke1, &no_record, &session).err(),
        Some(Error::Unsupported)
    );
    let (server_login, ke2) = server.login(&ke1, &no_record, &session).unwrap();
    let other_ke2 = Ke2::new(&RISTRETTO255_SMALL, ke2.as_ref()).unwrap();
    assert_eq!(
        client.finish(&other_ke2, &session).err(),
        Some(Error::Unsupported)
    );
    let ke3 = Ke3::new(&RISTRETTO255_SMALL, &[0; 64]).unwrap();
    assert_eq!(server_login.finish(&ke3).err(), Some(Error::Unsupported));
}

#[test]
fn refuses_bad_sessions_and_passwords() {
    let long = vec![0; usize::from(u16::MAX) + 1];
    let longest = vec![0; usize::from(u16::MAX)];
    for suite in [&RISTRETTO255_IDENTITY, &P256_IDENTITY] {
        // RFC 9497 5.1 bounds the OPRF's input below 2^16 - 1 bytes.
        let too_long = vec![0; usize::from(u16::MAX)];
        assert_eq!(
            ClientRegistration::start(suite, &too_long).err(),
            Some(Error::WrongLength)
        );
        assert_eq!(
            ClientLogin::start(suite, &too_long).err(),
            Some(Error::WrongLength)
        );

        let ok = Session {
            context: &longest,
            client_identity: Some(&longest),
            server_identity: Some(&longest),
        };
        assert_eq!(ok.check(), Ok(()));
        for bad in [
            Session {
                context: &long,
                ..Session::default()
            },
            Session {
                client_identity: Some(&long),
                ..Session::default()
            },
            Session {
                server_identity: Some(&long),
                ..Session::default()
            },
            Session {
                client_identity: Some(b""),
                ..Session::default()
            },
            Session {
                server_identity: Some(b""),
                ..Session::default()
            },
        ] {
            assert_eq!(bad.check(), Err(Error::WrongLength));
            let server = ServerSetup::generate(suite).unwrap();
            let (client, request) = ClientRegistration::start(suite, b"password").unwrap();
            let response = server.register(&request, b"alice").unwrap();
            assert_eq!(
                client.finish(&response, &bad).err(),
                Some(Error::WrongLength)
            );
            let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
            let credential = Credential {
                identifier: b"alice",
                record: None,
            };
            assert_eq!(
                server.login(&ke1, &credential, &bad).err(),
                Some(Error::WrongLength)
            );
            let (_, ke2) = server
                .login(&ke1, &credential, &Session::default())
                .unwrap();
            assert_eq!(client.finish(&ke2, &bad).err(), Some(Error::WrongLength));
        }
    }
}

/// A message's `new`, its value dropped.
type Parse = fn(&'static Suite, &[u8]) -> Result<(), Error>;

#[test]
fn refuses_bad_messages() {
    let rejected = |e: KeyFormatError| Some(Error::from(e));
    for suite in [&RISTRETTO255_IDENTITY, &P256_IDENTITY] {
        let (l, zeros_error) = match suite.group {
            GroupId::Ristretto255 => (<Ristretto255 as Ake>::LENS, KeyFormatError::SmallOrder),
            GroupId::P256 => (<P256 as Ake>::LENS, KeyFormatError::NotOnCurve),
        };
        let server = ServerSetup::generate(suite).unwrap();
        let pk = server.public_key().to_vec();
        let zeros = vec![0; l.npk];
        let fill = |n: usize| vec![7; n];

        // A wrong length.
        for len in [0, l.npk - 1, l.npk + 1] {
            assert_eq!(
                RegistrationRequest::new(suite, &fill(len)).err(),
                rejected(KeyFormatError::WrongLength)
            );
        }
        let checks: [(usize, Parse); 5] = [
            (2 * l.npk, |s, b| {
                RegistrationResponse::new(s, b).map(|_| ())
            }),
            (l.record(), |s, b| RegistrationRecord::new(s, b).map(|_| ())),
            (l.ke1(), |s, b| Ke1::new(s, b).map(|_| ())),
            (l.ke2(), |s, b| Ke2::new(s, b).map(|_| ())),
            (l.nh, |s, b| Ke3::new(s, b).map(|_| ())),
        ];
        for (len, new) in checks {
            for wrong in [0, len - 1, len + 1] {
                assert_eq!(
                    new(suite, &fill(wrong)).err(),
                    rejected(KeyFormatError::WrongLength)
                );
            }
        }

        // Each element, and only those, must decode and not be the identity.
        assert_eq!(
            RegistrationRequest::new(suite, &zeros).err(),
            rejected(zeros_error)
        );
        assert!(RegistrationRequest::new(suite, &pk).is_ok());
        let response = |a: &[u8], b: &[u8]| RegistrationResponse::new(suite, &[a, b].concat());
        assert!(response(&pk, &pk).is_ok());
        assert_eq!(response(&zeros, &pk).err(), rejected(zeros_error));
        assert_eq!(response(&pk, &zeros).err(), rejected(zeros_error));
        let rest = fill(l.record() - l.npk);
        assert!(RegistrationRecord::new(suite, &[&pk[..], &rest].concat()).is_ok());
        assert_eq!(
            RegistrationRecord::new(suite, &[&zeros[..], &rest].concat()).err(),
            rejected(zeros_error)
        );
        let ke1 = |a: &[u8], b: &[u8]| Ke1::new(suite, &[a, &fill(NN), b].concat());
        assert!(ke1(&pk, &pk).is_ok());
        assert_eq!(ke1(&zeros, &pk).err(), rejected(zeros_error));
        assert_eq!(ke1(&pk, &zeros).err(), rejected(zeros_error));
        let ke2 = |a: &[u8], b: &[u8]| {
            Ke2::new(
                suite,
                &[a, &fill(NN + l.masked() + NN), b, &fill(l.nh)].concat(),
            )
        };
        assert!(ke2(&pk, &pk).is_ok());
        assert_eq!(ke2(&zeros, &pk).err(), rejected(zeros_error));
        assert_eq!(ke2(&pk, &zeros).err(), rejected(zeros_error));
        assert!(Ke3::new(suite, &vec![0; l.nh]).is_ok());
    }
}

#[test]
fn setup_encoding() {
    for suite in [&RISTRETTO255_IDENTITY, &P256_IDENTITY] {
        let l = with_ake!(suite, G => G::LENS);
        let server = ServerSetup::generate(suite).unwrap();
        let bytes = server.to_bytes();
        assert_eq!(bytes.as_ref().len(), l.setup());
        let loaded = ServerSetup::from_bytes(suite, bytes.as_ref()).unwrap();
        assert_eq!(loaded.public_key(), server.public_key());
        let reloaded = loaded.to_bytes();
        ct::public_slice(reloaded.as_ref());
        ct::public_slice(bytes.as_ref());
        assert_eq!(reloaded.as_ref(), bytes.as_ref());

        // A login against the loaded setup verifies a record the original
        // registered.
        let (record, _) = Run::new(suite).register(&server);
        let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
        let credential = Credential {
            identifier: b"alice",
            record: Some(&record),
        };
        let session = Session::default();
        let (server_login, ke2) = loaded.login(&ke1, &credential, &session).unwrap();
        let (ke3, _, _) = client.finish(&ke2, &session).unwrap();
        server_login.finish(&ke3).unwrap();

        let rejected = |e: KeyFormatError| Some(Error::from(e));
        let mut bad = bytes.as_ref().to_vec();
        bad.pop();
        assert_eq!(
            ServerSetup::from_bytes(suite, &bad).err(),
            rejected(KeyFormatError::WrongLength)
        );
        let mut bad = bytes.as_ref().to_vec();
        bad[l.nh..l.nh + NSK].fill(0);
        assert_eq!(
            ServerSetup::from_bytes(suite, &bad).err(),
            rejected(KeyFormatError::ScalarOutOfRange)
        );
        bad[l.nh..l.nh + NSK].fill(0xff);
        assert_eq!(
            ServerSetup::from_bytes(suite, &bad).err(),
            rejected(KeyFormatError::ScalarOutOfRange)
        );
        let mut bad = bytes.as_ref().to_vec();
        bad[l.nh + NSK..].fill(0);
        assert!(ServerSetup::from_bytes(suite, &bad).is_err());
    }
}

/// Drops `value` in place and checks every byte of it reads zero after.
/// `tests/zeroing.rs` does this for the other key types, but a returned key
/// takes a login, which only the identity-stretch suites here run cheaply.
#[allow(unsafe_code)]
fn assert_wiped_on_drop<T>(value: T) {
    let mut value = core::mem::ManuallyDrop::new(value);
    // SAFETY: dropped once, and the value stays in place, so its bytes can be
    // read back; they are plain integers, never a pointer.
    let bytes = unsafe {
        core::mem::ManuallyDrop::drop(&mut value);
        core::slice::from_raw_parts((&raw const *value).cast::<u8>(), size_of::<T>())
    };
    assert!(bytes.iter().all(|&b| b == 0));
}

#[test]
fn debug_shows_no_secret() {
    let suite = &RISTRETTO255_IDENTITY;
    let server = ServerSetup::generate(suite).unwrap();
    let (client, request) = ClientRegistration::start(suite, b"password").unwrap();
    let response = server.register(&request, b"alice").unwrap();
    assert_eq!(
        format!("{client:?}"),
        "ClientRegistration { suite: OPAQUE-3DH(ristretto255-SHA512, Identity), .. }"
    );
    let (record, export_key) = client.finish(&response, &Session::default()).unwrap();
    assert_eq!(
        format!("{server:?}"),
        "ServerSetup { suite: OPAQUE-3DH(ristretto255-SHA512, Identity), .. }"
    );
    assert_eq!(format!("{:?}", server.to_bytes()), "SetupBytes(..)");
    assert_eq!(
        format!("{record:?}"),
        "RegistrationRecord { suite: OPAQUE-3DH(ristretto255-SHA512, Identity), .. }"
    );
    assert_eq!(format!("{export_key:?}"), "ExportKey(..)");
    let (client, ke1) = ClientLogin::start(suite, b"password").unwrap();
    assert_eq!(
        format!("{client:?}"),
        "ClientLogin { suite: OPAQUE-3DH(ristretto255-SHA512, Identity), .. }"
    );
    let credential = Credential {
        identifier: b"alice",
        record: Some(&record),
    };
    let (server_login, ke2) = server
        .login(&ke1, &credential, &Session::default())
        .unwrap();
    assert_eq!(
        format!("{server_login:?}"),
        "ServerLogin { suite: OPAQUE-3DH(ristretto255-SHA512, Identity), .. }"
    );
    let (ke3, session_key, _) = client.finish(&ke2, &Session::default()).unwrap();
    assert_eq!(format!("{session_key:?}"), "SessionKey(..)");
    assert_wiped_on_drop(session_key);
    assert_wiped_on_drop(export_key);
    for (shown, name) in [
        (format!("{request:?}"), "RegistrationRequest(["),
        (format!("{response:?}"), "RegistrationResponse(["),
        (format!("{ke1:?}"), "Ke1(["),
        (format!("{ke2:?}"), "Ke2(["),
        (format!("{ke3:?}"), "Ke3(["),
    ] {
        assert!(shown.starts_with(name), "{shown}");
    }
    assert_eq!(
        format!("{:?}", RISTRETTO255_SHA512_ARGON2ID),
        "OPAQUE-3DH(ristretto255-SHA512, Argon2id)"
    );
    assert_eq!(
        format!("{:?}", P256_SHA256_ARGON2ID),
        "OPAQUE-3DH(P256-SHA256, Argon2id)"
    );
}

#[test]
fn shipped_suites_stretch_with_rfc9807_argon2id() {
    // RFC 9807 section 7: m = 2^21, t = 1, p = 4.
    for suite in [&RISTRETTO255_SHA512_ARGON2ID, &P256_SHA256_ARGON2ID] {
        let Stretch::Argon2id(cost) = suite.stretch else {
            unreachable!()
        };
        assert_eq!((cost.memory_kib, cost.passes, cost.lanes), (1 << 21, 1, 4));
    }
}

#[test]
fn stays_secret() {
    // Under `admin/ctgrind`, nothing may branch on or index by the password,
    // the setup's OPRF seed or private key, or anything derived from them,
    // until a value is sent or a check's verdict is declassified. The
    // setup marks its own secrets when loaded.
    for suite in [&RISTRETTO255_IDENTITY, &P256_IDENTITY, &P256_SMALL] {
        let password = [0x5a; 24];
        ct::secret_slice(&password);
        let server = ServerSetup::generate(suite).unwrap();
        let session = Session {
            context: b"context",
            client_identity: Some(b"alice"),
            server_identity: None,
        };
        let (client, request) = ClientRegistration::start(suite, &password).unwrap();
        let response = server.register(&request, b"alice").unwrap();
        let (record, export_key) = client.finish(&response, &session).unwrap();

        let (client, ke1) = ClientLogin::start(suite, &password).unwrap();
        let credential = Credential {
            identifier: b"alice",
            record: Some(&record),
        };
        let (server_login, ke2) = server.login(&ke1, &credential, &session).unwrap();
        let (ke3, client_key, login_export_key) = client.finish(&ke2, &session).unwrap();
        let server_key = server_login.finish(&ke3).unwrap();
        ct::public_slice(client_key.as_ref());
        ct::public_slice(server_key.as_ref());
        ct::public_slice(export_key.as_ref());
        ct::public_slice(login_export_key.as_ref());
        assert_eq!(client_key.as_ref(), server_key.as_ref());
        assert_eq!(export_key.as_ref(), login_export_key.as_ref());

        // A wrong password and an unknown account fail closed.
        let mut wrong = password;
        wrong[0] ^= 1;
        ct::secret_slice(&wrong);
        let (client, ke1) = ClientLogin::start(suite, &wrong).unwrap();
        let (_, ke2) = server.login(&ke1, &credential, &session).unwrap();
        assert_eq!(
            client.finish(&ke2, &session).err(),
            Some(Error::BadSignature)
        );
        let (client, ke1) = ClientLogin::start(suite, &password).unwrap();
        let unknown = Credential {
            identifier: b"bob",
            record: None,
        };
        let (_, ke2) = server.login(&ke1, &unknown, &session).unwrap();
        assert_eq!(
            client.finish(&ke2, &session).err(),
            Some(Error::BadSignature)
        );
    }
}

/// opaque-ke's suites for each of rind's test suites.
#[cfg(not(any(miri, target_family = "wasm")))]
mod opaque_ke_suites {
    use opaque_ke::argon2::Argon2;
    use opaque_ke::ksf::Identity;
    use opaque_ke::{CipherSuite, Ristretto255, TripleDh};
    use p256_voprf::NistP256;
    use sha2_opaque::{Sha256, Sha512};

    pub(super) struct Ristretto255Identity;
    impl CipherSuite for Ristretto255Identity {
        type OprfCs = Ristretto255;
        type KeyExchange = TripleDh<Ristretto255, Sha512>;
        type Ksf = Identity;
    }

    pub(super) struct P256Identity;
    impl CipherSuite for P256Identity {
        type OprfCs = NistP256;
        type KeyExchange = TripleDh<NistP256, Sha256>;
        type Ksf = Identity;
    }

    pub(super) struct Ristretto255Argon2;
    impl CipherSuite for Ristretto255Argon2 {
        type OprfCs = Ristretto255;
        type KeyExchange = TripleDh<Ristretto255, Sha512>;
        type Ksf = Argon2<'static>;
    }

    pub(super) struct P256Argon2;
    impl CipherSuite for P256Argon2 {
        type OprfCs = NistP256;
        type KeyExchange = TripleDh<NistP256, Sha256>;
        type Ksf = Argon2<'static>;
    }
}

/// Runs a registration and logins each way between rind and opaque-ke,
/// under opaque-ke's suite `$cs` and `ksf`, and checks every message rind
/// sends parses there, and that both agree on every key.
#[cfg(not(any(miri, target_family = "wasm")))]
macro_rules! matches_opaque_ke {
    ($cs:ty, $suite:expr, $ksf:expr) => {{
        use opaque_ke::{
            ClientLoginFinishParameters, ClientRegistrationFinishParameters,
            CredentialFinalization, CredentialRequest, CredentialResponse, Identifiers,
            RegistrationRequest as OkRequest, RegistrationResponse as OkResponse,
            RegistrationUpload, ServerLoginParameters, ServerRegistration,
        };
        use rand_core_voprf::OsRng;

        type Cs = $cs;
        let suite: &'static Suite = $suite;
        let ksf = $ksf;
        let identifier: &[u8] = b"alice@example.com";
        for (context, client_identity, server_identity) in [
            (&b""[..], None, None),
            (
                &b"app v1"[..],
                Some(&b"alice"[..]),
                Some(&b"example.com"[..]),
            ),
        ] {
            let session = Session {
                context,
                client_identity,
                server_identity,
            };
            let identifiers = Identifiers {
                client: client_identity,
                server: server_identity,
            };
            let context = (!context.is_empty()).then_some(context);
            let server_params = || ServerLoginParameters {
                context,
                identifiers,
            };

            // The setups load each other's encodings.
            let theirs = opaque_ke::ServerSetup::<Cs>::new(&mut OsRng);
            let ours = ServerSetup::from_bytes(suite, &theirs.serialize()).unwrap();
            assert_eq!(
                ours.public_key(),
                &theirs.keypair().public().serialize()[..]
            );
            // opaque-ke's arithmetic is not constant time, so nothing it
            // takes is marked secret.
            let ours_bytes = ours.to_bytes();
            ct::public_slice(ours_bytes.as_ref());
            assert_eq!(ours_bytes.as_ref(), &theirs.serialize()[..]);
            let theirs = opaque_ke::ServerSetup::<Cs>::deserialize(ours_bytes.as_ref()).unwrap();

            for password in [&b"password"[..], b"", &[0xa5; 1000]] {
                // rind's client registers with both servers, whose
                // evaluations match.
                let (client, request) = ClientRegistration::start(suite, password).unwrap();
                let response = ours.register(&request, identifier).unwrap();
                let their_response = ServerRegistration::<Cs>::start(
                    &theirs,
                    OkRequest::deserialize(request.as_ref()).unwrap(),
                    identifier,
                )
                .unwrap()
                .message;
                assert_eq!(response.as_ref(), &their_response.serialize()[..]);
                let (our_record, our_export_key) = client.finish(&response, &session).unwrap();
                ct::public_slice(our_export_key.as_ref());
                let their_record = ServerRegistration::<Cs>::finish(
                    RegistrationUpload::deserialize(our_record.as_ref()).unwrap(),
                );
                assert_eq!(their_record.serialize().as_slice(), our_record.as_ref());

                // opaque-ke's client registers with rind's server.
                let start =
                    opaque_ke::ClientRegistration::<Cs>::start(&mut OsRng, password).unwrap();
                let request = RegistrationRequest::new(suite, &start.message.serialize()).unwrap();
                let response = ours.register(&request, identifier).unwrap();
                let finish = start
                    .state
                    .finish(
                        &mut OsRng,
                        password,
                        OkResponse::deserialize(response.as_ref()).unwrap(),
                        ClientRegistrationFinishParameters::new(identifiers, Some(&ksf)),
                    )
                    .unwrap();
                let their_export_key = finish.export_key;
                let record = RegistrationRecord::new(suite, &finish.message.serialize()).unwrap();

                // Each client logs in to the other's server, for the record
                // it registered and the one the other client did.
                for (record, export_key) in [
                    (&record, &their_export_key[..]),
                    (&our_record, our_export_key.as_ref()),
                ] {
                    // rind's client, opaque-ke's server.
                    let (client, ke1) = ClientLogin::start(suite, password).unwrap();
                    let their_server = opaque_ke::ServerLogin::<Cs>::start(
                        &mut OsRng,
                        &theirs,
                        Some(ServerRegistration::<Cs>::deserialize(record.as_ref()).unwrap()),
                        CredentialRequest::deserialize(ke1.as_ref()).unwrap(),
                        identifier,
                        server_params(),
                    )
                    .unwrap();
                    let ke2 = Ke2::new(suite, &their_server.message.serialize()).unwrap();
                    let (ke3, session_key, login_export_key) =
                        client.finish(&ke2, &session).unwrap();
                    ct::public_slice(session_key.as_ref());
                    ct::public_slice(login_export_key.as_ref());
                    assert_eq!(login_export_key.as_ref(), export_key);
                    let their_key = their_server
                        .state
                        .finish(
                            CredentialFinalization::deserialize(ke3.as_ref()).unwrap(),
                            server_params(),
                        )
                        .unwrap()
                        .session_key;
                    assert_eq!(session_key.as_ref(), &their_key[..]);

                    // opaque-ke's client, rind's server.
                    let start = opaque_ke::ClientLogin::<Cs>::start(&mut OsRng, password).unwrap();
                    let ke1 = Ke1::new(suite, &start.message.serialize()).unwrap();
                    let credential = Credential {
                        identifier,
                        record: Some(record),
                    };
                    let (server_login, ke2) = ours.login(&ke1, &credential, &session).unwrap();
                    let finish = start
                        .state
                        .finish(
                            &mut OsRng,
                            password,
                            CredentialResponse::deserialize(ke2.as_ref()).unwrap(),
                            ClientLoginFinishParameters::new(context, identifiers, Some(&ksf)),
                        )
                        .unwrap();
                    assert_eq!(&finish.export_key[..], export_key);
                    let ke3 = Ke3::new(suite, &finish.message.serialize()).unwrap();
                    let session_key = server_login.finish(&ke3).unwrap();
                    ct::public_slice(session_key.as_ref());
                    assert_eq!(session_key.as_ref(), &finish.session_key[..]);
                }

                // Neither client logs in to an account the other's server
                // does not hold, nor tells its response from a real one's.
                let (client, ke1) = ClientLogin::start(suite, password).unwrap();
                let their_server = opaque_ke::ServerLogin::<Cs>::start(
                    &mut OsRng,
                    &theirs,
                    None,
                    CredentialRequest::deserialize(ke1.as_ref()).unwrap(),
                    identifier,
                    server_params(),
                )
                .unwrap();
                let ke2 = Ke2::new(suite, &their_server.message.serialize()).unwrap();
                assert_eq!(
                    client.finish(&ke2, &session).err(),
                    Some(Error::BadSignature)
                );
                let start = opaque_ke::ClientLogin::<Cs>::start(&mut OsRng, password).unwrap();
                let ke1 = Ke1::new(suite, &start.message.serialize()).unwrap();
                let unknown = Credential {
                    identifier,
                    record: None,
                };
                let (_, ke2) = ours.login(&ke1, &unknown, &session).unwrap();
                assert!(
                    start
                        .state
                        .finish(
                            &mut OsRng,
                            password,
                            CredentialResponse::deserialize(ke2.as_ref()).unwrap(),
                            ClientLoginFinishParameters::new(context, identifiers, Some(&ksf)),
                        )
                        .is_err()
                );
            }
        }
    }};
}

#[cfg(not(any(miri, target_family = "wasm")))]
#[test]
fn matches_opaque_ke() {
    use opaque_ke::argon2::{Algorithm, Argon2, Params, Version};
    use opaque_ke::ksf::Identity;

    let small = || {
        Argon2::new(
            Algorithm::Argon2id,
            Version::V0x13,
            Params::new(
                SMALL_ARGON2ID.memory_kib,
                SMALL_ARGON2ID.passes,
                SMALL_ARGON2ID.lanes,
                None,
            )
            .unwrap(),
        )
    };
    matches_opaque_ke!(
        opaque_ke_suites::Ristretto255Identity,
        &RISTRETTO255_IDENTITY,
        Identity
    );
    matches_opaque_ke!(opaque_ke_suites::P256Identity, &P256_IDENTITY, Identity);
    matches_opaque_ke!(
        opaque_ke_suites::Ristretto255Argon2,
        &RISTRETTO255_SMALL,
        small()
    );
    matches_opaque_ke!(opaque_ke_suites::P256Argon2, &P256_SMALL, small());
}
