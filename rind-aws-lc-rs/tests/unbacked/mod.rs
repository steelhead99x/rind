//! EC, DSA, and DH keys that aws-lc parses or refuses and rind does not load
//! itself: keys on curves rind cannot back, keys whose curve is given by
//! explicit parameters, and DSA and DH keys. `keys.rs` checks each public key
//! through `rsa::PublicEncryptingKey::from_der` and `parity.rs` each private
//! key through `signature::PqdsaKeyPair::from_pkcs8`, both refusing it with
//! aws-lc-rs's kind.
//!
//! The curves' parameters are the crate's own `src/evp/*.der`, OpenSSL's
//! `openssl ecparam -name <curve> -param_enc explicit -outform DER`. The
//! keys here are `openssl genpkey -algorithm EC -pkeyopt
//! ec_paramgen_curve:<curve> -outform DER`.

#![allow(dead_code)]

/// A case's name, its DER, and the kind aws-lc-rs is expected to give, when
/// the case pins one.
pub type Case = (String, Vec<u8>, Option<&'static str>);

const WRONG: Option<&str> = Some("WrongAlgorithm");
const INVALID: Option<&str> = Some("InvalidEncoding");

const EC: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01];
const DSA: &[u8] = &[0x2a, 0x86, 0x48, 0xce, 0x38, 0x04, 0x01];
const DH: &[u8] = &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x03, 0x01];

pub struct Curve {
    pub name: &'static str,
    pub oid: &'static [u8],
    /// Whether rind backs it.
    pub backed: bool,
}

pub const CURVES: [Curve; 10] = [
    Curve {
        name: "p224",
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x21],
        backed: false,
    },
    Curve {
        name: "p256",
        oid: &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07],
        backed: true,
    },
    Curve {
        name: "p384",
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x22],
        backed: true,
    },
    Curve {
        name: "p521",
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x23],
        backed: true,
    },
    Curve {
        name: "secp256k1",
        oid: &[0x2b, 0x81, 0x04, 0x00, 0x0a],
        backed: false,
    },
    Curve {
        name: "brainpool_p224r1",
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x05],
        backed: false,
    },
    Curve {
        name: "brainpool_p256r1",
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07],
        backed: false,
    },
    Curve {
        name: "brainpool_p320r1",
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x09],
        backed: false,
    },
    Curve {
        name: "brainpool_p384r1",
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x0b],
        backed: false,
    },
    Curve {
        name: "brainpool_p512r1",
        oid: &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x0d],
        backed: false,
    },
];

fn read(path: &str) -> Vec<u8> {
    let path = format!("{}/{path}", env!("CARGO_MANIFEST_DIR"));
    std::fs::read(&path).unwrap_or_else(|e| panic!("{path}: {e}"))
}

/// A DER element tagged `tag` holding `contents`.
pub fn der(tag: u8, contents: &[u8]) -> Vec<u8> {
    let len = contents.len();
    let mut out = vec![tag];
    match len {
        0..=0x7f => out.push(len as u8),
        0x80..=0xff => out.extend([0x81, len as u8]),
        _ => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    out.extend_from_slice(contents);
    out
}

/// The elements of a DER body, each as its tag and contents.
fn elements(mut body: &[u8]) -> Vec<(u8, Vec<u8>)> {
    let mut out = Vec::new();
    while !body.is_empty() {
        let tag = body[0];
        let (len, header) = match body[1] {
            len @ 0..=0x7f => (len as usize, 2),
            0x81 => (body[2] as usize, 3),
            0x82 => (u16::from_be_bytes([body[2], body[3]]) as usize, 4),
            _ => panic!("long length"),
        };
        out.push((tag, body[header..header + len].to_vec()));
        body = &body[header + len..];
    }
    out
}

fn join(items: &[(u8, Vec<u8>)]) -> Vec<u8> {
    items
        .iter()
        .flat_map(|(tag, body)| der(*tag, body))
        .collect()
}

/// An unsigned INTEGER holding the big-endian `magnitude`.
pub fn uint(magnitude: &[u8]) -> Vec<u8> {
    let zeros = magnitude.iter().take_while(|byte| **byte == 0).count();
    let mut value = magnitude[zeros..].to_vec();
    if value.first().is_none_or(|top| *top >= 0x80) {
        value.insert(0, 0);
    }
    der(0x02, &value)
}

pub fn spki(oid: &[u8], parameters: &[u8], key: &[u8]) -> Vec<u8> {
    der(
        0x30,
        &[
            der(0x30, &[der(0x06, oid), parameters.to_vec()].concat()),
            der(0x03, &[&[0], key].concat()),
        ]
        .concat(),
    )
}

pub fn pkcs8(oid: &[u8], parameters: &[u8], private_key: &[u8], public: Option<&[u8]>) -> Vec<u8> {
    let mut body = der(0x02, &[u8::from(public.is_some())]);
    body.extend(der(0x30, &[der(0x06, oid), parameters.to_vec()].concat()));
    body.extend(der(0x04, private_key));
    if let Some(public) = public {
        body.extend(der(0x81, public));
    }
    der(0x30, &body)
}

/// A curve's explicit parameters, split into their top-level elements:
/// version, field, curve, base, order, and cofactor.
struct Explicit(Vec<(u8, Vec<u8>)>);

impl Explicit {
    fn of(curve: &Curve) -> Self {
        let der = read(&format!("src/evp/{}.der", curve.name));
        let (tag, body) = elements(&der).remove(0);
        assert_eq!(tag, 0x30);
        Self(elements(&body))
    }

    fn encode(&self) -> Vec<u8> {
        der(0x30, &join(&self.0))
    }

    fn base(&self) -> Vec<u8> {
        self.0[3].1.clone()
    }

    fn order(&self) -> Vec<u8> {
        let mut order = self.0[4].1.clone();
        if order[0] == 0 {
            order.remove(0);
        }
        order
    }

    fn prime(&self) -> Vec<u8> {
        let field = elements(&self.0[1].1);
        let mut p = field[1].1.clone();
        if p[0] == 0 {
            p.remove(0);
        }
        p
    }

    /// The parameters with element `at` replaced, or removed if `None`.
    fn with(&self, at: usize, item: Option<(u8, Vec<u8>)>) -> Vec<u8> {
        let mut items = self.0.clone();
        match item {
            Some(item) => items[at] = item,
            None => {
                items.remove(at);
            }
        }
        der(0x30, &join(&items))
    }

    /// The parameters with the curve's `b` changed, a curve aws-lc lacks.
    fn other_b(&self) -> Vec<u8> {
        let mut curve = elements(&self.0[2].1);
        *curve[1].1.last_mut().unwrap() ^= 1;
        self.with(2, Some((0x30, join(&curve))))
    }

    /// The parameters with zeros before `a` and `b`, which aws-lc tolerates.
    fn padded_ab(&self) -> Vec<u8> {
        let mut curve = elements(&self.0[2].1);
        for item in &mut curve[..2] {
            item.1.insert(0, 0);
        }
        self.with(2, Some((0x30, join(&curve))))
    }
}

/// `point`, uncompressed, in compressed form.
pub fn compressed(point: &[u8]) -> Vec<u8> {
    let len = (point.len() - 1) / 2;
    let mut out = vec![0x02 | (point[point.len() - 1] & 1)];
    out.extend_from_slice(&point[1..=len]);
    out
}

/// `point`, uncompressed, in hybrid form, with its parity bit flipped if
/// `wrong`.
fn hybrid(point: &[u8], wrong: bool) -> Vec<u8> {
    let mut out = point.to_vec();
    out[0] = 0x06 | ((point[point.len() - 1] & 1) ^ u8::from(wrong));
    out
}

fn off_curve(point: &[u8]) -> Vec<u8> {
    let mut out = point.to_vec();
    *out.last_mut().unwrap() ^= 1;
    out
}

/// An OpenSSL key's scalar and uncompressed public point.
fn key_of(curve: &Curve) -> (Vec<u8>, Vec<u8>) {
    let sec1 = read(&format!("tests/unbacked/{}.der", curve.name));
    let (tag, body) = elements(&sec1).remove(0);
    assert_eq!(tag, 0x30);
    let items = elements(&body);
    let point = elements(&items[3].1);
    (items[1].1.clone(), point[0].1[1..].to_vec())
}

/// An RFC 5915 `ECPrivateKey`; `parameters` is the DER inside `[0]`.
pub fn sec1(scalar: &[u8], parameters: Option<&[u8]>, point: Option<&[u8]>) -> Vec<u8> {
    let mut body = der(0x02, &[1]);
    body.extend(der(0x04, scalar));
    if let Some(parameters) = parameters {
        body.extend(der(0xa0, parameters));
    }
    if let Some(point) = point {
        body.extend(der(0xa1, &der(0x03, &[&[0], point].concat())));
    }
    der(0x30, &body)
}

/// Every EC, DSA, and DH `SubjectPublicKeyInfo` case.
pub fn public_keys() -> Vec<Case> {
    let mut cases = Vec::new();
    for curve in &CURVES {
        let name = curve.name;
        let explicit = Explicit::of(curve);
        let named = der(0x06, curve.oid);
        let g = explicit.base();
        let len = (g.len() - 1) / 2;
        let mut add = |label: &str, parameters: &[u8], key: &[u8], expected| {
            cases.push((
                format!("{name} {label}"),
                spki(EC, parameters, key),
                expected,
            ));
        };
        add("G", &named, &g, WRONG);
        add("G compressed", &named, &compressed(&g), WRONG);
        add("G hybrid", &named, &hybrid(&g, false), WRONG);
        add("G hybrid, wrong parity", &named, &hybrid(&g, true), INVALID);
        add("G with 0x05", &named, &[&[0x05], &g[1..]].concat(), INVALID);
        add("off curve", &named, &off_curve(&g), INVALID);
        add(
            "off curve, hybrid",
            &named,
            &hybrid(&off_curve(&g), false),
            INVALID,
        );
        add("infinity", &named, &[0], INVALID);
        add("no point", &named, &[], INVALID);
        add("truncated", &named, &g[..g.len() - 1], INVALID);
        add(
            "x = all ones",
            &named,
            &[&[0x04], &vec![0xff; 2 * len][..]].concat(),
            INVALID,
        );
        add(
            "compressed, x = all ones",
            &named,
            &[&[0x02], &vec![0xff; len][..]].concat(),
            INVALID,
        );
        for junk in [0x01, 0x5a, 0xa7] {
            let x = vec![junk; len];
            add(
                &format!("compressed, x = {junk:#x}s"),
                &named,
                &[&[0x02], &x[..]].concat(),
                None,
            );
        }
        add(
            "compressed, x = p",
            &named,
            &[&[0x03], &explicit.prime()[..]].concat(),
            INVALID,
        );
        add(
            "named, then NULL",
            &[named.clone(), vec![0x05, 0x00]].concat(),
            &g,
            INVALID,
        );
        if !curve.backed {
            let (_, q) = key_of(curve);
            add("Q", &named, &q, WRONG);
            add("Q compressed", &named, &compressed(&q), WRONG);
            add(
                "Q off curve, compressed",
                &named,
                &compressed(&off_curve(&q)),
                None,
            );
        }
        add("explicit, G", &explicit.encode(), &g, WRONG);
        add(
            "explicit, G compressed",
            &explicit.encode(),
            &compressed(&g),
            WRONG,
        );
        add(
            "explicit, off curve",
            &explicit.encode(),
            &off_curve(&g),
            INVALID,
        );
        add(
            "explicit, zeros before a and b",
            &explicit.padded_ab(),
            &g,
            WRONG,
        );
        add("explicit, no cofactor", &explicit.with(5, None), &g, WRONG);
        add(
            "explicit, cofactor 2",
            &explicit.with(5, Some((0x02, vec![2]))),
            &g,
            INVALID,
        );
        add("explicit, other b", &explicit.other_b(), &g, INVALID);
        add(
            "explicit, version 2",
            &explicit.with(0, Some((0x02, vec![2]))),
            &g,
            INVALID,
        );
        add(
            "explicit, compressed base",
            &explicit.with(3, Some((0x04, compressed(&g)))),
            &g,
            INVALID,
        );
        add(
            "explicit, then NULL",
            &[explicit.encode(), vec![0x05, 0x00]].concat(),
            &g,
            INVALID,
        );
    }
    let unknown = Explicit::of(&CURVES[4]).with(4, Some((0x02, vec![0x01, 0x00, 0x01])));
    cases.push((
        "explicit, unknown order".into(),
        spki(EC, &unknown, &[4; 65]),
        INVALID,
    ));
    cases.push((
        "ec, SEQUENCE parameters of garbage".into(),
        spki(EC, &der(0x30, &[0x02, 0x01, 0x01]), &[4; 65]),
        INVALID,
    ));

    // DSA. aws-lc bounds the parameters without checking primality.
    let p1024 = [&[0x80][..], &[0; 126], &[0x01]].concat();
    let q160 = [&[0x80][..], &[0; 18], &[0x01]].concat();
    let dss = |p: &[u8], q: &[u8], g: &[u8]| der(0x30, &[uint(p), uint(q), uint(g)].concat());
    let good = dss(&p1024, &q160, &[2]);
    let y = uint(&[5]);
    let mut dsa = |label: &str, parameters: Vec<u8>, key: Vec<u8>, expected| {
        cases.push((
            format!("dsa {label}"),
            spki(DSA, &parameters, &key),
            expected,
        ));
    };
    dsa("bounded", good.clone(), y.clone(), WRONG);
    dsa("parameters an INTEGER", uint(&[5]), y.clone(), INVALID);
    dsa("toy", dss(&[23], &[11], &[4]), y.clone(), INVALID);
    dsa(
        "key an OCTET STRING",
        good.clone(),
        der(0x04, &[5]),
        INVALID,
    );
    dsa("key 0", good.clone(), uint(&[]), WRONG);
    dsa("key above p", good.clone(), uint(&[0xff; 130]), WRONG);
    dsa(
        "key, then a byte",
        good.clone(),
        [y.clone(), vec![0]].concat(),
        INVALID,
    );
    dsa("key not minimal", good.clone(), der(0x02, &[0, 5]), INVALID);
    dsa("key negative", good.clone(), der(0x02, &[0xff]), INVALID);
    dsa(
        "parameters, then NULL",
        [good.clone(), vec![5, 0]].concat(),
        y.clone(),
        INVALID,
    );
    dsa(
        "four parameters",
        der(
            0x30,
            &[uint(&p1024), uint(&q160), uint(&[2]), uint(&[2])].concat(),
        ),
        y.clone(),
        INVALID,
    );
    dsa(
        "p not minimal",
        der(
            0x30,
            &[der(0x02, &[0, 0, 0x80]), uint(&q160), uint(&[2])].concat(),
        ),
        y.clone(),
        INVALID,
    );
    dsa(
        "g negative",
        der(
            0x30,
            &[uint(&p1024), uint(&q160), der(0x02, &[0x80])].concat(),
        ),
        y.clone(),
        INVALID,
    );
    let mut even = p1024.clone();
    *even.last_mut().unwrap() = 2;
    dsa("p even", dss(&even, &q160, &[2]), y.clone(), INVALID);
    let mut even_q = q160.clone();
    *even_q.last_mut().unwrap() = 2;
    dsa("q even", dss(&p1024, &even_q, &[2]), y.clone(), INVALID);
    dsa("g 0", dss(&p1024, &q160, &[]), y.clone(), INVALID);
    dsa("g 1", dss(&p1024, &q160, &[1]), y.clone(), WRONG);
    dsa("g = p", dss(&p1024, &q160, &p1024), y.clone(), INVALID);
    dsa(
        "g = p - 1",
        dss(&p1024, &q160, &offset(&p1024, -1)),
        y.clone(),
        WRONG,
    );
    let p160 = [&[0x80][..], &[0; 18], &[0x01]].concat();
    let mut q_above = p160.clone();
    *q_above.last_mut().unwrap() = 3;
    dsa("q above p", dss(&p160, &q_above, &[2]), y.clone(), INVALID);
    dsa("q = p", dss(&p160, &p160, &[2]), y.clone(), INVALID);
    for (bits, expected) in [
        (159usize, INVALID),
        (161, INVALID),
        (224, WRONG),
        (255, INVALID),
        (256, WRONG),
    ] {
        let mut q = vec![0u8; bits.div_ceil(8)];
        q[0] = 1 << ((bits - 1) % 8);
        *q.last_mut().unwrap() |= 1;
        dsa(
            &format!("q of {bits} bits"),
            dss(&p1024, &q, &[2]),
            y.clone(),
            expected,
        );
    }
    for (bits, expected) in [(10_000, WRONG), (10_001, INVALID)] {
        let mut p = vec![0u8; usize::div_ceil(bits, 8)];
        p[0] = 1 << ((bits - 1) % 8);
        *p.last_mut().unwrap() |= 1;
        dsa(
            &format!("p of {bits} bits"),
            dss(&p, &q160, &[2]),
            y.clone(),
            expected,
        );
    }

    // DH. aws-lc checks no size but p's, and reads no q.
    let dh_params =
        |p: &[u8], g: &[u8], rest: &[u8]| der(0x30, &[uint(p), uint(g), rest.to_vec()].concat());
    let mut dh = |label: &str, parameters: Vec<u8>, key: Vec<u8>, expected| {
        cases.push((format!("dh {label}"), spki(DH, &parameters, &key), expected));
    };
    let toy = dh_params(&[23], &[5], &[]);
    for (y, expected) in [
        (0, INVALID),
        (1, INVALID),
        (2, WRONG),
        (21, WRONG),
        (22, INVALID),
        (23, INVALID),
    ] {
        dh(&format!("toy, y = {y}"), toy.clone(), uint(&[y]), expected);
    }
    dh("1024 bits", dh_params(&p1024, &[2], &[]), uint(&[5]), WRONG);
    dh("parameters an INTEGER", uint(&[23]), uint(&[5]), INVALID);
    dh("p even", dh_params(&[24], &[5], &[]), uint(&[5]), INVALID);
    dh("g 0", dh_params(&[23], &[], &[]), uint(&[5]), INVALID);
    dh("g = p", dh_params(&[23], &[23], &[]), uint(&[5]), INVALID);
    dh("g = p - 1", dh_params(&[23], &[22], &[]), uint(&[5]), WRONG);
    dh(
        "private length 160",
        dh_params(&[23], &[5], &uint(&[160])),
        uint(&[5]),
        WRONG,
    );
    dh(
        "private length 2^32 - 1",
        dh_params(&[23], &[5], &uint(&[0xff; 4])),
        uint(&[5]),
        WRONG,
    );
    dh(
        "private length 2^32",
        dh_params(&[23], &[5], &uint(&[1, 0, 0, 0, 0])),
        uint(&[5]),
        INVALID,
    );
    dh(
        "private length negative",
        dh_params(&[23], &[5], &der(0x02, &[0xff])),
        uint(&[5]),
        INVALID,
    );
    dh(
        "two more fields",
        dh_params(&[23], &[5], &[uint(&[1]), uint(&[1])].concat()),
        uint(&[5]),
        INVALID,
    );
    dh(
        "parameters, then NULL",
        [toy.clone(), vec![5, 0]].concat(),
        uint(&[5]),
        WRONG,
    );
    dh("key an OCTET STRING", toy.clone(), der(0x04, &[5]), INVALID);
    dh(
        "key, then a byte",
        toy.clone(),
        [uint(&[5]), vec![0]].concat(),
        INVALID,
    );
    dh("no key", toy.clone(), vec![], INVALID);
    for (bits, expected) in [(10_000, WRONG), (10_001, INVALID)] {
        let mut p = vec![0u8; usize::div_ceil(bits, 8)];
        p[0] = 1 << ((bits - 1) % 8);
        *p.last_mut().unwrap() |= 1;
        dh(
            &format!("p of {bits} bits"),
            dh_params(&p, &[2], &[]),
            uint(&[5]),
            expected,
        );
    }
    cases
}

/// `order` plus `delta`, big-endian, for a small `delta`.
fn offset(order: &[u8], delta: i16) -> Vec<u8> {
    let mut out = order.to_vec();
    let mut carry = delta;
    for byte in out.iter_mut().rev() {
        let sum = i16::from(*byte) + carry;
        *byte = sum.rem_euclid(256) as u8;
        carry = sum.div_euclid(256);
        if carry == 0 {
            break;
        }
    }
    assert_eq!(carry, 0);
    out
}

/// Every EC and DSA PKCS#8 case but [`mismatched_private_keys`].
pub fn private_keys() -> Vec<Case> {
    let mut cases = Vec::new();
    for (index, curve) in CURVES.iter().enumerate() {
        let name = curve.name;
        let explicit = Explicit::of(curve);
        let named = der(0x06, curve.oid);
        let other = der(0x06, CURVES[(index + 1) % CURVES.len()].oid);
        let order = explicit.order();
        let len = order.len();
        let g = explicit.base();
        let one = offset(&vec![0; len], 1);
        let mut add = |label: &str, parameters: &[u8], key: Vec<u8>, expected| {
            cases.push((
                format!("{name} {label}"),
                pkcs8(EC, parameters, &key, None),
                expected,
            ));
        };
        add("scalar 1, G", &named, sec1(&one, None, Some(&g)), WRONG);
        add(
            "scalar 1, G, [0]",
            &named,
            sec1(&one, Some(&named), Some(&g)),
            WRONG,
        );
        add(
            "scalar 1, G, [0] explicit",
            &named,
            sec1(&one, Some(&explicit.encode()), Some(&g)),
            WRONG,
        );
        add(
            "explicit, scalar 1, G",
            &explicit.encode(),
            sec1(&one, None, Some(&g)),
            WRONG,
        );
        add(
            "explicit, scalar 1, G, [0]",
            &explicit.encode(),
            sec1(&one, Some(&named), Some(&g)),
            WRONG,
        );
        add(
            "explicit, scalar 1",
            &explicit.encode(),
            sec1(&one, None, None),
            WRONG,
        );
        if curve.backed {
            add(
                "explicit, scalar 2, G",
                &explicit.encode(),
                sec1(&offset(&one, 1), None, Some(&g)),
                INVALID,
            );
            add(
                "G hybrid, wrong parity",
                &named,
                sec1(&one, None, Some(&hybrid(&g, true))),
                INVALID,
            );
            add(
                "off curve, hybrid",
                &named,
                sec1(&one, None, Some(&hybrid(&off_curve(&g), false))),
                INVALID,
            );
        }
        add(
            "explicit, other b",
            &explicit.other_b(),
            sec1(&one, None, Some(&g)),
            INVALID,
        );
        add(
            "[0] another curve",
            &named,
            sec1(&one, Some(&other), Some(&g)),
            INVALID,
        );
        add(
            "[0] then NULL",
            &named,
            sec1(&one, Some(&[named.clone(), vec![5, 0]].concat()), None),
            INVALID,
        );
        add(
            "parameters, then NULL",
            &[named.clone(), vec![5, 0]].concat(),
            sec1(&one, None, None),
            INVALID,
        );
        add(
            "G compressed",
            &named,
            sec1(&one, None, Some(&compressed(&g))),
            WRONG,
        );
        add(
            "G hybrid",
            &named,
            sec1(&one, None, Some(&hybrid(&g, false))),
            WRONG,
        );
        add(
            "off curve",
            &named,
            sec1(&one, None, Some(&off_curve(&g))),
            INVALID,
        );
        add("infinity", &named, sec1(&one, None, Some(&[0])), INVALID);
        add(
            "scalar n - 1",
            &named,
            sec1(&offset(&order, -1), None, None),
            WRONG,
        );
        add("scalar n", &named, sec1(&order, None, None), INVALID);
        add(
            "scalar n + 1",
            &named,
            sec1(&offset(&order, 1), None, None),
            INVALID,
        );
        add("scalar 0", &named, sec1(&vec![0; len], None, None), INVALID);
        add("scalar empty", &named, sec1(&[], None, None), INVALID);
        add("scalar of one byte", &named, sec1(&[1], None, None), WRONG);
        add(
            "scalar n, one byte longer",
            &named,
            sec1(&[&[0], &order[..]].concat(), None, None),
            INVALID,
        );
        add(
            "scalar 1, one byte longer",
            &named,
            sec1(&[&[0], &one[..]].concat(), None, None),
            WRONG,
        );
        add(
            "scalar above the field",
            &named,
            sec1(&[&[1], &one[..]].concat(), None, None),
            INVALID,
        );
        let mut padding = sec1(&one, None, Some(&g));
        let at = padding.len() - g.len() - 1;
        padding[at] = 1;
        add("[1] with unused bits", &named, padding, INVALID);
        add(
            "[1] empty",
            &named,
            der(
                0x30,
                &[
                    der(0x02, &[1]),
                    der(0x04, &one),
                    der(0xa1, &der(0x03, &[0])),
                ]
                .concat(),
            ),
            INVALID,
        );
        add(
            "version 0",
            &named,
            der(0x30, &[der(0x02, &[0]), der(0x04, &one)].concat()),
            INVALID,
        );
        add(
            "then NULL",
            &named,
            [sec1(&one, None, None), vec![5, 0]].concat(),
            INVALID,
        );
        add(
            "NULL inside",
            &named,
            der(
                0x30,
                &[der(0x02, &[1]), der(0x04, &one), vec![5, 0]].concat(),
            ),
            INVALID,
        );
        cases.push((
            format!("{name} v2 public key"),
            pkcs8(
                EC,
                &named,
                &sec1(&one, None, None),
                Some(&[&[0], &g[..]].concat()),
            ),
            INVALID,
        ));
        if !curve.backed {
            let (d, q) = key_of(curve);
            let mut add = |label: &str, parameters: &[u8], key: Vec<u8>, expected| {
                cases.push((
                    format!("{name} {label}"),
                    pkcs8(EC, parameters, &key, None),
                    expected,
                ));
            };
            add(
                "OpenSSL key",
                &named,
                sec1(&d, Some(&named), Some(&q)),
                WRONG,
            );
            add(
                "OpenSSL key, compressed",
                &named,
                sec1(&d, None, Some(&compressed(&q))),
                WRONG,
            );
            add("OpenSSL scalar alone", &named, sec1(&d, None, None), WRONG);
        }
    }

    // DSA, bounded by `dsa_check_key`.
    let p1024 = [&[0x80][..], &[0; 126], &[0x01]].concat();
    let q160 = [&[0x80][..], &[0; 18], &[0x01]].concat();
    let dss = |p: &[u8], q: &[u8]| der(0x30, &[uint(p), uint(q), uint(&[2])].concat());
    let good = dss(&p1024, &q160);
    let mut dsa =
        |label: &str, parameters: Vec<u8>, key: Vec<u8>, public: Option<&[u8]>, expected| {
            cases.push((
                format!("dsa {label}"),
                pkcs8(DSA, &parameters, &key, public),
                expected,
            ));
        };
    dsa("x 1", good.clone(), uint(&[1]), None, WRONG);
    dsa("x 0", good.clone(), uint(&[]), None, INVALID);
    dsa(
        "x q - 1",
        good.clone(),
        uint(&offset(&q160, -1)),
        None,
        WRONG,
    );
    dsa("x q", good.clone(), uint(&q160), None, INVALID);
    dsa("x above q", good.clone(), uint(&[0xff; 21]), None, INVALID);
    dsa(
        "x not minimal",
        good.clone(),
        der(0x02, &[0, 1]),
        None,
        INVALID,
    );
    dsa(
        "x negative",
        good.clone(),
        der(0x02, &[0xff]),
        None,
        INVALID,
    );
    dsa(
        "x an OCTET STRING",
        good.clone(),
        der(0x04, &[1]),
        None,
        INVALID,
    );
    dsa(
        "x, then a byte",
        good.clone(),
        [uint(&[1]), vec![0]].concat(),
        None,
        INVALID,
    );
    dsa("x empty", good.clone(), der(0x02, &[]), None, INVALID);
    dsa("toy", dss(&[23], &[11]), uint(&[1]), None, INVALID);
    dsa(
        "parameters an INTEGER",
        uint(&[5]),
        uint(&[1]),
        None,
        INVALID,
    );
    dsa(
        "v2 public key",
        good.clone(),
        uint(&[1]),
        Some(&[0, 2, 1, 5]),
        INVALID,
    );
    cases
}

/// Keys on curves rind cannot back whose public key is on the curve but is
/// not the scalar's. aws-lc refuses them (`InvalidEncoding`); rind cannot
/// compute the scalar's point on these curves, so it refuses them as
/// another algorithm (`WrongAlgorithm`).
pub fn mismatched_private_keys() -> Vec<Case> {
    CURVES
        .iter()
        .filter(|curve| !curve.backed)
        .flat_map(|curve| {
            let (_, q) = key_of(curve);
            let explicit = Explicit::of(curve);
            let one = offset(&vec![0; explicit.order().len()], 1);
            let two = offset(&one, 1);
            [
                (
                    format!("{} scalar 1, OpenSSL point", curve.name),
                    pkcs8(EC, &der(0x06, curve.oid), &sec1(&one, None, Some(&q)), None),
                    INVALID,
                ),
                (
                    format!("{} explicit, scalar 2, G", curve.name),
                    pkcs8(
                        EC,
                        &explicit.encode(),
                        &sec1(&two, None, Some(&explicit.base())),
                        None,
                    ),
                    INVALID,
                ),
            ]
        })
        .collect()
}
