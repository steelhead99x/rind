// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
//! Key management for OpenSSL's `EC` key type on P-256, P-384, and P-521,
//! which the configuration's `ec = 1` registers.
//!
//! OpenSSL gives every curve the one key type, so a key on any other curve,
//! or with explicit domain parameters, reaches this provider too. It is
//! refused rather than handed to OpenSSL's default provider: a key moving
//! here imports, as a mismatched key does, and fails each use with rind's
//! error, and generating one fails.
//!
//! A key's parameters are those OpenSSL's default provider moves keys by in
//! `ec_kmgmt.c`: `group`, `pub`, `priv`, and the encodings. `priv` is a
//! bignum, in the native byte order of an `OSSL_PARAM` integer.

use core::ffi::{CStr, c_char, c_int, c_void};
use core::mem::ManuallyDrop;
use std::sync::{Arc, OnceLock};

use rind::agreement::{self, ECDH_P256, ECDH_P384, ECDH_P521};
use rind::digest::{self, SHA256, SHA384, SHA512};
use rind::ecdsa::{self, KeyPair, sign, verify};
use zeroize::Zeroizing;

use crate::ffi::{
    Callback, Dispatch, INTEGER, OCTET_STRING, OP_KEYEXCH, OP_SIGNATURE, Param,
    SELECT_DOMAIN_PARAMETERS, SELECT_KEYPAIR, SELECT_PRIVATE_KEY, SELECT_PUBLIC_KEY, UNMODIFIED,
    UNSIGNED_INTEGER, UTF8_STRING,
};
use crate::params::{Params, ParamsMut};
use crate::provider::{Failure, Provider, Reason};

/// Tells EC key objects from the other kinds'.
const TAG: u8 = 3;

/// A curve rind backs.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Curve {
    P256,
    P384,
    P521,
}

/// A hash ECDSA verifies with, as OpenSSL names it.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Hash {
    Sha256,
    Sha384,
    Sha512,
}

impl Hash {
    /// The hash a digest name of OpenSSL's means, or `None` for one rind does
    /// not verify with, such as SHA-1.
    pub(crate) fn from_name(name: &[u8]) -> Option<Self> {
        let name = name.to_ascii_uppercase();
        Some(match &name[..] {
            b"SHA256" | b"SHA-256" | b"SHA2-256" | b"2.16.840.1.101.3.4.2.1" => Self::Sha256,
            b"SHA384" | b"SHA-384" | b"SHA2-384" | b"2.16.840.1.101.3.4.2.2" => Self::Sha384,
            b"SHA512" | b"SHA-512" | b"SHA2-512" | b"2.16.840.1.101.3.4.2.3" => Self::Sha512,
            _ => return None,
        })
    }

    /// The name OpenSSL gives the hash.
    pub(crate) fn name(self) -> &'static CStr {
        match self {
            Self::Sha256 => c"SHA2-256",
            Self::Sha384 => c"SHA2-384",
            Self::Sha512 => c"SHA2-512",
        }
    }

    pub(crate) fn len(self) -> usize {
        match self {
            Self::Sha256 => 32,
            Self::Sha384 => 48,
            Self::Sha512 => 64,
        }
    }

    pub(crate) fn digest(self) -> &'static digest::Algorithm {
        match self {
            Self::Sha256 => &SHA256,
            Self::Sha384 => &SHA384,
            Self::Sha512 => &SHA512,
        }
    }

    /// The DER `AlgorithmIdentifier` of ECDSA with the hash (RFC 5758):
    /// `ecdsa-with-SHA256` and its kin, with no parameters.
    pub(crate) fn algorithm_id(self) -> [u8; 12] {
        let last = match self {
            Self::Sha256 => 2,
            Self::Sha384 => 3,
            Self::Sha512 => 4,
        };
        [
            0x30, 0x0a, 0x06, 0x08, 0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, last,
        ]
    }
}

impl Curve {
    /// The curve OpenSSL's `group` names, by its short name (`prime256v1`),
    /// its NIST name (`P-256`), a name it also takes (`NIST P-256`), or its
    /// OID. Another is `None`.
    pub(crate) fn from_name(name: &[u8]) -> Option<Self> {
        Some(match name {
            b"prime256v1" | b"secp256r1" | b"P-256" | b"NIST P-256" | b"1.2.840.10045.3.1.7" => {
                Self::P256
            }
            b"secp384r1" | b"P-384" | b"NIST P-384" | b"1.3.132.0.34" => Self::P384,
            b"secp521r1" | b"P-521" | b"NIST P-521" | b"1.3.132.0.35" => Self::P521,
            _ => return None,
        })
    }

    /// The curve's name as OpenSSL's default provider exports it.
    pub(crate) fn name(self) -> &'static CStr {
        match self {
            Self::P256 => c"prime256v1",
            Self::P384 => c"secp384r1",
            Self::P521 => c"secp521r1",
        }
    }

    /// The bit length of the group order, which `bits` reports.
    pub(crate) fn bits(self) -> c_int {
        match self {
            Self::P256 => 256,
            Self::P384 => 384,
            Self::P521 => 521,
        }
    }

    pub(crate) fn security_bits(self) -> c_int {
        match self {
            Self::P256 => 128,
            Self::P384 => 192,
            Self::P521 => 256,
        }
    }

    /// The length of a scalar, and of an ECDH secret.
    pub(crate) fn scalar_len(self) -> usize {
        match self {
            Self::P256 => 32,
            Self::P384 => 48,
            Self::P521 => 66,
        }
    }

    /// The longest DER signature, which `max-size` reports as OpenSSL's
    /// `ECDSA_size` does.
    pub(crate) fn max_signature_len(self) -> usize {
        // A `SEQUENCE` of two `INTEGER`s, each with a sign byte.
        let content = 2 * (2 + self.scalar_len() + 1);
        let header = if content < 128 { 2 } else { 3 };
        header + content
    }

    /// The hash rind signs the curve's ECDSA with.
    pub(crate) fn own_hash(self) -> Hash {
        match self {
            Self::P256 => Hash::Sha256,
            Self::P384 => Hash::Sha384,
            Self::P521 => Hash::Sha512,
        }
    }

    fn agreement(self) -> &'static agreement::Algorithm {
        match self {
            Self::P256 => &ECDH_P256,
            Self::P384 => &ECDH_P384,
            Self::P521 => &ECDH_P521,
        }
    }

    fn signing(self) -> &'static ecdsa::SigningAlgorithm {
        match self {
            Self::P256 => &sign::P256_SHA256_ASN1,
            Self::P384 => &sign::P384_SHA384_ASN1,
            Self::P521 => &sign::P521_SHA512_ASN1,
        }
    }

    /// The algorithm that verifies the curve's signatures over `hash`.
    fn verifying(self, hash: Hash) -> &'static ecdsa::VerificationAlgorithm {
        match (self, hash) {
            (Self::P256, Hash::Sha256) => &verify::P256_SHA256_ASN1,
            (Self::P256, Hash::Sha384) => &verify::P256_SHA384_ASN1,
            (Self::P256, Hash::Sha512) => &verify::P256_SHA512_ASN1,
            (Self::P384, Hash::Sha256) => &verify::P384_SHA256_ASN1,
            (Self::P384, Hash::Sha384) => &verify::P384_SHA384_ASN1,
            (Self::P384, Hash::Sha512) => &verify::P384_SHA512_ASN1,
            (Self::P521, Hash::Sha256) => &verify::P521_SHA256_ASN1,
            (Self::P521, Hash::Sha384) => &verify::P521_SHA384_ASN1,
            (Self::P521, Hash::Sha512) => &verify::P521_SHA512_ASN1,
        }
    }
}

/// Zeroes every byte of `value`, with writes the compiler keeps.
///
/// # Safety
///
/// `value` holds no live field that needs its destructor, and every field of
/// it is valid with all bits zero.
unsafe fn wipe<T>(value: &mut T) {
    let bytes = (value as *mut T).cast::<u8>();
    for i in 0..size_of::<T>() {
        // SAFETY: `bytes` is `value`'s own memory.
        unsafe { core::ptr::write_volatile(bytes.add(i), 0) };
    }
}

/// A private key, which wipes its whole value on drop: the key pair that
/// signs, and the key that agrees, which is made the first time one agrees.
pub(crate) struct Private {
    sign: ManuallyDrop<KeyPair>,
    agree: ManuallyDrop<OnceLock<Option<agreement::PrivateKey>>>,
}

impl Private {
    /// Loads a private key from its scalar, which must be the curve's length.
    /// The public key it computes is returned beside it.
    fn from_scalar(curve: Curve, scalar: &[u8]) -> Result<Self, rind::Error> {
        let agree = agreement::PrivateKey::from_scalar(curve.agreement(), scalar)?;
        let sign = KeyPair::from_scalar_and_public_key(
            curve.signing(),
            scalar,
            agree.public_key().as_ref(),
        )?;
        let cell = OnceLock::new();
        let _ = cell.set(Some(agree));
        Ok(Self {
            sign: ManuallyDrop::new(sign),
            agree: ManuallyDrop::new(cell),
        })
    }

    fn generate(curve: Curve) -> Result<Self, rind::Error> {
        Ok(Self {
            sign: ManuallyDrop::new(KeyPair::generate(curve.signing())?),
            agree: ManuallyDrop::new(OnceLock::new()),
        })
    }

    /// The uncompressed public point.
    fn point(&self) -> &[u8] {
        self.sign.public_key().as_ref()
    }

    /// The scalar, which wipes itself.
    fn scalar(&self) -> ecdsa::Scalar {
        self.sign.to_scalar()
    }

    pub(crate) fn sign(&self, message: &[u8]) -> Result<ecdsa::Signature, rind::Error> {
        self.sign.sign(message)
    }

    /// The key that agrees, which costs a scalar multiplication the first
    /// time.
    pub(crate) fn agree(&self, curve: Curve) -> Result<&agreement::PrivateKey, rind::Error> {
        self.agree
            .get_or_init(|| {
                agreement::PrivateKey::from_scalar(curve.agreement(), self.scalar().as_ref()).ok()
            })
            .as_ref()
            .ok_or(rind::Error::Fault)
    }
}

impl Drop for Private {
    fn drop(&mut self) {
        // SAFETY: each field is dropped once, here, and the wipe that follows
        // only writes `self`'s own bytes, which nothing reads after. A key
        // pair, and an unset or dropped cell, are valid as zero.
        unsafe {
            ManuallyDrop::drop(&mut self.sign);
            ManuallyDrop::drop(&mut self.agree);
            wipe(self);
        }
    }
}

/// A public key alone, wiped whole on drop with its parsed verifier.
pub(crate) struct Public {
    point: [u8; Self::MAX_LEN],
    len: usize,
    verifier: ManuallyDrop<OnceLock<Option<ecdsa::PublicKey>>>,
}

impl Public {
    /// P-521's uncompressed point.
    const MAX_LEN: usize = 133;

    /// Parses a peer's point, uncompressed or compressed, refusing one off
    /// the curve.
    fn new(curve: Curve, encoded: &[u8]) -> Result<Self, rind::Error> {
        let parsed = agreement::PublicKey::new(curve.agreement(), encoded)?;
        let mut public = Self {
            point: [0; Self::MAX_LEN],
            len: parsed.as_ref().len(),
            verifier: ManuallyDrop::new(OnceLock::new()),
        };
        public.point[..public.len].copy_from_slice(parsed.as_ref());
        Ok(public)
    }

    fn point(&self) -> &[u8] {
        &self.point[..self.len]
    }

    /// The verifier for the curve's own hash, parsed the first time.
    pub(crate) fn verifier(&self, curve: Curve) -> Option<&ecdsa::PublicKey> {
        self.verifier
            .get_or_init(|| {
                ecdsa::PublicKey::new(curve.verifying(curve.own_hash()), self.point()).ok()
            })
            .as_ref()
    }
}

impl Drop for Public {
    fn drop(&mut self) {
        // SAFETY: as for `Private`'s.
        unsafe {
            ManuallyDrop::drop(&mut self.verifier);
            wipe(self);
        }
    }
}

/// What a key holds. A key is made once and shared, so the size difference
/// between its variants costs nothing worth a box.
#[allow(clippy::large_enum_variant)]
pub(crate) enum Material {
    Public(Public),
    Private(Private),
}

/// A key on one of the curves.
pub(crate) struct Key {
    pub(crate) curve: Curve,
    pub(crate) material: Material,
}

impl Key {
    /// The uncompressed public point.
    pub(crate) fn point(&self) -> &[u8] {
        match &self.material {
            Material::Public(public) => public.point(),
            Material::Private(private) => private.point(),
        }
    }

    pub(crate) fn private(&self) -> Option<&Private> {
        match &self.material {
            Material::Public(_) => None,
            Material::Private(private) => Some(private),
        }
    }

    /// The verifier for the curve's own hash, or none if rind refuses the
    /// point.
    pub(crate) fn verifier(&self) -> Option<&ecdsa::PublicKey> {
        match &self.material {
            Material::Public(public) => public.verifier(self.curve),
            Material::Private(private) => Some(private.sign.public_key()),
        }
    }
}

/// Why a key object that moved here fails each use.
enum Refusal {
    /// A private key whose public key is not its own.
    Mismatched,
    /// A key rind cannot back: another curve, explicit parameters, or a
    /// point format rind does not write.
    Unsupported(String),
}

impl Refusal {
    fn failure(&self) -> Failure {
        match self {
            Self::Mismatched => Failure::Raise(
                Reason::KeyRejected,
                "the public key is not the private key's".into(),
            ),
            Self::Unsupported(detail) => Failure::unsupported(detail),
        }
    }
}

/// What a key object holds.
enum Held {
    /// No key, until one is generated or imported.
    Empty,
    Key(Arc<Key>),
    Refused(Refusal),
}

/// The key object OpenSSL holds: a curve, if one is set, and a key on it
/// once one is generated or imported.
///
/// Operations hold the key itself, so they run on the key they began with
/// even if an import replaces it.
#[repr(C)]
pub(crate) struct KeyData {
    // First, so a pointer to any key object reads it.
    tag: u8,
    pub(crate) provider: Arc<Provider>,
    curve: Option<Curve>,
    held: Held,
}

impl KeyData {
    fn boxed(provider: Arc<Provider>, curve: Option<Curve>, held: Held) -> *mut c_void {
        Box::into_raw(Box::new(Self {
            tag: TAG,
            provider,
            curve,
            held,
        }))
        .cast()
    }

    /// The key a query reads, which finds none in a refused key.
    pub(crate) fn key(&self) -> Option<&Key> {
        match &self.held {
            Held::Key(key) => Some(key),
            Held::Empty | Held::Refused(_) => None,
        }
    }

    /// The key an operation runs on, or why there is none.
    pub(crate) fn operand(&self) -> Result<Arc<Key>, Failure> {
        match &self.held {
            Held::Key(key) => Ok(key.clone()),
            Held::Empty => Err(Failure::invalid("no key is set")),
            Held::Refused(refusal) => Err(refusal.failure()),
        }
    }

    /// The key object OpenSSL passes, or `None` if it is null or of another
    /// kind.
    ///
    /// # Safety
    ///
    /// `keydata` is null or a key object of this provider's that OpenSSL has
    /// not freed, and no one mutates it for `'a`.
    pub(crate) unsafe fn from_ptr<'a>(keydata: *const c_void) -> Option<&'a Self> {
        // SAFETY: every key object starts with its tag, per the caller.
        if keydata.is_null() || unsafe { *keydata.cast::<u8>() } != TAG {
            return None;
        }
        // SAFETY: the tag says it is a `KeyData`.
        Some(unsafe { &*keydata.cast::<Self>() })
    }

    /// As [`Self::from_ptr`], to mutate.
    ///
    /// # Safety
    ///
    /// As for [`Self::from_ptr`], and no one else reads it for `'a`.
    unsafe fn from_mut_ptr<'a>(keydata: *mut c_void) -> Option<&'a mut Self> {
        // SAFETY: as for `from_ptr`.
        if keydata.is_null() || unsafe { *keydata.cast::<u8>() } != TAG {
            return None;
        }
        // SAFETY: the tag says it is a `KeyData`, which the caller lends.
        Some(unsafe { &mut *keydata.cast::<Self>() })
    }
}

/// A key generation in progress.
struct Gen {
    provider: Arc<Provider>,
    selection: c_int,
    curve: Option<Curve>,
}

pub(crate) static KEYMGMT: [Dispatch; 22] = {
    use crate::ffi::*;
    [
        entry!(KEYMGMT_NEW, new, KeymgmtNew),
        entry!(KEYMGMT_FREE, free, KeymgmtFree),
        entry!(KEYMGMT_GET_PARAMS, get_params, KeymgmtGetParams),
        entry!(
            KEYMGMT_GETTABLE_PARAMS,
            gettable_params,
            KeymgmtGettableParams
        ),
        entry!(KEYMGMT_SET_PARAMS, set_params, KeymgmtSetParams),
        entry!(
            KEYMGMT_SETTABLE_PARAMS,
            settable_params,
            KeymgmtSettableParams
        ),
        entry!(KEYMGMT_HAS, has, KeymgmtHas),
        entry!(KEYMGMT_MATCH, matches, KeymgmtMatch),
        entry!(KEYMGMT_VALIDATE, validate, KeymgmtValidate),
        entry!(KEYMGMT_IMPORT, import, KeymgmtImport),
        entry!(KEYMGMT_IMPORT_TYPES, types, KeymgmtTypes),
        entry!(KEYMGMT_EXPORT, export, KeymgmtExport),
        entry!(KEYMGMT_EXPORT_TYPES, types, KeymgmtTypes),
        entry!(KEYMGMT_GEN_INIT, gen_init, KeymgmtGenInit),
        entry!(
            KEYMGMT_GEN_SET_TEMPLATE,
            gen_set_template,
            KeymgmtGenSetTemplate
        ),
        entry!(KEYMGMT_GEN_SET_PARAMS, gen_set_params, KeymgmtGenSetParams),
        entry!(
            KEYMGMT_GEN_SETTABLE_PARAMS,
            gen_settable_params,
            KeymgmtGenSettableParams
        ),
        entry!(KEYMGMT_GEN, generate, KeymgmtGen),
        entry!(KEYMGMT_GEN_CLEANUP, gen_cleanup, KeymgmtGenCleanup),
        entry!(KEYMGMT_DUP, dup, KeymgmtDup),
        entry!(
            KEYMGMT_QUERY_OPERATION_NAME,
            query_operation_name,
            KeymgmtQueryOperationName
        ),
        Dispatch::END,
    ]
};

unsafe extern "C" fn new(provctx: *mut c_void) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    KeyData::boxed(provider, None, Held::Empty)
}

unsafe extern "C" fn free(keydata: *mut c_void) {
    // SAFETY: OpenSSL frees a key object it holds, which no one uses after.
    if unsafe { KeyData::from_ptr(keydata) }.is_some() {
        // SAFETY: as above; `new`, `generate`, or `dup` boxed it.
        drop(unsafe { Box::from_raw(keydata.cast::<KeyData>()) });
    }
}

/// The operations OpenSSL's `EC` key type is fetched for, under the names
/// rind registers them: `ECDSA` and `ECDH`.
unsafe extern "C" fn query_operation_name(operation: c_int) -> *const c_char {
    match operation {
        OP_SIGNATURE => c"ECDSA".as_ptr(),
        OP_KEYEXCH => c"ECDH".as_ptr(),
        _ => core::ptr::null(),
    }
}

unsafe extern "C" fn has(keydata: *const c_void, selection: c_int) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::from_ptr(keydata) }) else {
        return 0;
    };
    let key = data.key();
    let domain = selection & SELECT_DOMAIN_PARAMETERS == 0 || data.curve.is_some();
    let public = selection & SELECT_PUBLIC_KEY == 0 || key.is_some();
    let private = selection & SELECT_PRIVATE_KEY == 0 || key.and_then(Key::private).is_some();
    (domain && public && private).into()
}

unsafe extern "C" fn matches(
    keydata1: *const c_void,
    keydata2: *const c_void,
    selection: c_int,
) -> c_int {
    // SAFETY: OpenSSL passes key objects it holds.
    let (Some(a), Some(b)) =
        (unsafe { (KeyData::from_ptr(keydata1), KeyData::from_ptr(keydata2)) })
    else {
        return 0;
    };
    equal(a, b, selection).into()
}

/// Whether two key objects match on `selection`: the same curve when
/// parameters are asked for, then the public keys when both are asked for
/// and present, else the private keys, as OpenSSL's do.
fn equal(a: &KeyData, b: &KeyData, selection: c_int) -> bool {
    if selection & SELECT_DOMAIN_PARAMETERS != 0 && (a.curve.is_none() || a.curve != b.curve) {
        return false;
    }
    if selection & SELECT_KEYPAIR == 0 {
        return true;
    }
    let (a, b) = (a.key(), b.key());
    let equal = match (a, b) {
        (Some(a), Some(b)) if selection & SELECT_PUBLIC_KEY != 0 => {
            Some(a.curve == b.curve && a.point() == b.point())
        }
        _ if selection & SELECT_PRIVATE_KEY != 0 => {
            match (a.and_then(Key::private), b.and_then(Key::private)) {
                (Some(x), Some(y)) => Some(
                    rind::constant_time::verify(x.scalar().as_ref(), y.scalar().as_ref()).is_ok(),
                ),
                _ => None,
            }
        }
        _ => None,
    };
    equal == Some(true)
}

unsafe extern "C" fn validate(
    keydata: *const c_void,
    selection: c_int,
    _checktype: c_int,
) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::from_ptr(keydata) }) else {
        return 0;
    };
    if let Held::Refused(refusal) = &data.held {
        return data.provider.status(Err(refusal.failure()));
    }
    // A private key's public key is the one rind computed or checked when it
    // loaded the key, and a public key is on its curve, so a key is always
    // consistent.
    // SAFETY: as above.
    unsafe { has(keydata, selection) }
}

/// The parameters a key moves by, with the group and encodings.
static DOMAIN_TYPES: [Param; 4] = [
    Param::describe(Some(c"group"), UTF8_STRING, 0),
    Param::describe(Some(c"encoding"), UTF8_STRING, 0),
    Param::describe(Some(c"point-format"), UTF8_STRING, 0),
    Param::END,
];
static PUBLIC_TYPES: [Param; 5] = [
    Param::describe(Some(c"group"), UTF8_STRING, 0),
    Param::describe(Some(c"encoding"), UTF8_STRING, 0),
    Param::describe(Some(c"point-format"), UTF8_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::END,
];
static PRIVATE_TYPES: [Param; 6] = [
    Param::describe(Some(c"group"), UTF8_STRING, 0),
    Param::describe(Some(c"encoding"), UTF8_STRING, 0),
    Param::describe(Some(c"point-format"), UTF8_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), UNSIGNED_INTEGER, 0),
    Param::END,
];

unsafe extern "C" fn types(selection: c_int) -> *const Param {
    if selection & SELECT_PRIVATE_KEY != 0 {
        PRIVATE_TYPES.as_ptr()
    } else if selection & SELECT_PUBLIC_KEY != 0 {
        PUBLIC_TYPES.as_ptr()
    } else if selection & SELECT_DOMAIN_PARAMETERS != 0 {
        DOMAIN_TYPES.as_ptr()
    } else {
        core::ptr::null()
    }
}

/// The parameters that give a key explicit domain parameters, which rind
/// does not back.
const EXPLICIT: [&CStr; 6] = [c"p", c"a", c"b", c"order", c"generator", c"field-type"];

/// Checks the encodings a key arrives with: named curves and uncompressed
/// points, the two rind writes.
fn check_encodings(params: Params<'_>) -> Result<(), Refusal> {
    if let Some(name) = EXPLICIT.iter().find(|name| params.find(name).is_some()) {
        return Err(Refusal::Unsupported(format!(
            "rind backs only named curves, not explicit domain parameters ({name:?} is given)"
        )));
    }
    if let Some(encoding) = params.find(c"encoding")
        && encoding.utf8() != Some(b"named_curve")
    {
        return Err(Refusal::Unsupported(
            "rind backs only named curves, not explicit domain parameters".into(),
        ));
    }
    if let Some(format) = params.find(c"point-format")
        && format.utf8() != Some(b"uncompressed")
    {
        return Err(Refusal::Unsupported(
            "rind backs only uncompressed points as a key's format".into(),
        ));
    }
    Ok(())
}

/// The curve `params` name, if any: `Ok(None)` if none, and a refusal if it
/// is one rind does not back.
fn group(params: Params<'_>) -> Result<Option<Curve>, Refusal> {
    let Some(group) = params.find(c"group") else {
        return Ok(None);
    };
    let name = group
        .utf8()
        .ok_or_else(|| Refusal::Unsupported("the group must be a UTF-8 string".into()))?;
    match Curve::from_name(name) {
        Some(curve) => Ok(Some(curve)),
        None => Err(Refusal::Unsupported(format!(
            "rind backs only P-256, P-384, and P-521, not {:?}",
            String::from_utf8_lossy(name)
        ))),
    }
}

unsafe extern "C" fn import(keydata: *mut c_void, selection: c_int, params: *const Param) -> c_int {
    // SAFETY: OpenSSL imports into a key object it holds, and passes an
    // array.
    let (Some(data), params) = (unsafe { KeyData::from_mut_ptr(keydata) }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    if selection & (SELECT_KEYPAIR | SELECT_DOMAIN_PARAMETERS) == 0 {
        return 0;
    }
    // A key rind cannot back imports, so that its every use fails with
    // rind's error: OpenSSL moves a key here from another provider before
    // each use, and runs the use on that provider when the move fails.
    let result = match load(data.curve, selection, params) {
        Ok((curve, held)) => {
            data.curve = curve;
            data.held = held;
            Ok(())
        }
        Err(Loading::Refused(refusal)) => {
            data.held = Held::Refused(refusal);
            Ok(())
        }
        Err(Loading::Failed(failure)) => Err(failure),
    };
    data.provider.status(result)
}

/// Why a key did not load.
enum Loading {
    /// It loads as a key that fails every use.
    Refused(Refusal),
    /// The import itself fails.
    Failed(Failure),
}

impl From<Refusal> for Loading {
    fn from(refusal: Refusal) -> Self {
        Self::Refused(refusal)
    }
}

impl From<Failure> for Loading {
    fn from(failure: Failure) -> Self {
        Self::Failed(failure)
    }
}

impl From<rind::Error> for Loading {
    fn from(error: rind::Error) -> Self {
        Self::Failed(error.into())
    }
}

/// The curve and key `params` hold for `selection`, on `current`'s curve if
/// they name none.
fn load(
    current: Option<Curve>,
    selection: c_int,
    params: Params<'_>,
) -> Result<(Option<Curve>, Held), Loading> {
    check_encodings(params)?;
    let curve = group(params)?.or(current);
    if selection & SELECT_KEYPAIR == 0 {
        return Ok((curve, Held::Empty));
    }
    let Some(curve) = curve else {
        return Err(Failure::invalid("the key has no group").into());
    };
    let public = params
        .find(c"pub")
        .map(|param| {
            param
                .octets()
                .ok_or_else(|| Failure::invalid("pub must be an octet string"))
        })
        .transpose()?;
    let private = match selection & SELECT_PRIVATE_KEY {
        0 => None,
        _ => params
            .find(c"priv")
            .map(|param| {
                // The scalar, big-endian and padded to the curve's length,
                // which wipes itself. Whether a value is too long for the
                // curve is told without branching on its bytes, which are
                // secret.
                let value = param
                    .unsigned_be()
                    .ok_or_else(|| Failure::invalid("priv must be an unsigned integer"))?;
                let len = curve.scalar_len();
                let mut scalar = Zeroizing::new(vec![0u8; len]);
                if value.len() >= len {
                    let (excess, tail) = value.split_at(value.len() - len);
                    let zeros = vec![0u8; excess.len()];
                    if rind::constant_time::verify(excess, &zeros).is_err() {
                        return Err(Failure::invalid("priv is longer than the curve's order"));
                    }
                    scalar.copy_from_slice(tail);
                } else {
                    scalar[len - value.len()..].copy_from_slice(&value);
                }
                Ok(scalar)
            })
            .transpose()?,
    };
    let key = match (private, public) {
        (Some(scalar), public) => {
            let private = Private::from_scalar(curve, &scalar)?;
            if let Some(public) = public {
                // The same point, whichever way it is encoded.
                let given = agreement::PublicKey::new(curve.agreement(), public)?;
                if given.as_ref() != private.point() {
                    return Ok((Some(curve), Held::Refused(Refusal::Mismatched)));
                }
            }
            Material::Private(private)
        }
        (None, Some(public)) => Material::Public(Public::new(curve, public)?),
        (None, None) => return Err(Failure::invalid("neither pub nor priv is given").into()),
    };
    Ok((
        Some(curve),
        Held::Key(Arc::new(Key {
            curve,
            material: key,
        })),
    ))
}

unsafe extern "C" fn export(
    keydata: *mut c_void,
    selection: c_int,
    callback: Option<Callback>,
    arg: *mut c_void,
) -> c_int {
    // SAFETY: OpenSSL exports a key object it holds.
    let (Some(data), Some(callback)) = (unsafe { KeyData::from_ptr(keydata) }, callback) else {
        return 0;
    };
    if let Held::Refused(refusal) = &data.held {
        return data.provider.status(Err(refusal.failure()));
    }
    if selection & (SELECT_KEYPAIR | SELECT_DOMAIN_PARAMETERS) == 0 {
        return 0;
    }
    let Some(curve) = data.curve else {
        return 0;
    };
    let key = data.key();
    if selection & SELECT_KEYPAIR != 0 && key.is_none() {
        return 0;
    }
    let text = |key: &'static CStr, value: &'static CStr| Param {
        key: key.as_ptr(),
        data_type: UTF8_STRING,
        data: value.as_ptr().cast_mut().cast(),
        data_size: value.to_bytes().len(),
        return_size: UNMODIFIED,
    };
    let mut params = vec![
        text(c"group", curve.name()),
        text(c"encoding", c"named_curve"),
        text(c"point-format", c"uncompressed"),
    ];
    if let Some(key) = key
        && selection & SELECT_PUBLIC_KEY != 0
    {
        params.push(Param {
            key: c"pub".as_ptr(),
            data_type: OCTET_STRING,
            // The callback only reads it.
            data: key.point().as_ptr().cast_mut().cast(),
            data_size: key.point().len(),
            return_size: UNMODIFIED,
        });
    }
    // The scalar, and the native-endian bytes of the bignum that holds it,
    // wipe themselves once the callback has copied them.
    let scalar = match (
        selection & SELECT_PRIVATE_KEY != 0,
        key.and_then(Key::private),
    ) {
        (true, Some(private)) => Some(private.scalar()),
        (true, None) => return 0,
        (false, _) => None,
    };
    let mut native = scalar.as_ref().map(|scalar| {
        let mut native = Zeroizing::new(scalar.as_ref().to_vec());
        if cfg!(target_endian = "little") {
            native.reverse();
        }
        native
    });
    if let Some(native) = native.as_mut() {
        params.push(Param {
            key: c"priv".as_ptr(),
            data_type: UNSIGNED_INTEGER,
            data: native.as_mut_ptr().cast(),
            data_size: native.len(),
            return_size: UNMODIFIED,
        });
    }
    params.push(Param::END);
    // SAFETY: the callback is OpenSSL's, and takes the terminated array.
    unsafe { callback(params.as_ptr(), arg) }
}

static GETTABLE: [Param; 14] = [
    Param::describe(Some(c"bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"security-bits"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"max-size"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"security-category"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"default-digest"), UTF8_STRING, 0),
    Param::describe(Some(c"group"), UTF8_STRING, 0),
    Param::describe(Some(c"encoding"), UTF8_STRING, 0),
    Param::describe(Some(c"point-format"), UTF8_STRING, 0),
    Param::describe(Some(c"use-cofactor-flag"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"decoded-from-explicit"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"encoded-pub-key"), OCTET_STRING, 0),
    Param::describe(Some(c"pub"), OCTET_STRING, 0),
    Param::describe(Some(c"priv"), UNSIGNED_INTEGER, 0),
    Param::END,
];

unsafe extern "C" fn get_params(keydata: *mut c_void, params: *mut Param) -> c_int {
    // SAFETY: OpenSSL passes a key object it holds and a writable array.
    let (Some(data), mut params) = (unsafe { KeyData::from_ptr(keydata) }, unsafe {
        ParamsMut::new(params)
    }) else {
        return 0;
    };
    if let Some(curve) = data.curve {
        let sizes = [
            (c"bits", curve.bits()),
            (c"security-bits", curve.security_bits()),
            (c"max-size", curve.max_signature_len() as c_int),
            (c"security-category", 0),
            (c"use-cofactor-flag", 0),
            (c"decoded-from-explicit", 0),
        ];
        for (name, value) in sizes {
            if let Some(param) = params.find(name)
                && !param.set_int(value)
            {
                return 0;
            }
        }
        // The hash rind signs the curve with, since it signs with no other:
        // a signature that names none uses this, where OpenSSL's default
        // provider uses SHA-256 on every curve.
        let texts = [
            (c"default-digest", curve.own_hash().name()),
            (c"group", curve.name()),
            (c"encoding", c"named_curve"),
            (c"point-format", c"uncompressed"),
        ];
        for (name, value) in texts {
            if let Some(param) = params.find(name)
                && !param.set_utf8(value)
            {
                return 0;
            }
        }
    }
    let Some(key) = data.key() else {
        return 1;
    };
    for name in [c"pub", c"encoded-pub-key"] {
        if let Some(param) = params.find(name)
            && !param.set_octets(key.point())
        {
            return 0;
        }
    }
    if let Some(private) = key.private()
        && let Some(param) = params.find(c"priv")
        && !param.set_unsigned_be(private.scalar().as_ref())
    {
        return 0;
    }
    1
}

unsafe extern "C" fn gettable_params(_provctx: *mut c_void) -> *const Param {
    GETTABLE.as_ptr()
}

static SETTABLE: [Param; 6] = [
    Param::describe(Some(c"encoded-pub-key"), OCTET_STRING, 0),
    Param::describe(Some(c"point-format"), UTF8_STRING, 0),
    Param::describe(Some(c"encoding"), UTF8_STRING, 0),
    Param::describe(Some(c"use-cofactor-flag"), INTEGER, size_of::<c_int>()),
    Param::describe(Some(c"properties"), UTF8_STRING, 0),
    Param::END,
];

unsafe extern "C" fn settable_params(_provctx: *mut c_void) -> *const Param {
    SETTABLE.as_ptr()
}

unsafe extern "C" fn set_params(keydata: *mut c_void, params: *const Param) -> c_int {
    // SAFETY: OpenSSL sets parameters on a key object it holds, and passes
    // an array.
    let (Some(data), params) = (unsafe { KeyData::from_mut_ptr(keydata) }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    let result = (|| {
        check_encodings(params).map_err(|refusal| refusal.failure())?;
        // The cofactor of every curve here is 1, so the flag changes nothing.
        if let Some(param) = params.find(c"use-cofactor-flag")
            && param.int().is_none()
        {
            return Err(Failure::invalid("use-cofactor-flag must be an integer"));
        }
        // rind fetches nothing, so it has no use for a property query.
        if let Some(properties) = params.find(c"properties")
            && properties.utf8().is_none()
        {
            return Err(Failure::invalid("properties must be a UTF-8 string"));
        }
        // TLS gives a peer's key this way, into a key that holds its group.
        if let Some(param) = params.find(c"encoded-pub-key") {
            let curve = data
                .curve
                .ok_or_else(|| Failure::invalid("the key has no group"))?;
            if data.key().and_then(Key::private).is_some() {
                return Err(Failure::invalid("the key already has a private key"));
            }
            let encoded = param
                .octets()
                .ok_or_else(|| Failure::invalid("encoded-pub-key must be an octet string"))?;
            let public = Public::new(curve, encoded)?;
            data.held = Held::Key(Arc::new(Key {
                curve,
                material: Material::Public(public),
            }));
        }
        Ok(())
    })();
    data.provider.status(result)
}

unsafe extern "C" fn gen_init(
    provctx: *mut c_void,
    selection: c_int,
    params: *const Param,
) -> *mut c_void {
    // SAFETY: OpenSSL passes the provider's context.
    let provider = unsafe { Provider::from_context(provctx) };
    let generation = Box::into_raw(Box::new(Gen {
        provider,
        selection,
        curve: None,
    }));
    // SAFETY: `generation` is the context just made, and OpenSSL passes an
    // array.
    if unsafe { gen_set_params(generation.cast(), params) } == 0 {
        // SAFETY: as above; no one else holds it.
        drop(unsafe { Box::from_raw(generation) });
        return core::ptr::null_mut();
    }
    generation.cast()
}

unsafe extern "C" fn gen_set_template(genctx: *mut c_void, template: *mut c_void) -> c_int {
    // SAFETY: OpenSSL passes the context `gen_init` made, and a key object.
    let (Some(generation), Some(template)) = (unsafe { genctx.cast::<Gen>().as_mut() }, unsafe {
        KeyData::from_ptr(template)
    }) else {
        return 0;
    };
    let result = match &template.held {
        Held::Refused(refusal) => Err(refusal.failure()),
        _ => {
            generation.curve = template.curve.or(generation.curve);
            Ok(())
        }
    };
    generation.provider.status(result)
}

unsafe extern "C" fn gen_set_params(genctx: *mut c_void, params: *const Param) -> c_int {
    // SAFETY: OpenSSL passes the context `gen_init` made, and an array.
    let (Some(generation), params) = (unsafe { genctx.cast::<Gen>().as_mut() }, unsafe {
        Params::new(params)
    }) else {
        return 0;
    };
    let result = (|| {
        check_encodings(params).map_err(|refusal| refusal.failure())?;
        if let Some(curve) = group(params).map_err(|refusal| refusal.failure())? {
            generation.curve = Some(curve);
        }
        if params
            .find(c"properties")
            .is_some_and(|properties| properties.utf8().is_none())
        {
            return Err(Failure::invalid("properties must be a UTF-8 string"));
        }
        Ok(())
    })();
    generation.provider.status(result)
}

static GEN_SETTABLE: [Param; 6] = [
    Param::describe(Some(c"group"), UTF8_STRING, 0),
    Param::describe(Some(c"encoding"), UTF8_STRING, 0),
    Param::describe(Some(c"point-format"), UTF8_STRING, 0),
    Param::describe(Some(c"properties"), UTF8_STRING, 0),
    Param::describe(Some(c"ecdh-cofactor-mode"), INTEGER, size_of::<c_int>()),
    Param::END,
];

unsafe extern "C" fn gen_settable_params(
    _genctx: *mut c_void,
    _provctx: *mut c_void,
) -> *const Param {
    GEN_SETTABLE.as_ptr()
}

unsafe extern "C" fn generate(
    genctx: *mut c_void,
    _callback: Option<Callback>,
    _arg: *mut c_void,
) -> *mut c_void {
    // SAFETY: OpenSSL passes the context `gen_init` made.
    let Some(generation) = (unsafe { genctx.cast::<Gen>().as_ref() }) else {
        return core::ptr::null_mut();
    };
    let provider = generation.provider.clone();
    let Some(curve) = generation.curve else {
        provider.status(Err(Failure::invalid("no group is set")));
        return core::ptr::null_mut();
    };
    // Asked for no key, as for parameters alone, it gives a key with a curve
    // and nothing more.
    if generation.selection & SELECT_KEYPAIR == 0 {
        return KeyData::boxed(provider, Some(curve), Held::Empty);
    }
    match Private::generate(curve) {
        Ok(private) => {
            let key = Key {
                curve,
                material: Material::Private(private),
            };
            KeyData::boxed(provider, Some(curve), Held::Key(Arc::new(key)))
        }
        Err(error) => {
            provider.status(Err(error.into()));
            core::ptr::null_mut()
        }
    }
}

unsafe extern "C" fn gen_cleanup(genctx: *mut c_void) {
    if !genctx.is_null() {
        // SAFETY: OpenSSL frees the context `gen_init` made.
        drop(unsafe { Box::from_raw(genctx.cast::<Gen>()) });
    }
}

unsafe extern "C" fn dup(keydata: *const c_void, selection: c_int) -> *mut c_void {
    // SAFETY: OpenSSL passes a key object it holds.
    let Some(data) = (unsafe { KeyData::from_ptr(keydata) }) else {
        return core::ptr::null_mut();
    };
    let curve = if selection & (SELECT_DOMAIN_PARAMETERS | SELECT_KEYPAIR) != 0 {
        data.curve
    } else {
        None
    };
    let held = match &data.held {
        Held::Key(key) => match (&key.material, selection & SELECT_KEYPAIR) {
            (Material::Private(_), SELECT_KEYPAIR | SELECT_PRIVATE_KEY)
            | (Material::Public(_), SELECT_KEYPAIR | SELECT_PUBLIC_KEY) => Held::Key(key.clone()),
            (Material::Private(private), SELECT_PUBLIC_KEY) => {
                match Public::new(key.curve, private.point()) {
                    Ok(public) => Held::Key(Arc::new(Key {
                        curve: key.curve,
                        material: Material::Public(public),
                    })),
                    Err(_) => Held::Empty,
                }
            }
            _ => Held::Empty,
        },
        // A copy of either half fails each use as the original does.
        Held::Refused(refusal) if selection & SELECT_KEYPAIR != 0 => Held::Refused(match refusal {
            Refusal::Mismatched => Refusal::Mismatched,
            Refusal::Unsupported(detail) => Refusal::Unsupported(detail.clone()),
        }),
        Held::Refused(_) | Held::Empty => Held::Empty,
    };
    KeyData::boxed(data.provider.clone(), curve, held)
}

/// The digest `hash` names for `digest::digest`, for the verifier's other
/// hashes.
pub(crate) fn hash_message(hash: Hash, message: &[u8]) -> digest::Digest {
    digest::digest(hash.digest(), message)
}

#[cfg(test)]
mod tests {
    use std::alloc::{Layout, dealloc};

    use super::*;

    fn scalar(curve: Curve) -> Vec<u8> {
        let mut scalar = vec![0x11u8; curve.scalar_len()];
        scalar[0] = 0x01;
        scalar
    }

    #[test]
    fn names_resolve_to_the_three_curves() {
        for (name, curve) in [
            (&b"prime256v1"[..], Curve::P256),
            (b"secp256r1", Curve::P256),
            (b"P-256", Curve::P256),
            (b"secp384r1", Curve::P384),
            (b"NIST P-521", Curve::P521),
            (b"1.3.132.0.35", Curve::P521),
        ] {
            assert_eq!(Curve::from_name(name), Some(curve));
        }
        for name in [&b"secp256k1"[..], b"brainpoolP256r1", b"", b"p-256"] {
            assert_eq!(Curve::from_name(name), None);
        }
    }

    #[test]
    fn sizes_are_what_openssl_reports() {
        assert_eq!(
            [Curve::P256, Curve::P384, Curve::P521].map(Curve::max_signature_len),
            [72, 104, 141]
        );
    }

    #[test]
    fn hash_names_resolve() {
        for name in [&b"SHA256"[..], b"sha2-256", b"SHA-256"] {
            assert_eq!(Hash::from_name(name), Some(Hash::Sha256));
        }
        for name in [&b"SHA1"[..], b"SHA224", b"SHA3-256", b""] {
            assert_eq!(Hash::from_name(name), None);
        }
    }

    /// A private key is zero in every byte once dropped, before it is freed,
    /// its agreeing key included. Reading it then is a deliberate use after
    /// drop, as `rind/tests/zeroing.rs` does.
    #[test]
    fn a_private_key_wipes_whole() {
        for curve in [Curve::P256, Curve::P384, Curve::P521] {
            let key = Box::into_raw(Box::new(
                Private::from_scalar(curve, &scalar(curve)).unwrap(),
            ));
            // SAFETY: `key` is a live allocation of `Private`'s size; it is
            // dropped once, read before it is freed, and freed with its
            // layout.
            unsafe {
                core::ptr::drop_in_place(key);
                let bytes = key.cast::<u8>();
                assert!(
                    (0..size_of::<Private>()).all(|i| core::ptr::read_volatile(bytes.add(i)) == 0)
                );
                dealloc(bytes, Layout::new::<Private>());
            }
        }
    }

    /// A public key alone, its parsed verifier included, wipes whole too.
    #[test]
    fn a_public_key_wipes_whole() {
        let private = Private::from_scalar(Curve::P256, &scalar(Curve::P256)).unwrap();
        let key = Box::into_raw(Box::new(Public::new(Curve::P256, private.point()).unwrap()));
        // SAFETY: as for the private key's.
        unsafe {
            assert!((*key).verifier(Curve::P256).is_some());
            core::ptr::drop_in_place(key);
            let bytes = key.cast::<u8>();
            assert!((0..size_of::<Public>()).all(|i| core::ptr::read_volatile(bytes.add(i)) == 0));
            dealloc(bytes, Layout::new::<Public>());
        }
    }
}
