"""Loading and writing keys: PEM and DER (PKCS#8, SubjectPublicKeyInfo, PKCS#1, and SEC1), and OpenSSH public keys."""

from pyrind import agreement as _agreement
from pyrind import signature as _signature

from pyrind_cryptography import _der
from pyrind_cryptography.exceptions import _Reasons, unsupported
from pyrind_cryptography.hazmat.primitives import _keys
from pyrind_cryptography.hazmat.primitives._serialization import (
    BestAvailableEncryption,
    Encoding,
    KeySerializationEncryption,
    NoEncryption,
    ParameterFormat,
    PrivateFormat,
    PublicFormat,
    _KeySerializationEncryption,
)
from pyrind_cryptography.hazmat.primitives.serialization import _ssh

_RSA = "1.2.840.113549.1.1.1"
_EC = "1.2.840.10045.2.1"
_ED25519 = "1.3.101.112"
_X25519 = "1.3.101.110"
_UNSUPPORTED = {
    "1.3.101.113": "Ed448",
    "1.3.101.111": "X448",
    "1.2.840.113549.1.1.10": "RSA-PSS keys",
    "1.2.840.10040.4.1": "DSA",
    "1.2.840.113549.1.3.1": "DH",
    "1.2.840.10046.2.1": "DH",
}
_PRIVATE_LABELS = ("PRIVATE KEY", "RSA PRIVATE KEY", "EC PRIVATE KEY", "ENCRYPTED PRIVATE KEY")
_PUBLIC_LABELS = ("PUBLIC KEY", "RSA PUBLIC KEY")


def _modules():
    from pyrind_cryptography.hazmat.primitives.asymmetric import ec, ed25519, rsa, x25519

    return ec, ed25519, rsa, x25519


def _unsupported_type(oid):
    raise unsupported(_UNSUPPORTED.get(oid, f"Key type {oid}"), _Reasons.UNSUPPORTED_PUBLIC_KEY_ALGORITHM)


def _check_password(password, encrypted):
    if password is not None:
        _keys.check_bytes("password", password)
    if encrypted and password is None:
        raise TypeError("Password was not given but private key is encrypted")
    if encrypted:
        raise unsupported("Encrypted private keys", _Reasons.UNSUPPORTED_SERIALIZATION)
    if password is not None:
        raise TypeError("Password was given but private key is not encrypted.")


def _pkcs8(der):
    ec, ed25519, rsa, x25519 = _modules()
    algorithm, parameter = _der.pkcs8_algorithm(der)
    with _keys.loading():
        if algorithm == _RSA:
            rsa._check_private_size(_der.pkcs8_key(der))
            return rsa.RSAPrivateKey(_signature.RsaKeyPair.from_pkcs8(der))
        if algorithm == _EC:
            if parameter is None:
                raise ValueError(_keys.DESERIALIZE)
            curve = ec._curve_for_oid(parameter)
            return ec.EllipticCurvePrivateKey(curve, _signature.EcdsaKeyPair.from_pkcs8(ec._rind(curve)[0], der))
        if algorithm == _ED25519:
            return ed25519.Ed25519PrivateKey(_signature.Ed25519KeyPair.from_pkcs8(der))
        if algorithm == _X25519:
            return x25519.X25519PrivateKey(_agreement.PrivateKey.from_pkcs8(_agreement.X25519, der))
    _unsupported_type(algorithm)


def _sec1(der, items):
    ec = _modules()[0]
    curve = None
    for tag, contents in items[2:]:
        if tag == 0xA0:
            curve = ec._curve_for_oid(_der.oid(_der.one(contents, _der.OID)))
    if curve is None:
        raise ValueError(_keys.DESERIALIZE)
    with _keys.loading():
        return ec.EllipticCurvePrivateKey(curve, _signature.EcdsaKeyPair.from_sec1(ec._rind(curve)[0], der))


def _pkcs1_private(der):
    rsa = _modules()[2]
    rsa._check_private_size(der)
    with _keys.loading():
        return rsa.RSAPrivateKey(_signature.RsaKeyPair.from_pkcs1(der))


def _private_der(der):
    """Routes a PKCS#8, PKCS#1, or SEC1 private key by its structure."""
    items = _der.elements(_der.one(der, _der.SEQUENCE))
    if len(items) >= 3 and items[0][0] == _der.INTEGER and items[1][0] == _der.SEQUENCE:
        return _pkcs8(der)
    if len(items) >= 2 and items[0] == (_der.INTEGER, b"\x01") and items[1][0] == _der.OCTET_STRING:
        return _sec1(der, items)
    if len(items) == 9 and all(tag == _der.INTEGER for tag, _ in items):
        return _pkcs1_private(der)
    raise ValueError(_keys.DESERIALIZE)


def _spki(der):
    ec, ed25519, rsa, x25519 = _modules()
    algorithm, parameter = _der.spki_algorithm(der)
    if algorithm == _RSA:
        return rsa.RSAPublicKey._from_spki(der)
    with _keys.loading():
        if algorithm == _EC:
            if parameter is None:
                raise ValueError(_keys.DESERIALIZE)
            curve = ec._curve_for_oid(parameter)
            ec._rind(curve)
            return ec.EllipticCurvePublicKey.from_encoded_point(curve, _der.spki_key(der))
        if algorithm == _ED25519:
            return ed25519.Ed25519PublicKey(_signature.PublicKey.from_spki(_signature.verify.ED25519, der))
        if algorithm == _X25519:
            return x25519.X25519PublicKey(_agreement.PublicKey.from_spki(_agreement.X25519, der))
    _unsupported_type(algorithm)


def _pkcs1_public(der):
    rsa = _modules()[2]
    return rsa.RSAPublicKey._from_spki(_der.spki(rsa._ALGORITHM, der))


def _public_der(der):
    """Routes a `SubjectPublicKeyInfo` or a PKCS#1 `RSAPublicKey` by its structure."""
    items = _der.elements(_der.one(der, _der.SEQUENCE))
    if items and items[0][0] == _der.SEQUENCE:
        return _spki(der)
    if len(items) == 2 and all(tag == _der.INTEGER for tag, _ in items):
        return _pkcs1_public(der)
    raise ValueError(_keys.DESERIALIZE)


def _pem(data, labels):
    _keys.check_bytes("data", data)
    for label, headers, der in _der.pem_blocks(data):
        if label in labels:
            return label, headers, der
    raise ValueError(_keys.DESERIALIZE)


def load_pem_private_key(data, password, backend=None, *, unsafe_skip_rsa_key_validation=False):
    """Loads a PEM private key: PKCS#8, PKCS#1, or SEC1, unencrypted."""
    label, headers, der = _pem(data, _PRIVATE_LABELS)
    _check_password(password, label == "ENCRYPTED PRIVATE KEY" or b"ENCRYPTED" in headers)
    if label == "PRIVATE KEY":
        return _pkcs8(der)
    if label == "RSA PRIVATE KEY":
        return _pkcs1_private(der)
    return _sec1(der, _der.elements(_der.one(der, _der.SEQUENCE)))


def load_der_private_key(data, password, backend=None, *, unsafe_skip_rsa_key_validation=False):
    """Loads a DER private key: PKCS#8, PKCS#1, or SEC1, unencrypted."""
    _keys.check_bytes("data", data)
    der = bytes(data)
    items = _der.elements(_der.one(der, _der.SEQUENCE))
    # An EncryptedPrivateKeyInfo is an AlgorithmIdentifier and an OCTET STRING.
    encrypted = len(items) == 2 and items[0][0] == _der.SEQUENCE and items[1][0] == _der.OCTET_STRING
    _check_password(password, encrypted)
    return _private_der(der)


def load_pem_public_key(data, backend=None):
    """Loads a PEM public key: `SubjectPublicKeyInfo` or PKCS#1."""
    label, _, der = _pem(data, _PUBLIC_LABELS)
    if label == "RSA PUBLIC KEY":
        return _pkcs1_public(der)
    return _spki(der)


def load_der_public_key(data, backend=None):
    """Loads a DER public key: `SubjectPublicKeyInfo` or PKCS#1."""
    _keys.check_bytes("data", data)
    return _public_der(bytes(data))


def load_ssh_public_key(data, backend=None):
    """Loads an OpenSSH public key line: RSA, ECDSA on P-256, P-384, or P-521, or Ed25519."""
    ec, ed25519, rsa, _ = _modules()
    _keys.check_bytes("data", data)
    kind, reader = _ssh.decode_public(data)
    if kind == b"ssh-rsa":
        e, n = reader.mpint(), reader.mpint()
        reader.done()
        return rsa.RSAPublicNumbers(e, n).public_key()
    if kind == b"ssh-ed25519":
        key = reader.string()
        reader.done()
        return ed25519.Ed25519PublicKey.from_public_bytes(key)
    curves = {b"ecdsa-sha2-nistp256": ec.SECP256R1, b"ecdsa-sha2-nistp384": ec.SECP384R1, b"ecdsa-sha2-nistp521": ec.SECP521R1}
    if kind in curves:
        if reader.string() != kind[len(b"ecdsa-sha2-") :]:
            raise ValueError("Curve name mismatch")
        point = reader.string()
        reader.done()
        return ec.EllipticCurvePublicKey.from_encoded_point(curves[kind](), point)
    raise unsupported("Key type", _Reasons.UNSUPPORTED_PUBLIC_KEY_ALGORITHM)


def load_ssh_private_key(data, password, backend=None, *, unsafe_skip_rsa_key_validation=False):
    """Loads an OpenSSH private key; rind reads none."""
    raise unsupported("OpenSSH private keys", _Reasons.UNSUPPORTED_SERIALIZATION)


def load_pem_parameters(data, backend=None):
    """Loads Diffie-Hellman parameters; rind has no finite-field Diffie-Hellman."""
    raise unsupported("DH parameters", _Reasons.UNSUPPORTED_DIFFIE_HELLMAN)


def load_der_parameters(data, backend=None):
    """Loads Diffie-Hellman parameters; rind has no finite-field Diffie-Hellman."""
    raise unsupported("DH parameters", _Reasons.UNSUPPORTED_DIFFIE_HELLMAN)


__all__ = [
    "BestAvailableEncryption", "Encoding", "KeySerializationEncryption", "NoEncryption", "ParameterFormat",
    "PrivateFormat", "PublicFormat", "_KeySerializationEncryption", "load_der_parameters", "load_der_private_key",
    "load_der_public_key", "load_pem_parameters", "load_pem_private_key", "load_pem_public_key",
    "load_ssh_private_key", "load_ssh_public_key",
]
