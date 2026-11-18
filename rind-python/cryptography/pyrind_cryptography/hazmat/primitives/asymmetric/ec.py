"""Elliptic curves: ECDSA and ECDH on P-256, P-384, and P-521, on rind's."""

import abc

import pyrind
from pyrind import agreement as _agreement
from pyrind import signature as _signature
from pyrind.signature import sign as _sign
from pyrind.signature import verify as _verify

from pyrind_cryptography import _der
from pyrind_cryptography.exceptions import _Reasons, unsupported
from pyrind_cryptography.hazmat.primitives import _keys, hashes
from pyrind_cryptography.hazmat.primitives.asymmetric import utils as _utils
from pyrind_cryptography.hazmat.primitives.serialization import _ssh


class EllipticCurve(metaclass=abc.ABCMeta):
    """An elliptic curve."""

    name: str
    key_size: int
    group_order: int


class EllipticCurveSignatureAlgorithm(metaclass=abc.ABCMeta):
    """A signature algorithm over an elliptic curve."""


def _curve(cls, name, key_size, group_order):
    return type(cls, (EllipticCurve,), {"name": name, "key_size": key_size, "group_order": group_order, "__doc__": f"The curve {name}."})


SECP256R1 = _curve("SECP256R1", "secp256r1", 256, 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551)
SECP384R1 = _curve(
    "SECP384R1", "secp384r1", 384,
    0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFC7634D81F4372DDF581A0DB248B0A77AECEC196ACCC52973,
)
SECP521R1 = _curve(
    "SECP521R1", "secp521r1", 521,
    0x1FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFA51868783BF2F966B7FCC0148F709A5D03BB5C9B8899C47AEBB6FB71E91386409,
)
SECP256K1 = _curve("SECP256K1", "secp256k1", 256, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141)
SECP224R1 = _curve("SECP224R1", "secp224r1", 224, 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFF16A2E0B8F03E13DD29455C5C2A3D)
SECP192R1 = _curve("SECP192R1", "secp192r1", 192, 0xFFFFFFFFFFFFFFFFFFFFFFFF99DEF836146BC9B1B4D22831)
BrainpoolP256R1 = _curve("BrainpoolP256R1", "brainpoolP256r1", 256, 0xA9FB57DBA1EEA9BC3E660A909D838D718C397AA3B561A6F7901E0E82974856A7)
BrainpoolP384R1 = _curve(
    "BrainpoolP384R1", "brainpoolP384r1", 384,
    0x8CB91E82A3386D280F5D6F7E50E641DF152F7109ED5456B31F166E6CAC0425A7CF3AB6AF6B7FC3103B883202E9046565,
)
BrainpoolP512R1 = _curve(
    "BrainpoolP512R1", "brainpoolP512r1", 512,
    0xAADD9DB8DBE9C48B3FD4E6AE33C9FC07CB308DB3B3C9D20ED6639CCA70330870553E5C414CA92619418661197FAC10471DB1D381085DDADDB58796829CA90069,
)

_CURVE_TYPES = {
    curve.name: curve
    for curve in (SECP192R1, SECP224R1, SECP256K1, SECP256R1, SECP384R1, SECP521R1, BrainpoolP256R1, BrainpoolP384R1, BrainpoolP512R1)
}
_CURVE_TYPES["prime192v1"] = SECP192R1
_CURVE_TYPES["prime256v1"] = SECP256R1

# Each curve rind has: its algorithms, the field prime and `b` for
# decompressing points (`a` is -3 on all three), its OID, and its SSH name.
_RIND = {
    "secp256r1": (
        _sign.ECDSA_P256_SHA256_ASN1, _agreement.ECDH_P256, 2**256 - 2**224 + 2**192 + 2**96 - 1,
        0x5AC635D8AA3A93E7B3EBBD55769886BC651D06B0CC53B0F63BCE3C3E27D2604B, "1.2.840.10045.3.1.7", b"nistp256",
    ),
    "secp384r1": (
        _sign.ECDSA_P384_SHA384_ASN1, _agreement.ECDH_P384, 2**384 - 2**128 - 2**96 + 2**32 - 1,
        0xB3312FA7E23EE7E4988E056BE3F82D19181D9C6EFE8141120314088F5013875AC656398D8A2ED19D2A85C8EDD3EC2AEF,
        "1.3.132.0.34", b"nistp384",
    ),
    "secp521r1": (
        _sign.ECDSA_P521_SHA512_ASN1, _agreement.ECDH_P521, 2**521 - 1,
        0x0051953EB9618E1C9A1F929A21A0B68540EEA2DA725B99B315F3B8B489918EF109E156193951EC7E937B1652C0BD3BB1BF073573DF883D2C34F1EF451FD46B503F00,
        "1.3.132.0.35", b"nistp521",
    ),
}
_OIDS = {
    "1.2.840.10045.3.1.7": SECP256R1, "1.3.132.0.34": SECP384R1, "1.3.132.0.35": SECP521R1,
    "1.3.132.0.10": SECP256K1, "1.3.132.0.33": SECP224R1, "1.2.840.10045.3.1.1": SECP192R1,
    "1.3.36.3.3.2.8.1.1.7": BrainpoolP256R1, "1.3.36.3.3.2.8.1.1.11": BrainpoolP384R1, "1.3.36.3.3.2.8.1.1.13": BrainpoolP512R1,
}

# The ECDSA algorithm rind verifies a curve and hash with.
_VERIFY = {
    ("secp256r1", "sha256"): _verify.ECDSA_P256_SHA256_ASN1,
    ("secp256r1", "sha384"): _verify.ECDSA_P256_SHA384_ASN1,
    ("secp256r1", "sha512"): _verify.ECDSA_P256_SHA512_ASN1,
    ("secp384r1", "sha256"): _verify.ECDSA_P384_SHA256_ASN1,
    ("secp384r1", "sha384"): _verify.ECDSA_P384_SHA384_ASN1,
    ("secp384r1", "sha512"): _verify.ECDSA_P384_SHA512_ASN1,
    ("secp521r1", "sha256"): _verify.ECDSA_P521_SHA256_ASN1,
    ("secp521r1", "sha384"): _verify.ECDSA_P521_SHA384_ASN1,
    ("secp521r1", "sha512"): _verify.ECDSA_P521_SHA512_ASN1,
}
_SIGN_HASH = {"secp256r1": "sha256", "secp384r1": "sha384", "secp521r1": "sha512"}


def _rind(curve):
    """rind's algorithms and constants for `curve`, raising `UnsupportedAlgorithm` for one it lacks."""
    if not isinstance(curve, EllipticCurve):
        raise TypeError("curve must be an EllipticCurve instance")
    try:
        return _RIND[curve.name]
    except KeyError:
        raise unsupported(f"Curve {curve.name}", _Reasons.UNSUPPORTED_ELLIPTIC_CURVE) from None


def _curve_for_oid(oid):
    try:
        return _OIDS[oid]()
    except KeyError:
        raise unsupported(f"Curve {oid}", _Reasons.UNSUPPORTED_ELLIPTIC_CURVE) from None


def _width(curve):
    return (curve.key_size + 7) // 8


class ECDSA(EllipticCurveSignatureAlgorithm):
    """ECDSA with `algorithm`; rind's signatures are randomized, never RFC 6979 deterministic."""

    def __init__(self, algorithm, deterministic_signing=False):
        if deterministic_signing:
            raise unsupported("Deterministic ECDSA signing", _Reasons.UNSUPPORTED_PUBLIC_KEY_ALGORITHM)
        self._algorithm = algorithm
        self._deterministic_signing = deterministic_signing

    @property
    def algorithm(self):
        return self._algorithm

    @property
    def deterministic_signing(self):
        return self._deterministic_signing


class ECDH:
    """Elliptic curve Diffie-Hellman."""


def _hash_name(signature_algorithm):
    if not isinstance(signature_algorithm, ECDSA):
        raise unsupported("Signature algorithm", _Reasons.UNSUPPORTED_PUBLIC_KEY_ALGORITHM)
    algorithm = signature_algorithm.algorithm
    if isinstance(algorithm, _utils.Prehashed):
        raise unsupported("Prehashed ECDSA", _Reasons.UNSUPPORTED_HASH)
    if not isinstance(algorithm, hashes.HashAlgorithm):
        raise TypeError("Expected instance of hashes.HashAlgorithm.")
    return algorithm.name


class EllipticCurvePublicNumbers:
    """An elliptic curve public key's coordinates."""

    def __init__(self, x, y, curve):
        if not isinstance(x, int) or not isinstance(y, int):
            raise TypeError("x and y must be integers.")
        if not isinstance(curve, EllipticCurve):
            raise TypeError("curve must provide the EllipticCurve interface.")
        self._x, self._y, self._curve = x, y, curve

    @property
    def x(self):
        return self._x

    @property
    def y(self):
        return self._y

    @property
    def curve(self):
        return self._curve

    def public_key(self, backend=None):
        """Loads the key; raises `ValueError` for a point not on the curve."""
        _rind(self._curve)
        width = _width(self._curve)
        if self._x < 0 or self._y < 0 or self._x.bit_length() > 8 * width or self._y.bit_length() > 8 * width:
            raise ValueError("Invalid EC key.")
        return EllipticCurvePublicKey._load(self._curve, b"\x04" + self._x.to_bytes(width, "big") + self._y.to_bytes(width, "big"))

    def __eq__(self, other):
        if not isinstance(other, EllipticCurvePublicNumbers):
            return NotImplemented
        return self.x == other.x and self.y == other.y and self.curve.name == other.curve.name and self.curve.key_size == other.curve.key_size

    def __hash__(self):
        return hash((self.x, self.y, self.curve.name, self.curve.key_size))

    def __repr__(self):
        return f"<EllipticCurvePublicNumbers(curve={self.curve.name}, x={self.x}, y={self.y})>"


class EllipticCurvePrivateNumbers:
    """An elliptic curve private key's scalar and public numbers."""

    def __init__(self, private_value, public_numbers):
        if not isinstance(private_value, int):
            raise TypeError("private_value must be an integer.")
        if not isinstance(public_numbers, EllipticCurvePublicNumbers):
            raise TypeError("public_numbers must be an EllipticCurvePublicNumbers instance.")
        self._private_value = private_value
        self._public_numbers = public_numbers

    @property
    def private_value(self):
        return self._private_value

    @property
    def public_numbers(self):
        return self._public_numbers

    def private_key(self, backend=None):
        """Loads the key; raises `ValueError` unless the public numbers match the scalar."""
        curve = self._public_numbers.curve
        sign = _rind(curve)[0]
        width = _width(curve)
        if not 0 < self._private_value < curve.group_order:
            raise ValueError("Invalid EC key.")
        public_key = self._public_numbers.public_key()
        with _keys.loading():
            key_pair = _signature.EcdsaKeyPair.from_scalar_and_public_key(
                sign, self._private_value.to_bytes(width, "big"), public_key._point
            )
        return EllipticCurvePrivateKey(curve, key_pair)

    def __eq__(self, other):
        if not isinstance(other, EllipticCurvePrivateNumbers):
            return NotImplemented
        return self.private_value == other.private_value and self.public_numbers == other.public_numbers

    def __hash__(self):
        return hash((self.private_value, self.public_numbers))


def _decompress(curve, point):
    """The uncompressed form of the compressed point `point`, which is public, so plain integer arithmetic serves."""
    _, _, p, b, _, _ = _rind(curve)
    width = _width(curve)
    if len(point) != 1 + width:
        raise ValueError("Invalid EC key.")
    x = int.from_bytes(point[1:], "big")
    if x >= p:
        raise ValueError("Invalid EC key.")
    rhs = (pow(x, 3, p) - 3 * x + b) % p
    # Each curve's prime is 3 mod 4, so this is a square root when one exists.
    y = pow(rhs, (p + 1) // 4, p)
    if y * y % p != rhs:
        raise ValueError("Invalid EC key.")
    if y & 1 != point[0] & 1:
        y = p - y
    return b"\x04" + point[1:] + y.to_bytes(width, "big")


class EllipticCurvePublicKey(metaclass=abc.ABCMeta):
    """An elliptic curve public key."""

    def __init__(self, curve, point):
        self._curve = curve
        self._point = point
        self._verifiers = {}

    @classmethod
    def _load(cls, curve, point):
        """Loads the uncompressed point `point` on `curve`, refusing one off the curve."""
        _rind(curve)
        with _keys.loading():
            key = _signature.PublicKey(_VERIFY[curve.name, _SIGN_HASH[curve.name]], point)
        public_key = EllipticCurvePublicKey(curve, point)
        public_key._verifiers[_SIGN_HASH[curve.name]] = key
        return public_key

    @classmethod
    def from_encoded_point(cls, curve, data):
        """Loads an X9.62 point, compressed or not, on `curve`."""
        _keys.check_bytes("data", data)
        data = bytes(data)
        if not isinstance(curve, EllipticCurve):
            raise TypeError("curve must be an EllipticCurve instance")
        if len(data) == 0:
            raise ValueError("data must not be an empty byte string")
        if data[0] not in (0x02, 0x03, 0x04):
            raise ValueError("Unsupported elliptic curve point type")
        _rind(curve)
        if data[0] != 0x04:
            data = _decompress(curve, data)
        return cls._load(curve, data)

    @property
    def curve(self):
        return self._curve

    @property
    def key_size(self):
        return self._curve.key_size

    def public_numbers(self):
        width = _width(self._curve)
        x = int.from_bytes(self._point[1 : 1 + width], "big")
        y = int.from_bytes(self._point[1 + width :], "big")
        return EllipticCurvePublicNumbers(x, y, self._curve)

    def _spki(self):
        oid = _rind(self._curve)[4]
        algorithm = _der.sequence(_der.encode(_der.OID, _der.encode_oid("1.2.840.10045.2.1")), _der.encode(_der.OID, _der.encode_oid(oid)))
        return _der.spki(algorithm, self._point)

    def _encode_point(self, compressed):
        if not compressed:
            return self._point
        width = _width(self._curve)
        return bytes([2 | self._point[-1] & 1]) + self._point[1 : 1 + width]

    def _openssh(self):
        name = _rind(self._curve)[5]
        kind = b"ecdsa-sha2-" + name
        return _ssh.encode_public(kind, _ssh.string(name) + _ssh.string(self._point))

    def public_bytes(self, encoding, format):
        """Writes the key as `encoding` and `format`."""
        return _keys.public_bytes(encoding, format, spki=self._spki, point=self._encode_point, openssh=self._openssh)

    def verify(self, signature, data, signature_algorithm):
        """Checks the DER `signature` over `data`; raises `InvalidSignature` if it does not verify."""
        hash_name = _hash_name(signature_algorithm)
        key = self._verifiers.get(hash_name)
        if key is None:
            try:
                algorithm = _VERIFY[self._curve.name, hash_name]
            except KeyError:
                raise unsupported(f"ECDSA on {self._curve.name} with {hash_name}", _Reasons.UNSUPPORTED_HASH) from None
            key = self._verifiers[hash_name] = _signature.PublicKey(algorithm, self._point)
        with _keys.verifying():
            key.verify(data, signature)

    def __eq__(self, other):
        if not isinstance(other, EllipticCurvePublicKey):
            return NotImplemented
        return self._curve.name == other._curve.name and self._point == other._point

    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self


class EllipticCurvePrivateKey(metaclass=abc.ABCMeta):
    """An elliptic curve private key."""

    def __init__(self, curve, key_pair):
        self._curve = curve
        self._key_pair = key_pair
        self._agreement = None

    @property
    def curve(self):
        return self._curve

    @property
    def key_size(self):
        return self._curve.key_size

    def public_key(self):
        point = bytes(self._key_pair.public_key())
        public_key = EllipticCurvePublicKey(self._curve, point)
        public_key._verifiers[_SIGN_HASH[self._curve.name]] = self._key_pair.public_key()
        return public_key

    def private_numbers(self):
        value = int.from_bytes(self._key_pair.to_scalar(), "big")
        return EllipticCurvePrivateNumbers(value, self.public_key().public_numbers())

    def sign(self, data, signature_algorithm):
        """Signs `data`, returning a DER signature; rind signs each curve only with its own hash."""
        hash_name = _hash_name(signature_algorithm)
        if hash_name != _SIGN_HASH[self._curve.name]:
            raise unsupported(f"ECDSA signing on {self._curve.name} with {hash_name}", _Reasons.UNSUPPORTED_HASH)
        return self._key_pair.sign(data)

    def exchange(self, algorithm, peer_public_key):
        """The ECDH shared secret with `peer_public_key`."""
        if not isinstance(algorithm, ECDH):
            raise unsupported("Exchange algorithm", _Reasons.UNSUPPORTED_EXCHANGE_ALGORITHM)
        if not isinstance(peer_public_key, EllipticCurvePublicKey):
            raise TypeError("peer_public_key must be an EllipticCurvePublicKey")
        if peer_public_key.curve.name != self._curve.name:
            raise ValueError("peer_public_key and self are not on the same curve")
        if self._agreement is None:
            self._agreement = _agreement.PrivateKey.from_pkcs8(_rind(self._curve)[1], self._key_pair.to_pkcs8())
        try:
            return self._agreement.agree(peer_public_key._point)
        except pyrind.KeyRejected:
            raise ValueError("Error computing shared key.") from None

    def private_bytes(self, encoding, format, encryption_algorithm):
        """Writes the key as `encoding` and `format`."""
        return _keys.private_bytes(
            encoding, format, encryption_algorithm, pkcs8=self._key_pair.to_pkcs8, traditional=("EC PRIVATE KEY", self._key_pair.to_sec1)
        )

    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self


def generate_private_key(curve, backend=None):
    """Generates a key on `curve`."""
    return EllipticCurvePrivateKey(curve, _signature.EcdsaKeyPair.generate(_rind(curve)[0]))


def derive_private_key(private_value, curve, backend=None):
    """Loads the key on `curve` whose scalar is `private_value`."""
    if not isinstance(private_value, int):
        raise TypeError("private_value must be an integer type.")
    if private_value <= 0:
        raise ValueError("private_value must be a positive integer.")
    sign, ecdh, *_ = _rind(curve)
    if private_value >= curve.group_order:
        raise ValueError("Invalid EC key.")
    scalar = private_value.to_bytes(_width(curve), "big")
    with _keys.loading():
        point = bytes(_agreement.PrivateKey.from_scalar(ecdh, scalar).public_key())
        return EllipticCurvePrivateKey(curve, _signature.EcdsaKeyPair.from_scalar_and_public_key(sign, scalar, point))


__all__ = [
    "ECDH", "ECDSA", "EllipticCurve", "EllipticCurvePrivateKey", "EllipticCurvePrivateNumbers",
    "EllipticCurvePublicKey", "EllipticCurvePublicNumbers", "EllipticCurveSignatureAlgorithm",
    "BrainpoolP256R1", "BrainpoolP384R1", "BrainpoolP512R1", "SECP192R1", "SECP224R1", "SECP256K1",
    "SECP256R1", "SECP384R1", "SECP521R1", "derive_private_key", "generate_private_key",
]
