"""RSA: PKCS#1 v1.5 and PSS signatures and OAEP encryption, on rind's RSA."""

import abc

import pyrind
from pyrind import rsa as _rsa
from pyrind import signature as _signature
from pyrind.signature import sign as _sign
from pyrind.signature import verify as _verify

from pyrind_cryptography import _der
from pyrind_cryptography.exceptions import _Reasons, unsupported
from pyrind_cryptography.hazmat.primitives import _keys, hashes
from pyrind_cryptography.hazmat.primitives.asymmetric import padding as _padding
from pyrind_cryptography.hazmat.primitives.asymmetric import utils as _utils
from pyrind_cryptography.hazmat.primitives.serialization import _ssh

_ALGORITHM = _der.sequence(_der.encode(_der.OID, _der.encode_oid("1.2.840.113549.1.1.1")), _der.encode(_der.NULL, b""))

_SIZES = {
    2048: _rsa.KeySize.RSA_2048,
    3072: _rsa.KeySize.RSA_3072,
    4096: _rsa.KeySize.RSA_4096,
    6144: _rsa.KeySize.RSA_6144,
    8192: _rsa.KeySize.RSA_8192,
}
_PKCS1_SIGN = {"sha256": _sign.RSA_PKCS1_SHA256, "sha384": _sign.RSA_PKCS1_SHA384, "sha512": _sign.RSA_PKCS1_SHA512}
_PSS_SIGN = {"sha256": _sign.RSA_PSS_SHA256, "sha384": _sign.RSA_PSS_SHA384, "sha512": _sign.RSA_PSS_SHA512}
_PKCS1_VERIFY = {
    "sha1": _verify.legacy.RSA_PKCS1_SHA1,
    "sha256": _verify.RSA_PKCS1_SHA256,
    "sha384": _verify.RSA_PKCS1_SHA384,
    "sha512": _verify.RSA_PKCS1_SHA512,
}
# rind's PKCS#1 v1.5 verifiers for moduli from 1024 bits, which those above refuse below 2048.
_PKCS1_VERIFY_1024 = {
    "sha1": _verify.legacy.RSA_PKCS1_1024_SHA1,
    "sha256": _verify.legacy.RSA_PKCS1_1024_SHA256,
    "sha512": _verify.legacy.RSA_PKCS1_1024_SHA512,
}
_PSS_VERIFY = {"sha256": _verify.RSA_PSS_SHA256, "sha384": _verify.RSA_PSS_SHA384, "sha512": _verify.RSA_PSS_SHA512}
_PSS_VERIFY_ANY_SALT = {
    "sha256": _verify.RSA_PSS_SHA256_ANY_SALT,
    "sha384": _verify.RSA_PSS_SHA384_ANY_SALT,
    "sha512": _verify.RSA_PSS_SHA512_ANY_SALT,
}
_OAEP = {"sha1": _rsa.legacy.OAEP_SHA1, "sha256": _rsa.OAEP_SHA256, "sha384": _rsa.OAEP_SHA384, "sha512": _rsa.OAEP_SHA512}


def _check_size(bits, low):
    """Refuses a modulus size rind lacks, from `low` bits to 8192, as unsupported rather than malformed."""
    if not low <= bits <= 8192:
        raise unsupported(f"{bits}-bit RSA keys", _Reasons.UNSUPPORTED_PUBLIC_KEY_ALGORITHM)


def _check_private_size(pkcs1):
    """Refuses a PKCS#1 `RSAPrivateKey` whose modulus rind lacks; rind parses the rest."""
    try:
        n = _der.integers(pkcs1)[1]
    except (ValueError, IndexError):
        return
    _check_size(n.bit_length(), 2048)


def _hash_name(algorithm):
    if isinstance(algorithm, _utils.Prehashed):
        raise unsupported("Prehashed RSA", _Reasons.UNSUPPORTED_HASH)
    if not isinstance(algorithm, hashes.HashAlgorithm):
        raise TypeError("Expected instance of hashes.HashAlgorithm.")
    return algorithm.name


def _mgf1_hash(padding):
    if not isinstance(padding._mgf, _padding.MGF1):
        raise unsupported("Only MGF1", _Reasons.UNSUPPORTED_MGF)
    return padding._mgf._algorithm.name


def _choose(table, name, what):
    try:
        return table[name]
    except KeyError:
        raise unsupported(f"{what} with {name}", _Reasons.UNSUPPORTED_PADDING) from None


def _pss_salt_is_digest(padding, hash_name, digest_size, key_size, verifying):
    """Whether `padding`'s salt is the digest's length, which is all rind signs with; or None for any length, which rind verifies."""
    salt = padding._salt_length
    if isinstance(salt, _padding._DigestLength):
        return True
    if isinstance(salt, _padding._Auto):
        if not verifying:
            raise ValueError("PSS salt length can only be set to AUTO when verifying")
        return None
    if isinstance(salt, _padding._MaxLength):
        salt = (key_size + 6) // 8 - digest_size - 2
    if salt != digest_size:
        raise unsupported(f"PSS with a {salt}-byte salt and {hash_name}", _Reasons.UNSUPPORTED_PADDING)
    return True


def _oaep_algorithm(padding):
    if isinstance(padding, _padding.PKCS1v15):
        raise unsupported("PKCS#1 v1.5 encryption", _Reasons.UNSUPPORTED_PADDING)
    if not isinstance(padding, _padding.OAEP):
        if isinstance(padding, _padding.AsymmetricPadding):
            raise unsupported(f"{padding.name} encryption", _Reasons.UNSUPPORTED_PADDING)
        raise TypeError("Padding must be an instance of AsymmetricPadding.")
    name = padding.algorithm.name
    if _mgf1_hash(padding) != name:
        raise unsupported("OAEP with a different MGF1 hash", _Reasons.UNSUPPORTED_PADDING)
    return _choose(_OAEP, name, "OAEP"), padding._label or b""


class RSAPublicNumbers:
    """An RSA public key's exponent `e` and modulus `n`."""

    def __init__(self, e, n):
        if not isinstance(e, int) or not isinstance(n, int):
            raise TypeError("RSAPublicNumbers arguments must be integers.")
        self._e, self._n = e, n

    @property
    def e(self):
        return self._e

    @property
    def n(self):
        return self._n

    def public_key(self, backend=None):
        """Loads the key."""
        if self._e < 3 or self._n < 3:
            raise ValueError("Invalid RSA key")
        return RSAPublicKey._from_spki(_der.spki(_ALGORITHM, _der.sequence(_der.encode_integer(self._n), _der.encode_integer(self._e))))

    def __eq__(self, other):
        if not isinstance(other, RSAPublicNumbers):
            return NotImplemented
        return self.e == other.e and self.n == other.n

    def __hash__(self):
        return hash((self.e, self.n))

    def __repr__(self):
        return f"<RSAPublicNumbers(e={self.e}, n={self.n})>"


class RSAPrivateNumbers:
    """An RSA private key's primes, exponents, and CRT values."""

    def __init__(self, p, q, d, dmp1, dmq1, iqmp, public_numbers):
        if not all(isinstance(value, int) for value in (p, q, d, dmp1, dmq1, iqmp)):
            raise TypeError("RSAPrivateNumbers p, q, d, dmp1, dmq1, iqmp arguments must all be an integers.")
        if not isinstance(public_numbers, RSAPublicNumbers):
            raise TypeError("RSAPrivateNumbers public_numbers must be an RSAPublicNumbers instance.")
        self._p, self._q, self._d = p, q, d
        self._dmp1, self._dmq1, self._iqmp = dmp1, dmq1, iqmp
        self._public_numbers = public_numbers

    p = property(lambda self: self._p)
    q = property(lambda self: self._q)
    d = property(lambda self: self._d)
    dmp1 = property(lambda self: self._dmp1)
    dmq1 = property(lambda self: self._dmq1)
    iqmp = property(lambda self: self._iqmp)
    public_numbers = property(lambda self: self._public_numbers)

    def private_key(self, backend=None, *, unsafe_skip_rsa_key_validation=False):
        """Loads the key, which rind always validates."""
        values = (self._public_numbers.n, self._public_numbers.e, self._d, self._p, self._q, self._dmp1, self._dmq1, self._iqmp)
        if any(value < 0 for value in values):
            raise ValueError("Invalid RSA key")
        der = _der.sequence(_der.encode_integer(0), *map(_der.encode_integer, values))
        _check_private_size(der)
        with _keys.loading():
            return RSAPrivateKey(_signature.RsaKeyPair.from_pkcs1(der))

    def __eq__(self, other):
        if not isinstance(other, RSAPrivateNumbers):
            return NotImplemented
        return (self.p, self.q, self.d, self.dmp1, self.dmq1, self.iqmp, self.public_numbers) == (
            other.p, other.q, other.d, other.dmp1, other.dmq1, other.iqmp, other.public_numbers,
        )

    def __hash__(self):
        return hash((self.p, self.q, self.d, self.dmp1, self.dmq1, self.iqmp, self.public_numbers))


class RSAPublicKey(metaclass=abc.ABCMeta):
    """An RSA public key."""

    def __init__(self, spki, n, e):
        self._spki = spki
        self._n, self._e = n, e
        self._keys = {}

    @classmethod
    def _from_spki(cls, der):
        """Loads `SubjectPublicKeyInfo` DER, refusing a modulus under 1024 bits or over 8192."""
        try:
            n = _der.integers(_der.spki_key(der))[0]
        except (ValueError, IndexError):
            pass
        else:
            _check_size(n.bit_length(), 1024)
        with _keys.loading():
            key = _signature.PublicKey.from_spki(_verify.legacy.RSA_PKCS1_1024_SHA256, der)
        n, e = _der.integers(bytes(key))
        public_key = RSAPublicKey(key.to_spki(), n, e)
        public_key._keys[_verify.legacy.RSA_PKCS1_1024_SHA256] = key
        return public_key

    @property
    def key_size(self):
        return self._n.bit_length()

    def public_numbers(self):
        return RSAPublicNumbers(self._e, self._n)

    def _pkcs1(self):
        return _der.spki_key(self._spki)

    def _openssh(self):
        return _ssh.encode_public(b"ssh-rsa", _ssh.mpint(self._e) + _ssh.mpint(self._n))

    def public_bytes(self, encoding, format):
        """Writes the key as `encoding` and `format`."""
        return _keys.public_bytes(encoding, format, spki=lambda: self._spki, pkcs1=self._pkcs1, openssh=self._openssh)

    def _verifier(self, padding, algorithm):
        hash_name = _hash_name(algorithm)
        if isinstance(padding, _padding.PKCS1v15):
            table = _PKCS1_VERIFY if self.key_size >= 2048 else _PKCS1_VERIFY_1024
            chosen = _choose(table, hash_name, f"PKCS#1 v1.5 for a {self.key_size}-bit key")
        elif isinstance(padding, _padding.PSS):
            if _mgf1_hash(padding) != hash_name:
                raise unsupported("PSS with a different MGF1 hash", _Reasons.UNSUPPORTED_PADDING)
            _check_size(self.key_size, 2048)
            exact = _pss_salt_is_digest(padding, hash_name, algorithm.digest_size, self.key_size, verifying=True)
            chosen = _choose(_PSS_VERIFY if exact else _PSS_VERIFY_ANY_SALT, hash_name, "PSS")
        elif isinstance(padding, _padding.AsymmetricPadding):
            raise unsupported(f"{padding.name} signatures", _Reasons.UNSUPPORTED_PADDING)
        else:
            raise TypeError("Padding must be an instance of AsymmetricPadding.")
        key = self._keys.get(chosen)
        if key is None:
            with _keys.loading():
                key = self._keys[chosen] = _signature.PublicKey.from_spki(chosen, self._spki)
        return key

    def verify(self, signature, data, padding, algorithm):
        """Checks `signature` over `data`; raises `InvalidSignature` if it does not verify."""
        key = self._verifier(padding, algorithm)
        with _keys.verifying():
            key.verify(data, signature)

    def recover_data_from_signature(self, signature, padding, algorithm):
        """Recovers the signed digest; rind only verifies."""
        raise unsupported("Recovering data from an RSA signature", _Reasons.UNSUPPORTED_PADDING)

    def encrypt(self, plaintext, padding):
        """Encrypts `plaintext` with OAEP."""
        algorithm, label = _oaep_algorithm(padding)
        _check_size(self.key_size, 2048)
        key = self._keys.get(algorithm)
        if key is None:
            with _keys.loading():
                key = self._keys[algorithm] = _rsa.EncryptingKey(algorithm, self._spki)
        try:
            return key.encrypt(plaintext, label=label)
        except pyrind.WrongLength:
            raise ValueError("Encryption failed") from None

    def __eq__(self, other):
        if not isinstance(other, RSAPublicKey):
            return NotImplemented
        return self._spki == other._spki

    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self


class RSAPrivateKey(metaclass=abc.ABCMeta):
    """An RSA private key."""

    def __init__(self, key_pair):
        self._key_pair = key_pair
        self._public_key = RSAPublicKey._from_spki(key_pair.to_spki())
        self._decrypting = {}

    @property
    def key_size(self):
        return self._public_key.key_size

    def public_key(self):
        return self._public_key

    def private_numbers(self):
        _, n, e, d, p, q, dmp1, dmq1, iqmp = _der.integers(_der.pkcs8_key(self._key_pair.to_pkcs8()))
        return RSAPrivateNumbers(p, q, d, dmp1, dmq1, iqmp, RSAPublicNumbers(e, n))

    def private_bytes(self, encoding, format, encryption_algorithm):
        """Writes the key as `encoding` and `format`."""
        return _keys.private_bytes(
            encoding, format, encryption_algorithm, pkcs8=self._key_pair.to_pkcs8,
            traditional=("RSA PRIVATE KEY", lambda: _der.pkcs8_key(self._key_pair.to_pkcs8())),
        )

    def sign(self, data, padding, algorithm):
        """Signs `data` with PKCS#1 v1.5 or PSS."""
        hash_name = _hash_name(algorithm)
        if isinstance(padding, _padding.PKCS1v15):
            chosen = _choose(_PKCS1_SIGN, hash_name, "PKCS#1 v1.5 signing")
        elif isinstance(padding, _padding.PSS):
            if _mgf1_hash(padding) != hash_name:
                raise unsupported("PSS with a different MGF1 hash", _Reasons.UNSUPPORTED_PADDING)
            _pss_salt_is_digest(padding, hash_name, algorithm.digest_size, self.key_size, verifying=False)
            chosen = _choose(_PSS_SIGN, hash_name, "PSS signing")
        elif isinstance(padding, _padding.AsymmetricPadding):
            raise unsupported(f"{padding.name} signatures", _Reasons.UNSUPPORTED_PADDING)
        else:
            raise TypeError("Padding must be an instance of AsymmetricPadding.")
        return self._key_pair.sign(chosen, data)

    def decrypt(self, ciphertext, padding):
        """Decrypts an OAEP `ciphertext`; raises `ValueError` for any that does not decrypt."""
        algorithm, label = _oaep_algorithm(padding)
        key = self._decrypting.get(algorithm)
        if key is None:
            with _keys.loading():
                key = self._decrypting[algorithm] = _rsa.DecryptingKey.from_pkcs8(algorithm, self._key_pair.to_pkcs8())
        try:
            return key.decrypt(ciphertext, label=label)
        except pyrind.DecryptFailed:
            raise ValueError("Decryption failed") from None

    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self


def generate_private_key(public_exponent, key_size, backend=None):
    """Generates a key of `key_size` bits; rind takes only exponent 65537 and sizes of 2048, 3072, 4096, 6144, and 8192 bits."""
    if public_exponent not in (3, 65537):
        raise ValueError("public_exponent must be either 3 (for legacy compatibility) or 65537. Almost everyone should choose 65537 here!")
    if key_size < 1024:
        raise ValueError("key_size must be at least 1024-bits.")
    if public_exponent != 65537 or key_size not in _SIZES:
        raise unsupported(f"RSA key generation with e={public_exponent} and {key_size} bits", _Reasons.UNSUPPORTED_PUBLIC_KEY_ALGORITHM)
    return RSAPrivateKey(_signature.RsaKeyPair.generate(_SIZES[key_size]))


def _secret_arithmetic(name):
    def refuse(*args, **kwargs):
        raise unsupported(f"{name}, whose arithmetic on secrets rind would run in variable time,", _Reasons.UNSUPPORTED_PUBLIC_KEY_ALGORITHM)

    refuse.__name__ = name
    refuse.__doc__ = f"pyca's {name}; rind has no constant-time version, so this raises `UnsupportedAlgorithm`."
    return refuse


rsa_crt_iqmp = _secret_arithmetic("rsa_crt_iqmp")
rsa_crt_dmp1 = _secret_arithmetic("rsa_crt_dmp1")
rsa_crt_dmq1 = _secret_arithmetic("rsa_crt_dmq1")
rsa_recover_prime_factors = _secret_arithmetic("rsa_recover_prime_factors")

__all__ = [
    "RSAPrivateKey", "RSAPrivateNumbers", "RSAPublicKey", "RSAPublicNumbers", "generate_private_key",
    "rsa_crt_dmp1", "rsa_crt_dmq1", "rsa_crt_iqmp", "rsa_recover_prime_factors",
]
