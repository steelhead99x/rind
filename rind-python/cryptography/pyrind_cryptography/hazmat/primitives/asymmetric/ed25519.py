"""Ed25519 signatures, on rind's Ed25519."""

import abc

from pyrind import signature as _signature
from pyrind.signature import verify as _verify

from pyrind_cryptography.hazmat.primitives import _keys
from pyrind_cryptography.hazmat.primitives.serialization import _ssh


class Ed25519PublicKey(metaclass=abc.ABCMeta):
    """An Ed25519 public key."""

    def __init__(self, key):
        self._key = key

    @classmethod
    def from_public_bytes(cls, data):
        """Loads a 32-byte public key."""
        _keys.check_bytes("data", data)
        if len(memoryview(data).cast("B")) != 32:
            raise ValueError("An Ed25519 public key is 32 bytes long")
        with _keys.loading():
            return Ed25519PublicKey(_signature.PublicKey(_verify.ED25519, data))

    def public_bytes(self, encoding, format):
        """Writes the key as `encoding` and `format`."""
        return _keys.public_bytes(
            encoding, format, spki=self._key.to_spki, raw=self.public_bytes_raw,
            openssh=lambda: _ssh.encode_public(b"ssh-ed25519", _ssh.string(bytes(self._key))),
        )

    def public_bytes_raw(self):
        """The key's 32 bytes."""
        return bytes(self._key)

    def verify(self, signature, data):
        """Checks `signature` over `data`; raises `InvalidSignature` if it does not verify."""
        with _keys.verifying():
            self._key.verify(data, signature)

    def __eq__(self, other):
        if not isinstance(other, Ed25519PublicKey):
            return NotImplemented
        return bytes(self._key) == bytes(other._key)

    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self


class Ed25519PrivateKey(metaclass=abc.ABCMeta):
    """An Ed25519 private key."""

    def __init__(self, key_pair):
        self._key_pair = key_pair

    @classmethod
    def generate(cls):
        """Generates a key."""
        return Ed25519PrivateKey(_signature.Ed25519KeyPair.generate())

    @classmethod
    def from_private_bytes(cls, data):
        """Loads a 32-byte private key."""
        _keys.check_bytes("data", data)
        if len(memoryview(data).cast("B")) != 32:
            raise ValueError("An Ed25519 private key is 32 bytes long")
        with _keys.loading():
            return Ed25519PrivateKey(_signature.Ed25519KeyPair.from_seed(data))

    def public_key(self):
        """The key's public key."""
        return Ed25519PublicKey(self._key_pair.public_key())

    def private_bytes(self, encoding, format, encryption_algorithm):
        """Writes the key as `encoding` and `format`."""
        return _keys.private_bytes(
            encoding, format, encryption_algorithm, pkcs8=self._key_pair.to_pkcs8v1, raw=self._key_pair.to_seed
        )

    def private_bytes_raw(self):
        """The key's 32 bytes."""
        return self._key_pair.to_seed()

    def sign(self, data):
        """Signs `data`."""
        return self._key_pair.sign(data)

    def __copy__(self):
        return self

    def __deepcopy__(self, memo):
        return self


__all__ = ["Ed25519PrivateKey", "Ed25519PublicKey"]
