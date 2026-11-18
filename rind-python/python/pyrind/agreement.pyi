"""Key agreement: X25519, and ECDH on P-256, P-384, and P-521."""

from typing import final

from typing_extensions import Buffer

@final
class Algorithm:
    """A key agreement algorithm."""

X25519: Algorithm
ECDH_P256: Algorithm
ECDH_P384: Algorithm
ECDH_P521: Algorithm

@final
class PrivateKey:
    """A private key for key agreement."""

    @staticmethod
    def generate(algorithm: Algorithm) -> PrivateKey:
        """Generates a key for `algorithm`."""
    @staticmethod
    def from_scalar(algorithm: Algorithm, scalar: Buffer) -> PrivateKey:
        """Loads a key for `algorithm` from its big-endian scalar, or for X25519 its 32 bytes."""
    @staticmethod
    def from_pkcs8(algorithm: Algorithm, der: Buffer) -> PrivateKey:
        """Loads a key for `algorithm` from PKCS#8 DER."""
    @staticmethod
    def from_sec1(algorithm: Algorithm, der: Buffer) -> PrivateKey:
        """Loads an ECDH key for `algorithm` from SEC1 `ECPrivateKey` DER."""
    def public_key(self) -> PublicKey:
        """The public key to send the peer."""
    def agree(self, peer: Buffer) -> bytes:
        """Agrees a shared secret with the peer's public key `peer`, as `bytes(PublicKey)` encodes it; raises `KeyRejected` for an invalid one."""
    def to_pkcs8(self) -> bytes:
        """Encodes the key as PKCS#8 DER."""
    def to_scalar(self) -> bytes:
        """Returns the key's scalar, as `from_scalar` takes it."""

@final
class PublicKey:
    """A public key for key agreement, whose `bytes` are what `agree` takes: 32 bytes for X25519, and an uncompressed SEC1 point for ECDH."""

    def __new__(cls, algorithm: Algorithm, data: Buffer) -> PublicKey:
        """Parses a public key for `algorithm` from its `bytes` encoding."""
    @staticmethod
    def from_spki(algorithm: Algorithm, der: Buffer) -> PublicKey:
        """Parses a public key for `algorithm` from `SubjectPublicKeyInfo` DER."""
    def to_spki(self) -> bytes:
        """Encodes the key as `SubjectPublicKeyInfo` DER."""
    def __bytes__(self) -> bytes: ...

__all__ = ["Algorithm", "PrivateKey", "PublicKey", "X25519", "ECDH_P256", "ECDH_P384", "ECDH_P521"]
