"""ECDSA signatures on P-256, P-384, and P-521.

A `KeyPair` signs with an `ecdsa.sign` algorithm, and a peer's `PublicKey`
is parsed for an `ecdsa.verify` algorithm.
"""

from typing import final

from typing_extensions import Buffer

from pyrind.ecdsa import sign as sign
from pyrind.ecdsa import verify as verify

@final
class SigningAlgorithm:
    """An algorithm a `KeyPair` signs with."""

@final
class VerificationAlgorithm:
    """An algorithm a `PublicKey` verifies with."""

@final
class PublicKey:
    """An ECDSA public key, which verifies with one algorithm, and whose `bytes` are its uncompressed SEC1 point."""

    def __new__(cls, algorithm: VerificationAlgorithm, point: Buffer) -> PublicKey:
        """Parses an uncompressed SEC1 point for `algorithm`."""
    @staticmethod
    def from_spki(algorithm: VerificationAlgorithm, der: Buffer) -> PublicKey:
        """Parses `SubjectPublicKeyInfo` DER for `algorithm`, refusing one that names another curve."""
    def verify(self, message: Buffer, signature: Buffer) -> None:
        """Checks `signature` over `message`; raises `BadSignature` if it does not verify."""
    def to_spki(self) -> bytes:
        """Encodes the key as `SubjectPublicKeyInfo` DER."""
    def __bytes__(self) -> bytes: ...

@final
class KeyPair:
    """An ECDSA key pair, which signs with one algorithm."""

    @staticmethod
    def generate(algorithm: SigningAlgorithm) -> KeyPair:
        """Generates a key pair for `algorithm`."""
    @staticmethod
    def from_pkcs8(algorithm: SigningAlgorithm, der: Buffer) -> KeyPair:
        """Loads a key pair for `algorithm` from PKCS#8 DER."""
    @staticmethod
    def from_sec1(algorithm: SigningAlgorithm, der: Buffer) -> KeyPair:
        """Loads a key pair for `algorithm` from SEC1 `ECPrivateKey` DER."""
    @staticmethod
    def from_scalar_and_public_key(algorithm: SigningAlgorithm, scalar: Buffer, public_key: Buffer) -> KeyPair:
        """Loads a key pair for `algorithm` from its big-endian scalar and its uncompressed public key, as a JWK's `d`, `x`, and `y` carry them, refused unless they match."""
    def public_key(self) -> PublicKey:
        """The public key, the same object each call, which verifies with the verification algorithm of the same name."""
    def sign(self, message: Buffer) -> bytes:
        """Signs `message`."""
    def to_pkcs8(self) -> bytes:
        """Encodes the key pair as PKCS#8 DER."""
    def to_sec1(self) -> bytes:
        """Encodes the key pair as SEC1 `ECPrivateKey` DER."""
    def to_scalar(self) -> bytes:
        """Returns the private key's big-endian scalar."""

__all__ = ["SigningAlgorithm", "VerificationAlgorithm", "PublicKey", "KeyPair", "sign", "verify"]
