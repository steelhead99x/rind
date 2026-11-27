"""Ed25519 signatures (RFC 8032)."""

from typing import final

from typing_extensions import Buffer

@final
class PublicKey:
    """An Ed25519 public key, whose `bytes` are its 32-byte encoding."""

    def __new__(cls, data: Buffer) -> PublicKey:
        """Parses a 32-byte public key, refusing one of small order."""
    @staticmethod
    def from_spki(der: Buffer) -> PublicKey:
        """Parses `SubjectPublicKeyInfo` DER, refusing one that names another algorithm."""
    def verify(self, message: Buffer, signature: Buffer) -> None:
        """Checks `signature` over `message`; raises `BadSignature` if it does not verify."""
    def to_spki(self) -> bytes:
        """Encodes the key as `SubjectPublicKeyInfo` DER."""
    def __bytes__(self) -> bytes: ...

@final
class KeyPair:
    """An Ed25519 key pair."""

    @staticmethod
    def generate() -> KeyPair:
        """Generates a key pair."""
    @staticmethod
    def from_pkcs8(der: Buffer) -> KeyPair:
        """Loads a key pair from PKCS#8 v1 or v2 DER, refused if a v2 key's public key does not match."""
    @staticmethod
    def from_seed(seed: Buffer) -> KeyPair:
        """Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public key."""
    @staticmethod
    def from_seed_and_public_key(seed: Buffer, public_key: Buffer) -> KeyPair:
        """Loads a 32-byte seed, refused unless `public_key` is its public key."""
    def public_key(self) -> PublicKey:
        """The public key, the same object each call."""
    def sign(self, message: Buffer) -> bytes:
        """Signs `message`."""
    def to_pkcs8(self) -> bytes:
        """Encodes the key pair as PKCS#8 v2 DER (RFC 5958), with its public key."""
    def to_pkcs8v1(self) -> bytes:
        """Encodes the private key as PKCS#8 v1 DER (RFC 8410), as OpenSSL writes it."""
    def to_seed(self) -> bytes:
        """Returns the private key's 32-byte seed."""

__all__ = ["PublicKey", "KeyPair"]
