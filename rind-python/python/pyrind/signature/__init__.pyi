"""Public key signatures: ECDSA on P-256, P-384, and P-521, RSA, and Ed25519.

A key pair signs with a `signature.sign` algorithm, and a peer's public key
is parsed for a `signature.verify` algorithm.
"""

from typing import final

from typing_extensions import Buffer

from pyrind.rsa import KeySize
from pyrind.signature import sign as sign
from pyrind.signature import verify as verify

@final
class EcdsaSigningAlgorithm:
    """An algorithm an `EcdsaKeyPair` signs with."""

@final
class RsaSigningAlgorithm:
    """An algorithm an `RsaKeyPair` signs with."""

@final
class VerificationAlgorithm:
    """An algorithm a `PublicKey` verifies with."""

@final
class RsaVerificationAlgorithm:
    """An RSA algorithm a `PublicKey` verifies with, which also loads a key from its components."""

@final
class PublicKey:
    """A public key that verifies signatures for one algorithm, whose `bytes` are its encoding: an uncompressed SEC1 point for ECDSA, 32 bytes for Ed25519, and a PKCS#1 `RSAPublicKey` for RSA."""

    def __new__(cls, algorithm: VerificationAlgorithm | RsaVerificationAlgorithm, data: Buffer) -> PublicKey:
        """Parses a public key for `algorithm` from its `bytes` encoding."""
    @staticmethod
    def from_spki(algorithm: VerificationAlgorithm | RsaVerificationAlgorithm, der: Buffer) -> PublicKey:
        """Parses a public key for `algorithm` from `SubjectPublicKeyInfo` DER, refusing one that names another algorithm or curve."""
    @staticmethod
    def from_components(algorithm: RsaVerificationAlgorithm, n: Buffer, e: Buffer) -> PublicKey:
        """Loads an RSA key for `algorithm` from its big-endian modulus `n` and exponent `e`, as a JWK carries them."""
    def verify(self, message: Buffer, signature: Buffer) -> None:
        """Checks `signature` over `message`; raises `BadSignature` if it does not verify."""
    def to_spki(self) -> bytes:
        """Encodes the key as `SubjectPublicKeyInfo` DER."""
    def __bytes__(self) -> bytes: ...

@final
class EcdsaKeyPair:
    """An ECDSA key pair, which signs with one algorithm."""

    @staticmethod
    def generate(algorithm: EcdsaSigningAlgorithm) -> EcdsaKeyPair:
        """Generates a key pair for `algorithm`."""
    @staticmethod
    def from_pkcs8(algorithm: EcdsaSigningAlgorithm, der: Buffer) -> EcdsaKeyPair:
        """Loads a key pair for `algorithm` from PKCS#8 DER."""
    @staticmethod
    def from_sec1(algorithm: EcdsaSigningAlgorithm, der: Buffer) -> EcdsaKeyPair:
        """Loads a key pair for `algorithm` from SEC1 `ECPrivateKey` DER."""
    @staticmethod
    def from_scalar_and_public_key(algorithm: EcdsaSigningAlgorithm, scalar: Buffer, public_key: Buffer) -> EcdsaKeyPair:
        """Loads a key pair for `algorithm` from its big-endian scalar and its uncompressed public key, as a JWK's `d`, `x`, and `y` carry them, refused unless they match."""
    def public_key(self) -> PublicKey:
        """The public key, which verifies with the verification algorithm of the same name."""
    def sign(self, message: Buffer) -> bytes:
        """Signs `message`."""
    def to_pkcs8(self) -> bytes:
        """Encodes the key pair as PKCS#8 DER."""
    def to_sec1(self) -> bytes:
        """Encodes the key pair as SEC1 `ECPrivateKey` DER."""
    def to_scalar(self) -> bytes:
        """Returns the private key's big-endian scalar."""
    def to_spki(self) -> bytes:
        """Encodes the public key as `SubjectPublicKeyInfo` DER."""

@final
class Ed25519KeyPair:
    """An Ed25519 key pair."""

    @staticmethod
    def generate() -> Ed25519KeyPair:
        """Generates a key pair."""
    @staticmethod
    def from_pkcs8(der: Buffer) -> Ed25519KeyPair:
        """Loads a key pair from PKCS#8 v1 or v2 DER, refused if a v2 key's public key does not match."""
    @staticmethod
    def from_seed(seed: Buffer) -> Ed25519KeyPair:
        """Loads a 32-byte seed, as a JWK's `d` holds it, deriving its public key."""
    @staticmethod
    def from_seed_and_public_key(seed: Buffer, public_key: Buffer) -> Ed25519KeyPair:
        """Loads a 32-byte seed, refused unless `public_key` is its public key."""
    def public_key(self) -> PublicKey:
        """The public key, which verifies with `verify.ED25519`."""
    def sign(self, message: Buffer) -> bytes:
        """Signs `message`."""
    def to_pkcs8(self) -> bytes:
        """Encodes the key pair as PKCS#8 v2 DER (RFC 5958), with its public key."""
    def to_pkcs8v1(self) -> bytes:
        """Encodes the private key as PKCS#8 v1 DER (RFC 8410), as OpenSSL writes it."""
    def to_seed(self) -> bytes:
        """Returns the private key's 32-byte seed."""
    def to_spki(self) -> bytes:
        """Encodes the public key as `SubjectPublicKeyInfo` DER."""

@final
class RsaKeyPair:
    """An RSA key pair, which signs with any RSA signing algorithm."""

    @staticmethod
    def generate(size: KeySize) -> RsaKeyPair:
        """Generates a key pair of `size`, releasing the GIL: about 30 milliseconds for 2048 bits, and seconds for the largest sizes."""
    @staticmethod
    def from_pkcs8(der: Buffer) -> RsaKeyPair:
        """Loads a PKCS#8 RSA private key."""
    @staticmethod
    def from_pkcs1(der: Buffer) -> RsaKeyPair:
        """Loads a PKCS#1 `RSAPrivateKey`."""
    def public_key(self, algorithm: RsaSigningAlgorithm) -> PublicKey:
        """The public key, which verifies what this key pair signs with `algorithm`."""
    def sign(self, algorithm: RsaSigningAlgorithm, message: Buffer) -> bytes:
        """Signs `message` with `algorithm`, releasing the GIL."""
    def to_pkcs8(self) -> bytes:
        """Encodes the private key as PKCS#8 DER."""
    def to_spki(self) -> bytes:
        """Encodes the public key as `SubjectPublicKeyInfo` DER."""

__all__ = ["EcdsaSigningAlgorithm", "RsaSigningAlgorithm", "VerificationAlgorithm", "RsaVerificationAlgorithm", "PublicKey", "EcdsaKeyPair", "Ed25519KeyPair", "RsaKeyPair", "sign", "verify"]
