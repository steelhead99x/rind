"""RSA signatures, and RSA-OAEP encryption with SHA-256, SHA-384, or SHA-512, and SHA-1 under `rsa.legacy`.

A `KeyPair` signs with an `rsa.sign` algorithm, and a `PublicKey`, bound to no algorithm, verifies with any `rsa.verify` algorithm whose modulus floor it meets.
"""

from typing import ClassVar, final

from typing_extensions import Buffer

from pyrind.rsa import legacy as legacy
from pyrind.rsa import sign as sign
from pyrind.rsa import verify as verify

@final
class KeySize:
    """An RSA modulus size for key generation."""

    RSA_2048: ClassVar[KeySize]
    RSA_3072: ClassVar[KeySize]
    RSA_4096: ClassVar[KeySize]
    RSA_6144: ClassVar[KeySize]
    RSA_8192: ClassVar[KeySize]

@final
class SigningAlgorithm:
    """An algorithm a `KeyPair` signs with."""

@final
class VerificationAlgorithm:
    """An algorithm a `PublicKey` verifies with, each with its own floor on the modulus."""

@final
class PublicKey:
    """An RSA public key of 1024 to 8192 bits, bound to no algorithm, whose `bytes` are its PKCS#1 `RSAPublicKey`."""

    def __new__(cls, der: Buffer) -> PublicKey:
        """Parses a PKCS#1 `RSAPublicKey`."""
    @staticmethod
    def from_spki(der: Buffer) -> PublicKey:
        """Parses `SubjectPublicKeyInfo` DER."""
    @staticmethod
    def from_components(n: Buffer, e: Buffer) -> PublicKey:
        """Loads a key from its big-endian modulus `n` and exponent `e`, as a JWK carries them."""
    def verify(self, algorithm: VerificationAlgorithm, message: Buffer, signature: Buffer) -> None:
        """Checks `signature` over `message` with `algorithm`; raises `KeyRejected` if the modulus is below the algorithm's floor, before reading the signature, and `BadSignature` if it does not verify."""
    def modulus_len(self) -> int:
        """The modulus's length in bytes."""
    def to_spki(self) -> bytes:
        """Encodes the key as `SubjectPublicKeyInfo` DER."""
    def __bytes__(self) -> bytes: ...

@final
class KeyPair:
    """An RSA key pair, which signs with any RSA signing algorithm."""

    @staticmethod
    def generate(size: KeySize) -> KeyPair:
        """Generates a key pair of `size`, releasing the GIL: about 30 milliseconds for 2048 bits, and seconds for the largest sizes."""
    @staticmethod
    def from_pkcs8(der: Buffer) -> KeyPair:
        """Loads a PKCS#8 RSA private key."""
    @staticmethod
    def from_pkcs1(der: Buffer) -> KeyPair:
        """Loads a PKCS#1 `RSAPrivateKey`."""
    def public_key(self) -> PublicKey:
        """The public key, the same object each call, which verifies what this key pair signs with the verification algorithm of the same name."""
    def sign(self, algorithm: SigningAlgorithm, message: Buffer) -> bytes:
        """Signs `message` with `algorithm`, releasing the GIL."""
    def to_pkcs8(self) -> bytes:
        """Encodes the private key as PKCS#8 DER."""

@final
class OaepAlgorithm:
    """An RSA-OAEP algorithm."""

OAEP_SHA256: OaepAlgorithm
OAEP_SHA384: OaepAlgorithm
OAEP_SHA512: OaepAlgorithm

@final
class DecryptingKey:
    """An RSA-OAEP private key, which decrypts."""

    @staticmethod
    def generate(algorithm: OaepAlgorithm, size: KeySize) -> DecryptingKey:
        """Generates a key of `size` for `algorithm`, releasing the GIL: about 30 milliseconds for 2048 bits, and seconds for the largest sizes."""
    @staticmethod
    def from_pkcs8(algorithm: OaepAlgorithm, der: Buffer) -> DecryptingKey:
        """Loads a PKCS#8 RSA private key for `algorithm`."""
    @staticmethod
    def from_pkcs1(algorithm: OaepAlgorithm, der: Buffer) -> DecryptingKey:
        """Loads a PKCS#1 `RSAPrivateKey` for `algorithm`."""
    def public_key(self) -> EncryptingKey:
        """The public key, the same object each call, which encrypts to this key with its algorithm."""
    def decrypt(self, ciphertext: Buffer, *, label: Buffer) -> bytes:
        """Decrypts `ciphertext`, encrypted with `label`, releasing the GIL; every malformed ciphertext raises the same `DecryptFailed`."""
    def to_pkcs8(self) -> bytes:
        """Encodes the private key as PKCS#8 DER."""

@final
class EncryptingKey:
    """An RSA-OAEP public key, which encrypts."""

    def __new__(cls, algorithm: OaepAlgorithm, der: Buffer) -> EncryptingKey:
        """Parses a PKCS#1 `RSAPublicKey` for `algorithm`."""
    @staticmethod
    def from_spki(algorithm: OaepAlgorithm, der: Buffer) -> EncryptingKey:
        """Parses `SubjectPublicKeyInfo` DER for `algorithm`."""
    @staticmethod
    def from_components(algorithm: OaepAlgorithm, n: Buffer, e: Buffer) -> EncryptingKey:
        """Loads a key for `algorithm` from its big-endian modulus `n` and exponent `e`, as a JWK carries them."""
    def encrypt(self, message: Buffer, *, label: Buffer) -> bytes:
        """Encrypts `message` with `label`, returning a ciphertext as long as the modulus; raises `WrongLength` past `max_message_len`."""
    @property
    def max_message_len(self) -> int:
        """The longest message this key encrypts."""
    def to_spki(self) -> bytes:
        """Encodes the key as `SubjectPublicKeyInfo` DER."""

__all__ = ["KeySize", "SigningAlgorithm", "VerificationAlgorithm", "PublicKey", "KeyPair", "OaepAlgorithm", "DecryptingKey", "EncryptingKey", "OAEP_SHA256", "OAEP_SHA384", "OAEP_SHA512", "legacy", "sign", "verify"]
