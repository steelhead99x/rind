"""RSA encryption: RSA-OAEP with SHA-256, SHA-384, or SHA-512, and SHA-1 under `rsa.legacy`.

RSA signatures are under `pyrind.signature`, which takes this module's `KeySize` too.
"""

from typing import ClassVar, final

from typing_extensions import Buffer

from pyrind.rsa import legacy as legacy

@final
class KeySize:
    """An RSA modulus size for key generation."""

    RSA_2048: ClassVar[KeySize]
    RSA_3072: ClassVar[KeySize]
    RSA_4096: ClassVar[KeySize]
    RSA_6144: ClassVar[KeySize]
    RSA_8192: ClassVar[KeySize]

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
        """The public key, which encrypts to this key with its algorithm."""
    def decrypt(self, ciphertext: Buffer, *, label: Buffer) -> bytes:
        """Decrypts `ciphertext`, encrypted with `label`, releasing the GIL; every malformed ciphertext raises the same `DecryptFailed`."""
    def to_pkcs8(self) -> bytes:
        """Encodes the private key as PKCS#8 DER."""
    def to_spki(self) -> bytes:
        """Encodes the public key as `SubjectPublicKeyInfo` DER."""

@final
class EncryptingKey:
    """An RSA-OAEP public key, which encrypts."""

    def __new__(cls, algorithm: OaepAlgorithm, der: Buffer) -> EncryptingKey:
        """Parses a PKCS#1 `RSAPublicKey` or a `SubjectPublicKeyInfo` for `algorithm`."""
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

__all__ = ["KeySize", "OaepAlgorithm", "DecryptingKey", "EncryptingKey", "OAEP_SHA256", "OAEP_SHA384", "OAEP_SHA512", "legacy"]
