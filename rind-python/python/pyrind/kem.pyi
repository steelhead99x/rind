"""Key encapsulation: ML-KEM-768."""

from typing import final

from typing_extensions import Buffer

@final
class Algorithm:
    """A key encapsulation mechanism."""

ML_KEM_768: Algorithm

@final
class DecapsulationKey:
    """The recipient's private key, which decapsulates."""

    @staticmethod
    def generate(algorithm: Algorithm) -> DecapsulationKey:
        """Generates a key for `algorithm`."""
    def public_key(self) -> EncapsulationKey:
        """The public key to send the sender."""
    def decapsulate(self, ciphertext: Buffer) -> bytes:
        """Recovers the shared secret from the sender's `ciphertext`."""

@final
class EncapsulationKey:
    """The recipient's public key, which encapsulates, and whose `bytes` are its encoding."""

    def __new__(cls, algorithm: Algorithm, data: Buffer) -> EncapsulationKey:
        """Parses a public key for `algorithm`."""
    def encapsulate(self) -> tuple[bytes, bytes]:
        """Encapsulates a fresh shared secret, returning the ciphertext to send the recipient and the secret."""
    def __bytes__(self) -> bytes: ...

__all__ = ["Algorithm", "DecapsulationKey", "EncapsulationKey", "ML_KEM_768"]
