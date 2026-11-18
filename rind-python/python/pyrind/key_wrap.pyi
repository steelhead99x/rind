"""Key wrapping with AES-KW (RFC 3394) and AES-KWP (RFC 5649), as JWE's `A128KW` and WebCrypto's `AES-KW` use it."""

from typing import final

from typing_extensions import Buffer

from pyrind.cipher import Algorithm

AES_128: Algorithm
AES_192: Algorithm
AES_256: Algorithm

@final
class AesKek:
    """An AES key-encryption key, which wraps keys with AES-KW (RFC 3394) and AES-KWP (RFC 5649)."""

    def __new__(cls, algorithm: Algorithm, key: Buffer) -> AesKek:
        """Expands `key` for `algorithm`; raises `WrongLength` unless it is that size."""
    def wrap(self, key: Buffer) -> bytes:
        """Wraps `key`, a multiple of 8 bytes from 16, with AES-KW; raises `WrongLength` for any other length."""
    def unwrap(self, wrapped: Buffer) -> bytes:
        """Unwraps an AES-KW `wrapped`; raises `DecryptFailed` unless this key wrapped it."""
    def wrap_padded(self, key: Buffer) -> bytes:
        """Wraps `key`, of any length from 1 byte, with AES-KWP."""
    def unwrap_padded(self, wrapped: Buffer) -> bytes:
        """Unwraps an AES-KWP `wrapped`; raises `DecryptFailed` unless this key wrapped it."""

__all__ = ["AesKek", "AES_128", "AES_192", "AES_256"]
