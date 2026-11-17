"""Key wrapping with AES-KW (RFC 3394) and AES-KWP (RFC 5649), as JWE's `A128KW` and WebCrypto's `AES-KW` use it."""

from typing import ClassVar, final

from typing_extensions import Buffer

from pyrind.cipher import Algorithm

AES_128: Algorithm
AES_192: Algorithm
AES_256: Algorithm

@final
class Mode:
    """A key-wrap mode: AES-KW (RFC 3394), for keys a multiple of 8 bytes from 16, or AES-KWP (RFC 5649), for keys of any length from 1 byte."""

    KW: ClassVar[Mode]
    KWP: ClassVar[Mode]

@final
class AesKek:
    """An AES key-encryption key, which wraps keys with AES-KW (RFC 3394) and AES-KWP (RFC 5649)."""

    def __new__(cls, algorithm: Algorithm, key: Buffer) -> AesKek:
        """Expands `key` for `algorithm`; raises `WrongLength` unless it is that size."""
    def wrap_key(self, mode: Mode, key: Buffer) -> bytes:
        """Wraps `key` with `mode`; raises `WrongLength` for a length the mode does not take."""
    def unwrap_key(self, mode: Mode, wrapped: Buffer) -> bytes:
        """Unwraps `wrapped` with `mode`; raises `DecryptFailed` unless this key wrapped it in that mode."""

__all__ = ["AesKek", "Mode", "AES_128", "AES_192", "AES_256"]
