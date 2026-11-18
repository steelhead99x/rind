"""AES key wrap (RFC 3394) and with padding (RFC 5649), on rind's."""

import pyrind
from pyrind import key_wrap as _key_wrap

from pyrind_cryptography.hazmat.primitives import _keys

_SIZES = {16: _key_wrap.AES_128, 24: _key_wrap.AES_192, 32: _key_wrap.AES_256}


class InvalidUnwrap(Exception):
    """A wrapped key did not unwrap."""


def _kek(wrapping_key):
    _keys.check_bytes("wrapping_key", wrapping_key)
    size = _SIZES.get(len(memoryview(wrapping_key).cast("B")))
    if size is None:
        raise ValueError("The wrapping key must be a valid AES key length")
    return _key_wrap.AesKek(size, wrapping_key)


def aes_key_wrap(wrapping_key, key_to_wrap, backend=None):
    """Wraps `key_to_wrap`, a multiple of 8 bytes from 16, under `wrapping_key`."""
    kek = _kek(wrapping_key)
    if len(key_to_wrap) < 16:
        raise ValueError("The key to wrap must be at least 16 bytes")
    if len(key_to_wrap) % 8 != 0:
        raise ValueError("The key to wrap must be a multiple of 8 bytes")
    return kek.wrap(key_to_wrap)


def aes_key_unwrap(wrapping_key, wrapped_key, backend=None):
    """Unwraps `wrapped_key` under `wrapping_key`; raises `InvalidUnwrap` unless it wrapped it."""
    if len(wrapped_key) < 24:
        raise InvalidUnwrap("Must be at least 24 bytes")
    if len(wrapped_key) % 8 != 0:
        raise InvalidUnwrap("The wrapped key must be a multiple of 8 bytes")
    kek = _kek(wrapping_key)
    try:
        return kek.unwrap(wrapped_key)
    except pyrind.DecryptFailed:
        raise InvalidUnwrap from None


def aes_key_wrap_with_padding(wrapping_key, key_to_wrap, backend=None):
    """Wraps `key_to_wrap`, of any length, under `wrapping_key` with RFC 5649's padding."""
    kek = _kek(wrapping_key)
    try:
        return kek.wrap_padded(key_to_wrap)
    except pyrind.WrongLength:
        raise ValueError("The key to wrap must be at least 1 byte") from None


def aes_key_unwrap_with_padding(wrapping_key, wrapped_key, backend=None):
    """Unwraps a key wrapped with RFC 5649's padding; raises `InvalidUnwrap` unless `wrapping_key` wrapped it."""
    if len(wrapped_key) < 16:
        raise InvalidUnwrap("Must be at least 16 bytes")
    kek = _kek(wrapping_key)
    try:
        return kek.unwrap_padded(wrapped_key)
    except pyrind.DecryptFailed:
        raise InvalidUnwrap from None


__all__ = ["InvalidUnwrap", "aes_key_unwrap", "aes_key_unwrap_with_padding", "aes_key_wrap", "aes_key_wrap_with_padding"]
