from pyrind import aead as aead
from pyrind import agreement as agreement
from pyrind import cipher as cipher
from pyrind import cpu as cpu
from pyrind import digest as digest
from pyrind import hkdf as hkdf
from pyrind import hmac as hmac
from pyrind import kem as kem
from pyrind import key_wrap as key_wrap
from pyrind import pbkdf2 as pbkdf2
from pyrind import rsa as rsa
from pyrind import signature as signature

class Error(Exception):
    """A rind call failed."""

class WrongLength(Error):
    """An input or output of fixed length, such as a key, a nonce, or a derived key, was another length."""

class KeyRejected(Error):
    """A private, public, or peer's key was refused; the message says why."""

class BadSignature(Error):
    """A signature, MAC tag, or PBKDF2 output did not verify."""

class DecryptFailed(Error):
    """An AEAD ciphertext, its tag, or its associated data did not authenticate, or an RSA-OAEP ciphertext did not decrypt."""

class RngFailed(Error):
    """The system random source failed."""

class Unsupported(Error):
    """A call was given an algorithm it does not take."""

class Fault(Error):
    """An internal consistency check failed, from a hardware fault or a rind bug."""

__all__ = ["Error", "WrongLength", "KeyRejected", "BadSignature", "DecryptFailed", "RngFailed", "Unsupported", "Fault", "aead", "agreement", "cipher", "cpu", "digest", "hkdf", "hmac", "kem", "key_wrap", "pbkdf2", "rsa", "signature"]
