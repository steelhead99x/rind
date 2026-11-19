"""rind's cryptography for Python.

Each rind module is a submodule: `pyrind.aead`, `pyrind.agreement`,
`pyrind.cipher`, `pyrind.cpu`, `pyrind.digest`, `pyrind.hkdf`,
`pyrind.hmac`, `pyrind.kem`, `pyrind.key_wrap`, `pyrind.pbkdf2`,
`pyrind.rsa`, and `pyrind.signature`. Every failure raises
a subclass of `pyrind.Error`.
"""

from pyrind._rind import (
    BadSignature,
    DecryptFailed,
    Error,
    Fault,
    KeyRejected,
    RngFailed,
    Unsupported,
    WrongLength,
    aead,
    agreement,
    cipher,
    cpu,
    digest,
    hkdf,
    hmac,
    kem,
    key_wrap,
    pbkdf2,
    rsa,
    signature,
)

__all__ = [
    "BadSignature",
    "DecryptFailed",
    "Error",
    "Fault",
    "KeyRejected",
    "RngFailed",
    "Unsupported",
    "WrongLength",
    "aead",
    "agreement",
    "cipher",
    "cpu",
    "digest",
    "hkdf",
    "hmac",
    "kem",
    "key_wrap",
    "pbkdf2",
    "rsa",
    "signature",
]
