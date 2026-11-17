"""rind's cryptography for Python.

Each rind module is a submodule: `pyrind.aead`, `pyrind.agreement`,
`pyrind.cipher`, `pyrind.cpu`, `pyrind.digest`, `pyrind.ecdsa`,
`pyrind.ed25519`, `pyrind.hkdf`, `pyrind.hmac`, `pyrind.kem`,
`pyrind.key_wrap`, `pyrind.pbkdf2`, and `pyrind.rsa`. Every failure raises
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
    ecdsa,
    ed25519,
    hkdf,
    hmac,
    kem,
    key_wrap,
    pbkdf2,
    rsa,
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
    "ecdsa",
    "ed25519",
    "hkdf",
    "hmac",
    "kem",
    "key_wrap",
    "pbkdf2",
    "rsa",
]
