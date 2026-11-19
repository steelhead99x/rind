"""Algorithms a public key verifies with, for moduli of 2048 to 8192 bits."""

from pyrind.rsa import VerificationAlgorithm
from pyrind.rsa.verify import legacy as legacy

PKCS1_SHA256: VerificationAlgorithm
PKCS1_SHA384: VerificationAlgorithm
PKCS1_SHA512: VerificationAlgorithm
PSS_SHA256: VerificationAlgorithm
PSS_SHA256_ANY_SALT: VerificationAlgorithm
PSS_SHA384: VerificationAlgorithm
PSS_SHA384_ANY_SALT: VerificationAlgorithm
PSS_SHA512: VerificationAlgorithm
PSS_SHA512_ANY_SALT: VerificationAlgorithm

__all__ = ["PKCS1_SHA256", "PKCS1_SHA384", "PKCS1_SHA512", "PSS_SHA256", "PSS_SHA256_ANY_SALT", "PSS_SHA384", "PSS_SHA384_ANY_SALT", "PSS_SHA512", "PSS_SHA512_ANY_SALT", "legacy"]
