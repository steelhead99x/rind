"""Algorithms with another modulus floor, or SHA-1, for old keys and signatures."""

from pyrind.rsa import VerificationAlgorithm

PKCS1_1024_SHA1: VerificationAlgorithm
PKCS1_1024_SHA256: VerificationAlgorithm
PKCS1_1024_SHA512: VerificationAlgorithm
PKCS1_3072_SHA384: VerificationAlgorithm
PKCS1_SHA1: VerificationAlgorithm

__all__ = ["PKCS1_1024_SHA1", "PKCS1_1024_SHA256", "PKCS1_1024_SHA512", "PKCS1_3072_SHA384", "PKCS1_SHA1"]
