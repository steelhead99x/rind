"""Algorithms a key pair signs with; each signs as the `verify` algorithm of the same name verifies."""

from pyrind.rsa import SigningAlgorithm

PKCS1_SHA256: SigningAlgorithm
PKCS1_SHA384: SigningAlgorithm
PKCS1_SHA512: SigningAlgorithm
PSS_SHA256: SigningAlgorithm
PSS_SHA384: SigningAlgorithm
PSS_SHA512: SigningAlgorithm

__all__ = ["PKCS1_SHA256", "PKCS1_SHA384", "PKCS1_SHA512", "PSS_SHA256", "PSS_SHA384", "PSS_SHA512"]
