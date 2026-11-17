"""Algorithms a key pair signs with; each signs as the `verify` algorithm of the same name verifies."""

from pyrind.ecdsa import SigningAlgorithm

P256_SHA256_ASN1: SigningAlgorithm
P256_SHA256_FIXED: SigningAlgorithm
P384_SHA384_ASN1: SigningAlgorithm
P384_SHA384_FIXED: SigningAlgorithm
P521_SHA512_ASN1: SigningAlgorithm
P521_SHA512_FIXED: SigningAlgorithm

__all__ = ["P256_SHA256_ASN1", "P256_SHA256_FIXED", "P384_SHA384_ASN1", "P384_SHA384_FIXED", "P521_SHA512_ASN1", "P521_SHA512_FIXED"]
