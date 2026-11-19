"""Algorithms a public key verifies with."""

from pyrind.ecdsa import VerificationAlgorithm

P256_SHA256_ASN1: VerificationAlgorithm
P256_SHA256_FIXED: VerificationAlgorithm
P256_SHA384_ASN1: VerificationAlgorithm
P256_SHA512_ASN1: VerificationAlgorithm
P384_SHA256_ASN1: VerificationAlgorithm
P384_SHA384_ASN1: VerificationAlgorithm
P384_SHA384_FIXED: VerificationAlgorithm
P384_SHA512_ASN1: VerificationAlgorithm
P521_SHA256_ASN1: VerificationAlgorithm
P521_SHA384_ASN1: VerificationAlgorithm
P521_SHA512_ASN1: VerificationAlgorithm
P521_SHA512_FIXED: VerificationAlgorithm

__all__ = ["P256_SHA256_ASN1", "P256_SHA256_FIXED", "P256_SHA384_ASN1", "P256_SHA512_ASN1", "P384_SHA256_ASN1", "P384_SHA384_ASN1", "P384_SHA384_FIXED", "P384_SHA512_ASN1", "P521_SHA256_ASN1", "P521_SHA384_ASN1", "P521_SHA512_ASN1", "P521_SHA512_FIXED"]
