"""Algorithms a key pair signs with; each signs as the `verify` algorithm of the same name verifies."""

from pyrind.signature import EcdsaSigningAlgorithm, RsaSigningAlgorithm

ECDSA_P256_SHA256_ASN1: EcdsaSigningAlgorithm
ECDSA_P256_SHA256_FIXED: EcdsaSigningAlgorithm
ECDSA_P384_SHA384_ASN1: EcdsaSigningAlgorithm
ECDSA_P384_SHA384_FIXED: EcdsaSigningAlgorithm
ECDSA_P521_SHA512_ASN1: EcdsaSigningAlgorithm
ECDSA_P521_SHA512_FIXED: EcdsaSigningAlgorithm
RSA_PKCS1_SHA256: RsaSigningAlgorithm
RSA_PKCS1_SHA384: RsaSigningAlgorithm
RSA_PKCS1_SHA512: RsaSigningAlgorithm
RSA_PSS_SHA256: RsaSigningAlgorithm
RSA_PSS_SHA384: RsaSigningAlgorithm
RSA_PSS_SHA512: RsaSigningAlgorithm

__all__ = ["ECDSA_P256_SHA256_ASN1", "ECDSA_P256_SHA256_FIXED", "ECDSA_P384_SHA384_ASN1", "ECDSA_P384_SHA384_FIXED", "ECDSA_P521_SHA512_ASN1", "ECDSA_P521_SHA512_FIXED", "RSA_PKCS1_SHA256", "RSA_PKCS1_SHA384", "RSA_PKCS1_SHA512", "RSA_PSS_SHA256", "RSA_PSS_SHA384", "RSA_PSS_SHA512"]
