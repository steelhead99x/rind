"""Algorithms a public key verifies with; RSA algorithms accept moduli of 2048 to 8192 bits."""

from pyrind.signature import RsaVerificationAlgorithm, VerificationAlgorithm
from pyrind.signature.verify import legacy as legacy

ECDSA_P256_SHA256_ASN1: VerificationAlgorithm
ECDSA_P256_SHA256_FIXED: VerificationAlgorithm
ECDSA_P256_SHA384_ASN1: VerificationAlgorithm
ECDSA_P256_SHA512_ASN1: VerificationAlgorithm
ECDSA_P384_SHA256_ASN1: VerificationAlgorithm
ECDSA_P384_SHA384_ASN1: VerificationAlgorithm
ECDSA_P384_SHA384_FIXED: VerificationAlgorithm
ECDSA_P384_SHA512_ASN1: VerificationAlgorithm
ECDSA_P521_SHA256_ASN1: VerificationAlgorithm
ECDSA_P521_SHA384_ASN1: VerificationAlgorithm
ECDSA_P521_SHA512_ASN1: VerificationAlgorithm
ECDSA_P521_SHA512_FIXED: VerificationAlgorithm
ED25519: VerificationAlgorithm
RSA_PKCS1_SHA256: RsaVerificationAlgorithm
RSA_PKCS1_SHA384: RsaVerificationAlgorithm
RSA_PKCS1_SHA512: RsaVerificationAlgorithm
RSA_PSS_SHA256: RsaVerificationAlgorithm
RSA_PSS_SHA256_ANY_SALT: RsaVerificationAlgorithm
RSA_PSS_SHA384: RsaVerificationAlgorithm
RSA_PSS_SHA384_ANY_SALT: RsaVerificationAlgorithm
RSA_PSS_SHA512: RsaVerificationAlgorithm
RSA_PSS_SHA512_ANY_SALT: RsaVerificationAlgorithm

__all__ = ["ECDSA_P256_SHA256_ASN1", "ECDSA_P256_SHA256_FIXED", "ECDSA_P256_SHA384_ASN1", "ECDSA_P256_SHA512_ASN1", "ECDSA_P384_SHA256_ASN1", "ECDSA_P384_SHA384_ASN1", "ECDSA_P384_SHA384_FIXED", "ECDSA_P384_SHA512_ASN1", "ECDSA_P521_SHA256_ASN1", "ECDSA_P521_SHA384_ASN1", "ECDSA_P521_SHA512_ASN1", "ECDSA_P521_SHA512_FIXED", "ED25519", "RSA_PKCS1_SHA256", "RSA_PKCS1_SHA384", "RSA_PKCS1_SHA512", "RSA_PSS_SHA256", "RSA_PSS_SHA256_ANY_SALT", "RSA_PSS_SHA384", "RSA_PSS_SHA384_ANY_SALT", "RSA_PSS_SHA512", "RSA_PSS_SHA512_ANY_SALT", "legacy"]
