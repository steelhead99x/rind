"""RSA algorithms with another modulus floor, or SHA-1, for old keys and signatures."""

from pyrind.signature import RsaVerificationAlgorithm

RSA_PKCS1_1024_SHA1: RsaVerificationAlgorithm
RSA_PKCS1_1024_SHA256: RsaVerificationAlgorithm
RSA_PKCS1_1024_SHA512: RsaVerificationAlgorithm
RSA_PKCS1_3072_SHA384: RsaVerificationAlgorithm
RSA_PKCS1_SHA1: RsaVerificationAlgorithm

__all__ = ["RSA_PKCS1_1024_SHA1", "RSA_PKCS1_1024_SHA256", "RSA_PKCS1_1024_SHA512", "RSA_PKCS1_3072_SHA384", "RSA_PKCS1_SHA1"]
