"""pyrind's key encodings, context copies, and algorithm reprs, which round
trip and continue as the API documents."""

import os
import unittest

PYCA = os.environ.get("PYRIND_TEST_PYCA") != "0"
requires_pyca = unittest.skipUnless(PYCA, "pyca dependencies have no wheel for this target")
if PYCA:
    from cryptography.hazmat.primitives import serialization
    from cryptography.hazmat.primitives.asymmetric import ec

import pyrind
from pyrind import aead, agreement, digest, hmac, kem

ECDH = (
    (agreement.ECDH_P256, "ECDH_P256"),
    (agreement.ECDH_P384, "ECDH_P384"),
    (agreement.ECDH_P521, "ECDH_P521"),
)


class Agreement(unittest.TestCase):
    def test_keys_round_trip(self):
        for algorithm, _ in ECDH + ((agreement.X25519, "X25519"),):
            key = agreement.PrivateKey.generate(algorithm)
            again = agreement.PrivateKey.from_pkcs8(algorithm, key.to_pkcs8())
            self.assertEqual(again.to_scalar(), key.to_scalar())
            public = key.public_key()
            parsed = agreement.PublicKey.from_spki(algorithm, public.to_spki())
            self.assertEqual(bytes(parsed), bytes(public))

    @requires_pyca
    def test_sec1_keys_load(self):
        for (algorithm, _), curve in zip(ECDH, (ec.SECP256R1(), ec.SECP384R1(), ec.SECP521R1())):
            theirs = ec.generate_private_key(curve)
            der = theirs.private_bytes(
                serialization.Encoding.DER,
                serialization.PrivateFormat.TraditionalOpenSSL,
                serialization.NoEncryption(),
            )
            key = agreement.PrivateKey.from_sec1(algorithm, der)
            self.assertEqual(int.from_bytes(key.to_scalar(), "big"), theirs.private_numbers().private_value)
            with self.assertRaises(pyrind.KeyRejected):
                agreement.PrivateKey.from_sec1(algorithm, der[:-1])

    def test_reprs_name_the_constant(self):
        self.assertEqual(repr(agreement.X25519), "pyrind.agreement.X25519")
        for algorithm, name in ECDH:
            self.assertEqual(repr(algorithm), f"pyrind.agreement.{name}")
        self.assertEqual(repr(aead.AES_128_GCM), "pyrind.aead.AES_128_GCM")
        self.assertEqual(repr(digest.SHA256), "pyrind.digest.SHA256")
        self.assertEqual(repr(kem.ML_KEM_768), "pyrind.kem.ML_KEM_768")


class Kem(unittest.TestCase):
    def test_public_key_round_trips(self):
        key = kem.DecapsulationKey.generate(kem.ML_KEM_768)
        public = kem.EncapsulationKey(kem.ML_KEM_768, bytes(key.public_key()))
        ciphertext, secret = public.encapsulate()
        self.assertEqual(key.decapsulate(ciphertext), secret)


class Copies(unittest.TestCase):
    def test_digest_copy_continues(self):
        context = digest.Context(digest.SHA256)
        context.update(b"a")
        copy = context.copy()
        copy.update(b"b")
        self.assertEqual(copy.finish(), digest.digest(digest.SHA256, b"ab"))
        self.assertEqual(context.finish(), digest.digest(digest.SHA256, b"a"))

    def test_hmac_copy_continues(self):
        key = hmac.Key(hmac.HMAC_SHA256, b"key")
        context = hmac.Context(key)
        context.update(b"a")
        copy = context.copy()
        copy.update(b"b")
        self.assertEqual(copy.sign(), hmac.sign(key, b"ab"))
        self.assertEqual(context.sign(), hmac.sign(key, b"a"))
        with self.assertRaises(ValueError):
            context.copy()


if __name__ == "__main__":
    unittest.main()
