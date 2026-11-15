"""Wycheproof's vectors through pyrind, so that every malformed input raises a
`pyrind.Error` rather than crashing, and every valid one passes.

rind runs the full suites itself; these check the binding's mapping of inputs
and errors. A vector Wycheproof calls acceptable may go either way.
"""

import json
import pathlib
import unittest

import pyrind
from pyrind import aead, agreement, cipher, hkdf, hmac, kem, key_wrap, rsa, signature
from pyrind.signature import verify

VECTORS = pathlib.Path(__file__).resolve().parents[2] / "thirdparty" / "vectors" / "wycheproof" / "testvectors_v1"


def groups(name):
    path = VECTORS / f"{name}_test.json"
    if not path.exists():
        raise FileNotFoundError(f"{path} is missing; run: admin/sync-vectors")
    return json.loads(path.read_text())["testGroups"]


class Wycheproof(unittest.TestCase):
    def run_vectors(self, name, check, select=lambda group: True):
        count = 0
        for group in groups(name):
            if not select(group):
                continue
            for test in group["tests"]:
                with self.subTest(file=name, tcId=test["tcId"]):
                    try:
                        check(group, test)
                    except pyrind.Error:
                        self.assertNotEqual(test["result"], "valid", test.get("comment"))
                    else:
                        self.assertNotEqual(test["result"], "invalid", test.get("comment"))
                count += 1
        self.assertGreater(count, 0)

    def test_aead(self):
        def check(algorithm):
            def run(group, test):
                key = aead.Key(algorithm[group["keySize"]], bytes.fromhex(test["key"]))
                nonce, aad = bytes.fromhex(test["iv"]), bytes.fromhex(test["aad"])
                msg = bytes.fromhex(test["msg"])
                sealed = bytes.fromhex(test["ct"] + test["tag"])
                self.assertEqual(key.open(nonce, sealed, aad=aad), msg)
                self.assertEqual(key.seal(nonce, msg, aad=aad), sealed)

            return run

        # rind takes only 96-bit nonces, which these files' other groups vary.
        def standard(group):
            return group["ivSize"] == 96 and group["tagSize"] == 128

        gcm = {128: aead.AES_128_GCM, 192: aead.AES_192_GCM, 256: aead.AES_256_GCM}
        self.run_vectors("aes_gcm", check(gcm), standard)
        self.run_vectors("chacha20_poly1305", check({256: aead.CHACHA20_POLY1305}), standard)

    def test_xchacha20_poly1305(self):
        def run(group, test):
            key = aead.RandomizedNonceKey(bytes.fromhex(test["key"]))
            sealed = bytes.fromhex(test["ct"] + test["tag"])
            opened = key.open(bytes.fromhex(test["iv"]), sealed, aad=bytes.fromhex(test["aad"]))
            self.assertEqual(opened, bytes.fromhex(test["msg"]))

        self.run_vectors("xchacha20_poly1305", run, lambda group: group["tagSize"] == 128)

    def test_aes_cbc(self):
        sizes = {128: cipher.AES_128, 192: cipher.AES_192, 256: cipher.AES_256}

        def run(group, test):
            size, key = sizes[group["keySize"]], bytes.fromhex(test["key"])
            iv, ct = bytes.fromhex(test["iv"]), bytes.fromhex(test["ct"])
            plain = cipher.AesCbcDecryptingKey(size, key).decrypt_blocks(iv, ct)
            self.assertEqual(cipher.AesCbcEncryptingKey(size, key).encrypt_blocks(iv, plain), ct)
            msg = bytes.fromhex(test["msg"])
            self.assertEqual(plain[: len(msg)], msg)

        # These blocks carry PKCS#7 padding, which the binding leaves to its
        # caller, so only the valid vectors say what the blocks decrypt to.
        count = 0
        for group in groups("aes_cbc_pkcs5"):
            for test in group["tests"]:
                if test["result"] == "valid":
                    with self.subTest(tcId=test["tcId"]):
                        run(group, test)
                    count += 1
        self.assertGreater(count, 0)

    def test_key_wrap(self):
        sizes = {128: key_wrap.AES_128, 192: key_wrap.AES_192, 256: key_wrap.AES_256}

        def check(padded):
            def run(group, test):
                kek = key_wrap.AesKek(sizes[group["keySize"]], bytes.fromhex(test["key"]))
                msg, ct = bytes.fromhex(test["msg"]), bytes.fromhex(test["ct"])
                self.assertEqual((kek.unwrap_padded if padded else kek.unwrap)(ct), msg)
                self.assertEqual((kek.wrap_padded if padded else kek.wrap)(msg), ct)

            return run

        self.run_vectors("aes_wrap", check(padded=False))
        self.run_vectors("aes_kwp", check(padded=True))

    def test_hmac(self):
        def run(group, test):
            key = hmac.Key(hmac.HMAC_SHA256, bytes.fromhex(test["key"]))
            hmac.verify(key, bytes.fromhex(test["msg"]), bytes.fromhex(test["tag"]))

        # rind verifies whole tags only.
        self.run_vectors("hmac_sha256", run, lambda group: group["tagSize"] == 256)

    def test_hkdf(self):
        def run(group, test):
            prk = hkdf.Salt(hkdf.HKDF_SHA256, bytes.fromhex(test["salt"])).extract(bytes.fromhex(test["ikm"]))
            self.assertEqual(prk.expand(bytes.fromhex(test["info"]), test["size"]), bytes.fromhex(test["okm"]))

        self.run_vectors("hkdf_sha256", run)

    def test_x25519(self):
        def run(group, test):
            key = agreement.PrivateKey.from_scalar(agreement.X25519, bytes.fromhex(test["private"]))
            self.assertEqual(key.agree(bytes.fromhex(test["public"])), bytes.fromhex(test["shared"]))

        self.run_vectors("x25519", run)

    def test_ecdh_p256(self):
        def run(group, test):
            key = agreement.PrivateKey.from_scalar(agreement.ECDH_P256, int(test["private"], 16).to_bytes(32, "big"))
            self.assertEqual(key.agree(bytes.fromhex(test["public"])), bytes.fromhex(test["shared"]))

        self.run_vectors("ecdh_secp256r1_ecpoint", run)

    def verify_vectors(self, name, algorithm, key_of):
        def run(group, test):
            public = key_of(group)
            public.verify(bytes.fromhex(test["msg"]), bytes.fromhex(test["sig"]))

        self.run_vectors(name, run)

    def test_ed25519(self):
        self.verify_vectors(
            "ed25519",
            verify.ED25519,
            lambda group: signature.PublicKey(verify.ED25519, bytes.fromhex(group["publicKey"]["pk"])),
        )

    def test_ecdsa_p256(self):
        algorithm = verify.ECDSA_P256_SHA256_ASN1
        self.verify_vectors(
            "ecdsa_secp256r1_sha256",
            algorithm,
            lambda group: signature.PublicKey.from_spki(algorithm, bytes.fromhex(group["publicKeyDer"])),
        )

    def test_rsa_pkcs1(self):
        algorithm = verify.RSA_PKCS1_SHA256
        self.verify_vectors(
            "rsa_signature_2048_sha256",
            algorithm,
            lambda group: signature.PublicKey.from_spki(algorithm, bytes.fromhex(group["publicKeyDer"])),
        )

    def test_rsa_pss(self):
        algorithm = verify.RSA_PSS_SHA256
        self.verify_vectors(
            "rsa_pss_2048_sha256_mgf1_32",
            algorithm,
            lambda group: signature.PublicKey.from_spki(algorithm, bytes.fromhex(group["publicKeyDer"])),
        )

    def test_rsa_oaep(self):
        def run(group, test):
            key = rsa.DecryptingKey.from_pkcs8(rsa.OAEP_SHA256, bytes.fromhex(group["privateKeyPkcs8"]))
            plaintext = key.decrypt(bytes.fromhex(test["ct"]), label=bytes.fromhex(test["label"]))
            self.assertEqual(plaintext, bytes.fromhex(test["msg"]))

        self.run_vectors("rsa_oaep_2048_sha256_mgf1sha256", run)

    def test_ml_kem_encapsulation_keys(self):
        def run(group, test):
            kem.EncapsulationKey(kem.ML_KEM_768, bytes.fromhex(test["ek"]))

        self.run_vectors("mlkem_768_encaps", run)


if __name__ == "__main__":
    unittest.main()
