"""pyrind's API, checked against known answers and against pyca/cryptography,
hashlib, and hmac."""

import array
import hashlib
import hmac as std_hmac
import os
import sys
import threading
import unittest

# Wheel CI explicitly opts out where pyca's dependencies have no wheel.
PYCA = os.environ.get("PYRIND_TEST_PYCA") != "0"
requires_pyca = unittest.skipUnless(PYCA, "pyca dependencies have no wheel for this target")
if PYCA:
    from cryptography.hazmat.primitives import hashes, keywrap, serialization
    from cryptography.hazmat.primitives.asymmetric import ec, ed25519, mlkem, padding
    from cryptography.hazmat.primitives.asymmetric import rsa as pyca_rsa
    from cryptography.hazmat.primitives.asymmetric import x25519
    from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
    from cryptography.hazmat.primitives.ciphers import aead as pyca_aead
    from cryptography.hazmat.primitives.kdf.hkdf import HKDF
    from cryptography.hazmat.primitives.kdf.pbkdf2 import PBKDF2HMAC

import pyrind
from pyrind import aead, agreement, cipher, cpu, digest, ecdsa, ed25519 as rind_ed25519, hkdf, hmac, kem, key_wrap, pbkdf2, rsa


def der(tag, contents):
    """One DER element."""
    if len(contents) < 0x80:
        return bytes([tag, len(contents)]) + contents
    length = len(contents).to_bytes((len(contents).bit_length() + 7) // 8, "big")
    return bytes([tag, 0x80 | len(length)]) + length + contents


def der_integer(value):
    """A non-negative DER INTEGER."""
    return der(0x02, value.to_bytes(value.bit_length() // 8 + 1, "big"))


class Package(unittest.TestCase):
    def test_submodules_import(self):
        import pyrind.digest.legacy
        import pyrind.ecdsa.sign
        import pyrind.ecdsa.verify
        import pyrind.rsa.sign
        import pyrind.rsa.verify.legacy

        self.assertIs(pyrind.rsa.verify.legacy, rsa.verify.legacy)
        self.assertIs(pyrind.ecdsa.sign, ecdsa.sign)
        self.assertIs(pyrind.rsa.sign, rsa.sign)
        self.assertFalse(hasattr(pyrind, "signature"))
        self.assertIs(pyrind.digest.legacy.SHA1, digest.legacy.SHA1)

    def test_constants_name_themselves(self):
        self.assertEqual(repr(aead.AES_128_GCM), "pyrind.aead.AES_128_GCM")
        self.assertEqual(repr(rsa.verify.legacy.PKCS1_SHA1), "pyrind.rsa.verify.legacy.PKCS1_SHA1")
        self.assertEqual(repr(ecdsa.sign.P256_SHA256_ASN1), "pyrind.ecdsa.sign.P256_SHA256_ASN1")
        self.assertEqual(repr(key_wrap.Mode.KWP), "Mode.KWP")
        # Enum constants hash, so they key a dict or fill a set.
        self.assertEqual(len({key_wrap.Mode.KW, key_wrap.Mode.KWP, key_wrap.Mode.KW}), 2)
        self.assertEqual(len({rsa.KeySize.RSA_2048, rsa.KeySize.RSA_2048}), 1)
        # They equal no int, as an int that equalled one would hash apart
        # from it, but still convert to the int of their position.
        for constant, value in ((key_wrap.Mode.KW, 0), (key_wrap.Mode.KWP, 1), (rsa.KeySize.RSA_2048, 0)):
            self.assertNotEqual(constant, value)
            self.assertNotIn(constant, {value})
            self.assertEqual(int(constant), value)
        self.assertEqual(aead.Key.__module__, "pyrind.aead")
        for cls, module in (
            (ecdsa.KeyPair, "pyrind.ecdsa"),
            (ecdsa.PublicKey, "pyrind.ecdsa"),
            (rind_ed25519.KeyPair, "pyrind.ed25519"),
            (rind_ed25519.PublicKey, "pyrind.ed25519"),
            (rsa.KeyPair, "pyrind.rsa"),
            (rsa.PublicKey, "pyrind.rsa"),
            (key_wrap.Mode, "pyrind.key_wrap"),
        ):
            self.assertEqual(cls.__module__, module)

    def test_errors_share_a_base(self):
        for error in (
            pyrind.WrongLength,
            pyrind.KeyRejected,
            pyrind.BadSignature,
            pyrind.DecryptFailed,
            pyrind.RngFailed,
            pyrind.Unsupported,
            pyrind.Fault,
        ):
            self.assertTrue(issubclass(error, pyrind.Error))

    def test_algorithms_are_not_constructible(self):
        with self.assertRaises(TypeError):
            aead.Algorithm()

    def test_another_modules_algorithm_is_a_type_error(self):
        with self.assertRaises(TypeError):
            aead.Key(digest.SHA256, bytes(16))
        rsa_key = rsa.KeyPair.generate(rsa.KeySize.RSA_2048)
        for call in (
            lambda: ecdsa.KeyPair.generate(ecdsa.verify.P256_SHA256_ASN1),
            lambda: ecdsa.PublicKey(ecdsa.sign.P256_SHA256_ASN1, bytes(65)),
            lambda: rsa_key.sign(rsa.verify.PKCS1_SHA256, b"m"),
            lambda: rsa_key.public_key().verify(ecdsa.verify.P256_SHA256_ASN1, b"", b""),
            lambda: rsa_key.public_key().verify(rsa.sign.PKCS1_SHA256, b"", b""),
            lambda: key_wrap.AesKek(key_wrap.AES_128, bytes(16)).wrap_key(rsa.KeySize.RSA_2048, bytes(16)),
        ):
            with self.assertRaises(TypeError):
                call()

    def test_keys_do_not_pickle(self):
        import pickle

        with self.assertRaises(TypeError):
            pickle.dumps(aead.Key(aead.AES_128_GCM, bytes(16)))

    def test_cpu(self):
        self.assertIsInstance(cpu.has_aes_hardware(), bool)


class BytesLike(unittest.TestCase):
    def test_any_buffer_is_accepted(self):
        expected = hashlib.sha256(b"abc").digest()
        for data in (b"abc", bytearray(b"abc"), memoryview(b"xabcx")[1:4]):
            self.assertEqual(digest.digest(digest.SHA256, data), expected)

    def test_str_is_refused(self):
        with self.assertRaises(TypeError):
            digest.digest(digest.SHA256, "abc")

    def test_strided_buffer_is_copied(self):
        expected = hashlib.sha256(b"ace").digest()
        self.assertEqual(digest.digest(digest.SHA256, memoryview(b"abcdef")[::2]), expected)

    def test_any_item_format_is_its_raw_bytes(self):
        strided = memoryview(bytearray(range(8))).cast("I")[::2]
        for data in (memoryview(b"abc").cast("b"), array.array("H", [1, 2]), strided):
            self.assertEqual(digest.digest(digest.SHA256, data), hashlib.sha256(bytes(data)).digest())
        self.assertEqual(digest.digest(digest.SHA256, bytearray()), hashlib.sha256(b"").digest())


class Digest(unittest.TestCase):
    ALGORITHMS = {
        "sha256": digest.SHA256,
        "sha384": digest.SHA384,
        "sha512": digest.SHA512,
        "sha512_256": digest.SHA512_256,
        "sha3_256": digest.SHA3_256,
        "sha3_384": digest.SHA3_384,
        "sha3_512": digest.SHA3_512,
        "md5": digest.legacy.MD5,
        "sha1": digest.legacy.SHA1,
    }

    def test_matches_hashlib(self):
        for name, algorithm in self.ALGORITHMS.items():
            for length in (0, 1, 55, 56, 64, 127, 128, 200, 1000):
                data = os.urandom(length)
                expected = hashlib.new(name, data).digest()
                self.assertEqual(digest.digest(algorithm, data), expected, name)
                self.assertEqual(algorithm.output_len, len(expected))

    def test_context_finishes_and_restarts(self):
        context = digest.Context(digest.SHA256)
        context.update(b"hello, ")
        context.update(b"world")
        self.assertEqual(context.finish(), hashlib.sha256(b"hello, world").digest())
        self.assertEqual(context.finish(), hashlib.sha256(b"").digest())

    def test_copy_continues_independently(self):
        context = digest.Context(digest.SHA256)
        context.update(b"hello, ")
        copy = context.copy()
        copy.update(b"world")
        context.update(b"there")
        self.assertEqual(copy.finish(), hashlib.sha256(b"hello, world").digest())
        self.assertEqual(context.finish(), hashlib.sha256(b"hello, there").digest())


class Hmac(unittest.TestCase):
    def test_rfc4231_case_2(self):
        key = hmac.Key(hmac.HMAC_SHA256, b"Jefe")
        tag = hmac.sign(key, b"what do ya want for nothing?")
        self.assertEqual(tag.hex(), "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843")
        hmac.verify(key, b"what do ya want for nothing?", tag)

    def test_matches_stdlib(self):
        for algorithm, name in (
            (hmac.HMAC_SHA256, "sha256"),
            (hmac.HMAC_SHA384, "sha384"),
            (hmac.HMAC_SHA512, "sha512"),
            (hmac.legacy.HMAC_SHA1, "sha1"),
        ):
            for key_len in (0, 16, 64, 200):
                raw = os.urandom(key_len)
                data = os.urandom(100)
                expected = std_hmac.digest(raw, data, name)
                self.assertEqual(hmac.sign(hmac.Key(algorithm, raw), data), expected)
                self.assertEqual(algorithm.tag_len, len(expected))

    def test_verify_refuses_wrong_and_truncated_tags(self):
        key = hmac.Key(hmac.HMAC_SHA256, b"key")
        tag = hmac.sign(key, b"data")
        with self.assertRaises(pyrind.BadSignature):
            hmac.verify(key, b"data", tag[:16])
        with self.assertRaises(pyrind.BadSignature):
            hmac.verify(key, b"Data", tag)

    def test_context_signs_once(self):
        key = hmac.Key(hmac.HMAC_SHA256, b"key")
        context = hmac.Context(key)
        context.update(b"da")
        context.update(b"ta")
        self.assertEqual(context.sign(), hmac.sign(key, b"data"))
        with self.assertRaises(ValueError):
            context.sign()
        with self.assertRaises(ValueError):
            context.update(b"more")

    def test_copy_continues_independently(self):
        key = hmac.Key(hmac.HMAC_SHA256, b"key")
        context = hmac.Context(key)
        context.update(b"da")
        copy = context.copy()
        copy.update(b"ta")
        context.update(b"te")
        self.assertEqual(copy.sign(), hmac.sign(key, b"data"))
        self.assertEqual(context.sign(), hmac.sign(key, b"date"))
        with self.assertRaises(ValueError):
            context.copy()


class Hkdf(unittest.TestCase):
    def test_rfc5869_case_1(self):
        prk = hkdf.Salt(hkdf.HKDF_SHA256, bytes.fromhex("000102030405060708090a0b0c")).extract(b"\x0b" * 22)
        okm = prk.expand(bytes.fromhex("f0f1f2f3f4f5f6f7f8f9"), 42)
        self.assertEqual(
            okm.hex(),
            "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865",
        )

    @requires_pyca
    def test_matches_pyca(self):
        salt, secret, info = os.urandom(16), os.urandom(32), os.urandom(10)
        expected = HKDF(hashes.SHA384(), 100, salt, info).derive(secret)
        self.assertEqual(hkdf.Salt(hkdf.HKDF_SHA384, salt).extract(secret).expand(info, 100), expected)

    def test_expands_into_keys(self):
        prk = hkdf.Salt(hkdf.HKDF_SHA256, b"salt").extract(b"secret")
        key = prk.expand(b"aead", aead.AES_256_GCM)
        self.assertIsInstance(key, aead.Key)
        raw = prk.expand(b"aead", 32)
        nonce = bytes(12)
        self.assertEqual(
            key.seal(nonce, b"m", aad=b""),
            aead.Key(aead.AES_256_GCM, raw).seal(nonce, b"m", aad=b""),
        )
        mac = prk.expand(b"hmac", hmac.HMAC_SHA256)
        self.assertEqual(hmac.sign(mac, b"m"), hmac.sign(hmac.Key(hmac.HMAC_SHA256, prk.expand(b"hmac", 32)), b"m"))

    def test_too_long_is_wrong_length(self):
        prk = hkdf.Salt(hkdf.HKDF_SHA256, b"").extract(b"secret")
        with self.assertRaises(pyrind.WrongLength):
            prk.expand(b"", 255 * 32 + 1)
        # Refused before allocating, rather than raising MemoryError.
        with self.assertRaises(pyrind.WrongLength):
            prk.expand(b"", sys.maxsize)


class Pbkdf2(unittest.TestCase):
    @requires_pyca
    def test_matches_pyca(self):
        secret = pbkdf2.Secret(pbkdf2.PBKDF2_HMAC_SHA256, b"password")
        expected = PBKDF2HMAC(hashes.SHA256(), 40, b"salt", 1000).derive(b"password")
        self.assertEqual(secret.derive(1000, b"salt", 40), expected)
        secret.verify(1000, b"salt", expected)
        with self.assertRaises(pyrind.BadSignature):
            secret.verify(1001, b"salt", expected)

    def test_rfc6070_sha1(self):
        secret = pbkdf2.Secret(pbkdf2.legacy.PBKDF2_HMAC_SHA1, b"password")
        self.assertEqual(secret.derive(2, b"salt", 20).hex(), "ea6c014dc72d6f8ccd1ed92ace1d41f0d8de8957")

    def test_zero_iterations_is_refused(self):
        secret = pbkdf2.Secret(pbkdf2.PBKDF2_HMAC_SHA256, b"password")
        with self.assertRaises(ValueError):
            secret.derive(0, b"salt", 32)
        with self.assertRaises(OverflowError):
            secret.derive(-1, b"salt", 32)

    def test_too_long_is_wrong_length(self):
        # One byte past each hash's limit, refused before allocating it.
        # On 32-bit hosts these lengths overflow usize before reaching rind.
        error = pyrind.WrongLength if sys.maxsize > 2**32 else OverflowError
        for algorithm, hash_len in (
            (pbkdf2.PBKDF2_HMAC_SHA256, 32),
            (pbkdf2.PBKDF2_HMAC_SHA384, 48),
            (pbkdf2.PBKDF2_HMAC_SHA512, 64),
            (pbkdf2.legacy.PBKDF2_HMAC_SHA1, 20),
        ):
            secret = pbkdf2.Secret(algorithm, b"password")
            with self.assertRaises(error):
                secret.derive(1, b"salt", (2**32 - 1) * hash_len + 1)

    def test_releases_the_gil(self):
        secret = pbkdf2.Secret(pbkdf2.PBKDF2_HMAC_SHA256, b"password")
        results = []
        threads = [threading.Thread(target=lambda: results.append(secret.derive(20000, b"salt", 32))) for _ in range(4)]
        for thread in threads:
            thread.start()
        for thread in threads:
            thread.join()
        self.assertEqual(len(set(results)), 1)


class AesCbc(unittest.TestCase):
    SIZES = {16: cipher.AES_128, 24: cipher.AES_192, 32: cipher.AES_256}

    @requires_pyca
    def test_cbc_matches_pyca(self):
        for key_len, size in self.SIZES.items():
            key, iv, data = os.urandom(key_len), os.urandom(16), os.urandom(64)
            encryptor = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
            expected = encryptor.update(data) + encryptor.finalize()
            self.assertEqual(cipher.AesCbcEncryptingKey(size, key).encrypt_blocks(iv, data), expected)
            self.assertEqual(cipher.AesCbcDecryptingKey(size, key).decrypt_blocks(iv, expected), data)

    def test_cbc_lengths_are_checked(self):
        encrypting = cipher.AesCbcEncryptingKey(cipher.AES_128, bytes(16))
        decrypting = cipher.AesCbcDecryptingKey(cipher.AES_128, bytes(16))
        with self.assertRaises(pyrind.WrongLength):
            cipher.AesCbcEncryptingKey(cipher.AES_256, bytes(16))
        with self.assertRaises(pyrind.WrongLength):
            encrypting.encrypt_blocks(bytes(16), bytes(15))
        with self.assertRaises(pyrind.WrongLength):
            encrypting.encrypt_blocks(bytes(12), bytes(16))
        with self.assertRaises(pyrind.DecryptFailed):
            decrypting.decrypt_blocks(bytes(16), bytes(17))
        self.assertEqual(encrypting.encrypt_blocks(bytes(16), b""), b"")


class KeyWrap(unittest.TestCase):
    @requires_pyca
    def test_matches_pyca(self):
        for key_len, size in ((16, key_wrap.AES_128), (24, key_wrap.AES_192), (32, key_wrap.AES_256)):
            kek_bytes = os.urandom(key_len)
            kek = key_wrap.AesKek(size, kek_bytes)
            for length in (16, 24, 40):
                key = os.urandom(length)
                wrapped = keywrap.aes_key_wrap(kek_bytes, key)
                self.assertEqual(kek.wrap_key(key_wrap.Mode.KW, key), wrapped)
                self.assertEqual(kek.unwrap_key(key_wrap.Mode.KW, wrapped), key)
            for length in (1, 8, 9, 20):
                key = os.urandom(length)
                wrapped = keywrap.aes_key_wrap_with_padding(kek_bytes, key)
                self.assertEqual(kek.wrap_key(key_wrap.Mode.KWP, key), wrapped)
                self.assertEqual(kek.unwrap_key(key_wrap.Mode.KWP, wrapped), key)

    def test_refuses_what_it_did_not_wrap(self):
        kek = key_wrap.AesKek(key_wrap.AES_128, bytes(16))
        other = key_wrap.AesKek(key_wrap.AES_128, bytes(15) + b"\x01")
        kw, kwp = key_wrap.Mode.KW, key_wrap.Mode.KWP
        for wrapped in (other.wrap_key(kw, bytes(16)), bytes(23), bytes(25), bytes(8), bytes(7), b""):
            with self.assertRaises(pyrind.DecryptFailed):
                kek.unwrap_key(kw, wrapped)
        for wrapped in (other.wrap_key(kwp, bytes(5)), bytes(15), bytes(17), bytes(8), bytes(7), b""):
            with self.assertRaises(pyrind.DecryptFailed):
                kek.unwrap_key(kwp, wrapped)
        # Each mode refuses what the other wrapped.
        with self.assertRaises(pyrind.DecryptFailed):
            kek.unwrap_key(kwp, kek.wrap_key(kw, bytes(16)))
        with self.assertRaises(pyrind.DecryptFailed):
            kek.unwrap_key(kw, kek.wrap_key(kwp, bytes(16)))
        for key in (bytes(8), bytes(17)):
            with self.assertRaises(pyrind.WrongLength):
                kek.wrap_key(kw, key)
        with self.assertRaises(pyrind.WrongLength):
            kek.wrap_key(kwp, b"")
        self.assertEqual(len(kek.wrap_key(kwp, bytes(9))), 24)


class Aead(unittest.TestCase):
    @requires_pyca
    def test_matches_pyca(self):
        pyca = {
            id(aead.AES_128_GCM): pyca_aead.AESGCM,
            id(aead.AES_192_GCM): pyca_aead.AESGCM,
            id(aead.AES_256_GCM): pyca_aead.AESGCM,
            id(aead.CHACHA20_POLY1305): pyca_aead.ChaCha20Poly1305,
        }
        for algorithm in (aead.AES_128_GCM, aead.AES_192_GCM, aead.AES_256_GCM, aead.CHACHA20_POLY1305):
            raw = os.urandom(algorithm.key_len)
            key = aead.Key(algorithm, raw)
            other = pyca[id(algorithm)](raw)
            for length in (0, 1, 15, 16, 17, 255, 1350, 4096):
                nonce = os.urandom(algorithm.nonce_len)
                plaintext, aad = os.urandom(length), os.urandom(length % 40)
                sealed = key.seal(nonce, plaintext, aad=aad)
                self.assertEqual(sealed, other.encrypt(nonce, plaintext, aad))
                self.assertEqual(len(sealed), length + algorithm.tag_len)
                self.assertEqual(key.open(nonce, sealed, aad=aad), plaintext)

    def test_tampering_fails_to_open(self):
        key = aead.Key(aead.AES_128_GCM, bytes(16))
        nonce = bytes(12)
        sealed = key.seal(nonce, b"message", aad=b"header")
        with self.assertRaises(pyrind.DecryptFailed):
            key.open(nonce, sealed, aad=b"Header")
        with self.assertRaises(pyrind.DecryptFailed):
            key.open(nonce, sealed[:-1] + bytes([sealed[-1] ^ 1]), aad=b"header")
        with self.assertRaises(pyrind.DecryptFailed):
            key.open(nonce, sealed[:15], aad=b"header")

    def test_lengths_are_checked(self):
        with self.assertRaises(pyrind.WrongLength):
            aead.Key(aead.AES_128_GCM, bytes(32))
        key = aead.Key(aead.CHACHA20_POLY1305, bytes(32))
        with self.assertRaises(pyrind.WrongLength):
            key.seal(bytes(8), b"", aad=b"")

    def test_aad_is_keyword_only_and_required(self):
        key = aead.Key(aead.AES_128_GCM, bytes(16))
        with self.assertRaises(TypeError):
            key.seal(bytes(12), b"message", b"header")
        with self.assertRaises(TypeError):
            key.seal(bytes(12), b"message")

    def test_randomized_nonce_key(self):
        raw = os.urandom(32)
        key = aead.RandomizedNonceKey(raw)
        nonce, sealed = key.seal(b"message", aad=b"header")
        _, again = key.seal(b"message", aad=b"header")
        self.assertEqual(len(nonce), 24)
        self.assertNotEqual(sealed, again)
        self.assertEqual(key.open(nonce, sealed, aad=b"header"), b"message")
        with self.assertRaises(pyrind.DecryptFailed):
            key.open(nonce, sealed, aad=b"")
        with self.assertRaises(pyrind.WrongLength):
            key.open(nonce[:12], sealed, aad=b"header")
        with self.assertRaises(pyrind.WrongLength):
            aead.RandomizedNonceKey(bytes(16))


class Agreement(unittest.TestCase):
    def test_x25519_rfc7748(self):
        alice = agreement.PrivateKey.from_scalar(
            agreement.X25519,
            bytes.fromhex("77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a"),
        )
        self.assertEqual(
            bytes(alice.public_key()).hex(),
            "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a",
        )
        bob = bytes.fromhex("de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f")
        self.assertEqual(
            alice.agree(bob).hex(),
            "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742",
        )

    @requires_pyca
    def test_x25519_matches_pyca(self):
        ours = agreement.PrivateKey.generate(agreement.X25519)
        theirs = x25519.X25519PrivateKey.generate()
        their_public = theirs.public_key().public_bytes_raw()
        self.assertEqual(
            ours.agree(their_public),
            theirs.exchange(x25519.X25519PublicKey.from_public_bytes(bytes(ours.public_key()))),
        )

    @requires_pyca
    def test_ecdh_matches_pyca(self):
        for algorithm, curve in (
            (agreement.ECDH_P256, ec.SECP256R1()),
            (agreement.ECDH_P384, ec.SECP384R1()),
            (agreement.ECDH_P521, ec.SECP521R1()),
        ):
            ours = agreement.PrivateKey.generate(algorithm)
            theirs = ec.generate_private_key(curve)
            their_public = theirs.public_key().public_bytes(
                serialization.Encoding.X962, serialization.PublicFormat.UncompressedPoint
            )
            our_public = ec.EllipticCurvePublicKey.from_encoded_point(curve, bytes(ours.public_key()))
            self.assertEqual(ours.agree(their_public), theirs.exchange(ec.ECDH(), our_public))

    def test_keys_round_trip(self):
        for algorithm in (agreement.X25519, agreement.ECDH_P256):
            key = agreement.PrivateKey.generate(algorithm)
            public = bytes(key.public_key())
            for loaded in (
                agreement.PrivateKey.from_pkcs8(algorithm, key.to_pkcs8()),
                agreement.PrivateKey.from_scalar(algorithm, key.to_scalar()),
            ):
                self.assertEqual(bytes(loaded.public_key()), public)
            spki = key.public_key().to_spki()
            self.assertEqual(bytes(agreement.PublicKey.from_spki(algorithm, spki)), public)
            self.assertEqual(bytes(agreement.PublicKey(algorithm, public)), public)

    def test_invalid_peer_is_key_rejected(self):
        key = agreement.PrivateKey.generate(agreement.ECDH_P256)
        with self.assertRaises(pyrind.KeyRejected) as raised:
            key.agree(b"\x04" + bytes(64))
        self.assertTrue(str(raised.exception))


class Signature(unittest.TestCase):
    def test_ed25519_rfc8032_test_1(self):
        key = rind_ed25519.KeyPair.from_seed(
            bytes.fromhex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
        )
        self.assertEqual(
            bytes(key.public_key()).hex(),
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        )
        signed = key.sign(b"")
        self.assertEqual(
            signed.hex(),
            "e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e06522490155"
            "5fb8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b",
        )
        key.public_key().verify(b"", signed)
        with self.assertRaises(pyrind.BadSignature):
            key.public_key().verify(b"x", signed)
        public = rind_ed25519.PublicKey(bytes(key.public_key()))
        public.verify(b"", signed)
        self.assertEqual(bytes(rind_ed25519.PublicKey.from_spki(public.to_spki())), bytes(public))
        with self.assertRaises(pyrind.KeyRejected):
            rind_ed25519.PublicKey(public.to_spki())

    @requires_pyca
    def test_ed25519_matches_pyca(self):
        ours = rind_ed25519.KeyPair.generate()
        theirs = ed25519.Ed25519PrivateKey.from_private_bytes(ours.to_seed())
        self.assertEqual(ours.sign(b"message"), theirs.sign(b"message"))
        loaded = serialization.load_der_private_key(ours.to_pkcs8v1(), None)
        self.assertEqual(loaded.sign(b"m"), ours.sign(b"m"))
        self.assertEqual(rind_ed25519.KeyPair.from_pkcs8(ours.to_pkcs8()).to_seed(), ours.to_seed())
        their_spki = theirs.public_key().public_bytes(
            serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
        )
        self.assertEqual(ours.public_key().to_spki(), their_spki)

    @requires_pyca
    def test_ecdsa_against_pyca(self):
        for algorithm, check, curve, hash_ in (
            (ecdsa.sign.P256_SHA256_ASN1, ecdsa.verify.P256_SHA256_ASN1, ec.SECP256R1(), hashes.SHA256()),
            (ecdsa.sign.P384_SHA384_ASN1, ecdsa.verify.P384_SHA384_ASN1, ec.SECP384R1(), hashes.SHA384()),
            (ecdsa.sign.P521_SHA512_ASN1, ecdsa.verify.P521_SHA512_ASN1, ec.SECP521R1(), hashes.SHA512()),
        ):
            ours = ecdsa.KeyPair.generate(algorithm)
            their_view = serialization.load_der_public_key(ours.public_key().to_spki())
            their_view.verify(ours.sign(b"message"), b"message", ec.ECDSA(hash_))

            theirs = ec.generate_private_key(curve)
            der = theirs.private_bytes(
                serialization.Encoding.DER, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()
            )
            loaded = ecdsa.KeyPair.from_pkcs8(algorithm, der)
            spki = theirs.public_key().public_bytes(
                serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
            )
            public = ecdsa.PublicKey.from_spki(check, spki)
            public.verify(b"message", theirs.sign(b"message", ec.ECDSA(hash_)))
            public.verify(b"message", loaded.sign(b"message"))
            self.assertEqual(loaded.public_key().to_spki(), spki)
            with self.assertRaises(pyrind.BadSignature):
                public.verify(b"massage", loaded.sign(b"message"))

    def test_ecdsa_fixed_and_encodings(self):
        key = ecdsa.KeyPair.generate(ecdsa.sign.P256_SHA256_FIXED)
        signed = key.sign(b"m")
        self.assertEqual(len(signed), 64)
        public = ecdsa.PublicKey(ecdsa.verify.P256_SHA256_FIXED, bytes(key.public_key()))
        public.verify(b"m", signed)
        key.public_key().verify(b"m", signed)
        for loaded in (
            ecdsa.KeyPair.from_sec1(ecdsa.sign.P256_SHA256_FIXED, key.to_sec1()),
            ecdsa.KeyPair.from_scalar_and_public_key(
                ecdsa.sign.P256_SHA256_FIXED, key.to_scalar(), bytes(key.public_key())
            ),
        ):
            public.verify(b"m", loaded.sign(b"m"))
        with self.assertRaises(pyrind.KeyRejected):
            ecdsa.KeyPair.from_pkcs8(ecdsa.sign.P384_SHA384_ASN1, key.to_pkcs8())
        # The constructor takes a bare point, and only `from_spki` takes SPKI.
        spki = public.to_spki()
        self.assertEqual(bytes(ecdsa.PublicKey.from_spki(ecdsa.verify.P256_SHA256_FIXED, spki)), bytes(public))
        with self.assertRaises(pyrind.KeyRejected):
            ecdsa.PublicKey(ecdsa.verify.P256_SHA256_FIXED, spki)
        with self.assertRaises(pyrind.KeyRejected):
            ecdsa.PublicKey.from_spki(ecdsa.verify.P384_SHA384_ASN1, spki)

    def test_public_key_is_one_object(self):
        for key in (
            ecdsa.KeyPair.generate(ecdsa.sign.P256_SHA256_ASN1),
            rind_ed25519.KeyPair.generate(),
            rsa.KeyPair.generate(rsa.KeySize.RSA_2048),
            rsa.DecryptingKey.generate(rsa.OAEP_SHA256, rsa.KeySize.RSA_2048),
            agreement.PrivateKey.generate(agreement.X25519),
            agreement.PrivateKey.generate(agreement.ECDH_P256),
            kem.DecapsulationKey.generate(kem.ML_KEM_768),
        ):
            self.assertIs(key.public_key(), key.public_key())
        self.assertFalse(hasattr(ecdsa.KeyPair, "to_spki"))
        self.assertFalse(hasattr(rind_ed25519.KeyPair, "to_spki"))
        self.assertFalse(hasattr(rsa.KeyPair, "to_spki"))
        self.assertFalse(hasattr(rsa.DecryptingKey, "to_spki"))

    @requires_pyca
    def test_rsa_against_pyca(self):
        theirs = pyca_rsa.generate_private_key(65537, 2048)
        der = theirs.private_bytes(
            serialization.Encoding.DER, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()
        )
        ours = rsa.KeyPair.from_pkcs8(der)
        their_public = theirs.public_key()
        their_spki = their_public.public_bytes(
            serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
        )
        their_pkcs1 = their_public.public_bytes(serialization.Encoding.DER, serialization.PublicFormat.PKCS1)
        public = rsa.PublicKey.from_spki(their_spki)
        self.assertEqual(bytes(public), their_pkcs1)
        self.assertEqual(bytes(rsa.PublicKey(their_pkcs1)), their_pkcs1)
        self.assertEqual(ours.public_key().to_spki(), their_spki)
        self.assertEqual(public.modulus_len(), 256)
        for algorithm, check, pad in (
            (rsa.sign.PKCS1_SHA256, rsa.verify.PKCS1_SHA256, padding.PKCS1v15()),
            (rsa.sign.PSS_SHA256, rsa.verify.PSS_SHA256, padding.PSS(padding.MGF1(hashes.SHA256()), 32)),
        ):
            their_public.verify(ours.sign(algorithm, b"message"), b"message", pad, hashes.SHA256())
            # One key verifies with every algorithm whose floor it meets.
            public.verify(check, b"message", theirs.sign(b"message", pad, hashes.SHA256()))
            ours.public_key().verify(check, b"message", ours.sign(algorithm, b"message"))
        public.verify(
            rsa.verify.PSS_SHA256_ANY_SALT,
            b"message",
            theirs.sign(b"message", padding.PSS(padding.MGF1(hashes.SHA256()), 0), hashes.SHA256()),
        )
        with self.assertRaises(pyrind.BadSignature):
            public.verify(rsa.verify.PSS_SHA256, b"message", ours.sign(rsa.sign.PKCS1_SHA256, b"message"))
        numbers = their_public.public_numbers()
        n = numbers.n.to_bytes((numbers.n.bit_length() + 7) // 8, "big")
        e = numbers.e.to_bytes(3, "big")
        components = rsa.PublicKey.from_components(n, e)
        self.assertEqual(bytes(components), their_pkcs1)
        components.verify(rsa.verify.PKCS1_SHA256, b"m", ours.sign(rsa.sign.PKCS1_SHA256, b"m"))

    def test_rsa_generate(self):
        key = rsa.KeyPair.generate(rsa.KeySize.RSA_2048)
        public = key.public_key()
        spki = public.to_spki()
        self.assertEqual(bytes(rsa.PublicKey.from_spki(spki)), bytes(public))
        rsa.PublicKey(bytes(public)).verify(rsa.verify.PSS_SHA256, b"m", key.sign(rsa.sign.PSS_SHA256, b"m"))
        # The constructor takes PKCS#1 only, and `from_spki` SPKI only.
        with self.assertRaises(pyrind.KeyRejected):
            rsa.PublicKey(spki)
        with self.assertRaises(pyrind.KeyRejected):
            rsa.PublicKey.from_spki(bytes(public))
        # A key loads whatever its size, and `verify` refuses a modulus below
        # the algorithm's floor before it reads the signature.
        floor = rsa.verify.legacy.PKCS1_3072_SHA384
        for signature in (b"", key.sign(rsa.sign.PKCS1_SHA384, b"m")):
            with self.assertRaises(pyrind.KeyRejected):
                public.verify(floor, b"m", signature)
        self.assertEqual(public.modulus_len(), 256)
        if PYCA:
            loaded = serialization.load_der_private_key(key.to_pkcs8(), None)
            self.assertEqual(loaded.key_size, 2048)
            numbers = loaded.public_key().public_numbers()
            n = numbers.n.to_bytes(256, "big")
            e = numbers.e.to_bytes(3, "big")
            components = rsa.PublicKey.from_components(n, e)
            components.verify(rsa.verify.PSS_SHA256, b"m", key.sign(rsa.sign.PSS_SHA256, b"m"))
            with self.assertRaises(pyrind.KeyRejected):
                components.verify(floor, b"m", b"")

    @requires_pyca
    def test_rsa_1024_verifies_only_with_legacy(self):
        theirs = pyca_rsa.generate_private_key(65537, 1024)
        spki = theirs.public_key().public_bytes(
            serialization.Encoding.DER, serialization.PublicFormat.SubjectPublicKeyInfo
        )
        public = rsa.PublicKey.from_spki(spki)
        signed = theirs.sign(b"m", padding.PKCS1v15(), hashes.SHA256())
        public.verify(rsa.verify.legacy.PKCS1_1024_SHA256, b"m", signed)
        with self.assertRaises(pyrind.KeyRejected):
            public.verify(rsa.verify.PKCS1_SHA256, b"m", signed)

    def test_rsa_public_key_edges(self):
        # Public moduli need no factors, so these are made to measure: odd,
        # with the top bit of their size set.
        def modulus(bits):
            return (1 << bits - 1) | 1

        def unsigned(value):
            return value.to_bytes((value.bit_length() + 7) // 8, "big")

        def pkcs1(n, e=65537):
            return der(0x30, der_integer(n) + der_integer(e))

        e = unsigned(65537)
        for bits in (1024, 1025, 2047, 8192):
            n = modulus(bits)
            key = rsa.PublicKey.from_components(unsigned(n), e)
            self.assertEqual(key.modulus_len(), (bits + 7) // 8)
            # Each way in reads the same key, and each way out round trips.
            self.assertEqual(bytes(key), pkcs1(n))
            self.assertEqual(bytes(rsa.PublicKey(pkcs1(n))), pkcs1(n))
            self.assertEqual(bytes(rsa.PublicKey.from_spki(key.to_spki())), pkcs1(n))
        for n, e_bytes in (
            (modulus(1023), e),  # below 1024 bits
            (modulus(8193), e),  # above 8192 bits
            (modulus(2048) + 1, e),  # even
            (modulus(2048), unsigned(1)),
            (modulus(2048), unsigned(65536)),  # even
            (modulus(2048), unsigned(1 << 33 | 1)),  # past 33 bits
        ):
            with self.assertRaises(pyrind.KeyRejected):
                rsa.PublicKey.from_components(unsigned(n), e_bytes)
            with self.assertRaises(pyrind.KeyRejected):
                rsa.PublicKey(pkcs1(n, int.from_bytes(e_bytes, "big")))
        rsa.PublicKey.from_components(unsigned(modulus(2048)), unsigned((1 << 33) - 1))
        for n_bytes, e_bytes in ((b"\x00" + unsigned(modulus(2048)), e), (unsigned(modulus(2048)), b"\x00" + e), (b"", e)):
            with self.assertRaises(pyrind.KeyRejected):
                rsa.PublicKey.from_components(n_bytes, e_bytes)
        good = pkcs1(modulus(2048))
        for bad in (good + b"\x00", good[:-1], b"\x30" + good[1:2] + der_integer(modulus(2048))):
            with self.assertRaises(pyrind.KeyRejected):
                rsa.PublicKey(bad)

        # A modulus at an algorithm's floor reads the signature, so one too
        # short fails as a bad signature; a bit below, `verify` refuses the
        # key whatever the signature.
        floors = (
            (1024, rsa.verify.legacy.PKCS1_1024_SHA256),
            (2048, rsa.verify.PKCS1_SHA256),
            (2048, rsa.verify.PSS_SHA256),
            (2048, rsa.verify.PSS_SHA256_ANY_SALT),
            (3072, rsa.verify.legacy.PKCS1_3072_SHA384),
        )
        for floor, algorithm in floors:
            at = rsa.PublicKey.from_components(unsigned(modulus(floor)), e)
            for signature in (b"", bytes(at.modulus_len()), bytes(at.modulus_len() + 1)):
                with self.assertRaises(pyrind.BadSignature):
                    at.verify(algorithm, b"m", signature)
            if floor > 1024:
                below = rsa.PublicKey.from_components(unsigned(modulus(floor - 1)), e)
                for signature in (b"", bytes(below.modulus_len())):
                    with self.assertRaises(pyrind.KeyRejected):
                        below.verify(algorithm, b"m", signature)

        # RSA-OAEP's floor is 2048 bits, refused as the key loads.
        oaep = rsa.OAEP_SHA256
        at = pkcs1(modulus(2048))
        self.assertEqual(rsa.EncryptingKey(oaep, at).to_spki(), rsa.PublicKey(at).to_spki())
        rsa.EncryptingKey.from_components(oaep, unsigned(modulus(2048)), e)
        below = pkcs1(modulus(2047))
        for call in (
            lambda: rsa.EncryptingKey(oaep, below),
            lambda: rsa.EncryptingKey.from_spki(oaep, rsa.PublicKey(below).to_spki()),
            lambda: rsa.EncryptingKey.from_components(oaep, unsigned(modulus(2047)), e),
        ):
            with self.assertRaises(pyrind.KeyRejected):
                call()

    def test_garbage_keys_are_rejected(self):
        for call in (
            lambda: rind_ed25519.KeyPair.from_pkcs8(b"\x30\x00"),
            lambda: rsa.KeyPair.from_pkcs1(os.urandom(100)),
            lambda: ecdsa.PublicKey(ecdsa.verify.P256_SHA256_ASN1, os.urandom(65)),
            lambda: rind_ed25519.PublicKey.from_spki(b""),
            lambda: rsa.PublicKey(b""),
            lambda: rsa.PublicKey.from_spki(os.urandom(100)),
        ):
            with self.assertRaises(pyrind.KeyRejected):
                call()


class Rsa(unittest.TestCase):
    @requires_pyca
    def test_oaep_against_pyca(self):
        theirs = pyca_rsa.generate_private_key(65537, 2048)
        der = theirs.private_bytes(
            serialization.Encoding.DER, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()
        )
        ours = rsa.DecryptingKey.from_pkcs8(rsa.OAEP_SHA256, der)
        pad = padding.OAEP(padding.MGF1(hashes.SHA256()), hashes.SHA256(), b"label")
        self.assertEqual(ours.decrypt(theirs.public_key().encrypt(b"secret", pad), label=b"label"), b"secret")
        spki = ours.public_key().to_spki()
        encrypting = rsa.EncryptingKey.from_spki(rsa.OAEP_SHA256, spki)
        pkcs1 = theirs.public_key().public_bytes(serialization.Encoding.DER, serialization.PublicFormat.PKCS1)
        self.assertEqual(rsa.EncryptingKey(rsa.OAEP_SHA256, pkcs1).to_spki(), spki)
        # The constructor takes PKCS#1 only, and `from_spki` SPKI only.
        with self.assertRaises(pyrind.KeyRejected):
            rsa.EncryptingKey(rsa.OAEP_SHA256, spki)
        with self.assertRaises(pyrind.KeyRejected):
            rsa.EncryptingKey.from_spki(rsa.OAEP_SHA256, pkcs1)
        self.assertEqual(theirs.decrypt(encrypting.encrypt(b"secret", label=b"label"), pad), b"secret")
        self.assertEqual(encrypting.max_message_len, 256 - 2 * 32 - 2)
        with self.assertRaises(pyrind.WrongLength):
            encrypting.encrypt(bytes(encrypting.max_message_len + 1), label=b"")
        with self.assertRaises(pyrind.DecryptFailed):
            ours.decrypt(encrypting.encrypt(b"secret", label=b"label"), label=b"other")

    def test_generate(self):
        key = rsa.DecryptingKey.generate(rsa.OAEP_SHA512, rsa.KeySize.RSA_2048)
        ciphertext = key.public_key().encrypt(b"m", label=b"")
        self.assertEqual(key.decrypt(ciphertext, label=b""), b"m")
        self.assertEqual(rsa.KeySize.RSA_2048, rsa.KeySize.RSA_2048)
        self.assertNotEqual(rsa.KeySize.RSA_2048, rsa.KeySize.RSA_3072)


class Kem(unittest.TestCase):
    def test_keys_at_any_address(self):
        # rind's AVX2 ML-KEM loads key data aligned to 32 bytes, which an
        # object's own storage only reaches by chance; holding many keys at
        # once places some of them off it.
        keys = [kem.DecapsulationKey.generate(kem.ML_KEM_768) for _ in range(32)]
        public = [key.public_key() for key in keys]
        for key, encapsulation_key in zip(keys, public):
            ciphertext, secret = encapsulation_key.encapsulate()
            self.assertEqual(key.decapsulate(ciphertext), secret)

    @requires_pyca
    def test_against_pyca(self):
        ours = kem.DecapsulationKey.generate(kem.ML_KEM_768)
        their_view = mlkem.MLKEM768PublicKey.from_public_bytes(bytes(ours.public_key()))
        secret, ciphertext = their_view.encapsulate()
        self.assertEqual(ours.decapsulate(ciphertext), secret)

        theirs = mlkem.MLKEM768PrivateKey.generate()
        ciphertext, secret = kem.EncapsulationKey(kem.ML_KEM_768, theirs.public_key().public_bytes_raw()).encapsulate()
        self.assertEqual(theirs.decapsulate(ciphertext), secret)

    def test_round_trip(self):
        recipient = kem.DecapsulationKey.generate(kem.ML_KEM_768)
        public = kem.EncapsulationKey(kem.ML_KEM_768, bytes(recipient.public_key()))
        ciphertext, secret = public.encapsulate()
        self.assertEqual(len(secret), 32)
        self.assertEqual(recipient.decapsulate(ciphertext), secret)
        # A tampered ciphertext yields an unrelated secret, not an error.
        tampered = bytes([ciphertext[0] ^ 1]) + ciphertext[1:]
        self.assertNotEqual(recipient.decapsulate(tampered), secret)
        with self.assertRaises(pyrind.Error):
            recipient.decapsulate(ciphertext[:-1])
        with self.assertRaises(pyrind.Error):
            kem.EncapsulationKey(kem.ML_KEM_768, bytes(100))


if __name__ == "__main__":
    unittest.main()
