"""pyrind-cryptography against pyca/cryptography: each primitive's outputs,
keys written by one and read by the other, and the errors pyca raises."""

import itertools
import json
import os
import pathlib
import unittest

from cryptography.hazmat.primitives import hashes as pyca_hashes
from cryptography.hazmat.primitives import hmac as pyca_hmac
from cryptography.hazmat.primitives import keywrap as pyca_keywrap
from cryptography.hazmat.primitives import padding as pyca_padding
from cryptography.hazmat.primitives import serialization as pyca_serialization
from cryptography.hazmat.primitives.asymmetric import ec as pyca_ec
from cryptography.hazmat.primitives.asymmetric import ed25519 as pyca_ed25519
from cryptography.hazmat.primitives.asymmetric import padding as pyca_asym_padding
from cryptography.hazmat.primitives.asymmetric import rsa as pyca_rsa
from cryptography.hazmat.primitives.asymmetric import x25519 as pyca_x25519
from cryptography.hazmat.primitives.ciphers import Cipher as PycaCipher
from cryptography.hazmat.primitives.ciphers import aead as pyca_aead
from cryptography.hazmat.primitives.ciphers import algorithms as pyca_algorithms
from cryptography.hazmat.primitives.ciphers import modes as pyca_modes
from cryptography.hazmat.primitives.kdf import concatkdf as pyca_concatkdf
from cryptography.hazmat.primitives.kdf import hkdf as pyca_hkdf
from cryptography.hazmat.primitives.kdf import pbkdf2 as pyca_pbkdf2
from cryptography.hazmat.primitives.kdf import x963kdf as pyca_x963kdf

from pyrind_cryptography import exceptions
from pyrind_cryptography.hazmat.primitives import constant_time, hashes, hmac, keywrap, padding, serialization
from pyrind_cryptography.hazmat.primitives.asymmetric import ec, ed448, ed25519, rsa, utils, x25519
from pyrind_cryptography.hazmat.primitives.asymmetric import padding as asym_padding
from pyrind_cryptography.hazmat.primitives.ciphers import Cipher, aead, algorithms, modes
from pyrind_cryptography.hazmat.primitives.kdf import concatkdf, hkdf, pbkdf2, x963kdf

VECTORS = pathlib.Path(__file__).resolve().parents[3] / "thirdparty" / "vectors" / "wycheproof" / "testvectors_v1"

HASHES = ["SHA1", "SHA256", "SHA384", "SHA512", "SHA512_256", "SHA3_256", "SHA3_384", "SHA3_512", "MD5"]
HMAC_HASHES = ["SHA1", "SHA256", "SHA384", "SHA512"]
CURVES = ["SECP256R1", "SECP384R1", "SECP521R1"]
CURVE_HASH = {"SECP256R1": "SHA256", "SECP384R1": "SHA384", "SECP521R1": "SHA512"}
ENC = serialization.Encoding
PRIV = serialization.PrivateFormat
PUB = serialization.PublicFormat
NONE = serialization.NoEncryption()


def ours(name):
    return getattr(hashes, name)()


def theirs(name):
    return getattr(pyca_hashes, name)()


def pyca_format(value):
    """pyca's enum member of the same name as ours."""
    return getattr(getattr(pyca_serialization, type(value).__name__), value.name)


def vectors(name):
    path = VECTORS / f"{name}_test.json"
    if not path.exists():
        raise FileNotFoundError(f"{path} is missing; run: admin/sync-vectors")
    for group in json.loads(path.read_text())["testGroups"]:
        for test in group["tests"]:
            yield group, test


def chunks(data, sizes=(1, 7, 16, 33)):
    out, pos = [], 0
    for size in itertools.cycle(sizes):
        if pos >= len(data):
            return out
        out.append(data[pos : pos + size])
        pos += size


class Hashes(unittest.TestCase):
    def test_match_pyca(self):
        for name in HASHES:
            data = os.urandom(300)
            expected = pyca_hashes.Hash(theirs(name))
            expected.update(data)
            context = hashes.Hash(ours(name))
            for piece in chunks(data):
                context.update(piece)
            copy = context.copy()
            self.assertEqual(context.finalize(), expected.finalize(), name)
            copy.update(b"more")
            self.assertEqual(copy.finalize(), _pyca_hash(name, data + b"more"))
            self.assertEqual((ours(name).digest_size, ours(name).block_size, ours(name).name),
                             (theirs(name).digest_size, theirs(name).block_size, theirs(name).name))

    def test_finalize_once(self):
        context = hashes.Hash(hashes.SHA256())
        context.finalize()
        for call in (lambda: context.update(b""), context.finalize, context.copy):
            with self.assertRaises(exceptions.AlreadyFinalized):
                call()

    def test_unsupported(self):
        for algorithm in (hashes.SHA224(), hashes.SHA3_224(), hashes.BLAKE2b(64), hashes.SM3(), hashes.SHAKE128(16)):
            with self.assertRaises(exceptions.UnsupportedAlgorithm):
                hashes.Hash(algorithm)
        with self.assertRaises(TypeError):
            hashes.Hash("sha256")


def _pyca_hash(name, data):
    context = pyca_hashes.Hash(theirs(name))
    context.update(data)
    return context.finalize()


class Hmac(unittest.TestCase):
    def test_matches_pyca(self):
        for name in HMAC_HASHES:
            key, data = os.urandom(70), os.urandom(200)
            expected = pyca_hmac.HMAC(key, theirs(name))
            expected.update(data)
            tag = expected.finalize()
            context = hmac.HMAC(key, ours(name))
            for piece in chunks(data):
                context.update(piece)
            copy = context.copy()
            self.assertEqual(context.finalize(), tag)
            copy.verify(tag)
            with self.assertRaises(exceptions.InvalidSignature):
                bad = hmac.HMAC(key, ours(name))
                bad.update(data)
                bad.verify(tag[:-1])

    def test_unsupported(self):
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            hmac.HMAC(b"k", hashes.MD5())


class Kdfs(unittest.TestCase):
    def test_hkdf(self):
        for name in HMAC_HASHES:
            for salt, info, length in ((None, None, 32), (b"salt", b"info", 255 * theirs(name).digest_size), (b"", b"x", 1)):
                ikm = os.urandom(40)
                expected = pyca_hkdf.HKDF(theirs(name), length, salt, info).derive(ikm)
                self.assertEqual(hkdf.HKDF(ours(name), length, salt, info).derive(ikm), expected)
                prk = pyca_hkdf.HKDF.extract(theirs(name), salt, ikm)
                self.assertEqual(hkdf.HKDF.extract(ours(name), salt, ikm), prk)
                self.assertEqual(hkdf.HKDFExpand(ours(name), length, info).derive(prk), expected)
        with self.assertRaises(ValueError):
            hkdf.HKDF(hashes.SHA256(), 255 * 32 + 1, None, None)
        kdf = hkdf.HKDF(hashes.SHA256(), 16, None, None)
        kdf.verify(b"k", pyca_hkdf.HKDF(pyca_hashes.SHA256(), 16, None, None).derive(b"k"))
        with self.assertRaises(exceptions.AlreadyFinalized):
            kdf.derive(b"k")
        with self.assertRaises(exceptions.InvalidKey):
            hkdf.HKDF(hashes.SHA256(), 16, None, None).verify(b"k", bytes(16))

    def test_hkdf_wycheproof(self):
        for size in (1, 256, 384, 512):
            for group, test in vectors(f"hkdf_sha{size}"):
                name = f"SHA{size}"
                ikm, salt, info = (bytes.fromhex(test[k]) for k in ("ikm", "salt", "info"))
                with self.subTest(size=size, tcId=test["tcId"]):
                    try:
                        okm = hkdf.HKDF(ours(name), test["size"], salt, info).derive(ikm)
                    except ValueError:
                        self.assertEqual(test["result"], "invalid")
                    else:
                        self.assertEqual(okm.hex(), test["okm"])

    def test_pbkdf2(self):
        for name in HMAC_HASHES:
            expected = pyca_pbkdf2.PBKDF2HMAC(theirs(name), 40, b"salt", 1000).derive(b"password")
            self.assertEqual(pbkdf2.PBKDF2HMAC(ours(name), 40, b"salt", 1000).derive(b"password"), expected)
            pbkdf2.PBKDF2HMAC(ours(name), 40, b"salt", 1000).verify(b"password", expected)
            with self.assertRaises(exceptions.InvalidKey):
                pbkdf2.PBKDF2HMAC(ours(name), 40, b"salt", 1000).verify(b"passwort", expected)

    def test_concat_and_x963(self):
        for name in ("SHA256", "SHA384", "SHA512", "SHA1"):
            z, info = os.urandom(32), os.urandom(20)
            for length in (1, 32, 100):
                self.assertEqual(
                    concatkdf.ConcatKDFHash(ours(name), length, info).derive(z),
                    pyca_concatkdf.ConcatKDFHash(theirs(name), length, info).derive(z),
                )
                for salt in (None, b"salt"):
                    self.assertEqual(
                        concatkdf.ConcatKDFHMAC(ours(name), length, salt, info).derive(z),
                        pyca_concatkdf.ConcatKDFHMAC(theirs(name), length, salt, info).derive(z),
                    )
                self.assertEqual(
                    x963kdf.X963KDF(ours(name), length, info).derive(z),
                    pyca_x963kdf.X963KDF(theirs(name), length, info).derive(z),
                )

    def test_derive_into(self):
        buffer = bytearray(32)
        self.assertEqual(hkdf.HKDF(hashes.SHA256(), 32, None, None).derive_into(b"k", buffer), 32)
        self.assertEqual(bytes(buffer), pyca_hkdf.HKDF(pyca_hashes.SHA256(), 32, None, None).derive(b"k"))
        with self.assertRaises(ValueError):
            hkdf.HKDF(hashes.SHA256(), 32, None, None).derive_into(b"k", bytearray(31))


class Aeads(unittest.TestCase):
    def test_match_pyca(self):
        cases = [(aead.AESGCM, pyca_aead.AESGCM, n) for n in (16, 24, 32)]
        cases.append((aead.ChaCha20Poly1305, pyca_aead.ChaCha20Poly1305, 32))
        for ours_class, theirs_class, key_len in cases:
            key, nonce = os.urandom(key_len), os.urandom(12)
            for data, aad in ((b"", None), (os.urandom(100), b"aad")):
                sealed = theirs_class(key).encrypt(nonce, data, aad)
                self.assertEqual(ours_class(key).encrypt(nonce, data, aad), sealed)
                self.assertEqual(ours_class(key).decrypt(nonce, sealed, aad), data)
                with self.assertRaises(exceptions.InvalidTag):
                    ours_class(key).decrypt(nonce, sealed[:-1] + bytes([sealed[-1] ^ 1]), aad)
                buffer = bytearray(len(data) + 16)
                ours_class(key).encrypt_into(nonce, data, aad, buffer)
                self.assertEqual(bytes(buffer), sealed)

    def test_errors(self):
        with self.assertRaises(ValueError):
            aead.AESGCM(bytes(20))
        with self.assertRaises(ValueError):
            aead.ChaCha20Poly1305(bytes(16))
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            aead.AESGCM(bytes(16)).encrypt(bytes(16), b"", None)
        with self.assertRaises(ValueError):
            aead.AESGCM(bytes(16)).encrypt(bytes(7), b"", None)
        with self.assertRaises(ValueError):
            aead.ChaCha20Poly1305(bytes(32)).encrypt(bytes(16), b"", None)
        with self.assertRaises(exceptions.InvalidTag):
            aead.AESGCM(bytes(16)).decrypt(bytes(12), bytes(15), None)
        for missing in (aead.AESCCM, aead.AESSIV, aead.AESOCB3, aead.AESGCMSIV):
            with self.assertRaises(exceptions.UnsupportedAlgorithm):
                missing(bytes(32))
        self.assertEqual(len(aead.AESGCM.generate_key(192)), 24)


class Ciphers(unittest.TestCase):
    def test_cbc_streams_like_pyca(self):
        for key_len in (16, 24, 32):
            key, iv, data = os.urandom(key_len), os.urandom(16), os.urandom(160)
            pyca = PycaCipher(pyca_algorithms.AES(key), pyca_modes.CBC(iv)).encryptor()
            expected = pyca.update(data) + pyca.finalize()
            encryptor = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
            self.assertEqual(b"".join(encryptor.update(piece) for piece in chunks(data)) + encryptor.finalize(), expected)
            decryptor = Cipher(algorithms.AES(key), modes.CBC(iv)).decryptor()
            self.assertEqual(b"".join(decryptor.update(piece) for piece in chunks(expected)) + decryptor.finalize(), data)
        partial = Cipher(algorithms.AES(bytes(16)), modes.CBC(bytes(16))).encryptor()
        partial.update(bytes(17))
        with self.assertRaises(ValueError):
            partial.finalize()

    def test_gcm_matches_pyca(self):
        key, iv, data, aad = os.urandom(32), os.urandom(12), os.urandom(50), os.urandom(9)
        pyca = PycaCipher(pyca_algorithms.AES(key), pyca_modes.GCM(iv)).encryptor()
        pyca.authenticate_additional_data(aad)
        expected = pyca.update(data) + pyca.finalize()
        encryptor = Cipher(algorithms.AES(key), modes.GCM(iv)).encryptor()
        with self.assertRaises(exceptions.NotYetFinalized):
            encryptor.tag
        encryptor.authenticate_additional_data(aad)
        self.assertEqual(encryptor.update(data) + encryptor.finalize(), expected)
        self.assertEqual(encryptor.tag, pyca.tag)
        decryptor = Cipher(algorithms.AES(key), modes.GCM(iv, pyca.tag)).decryptor()
        decryptor.authenticate_additional_data(aad)
        self.assertEqual(decryptor.update(expected) + decryptor.finalize(), data)
        decryptor = Cipher(algorithms.AES(key), modes.GCM(iv)).decryptor()
        decryptor.update(expected)
        with self.assertRaises(exceptions.InvalidTag):
            decryptor.finalize_with_tag(bytes(16))

    def test_update_into_refuses_a_buffer_before_advancing(self):
        key, iv, data = os.urandom(16), os.urandom(16), os.urandom(32)
        expected = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor().update(data)
        encryptor = Cipher(algorithms.AES(key), modes.CBC(iv)).encryptor()
        with self.assertRaises(ValueError):
            encryptor.update_into(data, bytearray(32))
        with self.assertRaises(TypeError):
            encryptor.update_into(data, bytes(64))
        buffer = bytearray(47)
        self.assertEqual(encryptor.update_into(data, buffer), 32)
        self.assertEqual(bytes(buffer[:32]), expected)

    def test_unsupported(self):
        for mode in (modes.CTR(bytes(16)), modes.ECB(), modes.OFB(bytes(16)), modes.CFB(bytes(16))):
            with self.assertRaises(exceptions.UnsupportedAlgorithm):
                Cipher(algorithms.AES(bytes(16)), mode).encryptor()
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            Cipher(algorithms.AES(bytes(16)), modes.GCM(bytes(16))).encryptor()
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            Cipher(algorithms.ChaCha20(bytes(32), bytes(16)), None).encryptor()
        with self.assertRaises(ValueError):
            Cipher(algorithms.AES(bytes(16)), modes.CBC(bytes(8)))

    def test_cbc_pkcs7_wycheproof(self):
        for _, test in vectors("aes_cbc_pkcs5"):
            key, iv, ct, msg = (bytes.fromhex(test[k]) for k in ("key", "iv", "ct", "msg"))
            with self.subTest(tcId=test["tcId"]):
                decryptor = Cipher(algorithms.AES(key), modes.CBC(iv)).decryptor()
                unpadder = padding.PKCS7(128).unpadder()
                try:
                    plain = decryptor.update(ct) + decryptor.finalize()
                    plain = unpadder.update(plain) + unpadder.finalize()
                except ValueError:
                    self.assertEqual(test["result"], "invalid", test["comment"])
                else:
                    self.assertEqual(test["result"], "valid", test["comment"])
                    self.assertEqual(plain, msg)


class Padding(unittest.TestCase):
    def test_matches_pyca(self):
        for ours_class, theirs_class in ((padding.PKCS7, pyca_padding.PKCS7), (padding.ANSIX923, pyca_padding.ANSIX923)):
            for block_size in (64, 128, 2040):
                for length in (0, 1, 15, 16, 17, 300):
                    data = os.urandom(length)
                    padder = theirs_class(block_size).padder()
                    padded = padder.update(data) + padder.finalize()
                    ours_padder = ours_class(block_size).padder()
                    self.assertEqual(b"".join(ours_padder.update(p) for p in chunks(data)) + ours_padder.finalize(), padded)
                    unpadder = ours_class(block_size).unpadder()
                    self.assertEqual(b"".join(unpadder.update(p) for p in chunks(padded)) + unpadder.finalize(), data)

    def test_bad_padding(self):
        for bad in (bytes(16), bytes(15) + b"\x11", bytes(14) + b"\x01\x02", b"\x03" * 15):
            unpadder = padding.PKCS7(128).unpadder()
            unpadder.update(bad)
            with self.assertRaises(ValueError):
                unpadder.finalize()
        unpadder = padding.ANSIX923(128).unpadder()
        unpadder.update(bytes(13) + b"\x01\x00\x03")
        with self.assertRaises(ValueError):
            unpadder.finalize()


class KeyWrap(unittest.TestCase):
    def test_matches_pyca(self):
        for kek_len in (16, 24, 32):
            kek = os.urandom(kek_len)
            key = os.urandom(24)
            wrapped = pyca_keywrap.aes_key_wrap(kek, key)
            self.assertEqual(keywrap.aes_key_wrap(kek, key), wrapped)
            self.assertEqual(keywrap.aes_key_unwrap(kek, wrapped), key)
            for length in (1, 8, 20):
                key = os.urandom(length)
                wrapped = pyca_keywrap.aes_key_wrap_with_padding(kek, key)
                self.assertEqual(keywrap.aes_key_wrap_with_padding(kek, key), wrapped)
                self.assertEqual(keywrap.aes_key_unwrap_with_padding(kek, wrapped), key)

    def test_errors(self):
        with self.assertRaises(keywrap.InvalidUnwrap):
            keywrap.aes_key_unwrap(bytes(16), bytes(24))
        with self.assertRaises(keywrap.InvalidUnwrap):
            keywrap.aes_key_unwrap(bytes(16), bytes(16))
        with self.assertRaises(keywrap.InvalidUnwrap):
            keywrap.aes_key_unwrap_with_padding(bytes(16), bytes(16))
        with self.assertRaises(ValueError):
            keywrap.aes_key_wrap(bytes(15), bytes(16))
        with self.assertRaises(ValueError):
            keywrap.aes_key_wrap(bytes(16), bytes(12))


class Keys(unittest.TestCase):
    """Each key type written in every format by one library and read by the other."""

    PRIVATE_FORMATS = [(ENC.PEM, PRIV.PKCS8), (ENC.DER, PRIV.PKCS8), (ENC.PEM, PRIV.TraditionalOpenSSL), (ENC.DER, PRIV.TraditionalOpenSSL)]
    PUBLIC_FORMATS = [(ENC.PEM, PUB.SubjectPublicKeyInfo), (ENC.DER, PUB.SubjectPublicKeyInfo), (ENC.OpenSSH, PUB.OpenSSH)]

    def round_trip(self, ours_key, pyca_key, private_formats, public_formats, same):
        """Writes each key in each format, reads it with the other library, and checks it is the same key with `same`."""
        for encoding, format in private_formats:
            with self.subTest(encoding=encoding, format=format, direction="pyca reads ours"):
                data = ours_key.private_bytes(encoding, format, NONE)
                loader = pyca_serialization.load_pem_private_key if encoding is ENC.PEM else pyca_serialization.load_der_private_key
                self.assertTrue(same(loader(data, None), ours_key))
            with self.subTest(encoding=encoding, format=format, direction="ours reads pyca"):
                data = pyca_key.private_bytes(pyca_format(encoding), pyca_format(format), pyca_serialization.NoEncryption())
                loader = serialization.load_pem_private_key if encoding is ENC.PEM else serialization.load_der_private_key
                self.assertTrue(same(pyca_key, loader(data, None)))
        for encoding, format in public_formats:
            with self.subTest(encoding=encoding, format=format):
                ours_bytes = ours_key.public_key().public_bytes(encoding, format)
                theirs_bytes = pyca_key.public_key().public_bytes(pyca_format(encoding), pyca_format(format))
                loader = {
                    ENC.PEM: serialization.load_pem_public_key,
                    ENC.DER: serialization.load_der_public_key,
                    ENC.OpenSSH: serialization.load_ssh_public_key,
                }.get(encoding)
                if loader is not None:
                    self.assertEqual(loader(theirs_bytes).public_bytes(encoding, format), theirs_bytes)
                pyca_loader = {
                    ENC.PEM: pyca_serialization.load_pem_public_key,
                    ENC.DER: pyca_serialization.load_der_public_key,
                    ENC.OpenSSH: pyca_serialization.load_ssh_public_key,
                }.get(encoding)
                if pyca_loader is not None:
                    pyca_loader(ours_bytes)

    def test_ec(self):
        for name in CURVES:
            ours_key = ec.generate_private_key(getattr(ec, name)())
            pyca_key = pyca_ec.generate_private_key(getattr(pyca_ec, name)())

            def same(a, b):
                return a.private_numbers().private_value == b.private_numbers().private_value

            self.round_trip(ours_key, pyca_key, self.PRIVATE_FORMATS, self.PUBLIC_FORMATS + [
                (ENC.X962, PUB.UncompressedPoint), (ENC.X962, PUB.CompressedPoint)], same)
            # Our key read through pyca's numbers, and pyca's through ours.
            numbers = pyca_key.private_numbers()
            ours_from_numbers = ec.EllipticCurvePrivateNumbers(
                numbers.private_value,
                ec.EllipticCurvePublicNumbers(numbers.public_numbers.x, numbers.public_numbers.y, getattr(ec, name)()),
            ).private_key()
            self.assertEqual(ours_from_numbers.public_key().public_numbers().x, numbers.public_numbers.x)
            self.assertEqual(ec.derive_private_key(numbers.private_value, getattr(ec, name)()).private_numbers().private_value, numbers.private_value)
            for compressed in (PUB.CompressedPoint, PUB.UncompressedPoint):
                point = pyca_key.public_key().public_bytes(pyca_serialization.Encoding.X962, pyca_format(compressed))
                loaded = ec.EllipticCurvePublicKey.from_encoded_point(getattr(ec, name)(), point)
                self.assertEqual(loaded.public_bytes(ENC.X962, compressed), point)

    def test_ecdsa_and_ecdh(self):
        for name in CURVES:
            hash_name = CURVE_HASH[name]
            ours_key = ec.generate_private_key(getattr(ec, name)())
            pyca_key = pyca_serialization.load_der_private_key(ours_key.private_bytes(ENC.DER, PRIV.PKCS8, NONE), None)
            signed = ours_key.sign(b"message", ec.ECDSA(ours(hash_name)))
            pyca_key.public_key().verify(signed, b"message", pyca_ec.ECDSA(theirs(hash_name)))
            for verify_hash in ("SHA256", "SHA384", "SHA512"):
                signed = pyca_key.sign(b"message", pyca_ec.ECDSA(theirs(verify_hash)))
                ours_key.public_key().verify(signed, b"message", ec.ECDSA(ours(verify_hash)))
                with self.assertRaises(exceptions.InvalidSignature):
                    ours_key.public_key().verify(signed, b"messagf", ec.ECDSA(ours(verify_hash)))
            peer = pyca_ec.generate_private_key(getattr(pyca_ec, name)())
            peer_public = serialization.load_der_public_key(
                peer.public_key().public_bytes(pyca_serialization.Encoding.DER, pyca_serialization.PublicFormat.SubjectPublicKeyInfo)
            )
            self.assertEqual(ours_key.exchange(ec.ECDH(), peer_public), peer.exchange(pyca_ec.ECDH(), pyca_key.public_key()))
        key = ec.generate_private_key(ec.SECP256R1())
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            key.sign(b"m", ec.ECDSA(hashes.SHA384()))
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            key.sign(b"m", ec.ECDSA(utils.Prehashed(hashes.SHA256())))
        with self.assertRaises(ValueError):
            key.exchange(ec.ECDH(), ec.generate_private_key(ec.SECP384R1()).public_key())
        for curve in (ec.SECP256K1(), ec.SECP192R1(), ec.BrainpoolP256R1()):
            with self.assertRaises(exceptions.UnsupportedAlgorithm):
                ec.generate_private_key(curve)

    def test_dss_signature(self):
        r, s = 2**255 + 7, 12345
        self.assertEqual(utils.decode_dss_signature(utils.encode_dss_signature(r, s)), (r, s))
        from cryptography.hazmat.primitives.asymmetric import utils as pyca_utils

        self.assertEqual(utils.encode_dss_signature(r, s), pyca_utils.encode_dss_signature(r, s))

    def test_ed25519(self):
        ours_key = ed25519.Ed25519PrivateKey.generate()
        pyca_key = pyca_ed25519.Ed25519PrivateKey.generate()

        def same(a, b):
            return a.private_bytes_raw() == b.private_bytes_raw()

        self.round_trip(ours_key, pyca_key, self.PRIVATE_FORMATS[:2], self.PUBLIC_FORMATS + [(ENC.Raw, PUB.Raw)], same)
        self.assertEqual(
            ours_key.private_bytes(ENC.DER, PRIV.PKCS8, NONE),
            pyca_ed25519.Ed25519PrivateKey.from_private_bytes(ours_key.private_bytes_raw()).private_bytes(
                pyca_serialization.Encoding.DER, pyca_serialization.PrivateFormat.PKCS8, pyca_serialization.NoEncryption()
            ),
        )
        mirror = ed25519.Ed25519PrivateKey.from_private_bytes(pyca_key.private_bytes_raw())
        self.assertEqual(mirror.sign(b"m"), pyca_key.sign(b"m"))
        mirror.public_key().verify(pyca_key.sign(b"m"), b"m")
        with self.assertRaises(exceptions.InvalidSignature):
            mirror.public_key().verify(pyca_key.sign(b"m"), b"n")
        with self.assertRaises(ValueError):
            ours_key.private_bytes(ENC.PEM, PRIV.TraditionalOpenSSL, NONE)
        self.assertEqual(mirror.public_key(), ed25519.Ed25519PublicKey.from_public_bytes(pyca_key.public_key().public_bytes_raw()))

    def test_x25519(self):
        ours_key = x25519.X25519PrivateKey.generate()
        pyca_key = pyca_x25519.X25519PrivateKey.generate()

        def same(a, b):
            return a.private_bytes_raw() == b.private_bytes_raw()

        self.round_trip(ours_key, pyca_key, self.PRIVATE_FORMATS[:2], self.PUBLIC_FORMATS[:2] + [(ENC.Raw, PUB.Raw)], same)
        peer = x25519.X25519PublicKey.from_public_bytes(pyca_key.public_key().public_bytes_raw())
        expected = pyca_key.exchange(pyca_x25519.X25519PublicKey.from_public_bytes(ours_key.public_key().public_bytes_raw()))
        self.assertEqual(ours_key.exchange(peer), expected)
        with self.assertRaises(ValueError):
            ours_key.exchange(x25519.X25519PublicKey.from_public_bytes(bytes(32)))

    def test_rsa(self):
        ours_key = rsa.generate_private_key(65537, 2048)
        pyca_key = pyca_rsa.generate_private_key(65537, 2048)

        def same(a, b):
            return a.private_numbers() == b.private_numbers() if type(a) is type(b) else (
                (a.private_numbers().d, a.private_numbers().p) == (b.private_numbers().d, b.private_numbers().p)
            )

        self.round_trip(ours_key, pyca_key, self.PRIVATE_FORMATS, self.PUBLIC_FORMATS + [
            (ENC.PEM, PUB.PKCS1), (ENC.DER, PUB.PKCS1)], same)
        numbers = pyca_key.private_numbers()
        mirror = rsa.RSAPrivateNumbers(
            numbers.p, numbers.q, numbers.d, numbers.dmp1, numbers.dmq1, numbers.iqmp,
            rsa.RSAPublicNumbers(numbers.public_numbers.e, numbers.public_numbers.n),
        ).private_key()
        self.assertEqual(mirror.key_size, 2048)
        self.assertEqual(mirror.public_key().public_numbers().n, numbers.public_numbers.n)

        for name in ("SHA256", "SHA384", "SHA512"):
            self.assertEqual(mirror.sign(b"m", asym_padding.PKCS1v15(), ours(name)), pyca_key.sign(b"m", pyca_asym_padding.PKCS1v15(), theirs(name)))
            for salt, pyca_salt in ((asym_padding.PSS.DIGEST_LENGTH, pyca_asym_padding.PSS.DIGEST_LENGTH), (ours(name).digest_size, theirs(name).digest_size)):
                signed = mirror.sign(b"m", asym_padding.PSS(asym_padding.MGF1(ours(name)), salt), ours(name))
                pyca_key.public_key().verify(signed, b"m", pyca_asym_padding.PSS(pyca_asym_padding.MGF1(theirs(name)), pyca_salt), theirs(name))
            for pyca_salt in (pyca_asym_padding.PSS.MAX_LENGTH, 0, 20):
                signed = pyca_key.sign(b"m", pyca_asym_padding.PSS(pyca_asym_padding.MGF1(theirs(name)), pyca_salt), theirs(name))
                mirror.public_key().verify(signed, b"m", asym_padding.PSS(asym_padding.MGF1(ours(name)), asym_padding.PSS.AUTO), ours(name))
                with self.assertRaises(exceptions.InvalidSignature):
                    mirror.public_key().verify(signed, b"n", asym_padding.PSS(asym_padding.MGF1(ours(name)), asym_padding.PSS.AUTO), ours(name))
            signed = pyca_key.sign(b"m", pyca_asym_padding.PKCS1v15(), theirs(name))
            with self.assertRaises(exceptions.InvalidSignature):
                mirror.public_key().verify(signed, b"n", asym_padding.PKCS1v15(), ours(name))
        mirror.public_key().verify(pyca_key.sign(b"m", pyca_asym_padding.PKCS1v15(), pyca_hashes.SHA1()), b"m", asym_padding.PKCS1v15(), hashes.SHA1())

        for name in ("SHA1", "SHA256", "SHA384", "SHA512"):
            for label in (None, b"label"):
                ours_oaep = asym_padding.OAEP(asym_padding.MGF1(ours(name)), ours(name), label)
                theirs_oaep = pyca_asym_padding.OAEP(pyca_asym_padding.MGF1(theirs(name)), theirs(name), label)
                self.assertEqual(mirror.decrypt(pyca_key.public_key().encrypt(b"secret", theirs_oaep), ours_oaep), b"secret")
                self.assertEqual(pyca_key.decrypt(mirror.public_key().encrypt(b"secret", ours_oaep), theirs_oaep), b"secret")
                with self.assertRaises(ValueError):
                    mirror.decrypt(bytes(256), ours_oaep)

    def test_rsa_unsupported(self):
        key = rsa.generate_private_key(65537, 2048)
        sha256 = hashes.SHA256()
        refused = [
            lambda: key.sign(b"m", asym_padding.PKCS1v15(), hashes.SHA1()),
            lambda: key.sign(b"m", asym_padding.PSS(asym_padding.MGF1(sha256), 20), sha256),
            lambda: key.sign(b"m", asym_padding.PSS(asym_padding.MGF1(sha256), asym_padding.PSS.MAX_LENGTH), sha256),
            lambda: key.sign(b"m", asym_padding.PSS(asym_padding.MGF1(hashes.SHA1()), 32), sha256),
            lambda: key.public_key().encrypt(b"m", asym_padding.PKCS1v15()),
            lambda: key.decrypt(bytes(256), asym_padding.PKCS1v15()),
            lambda: rsa.generate_private_key(65537, 1024),
            lambda: rsa.generate_private_key(3, 2048),
            lambda: rsa.rsa_crt_iqmp(5, 7),
            lambda: rsa.rsa_recover_prime_factors(1, 2, 3),
        ]
        for call in refused:
            with self.assertRaises(exceptions.UnsupportedAlgorithm):
                call()
        with self.assertRaises(ValueError):
            rsa.generate_private_key(5, 2048)

    def test_unsupported_types(self):
        for call in (ed448.Ed448PrivateKey.generate, lambda: ed448.Ed448PublicKey.from_public_bytes(bytes(57))):
            with self.assertRaises(exceptions.UnsupportedAlgorithm):
                call()
        from cryptography.hazmat.primitives.asymmetric import ed448 as pyca_ed448

        der = pyca_ed448.Ed448PrivateKey.generate().private_bytes(
            pyca_serialization.Encoding.DER, pyca_serialization.PrivateFormat.PKCS8, pyca_serialization.NoEncryption()
        )
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            serialization.load_der_private_key(der, None)
        key = ec.generate_private_key(ec.SECP256R1())
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            key.private_bytes(ENC.PEM, PRIV.PKCS8, serialization.BestAvailableEncryption(b"password"))

    def test_passwords(self):
        pyca_key = pyca_ec.generate_private_key(pyca_ec.SECP256R1())
        encrypted = pyca_key.private_bytes(
            pyca_serialization.Encoding.PEM, pyca_serialization.PrivateFormat.PKCS8, pyca_serialization.BestAvailableEncryption(b"pw")
        )
        with self.assertRaises(TypeError):
            serialization.load_pem_private_key(encrypted, None)
        with self.assertRaises(exceptions.UnsupportedAlgorithm):
            serialization.load_pem_private_key(encrypted, b"pw")
        plain = pyca_key.private_bytes(
            pyca_serialization.Encoding.PEM, pyca_serialization.PrivateFormat.PKCS8, pyca_serialization.NoEncryption()
        )
        with self.assertRaises(TypeError):
            serialization.load_pem_private_key(plain, b"pw")

    def test_malformed_keys_raise_value_error(self):
        encodings = [
            ec.generate_private_key(ec.SECP384R1()).private_bytes(ENC.DER, PRIV.PKCS8, NONE),
            ec.generate_private_key(ec.SECP256R1()).private_bytes(ENC.DER, PRIV.TraditionalOpenSSL, NONE),
            ed25519.Ed25519PrivateKey.generate().private_bytes(ENC.DER, PRIV.PKCS8, NONE),
            rsa.generate_private_key(65537, 2048).private_bytes(ENC.DER, PRIV.TraditionalOpenSSL, NONE),
        ]
        for der in encodings:
            serialization.load_der_private_key(der, None)
            for cut in range(0, len(der), max(1, len(der) // 40)):
                with self.assertRaises((ValueError, exceptions.UnsupportedAlgorithm)):
                    serialization.load_der_private_key(der[:cut], None)
            for position in range(0, len(der), max(1, len(der) // 40)):
                mutated = bytearray(der)
                mutated[position] ^= 0x41
                try:
                    serialization.load_der_private_key(bytes(mutated), None)
                except (ValueError, exceptions.UnsupportedAlgorithm):
                    pass
        public = ec.generate_private_key(ec.SECP256R1()).public_key().public_bytes(ENC.DER, PUB.SubjectPublicKeyInfo)
        for cut in range(len(public)):
            with self.assertRaises((ValueError, exceptions.UnsupportedAlgorithm)):
                serialization.load_der_public_key(public[:cut])
        for garbage in (b"", b"-----BEGIN PUBLIC KEY-----\n!!\n-----END PUBLIC KEY-----\n", b"ssh-rsa AAAA", b"\x30\x84\xff\xff\xff\xff"):
            for loader in (serialization.load_der_public_key, serialization.load_pem_public_key, serialization.load_ssh_public_key):
                with self.assertRaises((ValueError, exceptions.UnsupportedAlgorithm)):
                    loader(garbage)

    def test_unterminated_pem_is_refused(self):
        # A quadratic scan would take hours over this.
        with self.assertRaises(ValueError):
            serialization.load_pem_public_key(b"-----BEGIN PUBLIC KEY-----\n" * 200_000)
        with self.assertRaises(ValueError):
            serialization.load_pem_public_key(b"-----BEGIN PUBLIC KEY-----\nAAAA\n")

    def test_constant_time(self):
        self.assertTrue(constant_time.bytes_eq(b"ab", b"ab"))
        self.assertFalse(constant_time.bytes_eq(b"ab", b"ac"))


class Readme(unittest.TestCase):
    def test_example_runs(self):
        import re

        readme = pathlib.Path(__file__).resolve().parents[1] / "README.md"
        blocks = re.findall(r"```python\n(.*?)```", readme.read_text(), re.S)
        self.assertTrue(blocks)
        for block in blocks:
            exec(compile(block, str(readme), "exec"), {})


if __name__ == "__main__":
    unittest.main()
