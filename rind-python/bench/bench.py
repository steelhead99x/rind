"""Per-call cost of pyrind against pyca/cryptography, hashlib, and hmac.

Each operation runs as a Python program calls it, inputs already in hand, so
the times include each library's per-call overhead, which dominates small
messages. Prints a Markdown table; `sh/python.sh bench` runs it.
"""

import argparse
import hashlib
import hmac as std_hmac
import os
import platform
import timeit

import cryptography
from cryptography.hazmat.backends.openssl import backend
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives import hmac as pyca_hmac
from cryptography.hazmat.primitives.asymmetric import ec, ed25519, mlkem, padding, x25519
from cryptography.hazmat.primitives.asymmetric import rsa as pyca_rsa
from cryptography.hazmat.primitives.ciphers import aead as pyca_aead
from cryptography.hazmat.primitives.kdf.hkdf import HKDF

from pyrind import aead, agreement, digest, hkdf, hmac, kem, signature
from pyrind.signature import sign, verify


def cases():
    """Yields (operation, {library: callable})."""
    message = os.urandom(21)
    yield "SHA-256, 21 B", {
        "pyrind": lambda: digest.digest(digest.SHA256, message),
        "cryptography": lambda: _pyca_hash(message),
        "hashlib": lambda: hashlib.sha256(message).digest(),
    }

    raw = os.urandom(32)
    key = hmac.Key(hmac.HMAC_SHA256, raw)
    yield "HMAC-SHA256, 21 B", {
        "pyrind": lambda: hmac.sign(key, message),
        "cryptography": lambda: _pyca_hmac(raw, message),
        "hashlib": lambda: std_hmac.digest(raw, message, "sha256"),
    }

    yield "HKDF-SHA256, 32 B key", {
        "pyrind": lambda: hkdf.Salt(hkdf.HKDF_SHA256, b"salt").extract(raw).expand(b"info", 32),
        "cryptography": lambda: HKDF(hashes.SHA256(), 32, b"salt", b"info").derive(raw),
    }

    nonce = os.urandom(12)
    for name, algorithm, other in (
        ("AES-128-GCM", aead.AES_128_GCM, pyca_aead.AESGCM),
        ("ChaCha20-Poly1305", aead.CHACHA20_POLY1305, pyca_aead.ChaCha20Poly1305),
    ):
        raw_key = os.urandom(algorithm.key_len)
        ours, theirs = aead.Key(algorithm, raw_key), other(raw_key)
        for size in (32, 1350, 16384):
            plaintext = os.urandom(size)
            sealed = ours.seal(nonce, plaintext, aad=b"")
            yield f"{name} seal, {size} B", {
                "pyrind": lambda ours=ours, plaintext=plaintext: ours.seal(nonce, plaintext, aad=b""),
                "cryptography": lambda theirs=theirs, plaintext=plaintext: theirs.encrypt(nonce, plaintext, b""),
            }
            yield f"{name} open, {size} B", {
                "pyrind": lambda ours=ours, sealed=sealed: ours.open(nonce, sealed, aad=b""),
                "cryptography": lambda theirs=theirs, sealed=sealed: theirs.decrypt(nonce, sealed, b""),
            }

    # Key agreement takes the peer's key as bytes, as it arrives.
    ours = agreement.PrivateKey.generate(agreement.X25519)
    theirs = x25519.X25519PrivateKey.generate()
    peer = theirs.public_key().public_bytes_raw()
    yield "X25519 agree", {
        "pyrind": lambda: ours.agree(peer),
        "cryptography": lambda: theirs.exchange(x25519.X25519PublicKey.from_public_bytes(peer)),
    }

    ours_p256 = agreement.PrivateKey.generate(agreement.ECDH_P256)
    theirs_p256 = ec.generate_private_key(ec.SECP256R1())
    peer_p256 = bytes(ours_p256.public_key())
    yield "ECDH P-256 agree", {
        "pyrind": lambda: ours_p256.agree(peer_p256),
        "cryptography": lambda: theirs_p256.exchange(
            ec.ECDH(), ec.EllipticCurvePublicKey.from_encoded_point(ec.SECP256R1(), peer_p256)
        ),
    }

    ours_ed = signature.Ed25519KeyPair.generate()
    theirs_ed = ed25519.Ed25519PrivateKey.from_private_bytes(ours_ed.to_seed())
    signed_ed = ours_ed.sign(message)
    public_ed, their_public_ed = ours_ed.public_key(), theirs_ed.public_key()
    yield "Ed25519 sign, 21 B", {
        "pyrind": lambda: ours_ed.sign(message),
        "cryptography": lambda: theirs_ed.sign(message),
    }
    yield "Ed25519 verify, 21 B", {
        "pyrind": lambda: public_ed.verify(message, signed_ed),
        "cryptography": lambda: their_public_ed.verify(signed_ed, message),
    }

    ours_ec = signature.EcdsaKeyPair.generate(sign.ECDSA_P256_SHA256_ASN1)
    public_ec = signature.PublicKey(verify.ECDSA_P256_SHA256_ASN1, bytes(ours_ec.public_key()))
    theirs_ec = ec.generate_private_key(ec.SECP256R1())
    their_public_ec = theirs_ec.public_key()
    signed_ec, their_signed_ec = ours_ec.sign(message), theirs_ec.sign(message, ec.ECDSA(hashes.SHA256()))
    yield "ECDSA P-256 sign, 21 B", {
        "pyrind": lambda: ours_ec.sign(message),
        "cryptography": lambda: theirs_ec.sign(message, ec.ECDSA(hashes.SHA256())),
    }
    yield "ECDSA P-256 verify, 21 B", {
        "pyrind": lambda: public_ec.verify(message, signed_ec),
        "cryptography": lambda: their_public_ec.verify(their_signed_ec, message, ec.ECDSA(hashes.SHA256())),
    }

    theirs_rsa = pyca_rsa.generate_private_key(65537, 2048)
    from cryptography.hazmat.primitives import serialization

    der = theirs_rsa.private_bytes(
        serialization.Encoding.DER, serialization.PrivateFormat.PKCS8, serialization.NoEncryption()
    )
    ours_rsa = signature.RsaKeyPair.from_pkcs8(der)
    public_rsa = ours_rsa.public_key(sign.RSA_PKCS1_SHA256)
    their_public_rsa = theirs_rsa.public_key()
    signed_rsa = ours_rsa.sign(sign.RSA_PKCS1_SHA256, message)
    yield "RSA-2048 PKCS#1 sign, 21 B", {
        "pyrind": lambda: ours_rsa.sign(sign.RSA_PKCS1_SHA256, message),
        "cryptography": lambda: theirs_rsa.sign(message, padding.PKCS1v15(), hashes.SHA256()),
    }
    yield "RSA-2048 PKCS#1 verify, 21 B", {
        "pyrind": lambda: public_rsa.verify(message, signed_rsa),
        "cryptography": lambda: their_public_rsa.verify(signed_rsa, message, padding.PKCS1v15(), hashes.SHA256()),
    }

    ours_kem = kem.DecapsulationKey.generate(kem.ML_KEM_768)
    public_kem = ours_kem.public_key()
    ciphertext, _ = public_kem.encapsulate()
    theirs_kem = mlkem.MLKEM768PrivateKey.generate()
    their_public_kem = theirs_kem.public_key()
    _, their_ciphertext = their_public_kem.encapsulate()
    yield "ML-KEM-768 encapsulate", {
        "pyrind": public_kem.encapsulate,
        "cryptography": their_public_kem.encapsulate,
    }
    yield "ML-KEM-768 decapsulate", {
        "pyrind": lambda: ours_kem.decapsulate(ciphertext),
        "cryptography": lambda: theirs_kem.decapsulate(their_ciphertext),
    }


def _pyca_hash(message):
    context = hashes.Hash(hashes.SHA256())
    context.update(message)
    return context.finalize()


def _pyca_hmac(key, message):
    context = pyca_hmac.HMAC(key, hashes.SHA256())
    context.update(message)
    return context.finalize()


def seconds_per_call(function, repeat):
    """The fastest of `repeat` runs, each long enough to time reliably."""
    timer = timeit.Timer(function)
    number, _ = timer.autorange()
    return min(timer.repeat(repeat, number)) / number


def human(seconds):
    if seconds < 1e-6:
        return f"{seconds * 1e9:.0f} ns"
    if seconds < 1e-3:
        return f"{seconds * 1e6:.2f} µs"
    return f"{seconds * 1e3:.2f} ms"


def cpu_model():
    try:
        with open("/proc/cpuinfo") as cpuinfo:
            for line in cpuinfo:
                if line.startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return platform.processor() or platform.machine()


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--repeat", type=int, default=7, help="timed runs per operation, of which the fastest counts")
    args = parser.parse_args()

    print(f"{cpu_model()}, {platform.system()} {platform.release()}, Python {platform.python_version()},")
    print(f"cryptography {cryptography.__version__} on {backend.openssl_version_text()}.\n")
    libraries = ["pyrind", "cryptography", "hashlib"]
    print("| Operation | pyrind | cryptography | hashlib, hmac | cryptography ÷ pyrind |")
    print("|---|" + "---:|" * (len(libraries) + 1))
    for operation, functions in cases():
        times = {name: seconds_per_call(function, args.repeat) for name, function in functions.items()}
        cells = [human(times[name]) if name in times else "-" for name in libraries]
        ratio = times["cryptography"] / times["pyrind"]
        print(f"| {operation} | " + " | ".join(cells) + f" | {ratio:.1f}x |", flush=True)


if __name__ == "__main__":
    main()
