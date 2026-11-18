"""Strict DER and PEM, for the key encodings rind parses itself.

Only enough is read to route an encoding to the rind parser for its key type,
or to take apart what rind itself wrote; rind then parses the whole encoding.
Every malformed input raises `ValueError`, and reading is linear in its size.
"""

import base64
import binascii

INTEGER = 0x02
BIT_STRING = 0x03
OCTET_STRING = 0x04
NULL = 0x05
OID = 0x06
SEQUENCE = 0x30


def _read(data, pos):
    """Reads the element at `pos`: its tag, its contents, and where it ends."""
    if len(data) - pos < 2:
        raise ValueError("truncated DER")
    tag = data[pos]
    if tag & 0x1F == 0x1F:
        raise ValueError("DER tag too long")
    length = data[pos + 1]
    pos += 2
    if length & 0x80:
        count = length & 0x7F
        if count == 0 or count > 4 or len(data) - pos < count or data[pos] == 0:
            raise ValueError("bad DER length")
        length = int.from_bytes(data[pos : pos + count], "big")
        if length < 0x80:
            raise ValueError("non-minimal DER length")
        pos += count
    if len(data) - pos < length:
        raise ValueError("truncated DER")
    return tag, data[pos : pos + length], pos + length


def elements(data):
    """Splits `data` into its elements, as (tag, contents) pairs."""
    data = bytes(data)
    out, pos = [], 0
    while pos < len(data):
        tag, contents, pos = _read(data, pos)
        out.append((tag, contents))
    return out


def one(data, tag):
    """Returns the contents of `data`, which must be exactly one element of `tag`."""
    items = elements(data)
    if len(items) != 1 or items[0][0] != tag:
        raise ValueError("unexpected DER")
    return items[0][1]


def integer(contents):
    """Decodes an INTEGER's contents, refusing a negative or non-minimal one."""
    if not contents or contents[0] & 0x80 or (len(contents) > 1 and contents[0] == 0 and not contents[1] & 0x80):
        raise ValueError("bad DER integer")
    return int.from_bytes(contents, "big")


def oid(contents):
    """Decodes an OBJECT IDENTIFIER's contents to dotted form."""
    if not contents or contents[-1] & 0x80:
        raise ValueError("bad DER object identifier")
    arcs, value = [], 0
    for i, byte in enumerate(contents):
        if value == 0 and byte == 0x80:
            raise ValueError("bad DER object identifier")
        value = value << 7 | byte & 0x7F
        if not byte & 0x80:
            arcs.append(value)
            value = 0
        elif i > 64:
            raise ValueError("DER object identifier too long")
    first = min(arcs[0] // 40, 2)
    return ".".join(map(str, [first, arcs[0] - 40 * first, *arcs[1:]]))


def encode(tag, contents):
    """Encodes one element."""
    n = len(contents)
    if n < 0x80:
        return bytes([tag, n]) + contents
    length = n.to_bytes((n.bit_length() + 7) // 8, "big")
    return bytes([tag, 0x80 | len(length)]) + length + contents


def encode_oid(dotted):
    """Encodes the contents of an OBJECT IDENTIFIER in dotted form."""
    arcs = [int(arc) for arc in dotted.split(".")]
    out = bytearray()
    for arc in [40 * arcs[0] + arcs[1], *arcs[2:]]:
        chunk = [arc & 0x7F]
        arc >>= 7
        while arc:
            chunk.append(0x80 | arc & 0x7F)
            arc >>= 7
        out += bytes(reversed(chunk))
    return bytes(out)


def encode_integer(value):
    """Encodes a non-negative INTEGER."""
    if value < 0:
        raise ValueError("negative integer")
    return encode(INTEGER, value.to_bytes(value.bit_length() // 8 + 1, "big"))


def sequence(*items):
    """Encodes a SEQUENCE of already encoded elements."""
    return encode(SEQUENCE, b"".join(items))


def algorithm(data):
    """The OID of an `AlgorithmIdentifier`'s contents, and its parameter's OID or None."""
    items = elements(data)
    if not items or items[0][0] != OID or len(items) > 2:
        raise ValueError("bad AlgorithmIdentifier")
    parameter = None
    if len(items) == 2 and items[1][0] == OID:
        parameter = oid(items[1][1])
    elif len(items) == 2 and items[1] != (NULL, b""):
        raise ValueError("bad AlgorithmIdentifier parameters")
    return oid(items[0][1]), parameter


def pkcs8_algorithm(der):
    """The algorithm and parameter OIDs a PKCS#8 `PrivateKeyInfo` names."""
    items = elements(one(der, SEQUENCE))
    if len(items) < 3 or items[0][0] != INTEGER or items[1][0] != SEQUENCE or items[2][0] != OCTET_STRING:
        raise ValueError("bad PKCS#8")
    return algorithm(items[1][1])


def pkcs8_key(der):
    """The `privateKey` octets of a PKCS#8 `PrivateKeyInfo`."""
    return elements(one(der, SEQUENCE))[2][1]


def spki_algorithm(der):
    """The algorithm and parameter OIDs a `SubjectPublicKeyInfo` names."""
    items = elements(one(der, SEQUENCE))
    if len(items) != 2 or items[0][0] != SEQUENCE or items[1][0] != BIT_STRING:
        raise ValueError("bad SubjectPublicKeyInfo")
    return algorithm(items[0][1])


def spki_key(der):
    """The `subjectPublicKey` octets of a `SubjectPublicKeyInfo`."""
    bits = elements(one(der, SEQUENCE))[1][1]
    if not bits or bits[0] != 0:
        raise ValueError("bad SubjectPublicKeyInfo")
    return bits[1:]


def spki(algorithm_der, key):
    """Encodes a `SubjectPublicKeyInfo` from its encoded `AlgorithmIdentifier` and key octets."""
    return sequence(algorithm_der, encode(BIT_STRING, b"\x00" + key))


def integers(der):
    """The INTEGERs of a SEQUENCE of nothing else, such as a PKCS#1 key or an ECDSA signature."""
    items = elements(one(der, SEQUENCE))
    if any(tag != INTEGER for tag, _ in items):
        raise ValueError("unexpected DER")
    return [integer(contents) for _, contents in items]


def pem_blocks(data):
    """Each PEM block in `data`, as (label, headers, DER) triples, in order, read in one pass over its lines."""
    blocks, label, end, body = [], None, None, []
    for line in bytes(data).splitlines():
        line = line.strip()
        if label is None:
            if line.startswith(b"-----BEGIN ") and line.endswith(b"-----"):
                label, body = line[11:-5], []
                end = b"-----END " + label + b"-----"
            continue
        if line.startswith(b"-----BEGIN "):
            raise ValueError("unterminated PEM block")
        if line == end:
            blocks.append(_pem_block(label, body))
            label = None
        else:
            body.append(line)
    return blocks


def _pem_block(label, lines):
    headers = b""
    if lines and b":" in lines[0]:
        if b"" not in lines:
            raise ValueError("bad PEM headers")
        split = lines.index(b"")
        headers, lines = b"\n".join(lines[:split]), lines[split + 1 :]
    try:
        der = base64.b64decode(b"".join(lines), validate=True)
    except binascii.Error:
        raise ValueError("bad PEM base64") from None
    try:
        return label.decode("ascii"), headers, der
    except UnicodeDecodeError:
        raise ValueError("bad PEM label") from None


def pem(label, der):
    """Encodes `der` as a PEM block labelled `label`, in 64-column lines."""
    body = base64.b64encode(der)
    lines = b"".join(body[i : i + 64] + b"\n" for i in range(0, len(body), 64))
    return b"-----BEGIN %s-----\n%s-----END %s-----\n" % (label.encode(), lines, label.encode())
