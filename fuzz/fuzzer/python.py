"""Calls pyrind's native module, `_rind`, as libFuzzer's bytes direct.

It finds every function, class, method, and constant the module exports, so
a new one is fuzzed without a change here. Each input is a sequence of
calls: each picks a callable and fills its parameters with bytes-likes of
every buffer shape (bytes, bytearray, strided, multi-dimensional, and
non-byte-format memoryviews, arrays), strings, ints in and out of range,
None, any module's algorithm constants, the objects and bytes earlier calls
returned, and rind's test keys. A call may raise only `pyrind.Error` or the
TypeError, ValueError, or OverflowError of an argument Python could not
convert; anything else, a `PanicException` from a Rust panic included,
fails the input.
"""

import array
import inspect
import types

import _rind

ALLOWED = (_rind.Error, TypeError, ValueError, OverflowError)

# RSA key generation takes seconds, so it is left out.
SLOW = {"RsaKeyPair.generate", "DecryptingKey.generate"}


def _exports(module, seen):
    for name in sorted(dir(module)):
        if name.startswith("_"):
            continue
        value = getattr(module, name)
        if isinstance(value, types.ModuleType):
            if value.__name__ not in seen:
                seen.add(value.__name__)
                yield from _exports(value, seen)
        else:
            yield value


EXPORTS = list(_exports(_rind, set()))
CLASSES = [v for v in EXPORTS if isinstance(v, type) and not issubclass(v, BaseException)]
CONSTANTS = [v for v in EXPORTS if not callable(v)]
# Each callable, and the class whose instance it needs, if any.
CALLABLES = [(None, v) for v in EXPORTS if callable(v) and not isinstance(v, type)]
for cls in CLASSES:
    CALLABLES.append((None, cls))
    for name, member in sorted(vars(cls).items()):
        if name.startswith("_") or f"{cls.__name__}.{name}" in SLOW:
            continue
        if isinstance(member, (staticmethod, classmethod)):
            CALLABLES.append((None, getattr(cls, name)))
        elif callable(member):
            CALLABLES.append((cls, name))
# Each enum-like class's variants, such as `rsa.KeySize`'s.
for cls in CLASSES:
    for name, value in sorted(vars(cls).items()):
        if isinstance(value, cls):
            CONSTANTS.append(value)

INTS = [0, 1, -1, 7, 12, 16, 24, 32, 64, 255, 256, 2**31, 2**32, 2**64, -(2**64), 2**200]

# Parameters a call's work grows with, by name: the most one call may ask
# for, and the bound of the Rust type that takes it. An int between the two,
# such as 2**31 PBKDF2 iterations or a 4 GiB output, would only stop the
# fuzzer on a timeout or out-of-memory, so it is cut below the cap; one past
# the type's range still checks its conversion.
COSTS = {"iterations": (1 << 10, 1 << 32), "length": (1 << 9, 1 << 64)}

# How deep a list argument may nest, so generating one never reaches
# Python's recursion limit.
DEPTH = 3


# The input ran out: a class of its own, so an EOFError a call raises still
# fails the input.
class Exhausted(Exception):
    pass


class Input:
    def __init__(self, data):
        self.data = data
        self.at = 0

    def byte(self):
        if self.at >= len(self.data):
            raise Exhausted
        self.at += 1
        return self.data[self.at - 1]

    def pick(self, choices):
        return choices[self.byte() % len(choices)]

    def bytes(self):
        n = self.byte()
        if n == 255:
            n = self.byte() << 8 | self.byte()
        chunk = self.data[self.at : self.at + n]
        self.at += n
        return chunk


def _buffer(raw, kind):
    if kind == 0:
        return raw
    if kind == 1:
        return bytearray(raw)
    if kind == 2:
        return memoryview(raw)
    if kind == 3:
        # Strided: not contiguous.
        return memoryview(raw)[::2]
    if kind == 4:
        # Of 4-byte items.
        return memoryview(raw[: len(raw) // 4 * 4]).cast("I")
    if kind == 5:
        # Two-dimensional, which an empty view cannot be cast to.
        even = raw[: len(raw) // 2 * 2]
        if not even:
            return memoryview(even)
        return memoryview(even).cast("B", shape=[2, len(even) // 2])
    if kind == 6:
        return array.array("H", raw[: len(raw) // 2 * 2])
    # A read-only view of a writable buffer.
    return memoryview(bytearray(raw)).toreadonly()


class State:
    def __init__(self, data, fixtures):
        self.input = Input(data)
        self.objects = []
        self.byte_pool = list(fixtures)

    def value(self, depth=0):
        kind = self.input.byte()
        if kind < 96:
            return _buffer(self.input.bytes(), kind % 8)
        if kind < 128:
            # Bytes an earlier call returned, or a test key, as any buffer.
            return _buffer(self.input.pick(self.byte_pool), kind % 8)
        if kind < 168:
            return self.input.pick(CONSTANTS)
        if kind < 200 and self.objects:
            return self.input.pick(self.objects)
        if kind < 216:
            return self.input.pick(INTS) if kind % 2 else self.input.byte()
        if kind < 224 and depth < DEPTH:
            return [self.value(depth + 1) for _ in range(self.input.byte() % 4)]
        if kind < 232:
            return self.input.bytes().decode("latin-1")
        return self.input.pick([None, True, False, 1.5, object()])

    def call(self):
        owner, target = self.input.pick(CALLABLES)
        if owner is not None:
            # A method on an instance, usually of its own class.
            instances = [o for o in self.objects if isinstance(o, owner)]
            if self.input.byte() % 8 and instances:
                receiver = self.input.pick(instances)
            elif self.objects:
                receiver = self.input.pick(self.objects)
            else:
                return
            target = getattr(receiver, target, None)
            if target is None:
                return
        args, kwargs = self.arguments(target)
        try:
            result = target(*args, **kwargs)
        except ALLOWED:
            return
        self.keep(result)

    def arguments(self, target):
        try:
            parameters = inspect.signature(target).parameters.values()
        except (TypeError, ValueError):
            return [self.value() for _ in range(self.input.byte() % 4)], {}
        args, kwargs = [], {}
        for p in parameters:
            if p.kind == p.VAR_POSITIONAL or p.kind == p.VAR_KEYWORD:
                continue
            # Now and then a parameter goes missing.
            if self.input.byte() == 0:
                continue
            value = self.value()
            cap, limit = COSTS.get(p.name, (0, 0))
            if type(value) is int and cap <= value < limit:
                value %= cap
            if p.kind == p.KEYWORD_ONLY:
                kwargs[p.name] = value
            else:
                args.append(value)
        return args, kwargs

    def keep(self, result):
        values = result if isinstance(result, tuple) else (result,)
        for v in values:
            if isinstance(v, bytes) and len(self.byte_pool) < 64:
                self.byte_pool.append(v)
            elif type(v).__module__.startswith("pyrind") and len(self.objects) < 16:
                self.objects.append(v)


def fuzz(data, fixtures):
    state = State(data, fixtures)
    try:
        for _ in range(32):
            state.call()
    except Exhausted:
        pass
