"""Translate one AT&T instruction of aws-lc's x86_64 ChaCha20-Poly1305 text
into a term of rind's x86_64 model (`RindIsa/X86_64.lean`)."""
import re

GPR = {'rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi',
       'r8', 'r9', 'r10', 'r11', 'r12', 'r13', 'r14', 'r15'}
GPR32 = {'eax': 'rax', 'ecx': 'rcx', 'edx': 'rdx', 'ebx': 'rbx'}


def split_ops(s):
    out, d, cur = [], 0, ''
    for ch in s:
        if ch == '(':
            d += 1
        if ch == ')':
            d -= 1
        if ch == ',' and d == 0:
            out.append(cur.strip())
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def num(s):
    s = s.replace(' ', '')
    if not re.fullmatch(r'[-+0-9x*a-fA-F()]+', s):
        raise ValueError(s)
    return int(eval(s))


def lean_int(v):
    return f'({v})' if v < 0 else str(v)


class Op:
    """An operand: kind is 'r' (gpr), 'r32', 'x' (xmm), 'y' (ymm), 'imm',
    'mem' (base, index, disp), 'sym' (static, disp)."""

    def __init__(s, text):
        s.text = text
        t = text
        if t.startswith('$'):
            s.kind, s.v = 'imm', num(t[1:])
        elif t.startswith('%xmm'):
            s.kind, s.v = 'x', int(t[4:])
        elif t.startswith('%ymm'):
            s.kind, s.v = 'y', int(t[4:])
        elif t.startswith('%') and t[1:] in GPR:
            s.kind, s.v = 'r', t[1:]
        elif t.startswith('%') and t[1:] in GPR32:
            s.kind, s.v = 'r32', GPR32[t[1:]]
        elif t.endswith('(%rip)'):
            m = re.fullmatch(r'\{(chacha20_consts|and_masks)\}([-+0-9 ]*)\(%rip\)', t)
            if not m:
                raise ValueError(t)
            d = num(m.group(2)) if m.group(2).strip() else 0
            if m.group(1) == 'and_masks':
                d += 192
            s.kind, s.v = 'sym', d
        else:
            m = re.fullmatch(r'([-+0-9 *x]*)\((%\w+)(?:,(%\w+),(\d))?\)', t)
            if not m:
                raise ValueError(t)
            d = num(m.group(1)) if m.group(1).strip() else 0
            base = m.group(2)[1:]
            idx = m.group(3)[1:] if m.group(3) else None
            sc = int(m.group(4)) if m.group(4) else 1
            assert base in GPR and (idx is None or idx in GPR) and sc == 1, t
            s.kind, s.v = 'mem', (base, idx, d)

    def reg(s):
        assert s.kind in ('r', 'r32'), s.text
        return '.' + s.v

    def xr(s):
        assert s.kind in ('x', 'y'), s.text
        return f'.xmm{s.v}'

    def memop(s):
        assert s.kind == 'mem', s.text
        b, i, d = s.v
        if i is None:
            return f'(m .{b} {lean_int(d)})'
        return f'(mi .{b} .{i} {lean_int(d)})'

    def mem(s):
        """A rind `Mem`: a MemOp or the constants."""
        if s.kind == 'sym':
            return f'(.sym (k {lean_int(s.v)}))'
        return f'(.op {s.memop()})'

    def src(s):
        if s.kind == 'r':
            return f'(.reg .{s.v})'
        if s.kind == 'imm':
            return f'(.imm {lean_int(s.v)})'
        if s.kind == 'mem':
            return f'(.mem {s.memop()})'
        raise ValueError(s.text)


ALU = {'addq': 'add', 'adcq': 'adc', 'subq': 'sub', 'sbbq': 'sbb', 'andq': 'and',
       'xorq': 'xor', 'cmpq': 'cmp', 'testq': 'test', 'orq': 'or'}
XBIN = {'paddd': 'paddd', 'pxor': 'pxor', 'pand': 'pand', 'pshufb': 'pshufb', 'por': 'por',
        'movdqa': 'movdqa'}
XSHIFT = {'pslld', 'psrld', 'pslldq', 'psrldq'}
VBIN = {'vpaddd': 'vpaddd', 'vpxor': 'vpxor', 'vpshufb': 'vpshufb', 'vpand': 'vpand'}
VSHIFT = {'vpslld': 'pslld', 'vpsrld': 'psrld'}


def vlen(o):
    return '.l256' if o.kind == 'y' else '.l128'


def decode_bytes(bs):
    """The `.byte` instructions aws-lc's perlasm writes: PALIGNR, PSHUFB, and
    MOVQ r64, xmm."""
    assert bs[0] == 0x66
    i = 1
    rex = 0
    if 0x40 <= bs[i] <= 0x4F:
        rex = bs[i]
        i += 1
    r_ext, b_ext = (rex >> 2) & 1, rex & 1
    w = (rex >> 3) & 1
    if bs[i:i + 3] == [0x0F, 0x3A, 0x0F]:
        modrm, imm = bs[i + 3], bs[i + 4]
        assert modrm >> 6 == 3 and len(bs) == i + 5
        d = r_ext * 8 + ((modrm >> 3) & 7)
        s = b_ext * 8 + (modrm & 7)
        return f'palignr\t${imm},%xmm{s},%xmm{d}'
    if bs[i:i + 3] == [0x0F, 0x38, 0x00]:
        modrm = bs[i + 3]
        assert modrm >> 6 == 3 and len(bs) == i + 4
        d = r_ext * 8 + ((modrm >> 3) & 7)
        s = b_ext * 8 + (modrm & 7)
        return f'pshufb\t%xmm{s},%xmm{d}'
    if bs[i:i + 2] == [0x0F, 0x7E] and w:
        modrm = bs[i + 2]
        assert modrm >> 6 == 3 and len(bs) == i + 3
        x = r_ext * 8 + ((modrm >> 3) & 7)
        g = ['rax', 'rcx', 'rdx', 'rbx', 'rsp', 'rbp', 'rsi', 'rdi'][modrm & 7] if not b_ext else f'r{8 + (modrm & 7)}'
        return f'movq\t%xmm{x},%{g}'
    raise ValueError(bs)


def normalize(s):
    """aws-lc's text of an instruction, `.byte` lines decoded to mnemonics."""
    s = s.strip()
    if s.startswith('.byte'):
        bs = [int(b, 0) for b in s.split(None, 1)[1].split(',')]
        return decode_bytes(bs)
    return s


def tr(s):
    """The Lean term of the instruction `s`."""
    parts = s.split(None, 1)
    mn = parts[0]
    ops = [Op(o) for o in split_ops(parts[1])] if len(parts) > 1 else []
    n = len(ops)
    # Scalar.
    if mn == 'movq' and n == 2:
        a, b = ops
        if a.kind == 'x' and b.kind == 'r':
            return f'.vg (.movqR {b.reg()} {a.xr()})'
        if b.kind == 'r':
            return f'.vg (.mov {b.reg()} {a.src()})'
        if b.kind == 'mem' and a.kind == 'r':
            return f'.vg (.store {b.memop()} {a.reg()})'
    if mn == 'xorl' and n == 2 and ops[0].kind == 'r32' and ops[1].kind == 'r32':
        return f'.vg (.alu32 .xor {ops[1].reg()} (.reg {ops[0].reg()}))'
    if mn in ALU and n == 2:
        a, b = ops
        if b.kind == 'r' and b.v == 'rsp' and a.kind == 'imm' and mn in ('addq', 'subq'):
            return f'.aluRsp .{ALU[mn]} {lean_int(a.v)}'
        return f'.vg (.alu .{ALU[mn]} {b.reg()} {a.src()})'
    if mn == 'mulq' and n == 1:
        return f'.vg (.mul {ops[0].reg()})'
    if mn == 'imulq' and n == 2:
        return f'.vg (.imul {ops[1].reg()} {ops[0].reg()})'
    if mn in ('shrq', 'shlq') and n == 2:
        return f'.vg (.shift .{mn[:3]} {ops[1].reg()} {ops[0].v})'
    if mn == 'shrdq' and n == 3:
        return f'.shrd {ops[2].reg()} {ops[1].reg()} {ops[0].v}'
    if mn == 'decq' and n == 1:
        return f'.dec {ops[0].reg()}'
    if mn == 'incq' and n == 1:
        return f'.inc {ops[0].reg()}'
    if mn == 'leaq' and n == 2:
        a, b = ops
        if a.kind == 'sym':
            return f'.leaSym {b.reg()} (k {lean_int(a.v)})'
        assert b.v != 'rsp'
        return f'.lea {b.reg()} {a.memop()}'
    if mn == 'mulxq' and n == 3:
        return f'.vg (.mulx {ops[2].reg()} {ops[1].reg()} {ops[0].src()})'
    if mn == 'cmovcq' and n == 2:
        return f'.vg (.cmov .b {ops[1].reg()} {ops[0].src()})'
    if mn == 'cmovgq' and n == 2:
        return f'.cmov .g {ops[1].reg()} {ops[0].reg()}'
    if mn == 'pushq' and n == 1:
        return f'.push {ops[0].reg()}'
    if mn == 'popq' and n == 1:
        return f'.pop {ops[0].reg()}'
    # AVX2.
    if mn == 'vzeroupper':
        return 'v .vzeroupper'
    if mn in ('vmovdqa', 'vmovdqu') and n == 2:
        a, b = ops
        if a.kind in 'xy' and b.kind in 'xy' and mn == 'vmovdqa':
            return f'v (.vmovdqa {vlen(a)} {b.xr()} {a.xr()})'
        if mn == 'vmovdqa' and b.kind in 'xy':
            return f'.vmovdqaLoad {vlen(b)} {b.xr()} {a.mem()}'
        if mn == 'vmovdqa' and a.kind in 'xy':
            return f'.vmovdqaStore {vlen(a)} {b.memop()} {a.xr()}'
        if mn == 'vmovdqu' and b.kind in 'xy' and a.kind == 'mem':
            return f'.vg (.vmovdquLoad {vlen(b)} {b.xr()} {a.memop()})'
        if mn == 'vmovdqu' and a.kind in 'xy' and b.kind == 'mem':
            return f'.vg (.vmovdquStore {vlen(a)} {b.memop()} {a.xr()})'
    if mn == 'vbroadcasti128' and n == 2:
        return f'.vg (.vbroadcasti128 {ops[1].xr()} {ops[0].memop()})'
    if mn in VBIN and n == 3:
        a, b, d = ops
        op = VBIN[mn]
        if a.kind in 'xy':
            return f'v (.vbin .{op} {vlen(d)} {d.xr()} {b.xr()} {a.xr()})'
        if a.kind == 'mem':
            return f'.vg (.vbinLoad .{op} {vlen(d)} {d.xr()} {b.xr()} {a.memop()})'
        if a.kind == 'sym':
            return f'.vbinSym .{op} {vlen(d)} {d.xr()} {b.xr()} (k {lean_int(a.v)})'
    if mn in VSHIFT and n == 3:
        a, b, d = ops
        return f'v (.vshift .{VSHIFT[mn]} {vlen(d)} {d.xr()} {b.xr()} {a.v})'
    if mn == 'vpalignr' and n == 4:
        i, a, b, d = ops
        return f'v (.vpalignr {vlen(d)} {d.xr()} {b.xr()} {a.xr()} {i.v})'
    if mn == 'vperm2i128' and n == 4:
        i, a, b, d = ops
        return f'v (.vperm2i128 {d.xr()} {b.xr()} {a.xr()} {i.v})'
    if mn == 'vextracti128' and n == 3:
        i, a, d = ops
        return f'v (.vextracti128 {d.xr()} {a.xr()} {i.v})'
    # SSE.
    if mn == 'movdqa' and n == 2:
        a, b = ops
        if a.kind == 'x' and b.kind == 'x':
            return f'x (.bin .movdqa {b.xr()} {a.xr()})'
        if a.kind == 'mem' and b.kind == 'x':
            return f'.movdqaLoad {b.xr()} {a.memop()}'
        if a.kind == 'sym' and b.kind == 'x':
            return f'.xload .movdqa {b.xr()} {a.mem()}'
        if a.kind == 'x' and b.kind == 'mem':
            return f'.movdqaStore {b.memop()} {a.xr()}'
    if mn == 'movdqu' and n == 2:
        a, b = ops
        if a.kind == 'mem' and b.kind == 'x':
            return f'.vg (.movdquLoad {b.xr()} {a.memop()})'
        if a.kind == 'x' and b.kind == 'mem':
            return f'.vg (.movdquStore {b.memop()} {a.xr()})'
    if mn in XBIN and n == 2:
        a, b = ops
        if a.kind == 'x':
            return f'x (.bin .{XBIN[mn]} {b.xr()} {a.xr()})'
        return f'.xload .{XBIN[mn]} {b.xr()} {a.mem()}'
    if mn in XSHIFT and n == 2:
        return f'x (.shift .{mn} {ops[1].xr()} {ops[0].v})'
    if mn == 'palignr' and n == 3:
        return f'x (.palignr {ops[2].xr()} {ops[1].xr()} {ops[0].v})'
    if mn == 'pinsrb' and n == 3:
        return f'.pinsrb {ops[2].xr()} {ops[1].memop()} {ops[0].v}'
    if mn == 'pextrb' and n == 3:
        return f'.pextrb {ops[2].memop()} {ops[1].xr()} {ops[0].v}'
    if mn == 'pextrq' and n == 3:
        return f'.pextrq {ops[2].reg()} {ops[1].xr()} {ops[0].v}'
    raise ValueError(f'no translation: {s}')


COND = {'je': '.vg .e', 'jz': '.vg .e', 'jne': '.vg .ne', 'jnz': '.vg .ne', 'jb': '.vg .b',
        'jae': '.vg .ae', 'ja': '.a', 'jbe': '.be', 'jg': '.g', 'jge': '.ge', 'jl': '.l', 'jle': '.le'}
