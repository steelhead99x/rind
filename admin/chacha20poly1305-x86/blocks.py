"""aws-lc's x86_64 ChaCha20-Poly1305 text, as `admin/import-aws-lc` writes it,
split into basic blocks: each label's instructions up to the next label,
`.align`, or jump, named by the label and, after an `.align` or a jump
within it, `+k`."""
import re

JCC = {'ja','jae','jb','jbe','je','jz','jne','jnz','jg','jge','jl','jle'}

class Block:
    def __init__(s, name, start):
        s.name = name; s.lines = []; s.term = None; s.start = start; s.aligns = []
    def __repr__(s):
        return f'{s.name}[{len(s.lines)}]{s.term}'

def parse(path):
    blocks = []; cur = None; last_label = 'entry'; k = 0
    def new(name, ln):
        nonlocal cur
        cur = Block(name, ln); blocks.append(cur)
    new('entry', 0)
    for ln, raw in enumerate(open(path), 1):
        s = raw.split('#')[0].strip() if not raw.strip().startswith('.byte') else raw.strip()
        if not s or s.startswith('.cfi') or s.startswith('#'):
            continue
        m = re.match(r'^([A-Za-z_.][\w.]*):$', s)
        if m:
            name = m.group(1).replace('.Lchacha_poly_', '')
            if cur.lines or cur.term or cur.aligns:
                prev = cur
                new(name, ln)
                if prev.term is None: prev.term = ('fall', name)
            else:
                # A label with no instructions of its own names the next block too.
                cur.aliases = getattr(cur, 'aliases', []) + [name]
            last_label = name; k = 0
            continue
        if s.startswith('.align'):
            if cur.lines or cur.term:
                prev = cur; k += 1; new(f'{last_label}+{k}', ln)
                if prev.term is None: prev.term = ('fall', cur.name)
            cur.aligns.append(s); continue
        if s.startswith('.') and not s.startswith('.byte'):
            continue
        if cur.term is not None:
            k += 1; new(f'{last_label}+{k}', ln)
        op = s.split()[0]
        if op in JCC or op == 'jmp':
            tgt = s.split()[1].replace('.Lchacha_poly_', '')
            cur.term = (op, tgt)
        elif s == '.byte\t0xf3,0xc3' or s.startswith('.byte\t0xf3,0xc3'):
            cur.lines.append((ln, s)); cur.term = ('ret',)
        else:
            cur.lines.append((ln, s))
    # resolve aliases
    alias = {}
    for b in blocks:
        alias[b.name] = b.name
        for a in getattr(b, 'aliases', []): alias[a] = b.name
    for i, b in enumerate(blocks):
        if b.term is None and i + 1 < len(blocks): b.term = ('fall', blocks[i+1].name)
        if b.term and b.term[0] != 'ret':
            b.term = (b.term[0], alias.get(b.term[1], b.term[1]))
    return blocks

