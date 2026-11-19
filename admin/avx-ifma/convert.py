import glob
import os
import pathlib
import re
import subprocess
import sys

"""Re-encodes pyca/verified-garbage's AVX-512VL/IFMA x86_64 routines as VEX AVX-IFMA.

usage: convert.py REPO NAME CONVERTED_SIBLINGS(comma separated)

Writes rind/src/low/x86_64/avx_ifma/NAME.rs. Needs binutils (as, objdump, nm).
Every EVEX `vpmadd52luq`, `vpmadd52huq`, and `vpxorq` on ymm0 to ymm15 becomes its
`{vex}` form; a register above ymm15 is renamed onto a ymm register dead across its
whole live range, or else spilled around that range to a stack frame the routine allocates (no red zone, so Windows is safe), zeroed again before
`ret`; 512-bit zeroing becomes `vzeroall`. Anything else EVEX fails the run.
"""
REPO = sys.argv[1]
V = REPO + "/rind/src/low/x86_64/vg/"
name = sys.argv[2]
CONV = set(sys.argv[3].split(","))
WORK = os.environ.get("WORK", ".")
os.chdir(WORK)
src = pathlib.Path(V + name + ".rs").read_text()
m = re.search(r'naked_asm!\(\s*r#"(.*?)"#,(.*?)\n    \)\n\}', src, re.DOTALL)
body, tail = m.group(1), m.group(2)
syms = dict(re.findall(r"(\w+) = sym super::(\w+)::\w+", tail))
sig = (
    re.search(r'(pub\(crate\) unsafe extern "sysv64" fn \w+\([^)]*\)[^{]*)\{', src)
    .group(1)
    .strip()
)
docs = [l for l in src.splitlines() if l.startswith("///")]
# A function that spills allocates its frame with `lea` below the stack pointer, on
# top of whatever its callees use, so each contract's figure is VG's plus the sum of
# the frames the converted functions allocate. admin/avx-ifma/generate runs the
# converter twice, so the second pass has every function's frame size.
spill_max = sum(int(pathlib.Path(f).read_text()) for f in glob.glob("spill_*"))
docs = [
    re.sub(
        r"the (\d+) bytes of stack below it",
        lambda m: f"the {int(m.group(1)) + spill_max} bytes of stack below it",
        l,
    )
    for l in docs
]
docs = [
    re.sub(
        r"The CPU must support the .*",
        "The CPU must support the `avx`, `avx2`, `bmi1`, `bmi2`, `adx`, and `avxifma` target features.",
        l,
    )
    if "CPU must support" in l
    else l
    for l in docs
]
b2 = body
for k in syms:
    b2 = b2.replace("{" + k + "}", "stub_" + k)
stubs = "".join(f"stub_{k}: ret\n" for k in syms)
pathlib.Path(f"w_{name}.s").write_text(
    ".text\n.intel_syntax noprefix\n" + b2 + "\n" + stubs
)
subprocess.check_call(["as", f"w_{name}.s", "-o", f"w_{name}.o"])
dis = subprocess.check_output(["objdump", "-d", "-M", "att", f"w_{name}.o"]).decode()
ins = []
for l in dis.splitlines():
    mm = re.match(r"\s*([0-9a-f]+):\t([0-9a-f ]+?)\s*\t(.*)$", l)
    if mm:
        ins.append([int(mm.group(1), 16), mm.group(2).split(), mm.group(3).strip()])
    else:
        mm = re.match(r"\s*([0-9a-f]+):\t([0-9a-f ]+)$", l)
        if mm and ins:
            ins[-1][1].extend(mm.group(2).split())
# cut the stubs
first_stub = (
    min(
        int(l.split()[0].rstrip(":"), 16)
        for l in subprocess.check_output(["nm", "-n", f"w_{name}.o"])
        .decode()
        .splitlines()
        for _ in [0]
        if False
    )
    if False
    else None
)
nm = {
    l.split()[2]: int(l.split()[0], 16)
    for l in subprocess.check_output(["nm", f"w_{name}.o"]).decode().splitlines()
    if l.split()[2].startswith("stub_")
}
lim = min(nm.values()) if nm else 1 << 60
# trim padding between body end and first stub: body ends at last ret before lim
ins = [x for x in ins if x[0] < lim]
while ins and ins[-1][2].split()[0] not in ("ret", "jmp"):
    ins.pop()
stubaddr = {v: k[5:] for k, v in nm.items()}
addr2i = {a: i for i, (a, _, _) in enumerate(ins)}
N = len(ins)


def regs(t):
    return [int(x) for x in re.findall(r"%[xy]mm(\d+)", t)]


def rw(t):
    op = t.split()[0]
    if not op.startswith("v") or not re.search(r"[xyz]mm", t):
        return set(), set()
    if op == "vzeroupper" or op == "vzeroall":
        return set(), set()
    args = t.split(None, 1)[1].split("#")[0]
    ops = [o.strip() for o in re.split(r",(?![^()]*\))", args)]
    dst = ops[-1]
    rd = set()
    wr = set()
    for s in ops[:-1]:
        rd |= set(regs(s))
    mm = re.match(r"%[xy]mm(\d+)$", dst)
    if mm:
        d = int(mm.group(1))
        wr.add(d)
        if op.startswith("vpmadd52"):
            rd.add(d)
        if op in ("vpxor", "vpxorq") and len(set(ops)) == 1:
            rd.discard(d)
        if op in ("vpblendd", "vpblendvb"):
            pass
    else:
        rd |= set(regs(dst))
    return rd, wr


RW = [rw(t) for _, _, t in ins]
succ = []
for i, (a, b, t) in enumerate(ins):
    op = t.split()[0]
    s = []
    if op.startswith("j"):
        s.append(addr2i[int(t.split()[1], 16)])
        if op != "jmp":
            s.append(i + 1)
    elif op == "ret":
        pass
    else:
        if i + 1 < N:
            s.append(i + 1)
    succ.append(s)
live_in = [set() for _ in range(N)]
ch = True
while ch:
    ch = False
    for i in range(N - 1, -1, -1):
        lo = set()
        for s in succ[i]:
            lo |= live_in[s]
        rd, wr = RW[i]
        li = (lo - wr) | rd
        if li != live_in[i]:
            live_in[i] = li
            ch = True
live_out = [
    set().union(*[live_in[s] for s in succ[i]]) if succ[i] else set() for i in range(N)
]
HIGH = sorted({r for rd, wr in RW for r in rd | wr if r >= 16})
mapping = [{} for _ in range(N)]
spills = {}
spills_after = {}
slot = {}
jt = {addr2i[int(t.split()[1], 16)] for a, b, t in ins if t.split()[0].startswith("j")}
for hi in HIGH:
    idx = [i for i in range(N) if hi in RW[i][0] | RW[i][1]]
    webs = []
    cur = None
    for i in idx:
        rd, wr = RW[i]
        if hi in wr and hi not in rd:
            cur = [i]
            webs.append(cur)
        else:
            assert cur is not None, (name, hi, i, ins[i][2])
            cur.append(i)
    slot[hi] = len(slot) + 1
    for w in webs:
        s, e = w[0], w[-1]
        for i in range(s, e + 1):
            op = ins[i][2].split()[0]
            assert not op.startswith("j") and op != "call", (name, ins[i])
            if i > s:
                assert i not in jt, (name, "jump target inside web")
        used = set()
        for i in range(s, e + 1):
            used |= RW[i][0] | RW[i][1]
            used |= set(mapping[i].values())
        cand = None
        for p in range(16):
            if p in used:
                continue
            if any(p in live_in[i] for i in range(s, e + 1)) or p in live_out[e]:
                continue
            cand = p
            break
        if cand is None:
            for p in range(16):
                if p in used:
                    continue
                cand = p
                spills.setdefault(s, []).append((p, hi))
                spills_after.setdefault(e, []).append((p, hi))
                break
        assert cand is not None, (name, hi, s, e)
        for i in w:
            mapping[i][hi] = cand
nslots = len(slot)
assert not spills or 0 not in jt, (name, "entry is a jump target")
print(
    name,
    "high regs",
    HIGH,
    "spills",
    sum(len(v) for v in spills.values()),
    file=sys.stderr,
)
rets = [i for i, x in enumerate(ins) if x[2].startswith("ret")]
out = []
z = False
nv = 0
LP = name[3:] + "_"
FRAME = 32 * nslots if spills else 0
pathlib.Path(f"spill_{name}").write_text(str(FRAME))
if FRAME:
    out.append(f"lea -{FRAME}(%rsp), %rsp")
for i, (a, b, t) in enumerate(ins):
    out.append(f".L{LP}{a:x}:")
    for p, hi in spills.get(i, []):
        out.append(f"vmovdqu %ymm{p}, {(slot[hi] - 1) * 32}(%rsp)")
    op = t.split()[0]
    if op.startswith("j"):
        out.append(f"{op} .L{LP}{int(t.split()[1], 16):x}")
    elif op == "lea" and "<stub_" in t:
        sm = re.search(r"<stub_(\w+)>", t)
        reg = t.split("#")[0].strip().split(",")[-1]
        out.append("lea {" + sm.group(1) + "}(%rip), " + reg)
    elif op == "call":
        tgt = int(t.split()[1].split()[0], 16)
        out.append("call {" + stubaddr[tgt] + "}")
    elif op == "ret":
        if spills:
            out.append("vpxor %ymm0,%ymm0,%ymm0")
            out += [f"vmovdqu %ymm0,{k * 32}(%rsp)" for k in range(nslots)]
            out.append(f"lea {FRAME}(%rsp), %rsp")
        out.append(".byte 0xc3")
    elif b[0] == "62":
        tt = t.split("#")[0].strip()
        if op == "vpxorq" and "zmm" in tt:
            if not z:
                out.append("vzeroall")
                z = True
            continue
        for hi, lo in mapping[i].items():
            tt = re.sub(rf"%ymm{hi}\b", f"%ymm{lo}", tt)
        assert not re.search(r"ymm(1[6-9]|[23]\d)|zmm|\{k", tt), (name, tt)
        if tt.startswith("vpxorq"):
            tt = tt.replace("vpxorq", "vpxor", 1)
        out.append("{{vex}} " + tt)
        nv += 1
    else:
        assert not mapping[i], t
        out.append(".byte " + ",".join("0x" + x for x in b))
    for p, hi in spills_after.get(i, []):
        out.append(f"vmovdqu {(slot[hi] - 1) * 32}(%rsp), %ymm{p}")
symlines = ""
for k, v in syms.items():
    path = f"super::{k}::{k}" if k in CONV else f"super::super::vg::{v}::{k}"
    symlines += f"        {k} = sym {path},\n"
rs = f'''// SPDX-License-Identifier: Apache-2.0 OR BSD-3-Clause
// @generated by admin/avx-ifma/convert.py from rind/src/low/x86_64/vg/{name}.rs.
//
// pyca/verified-garbage's `{name}` with its AVX-512VL/IFMA instructions
// re-encoded as VEX AVX-IFMA, one for one, and its ymm16 to ymm31
// accumulators renamed onto free ymm0 to ymm15 or spilled to a 96-byte frame.
// Not VG's proven bytes: see the module docs.
//
// Its `# Safety` contract is `vg::{name}`'s, with `avx`, `avx2`, `bmi2`, `adx`,
// and `avx_ifma` as the CPU features in place of AVX-512's.

{chr(10).join(docs)}
#[unsafe(naked)]
{sig} {{
    core::arch::naked_asm!(
        r#"{chr(10).join(out)}
.p2align 6"#,
{symlines}        options(att_syntax),
    )
}}
'''
pathlib.Path(f"{REPO}/rind/src/low/x86_64/avx_ifma/{name}.rs").write_text(rs)
print(name, "ok vex", nv, file=sys.stderr)
