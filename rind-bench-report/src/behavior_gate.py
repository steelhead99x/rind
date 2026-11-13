import contextlib
import importlib.machinery
import importlib.util
import io
import os
import sys

root = sys.argv[1]
loader = importlib.machinery.SourceFileLoader("bench_report", os.path.join(root, "admin", "bench-report"))
spec = importlib.util.spec_from_loader("bench_report", loader)
br = importlib.util.module_from_spec(spec)
loader.exec_module(br)
br.GAPS = os.path.join(root, "benchmarks", "gaps.toml")
args = type("Args", (), {"dir": os.path.join(root, "now"), "previous": os.path.join(root, "then")})()
buf = io.StringIO()
with contextlib.redirect_stdout(buf):
    br.gate(args)
sys.stdout.write(buf.getvalue())
