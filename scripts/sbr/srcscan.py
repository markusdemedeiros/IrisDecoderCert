#!/usr/bin/env python3
"""Source scan of Kraken/: `sorry`, `admit`, `native_decide`, `bv_decide` and `axiom`
declarations, and the options and attributes that bypass or weaken kernel checking
(`debug.*` options such as `debug.skipKernelTC`, `implemented_by`, `extern`, `unsafe`),
outside comments and strings. Kraken/X64/Examples/Sbr/ must have none; the
rest of Kraken/ (upstream examples and benchmarks) must have nothing beyond
baseline/srcscan_baseline.txt. Run from the repository root. Exit 1 on a violation."""
import os, re, sys
bad = []
pat = re.compile(r"\b(sorry|admit|native_decide|bv_decide)\b|^\s*(private\s+|protected\s+)?axiom\s"
                 r"|\bdebug\.\w|\bimplemented_by\b|@\[\s*extern\b|\bunsafe\b")
for d, _, fs in os.walk("Kraken"):
  for f in fs:
    if not f.endswith(".lean"):
      continue
    p = os.path.join(d, f)
    txt = open(p, encoding="utf-8").read()
    # strip comments (nested block comments and line comments)
    out, i, depth = [], 0, 0
    while i < len(txt):
      if txt.startswith("/-", i):
        depth += 1; i += 2; continue
      if depth and txt.startswith("-/", i):
        depth -= 1; i += 2; continue
      if depth:
        out.append("\n" if txt[i] == "\n" else " "); i += 1; continue
      if txt.startswith("--", i):
        j = txt.find("\n", i); j = len(txt) if j < 0 else j
        out.append(" " * (j - i)); i = j; continue
      if txt[i] == '"':
        j = i + 1
        while j < len(txt) and txt[j] != '"':
          j += 2 if txt[j] == "\\" else 1
        out.append('"' + " " * (j - i - 1) + '"'); i = j + 1; continue
      out.append(txt[i]); i += 1
    for n, line in enumerate("".join(out).split("\n"), 1):
      if pat.search(line):
        bad.append(f"{p}:{n}: {line.strip()[:100]}")
# Sbr/: no hits at all. Elsewhere in Kraken/ (upstream examples, benchmarks): no hit beyond
# the baseline recorded at M5 start (file + matched text; `--record` rewrites it).
import collections
BASE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "baseline", "srcscan_baseline.txt")
key = lambda b: b.split(":")[0] + " " + b.split(":", 2)[2].strip()
if "--record" in sys.argv:
  open(BASE, "w").write("".join(key(b) + "\n" for b in bad if "/Examples/Sbr/" not in b))
base = collections.Counter(l.rstrip("\n") for l in open(BASE))
fails = [b for b in bad if "/Examples/Sbr/" in b]
cur = collections.Counter(key(b) for b in bad if "/Examples/Sbr/" not in b)
fails += [f"{k} (x{c - base[k]} beyond baseline)" for k, c in cur.items() if c > base[k]]
for b in fails:
  print("FAIL", b)
print(f"srcscan: {len(bad)} hits, {len(bad) - len(fails)} in the upstream baseline, {len(fails)} new or in Sbr/")
sys.exit(1 if fails else 0)
