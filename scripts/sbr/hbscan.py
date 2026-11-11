#!/usr/bin/env python3
"""Heartbeat discipline for the SBR proofs.
1. Every generated `set_option maxHeartbeats N in` before `theorem blk_<id>` in
   Sbr/Apply/*.lean has N = baseline/hb_table.txt[id] (default 400000). hb_table.txt is
   the generator's per-block table.
2. Every other maxHeartbeats / maxRecDepth option under Sbr/ is in baseline/hb_baseline.txt
   (file, option, value, count): no new option, no higher value. `--record` rewrites it.
Exit 1 on any violation."""
import collections, glob, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("SBR_ROOT") or os.path.abspath(os.path.join(HERE, "..", ".."))
HB = os.path.join(HERE, "baseline", "hb_table.txt")
BASE = os.path.join(HERE, "baseline", "hb_baseline.txt")
OPT = re.compile(r"^\s*set_option (maxHeartbeats|maxRecDepth) (\d+)")

hb = {}
for line in open(HB):
  p = line.split()
  if len(p) >= 2:
    hb[p[0]] = int(p[1])

bad, nblk = [], 0
other = collections.Counter()  # (file, option, value) -> count
for f in sorted(glob.glob(os.path.join(ROOT, "Kraken/X64/Examples/Sbr/**/*.lean"), recursive=True)):
  rel = os.path.relpath(f, ROOT)
  # a proof split into modules (HfAssemble/Base.lean, Part*.lean) counts as its parent file
  rel = re.sub(r"/HfAssemble/[^/]+\.lean$", "/HfAssemble.lean", rel)
  L = open(f).read().split("\n")
  for i, l in enumerate(L):
    m = OPT.match(l)
    if not m:
      continue
    opt, n = m[1], int(m[2])
    j = i + 1
    while j < len(L) and OPT.match(L[j]):
      j += 1
    mm = re.match(r"\s*(?:private )?theorem blk_(\S+)", L[j]) if j < len(L) else None
    if opt == "maxHeartbeats" and mm and "/Apply/" in rel:
      nblk += 1
      exp = hb.get(mm[1], 400000)
      if n != exp:
        bad.append(f"{rel}:{i+1}: blk_{mm[1]} maxHeartbeats {n} != hb_table {exp}")
    else:
      other[(rel, opt, n)] += 1

if "--record" in sys.argv:
  with open(BASE, "w") as o:
    for (rel, opt, n), c in sorted(other.items()):
      o.write(f"{rel} {opt} {n} {c}\n")
  print(f"recorded {sum(other.values())} options in {BASE}")
  sys.exit(0)

base = collections.Counter()
for line in open(BASE):
  rel, opt, n, c = line.split()
  base[(rel, opt, int(n))] = int(c)
for (rel, opt, n), c in sorted(other.items()):
  if c > base.get((rel, opt, n), 0):
    bad.append(f"{rel}: {c - base.get((rel, opt, n), 0)} new `set_option {opt} {n}` (not in baseline)")
for b in bad:
  print("FAIL", b)
print(f"hbscan: {nblk} blk options checked against hb_table, {sum(other.values())} other options "
      f"against baseline, {len(bad)} violations")
sys.exit(1 if bad else 0)
