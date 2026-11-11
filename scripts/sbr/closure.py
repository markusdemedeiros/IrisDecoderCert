#!/usr/bin/env python3
"""Which srcscan-baseline files are in the transitive import closure of the given
modules (source `import` lines; no build). Usage: closure.py Mod1 Mod2 ..."""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("SBR_ROOT") or os.path.abspath(os.path.join(HERE, "..", ".."))
BASE = os.path.join(HERE, "baseline", "srcscan_baseline.txt")

def path(mod):
  p = os.path.join(ROOT, *mod.split(".")) + ".lean"
  return p if os.path.exists(p) else None

seen, todo = set(), [m for m in sys.argv[1:] if path(m)]
while todo:
  m = todo.pop()
  if m in seen:
    continue
  seen.add(m)
  for line in open(path(m), encoding="utf-8"):
    mm = re.match(r"^\s*import\s+(.+)", line)
    if mm:
      for d in mm[1].split():
        if path(d) and d not in seen:
          todo.append(d)
files = sorted({l.split()[0] for l in open(BASE) if l.strip()})
inclos = [f for f in files if f[:-5].replace("/", ".") in seen]
print(f"import closure of {' '.join(sys.argv[1:])}: {len(seen)} project modules; "
      f"srcscan-baseline files in it: {inclos if inclos else 'none'} (of {len(files)}: {', '.join(files)})")
