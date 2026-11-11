#!/usr/bin/env python3
"""Build a target's local imports one at a time through the experiment cap.

The global lock is released between modules so the other experiment can
continue testing. Each Lake call has at most one uncached local Lean module.
"""
from pathlib import Path
import re
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[1]
cap = root / "tools" / "bounded-build"
target = sys.argv[1] if len(sys.argv) > 1 else "Kraken.X64.Examples.Sbr.SessionBin.Top"
out = root / ".lake" / "client-build"
out.mkdir(parents=True, exist_ok=True)
seen, modules = set(), []


def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = root / (module.replace(".", "/") + ".lean")
    if not source.exists():
        return
    for line in source.read_text().splitlines():
        match = re.match(r"\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", line)
        if match:
            visit(match.group(1))
    modules.append(module)


visit(target)
print(f"Building {len(modules)} modules for {target}", flush=True)
for index, module in enumerate(modules):
    log = out / (module + ".log")
    start = time.monotonic()
    with log.open("w") as stream:
        result = subprocess.run([str(cap), "lake", "build", module], cwd=root,
                                stdout=stream, stderr=subprocess.STDOUT)
    print(f"{index + 1}/{len(modules)} {module}: exit={result.returncode} "
          f"elapsed={time.monotonic() - start:.1f}s", flush=True)
    contents = log.read_text()
    if result.returncode or "declaration uses 'sorry'" in contents:
        print(contents[-12000:], flush=True)
        sys.exit(result.returncode or 1)
