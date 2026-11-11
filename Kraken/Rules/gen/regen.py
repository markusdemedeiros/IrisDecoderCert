#!/usr/bin/env python3
"""Regenerate the generated rule files under Kraken/Rules/ (see README.md).

Usage, from the repository root:
  python3 Kraken/Rules/gen/regen.py           # rewrite the three files
  python3 Kraken/Rules/gen/regen.py --check   # exit 1 if any file is stale

Each file is `<family>_header.lean.in` + generator output + `<family>_footer.lean.in`
(PackedSse's generator reads its header itself and has no footer). The one-line
rule lists go to Kraken/Rules/gen/out/ (not checked in; for review only).
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
RULES = os.path.dirname(HERE)


def run(*args, stdout=None):
  subprocess.run([sys.executable, *args], check=True, stdout=stdout)


def read(path):
  with open(path) as f:
    return f.read()


def build_int(tmp, lists):
  body = os.path.join(tmp, "int_body.lean")
  run(os.path.join(HERE, "gen_int.py"), body, os.path.join(lists, "int_rules.txt"))
  return read(os.path.join(HERE, "int_header.lean.in")) + read(body) + read(
      os.path.join(HERE, "int_footer.lean.in"))


def build_sse(tmp, lists):
  out = os.path.join(tmp, "PackedSse.lean")
  run(os.path.join(HERE, "gen_sse.py"), os.path.join(HERE, "sse_header.lean.in"), out,
      os.path.join(lists, "sse_rules.tsv"), stdout=subprocess.DEVNULL)
  return read(out)


def build_float(tmp, lists):
  body = os.path.join(tmp, "float_body.lean")
  with open(body, "w") as f:
    run(os.path.join(HERE, "gen_float.py"), stdout=f)
  return read(os.path.join(HERE, "float_header.lean.in")) + read(body) + read(
      os.path.join(HERE, "float_footer.lean.in"))


FAMILIES = [("IntMisc.lean", build_int), ("PackedSse.lean", build_sse),
            ("ScalarFloat.lean", build_float)]


def main():
  check = "--check" in sys.argv[1:]
  lists = os.path.join(HERE, "out")
  os.makedirs(lists, exist_ok=True)
  stale = []
  with tempfile.TemporaryDirectory() as tmp:
    for name, build in FAMILIES:
      text = build(tmp, lists)
      path = os.path.join(RULES, name)
      if check:
        if not os.path.exists(path) or read(path) != text:
          stale.append(name)
      else:
        with open(path, "w") as f:
          f.write(text)
        print(f"wrote {os.path.relpath(path)}")
  if stale:
    print("stale (run regen.py): " + ", ".join(stale))
    sys.exit(1)


if __name__ == "__main__":
  main()
