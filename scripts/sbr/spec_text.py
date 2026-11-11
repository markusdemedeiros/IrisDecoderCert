#!/usr/bin/env python3
"""Text checks of SessionSpec.lean (run by ci.sh, step `spec`, after SpecCheck.lean).

1. The generated part: `parse/init/foot.py --spec` (`EV`, `ElemS`) appears verbatim in
   SessionSpec.lean.
2. The quoted headline: the statement of `sbr_session_safe` quoted in SessionSpec.lean's module
   docstring (the code block starting `theorem sbr_session_safe`) equals the statement in
   SessionBin/Top.lean, from `theorem sbr_session_safe` up to its `:=`, whitespace-normalized.

Prints one line per check; exits 1 if either fails.
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
SBR = os.path.join(HERE, "../../Kraken/X64/Examples/Sbr")


def norm(s):
  return " ".join(s.split())


def main():
  spec = open(os.path.join(SBR, "SessionSpec.lean")).read()
  ok = True
  foot = subprocess.run([sys.executable, os.path.join(HERE, "parse/init/foot.py"), "--spec"],
                        capture_output=True, text=True, check=True).stdout
  if foot in spec:
    print("spec: SessionSpec.lean contains `foot.py --spec`")
  else:
    print("spec: FAIL: SessionSpec.lean does not contain `foot.py --spec` (EV, ElemS)")
    ok = False
  m = re.search(r"^```\n(theorem sbr_session_safe\b.*?)\n```$", spec, re.S | re.M)
  top = open(os.path.join(SBR, "SessionBin/Top.lean")).read()
  t = re.search(r"^theorem sbr_session_safe\b(.*?):=", top, re.S | re.M)
  if not m or not t:
    print("spec: FAIL: the quoted or the actual statement of `sbr_session_safe` was not found")
    ok = False
  elif norm(m.group(1)) == norm("theorem sbr_session_safe" + t.group(1)):
    print("spec: the statement quoted in SessionSpec.lean equals SessionBin/Top.lean's")
  else:
    print("spec: FAIL: the statement of `sbr_session_safe` quoted in SessionSpec.lean differs "
          "from SessionBin/Top.lean's:")
    print("  quoted: " + norm(m.group(1)))
    print("  actual: " + norm("theorem sbr_session_safe" + t.group(1)))
    ok = False
  sys.exit(0 if ok else 1)


if __name__ == "__main__":
  main()
