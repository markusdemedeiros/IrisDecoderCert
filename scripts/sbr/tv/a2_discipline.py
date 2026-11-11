#!/usr/bin/env python3
"""Row-crossing discipline check (M4b, D3 form A): `HfAssemble` crosses a row of `Y` only
through `a2_row_spill`.

The theorem only bounds hf_assemble's accesses by the union it owns (Y[ypos], 24 bytes,
g_temp, q_temp); row boundaries of Y are not theorem facts. The statement docstrings
(Spec.lean HfData / a2_row_spill, Apply.spec) promise that HfAssemble.lean crosses a
row of Y only through `a2_row_spill`. This script checks that promise:

1. `Lb1a0_carve` (the hf_apply_noise window, 32*ceil(m/4) bytes at 8kx + 512i) exists
   and its proof cites `a2_row_spill`.
2. Every other declaration in HfAssemble.lean whose text both carves (`carve`) and names
   the Y block (`0x7930`, `19456`, `19480` or `arg0`) either cites `a2_row_spill` or is in IN_ROW (carves
   whose windows are proved to stay inside one 512-byte row, e.g. `Lb01d_carve`:
   8m bytes at 8kx + 512i with kx + m <= 64).

Exit 0 if both hold, 1 otherwise.
"""
import re
import sys
import os

ROOT = os.environ.get("SBR_ROOT") or os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
F = os.path.join(ROOT, "Kraken/X64/Examples/Sbr/HfAssemble.lean")
# the proof may be split into modules: HfAssemble.lean plus HfAssemble/*.lean
import glob
FS = [F] + sorted(glob.glob(os.path.join(ROOT, "Kraken/X64/Examples/Sbr/HfAssemble/*.lean")))
IN_ROW = {"Lb01d_carve", "Lb01d_carve'"}  # Lb01d_carve': wrapper of Lb01d_carve (8m bytes at 8kx + 512r, kx + m <= 64)

src = "\n".join(open(f).read() for f in FS)
# split into top-level declarations
starts = [m.start() for m in re.finditer(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma|def|abbrev)\s", src, re.M)]
starts.append(len(src))
decls = {}
for a, b in zip(starts, starts[1:]):
    text = src[a:b]
    m = re.match(r"(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:theorem|lemma|def|abbrev)\s+(\S+)", text)
    if m:
        decls[m.group(1)] = text

rc = 0
if "Lb1a0_carve" not in decls:
    print("FAIL a2: Lb1a0_carve not found in HfAssemble.lean")
    rc = 1
elif "a2_row_spill" not in decls["Lb1a0_carve"]:
    print("FAIL a2: Lb1a0_carve does not cite a2_row_spill")
    rc = 1
else:
    print("ok a2: Lb1a0_carve cites a2_row_spill")

for name, text in decls.items():
    if name == "Lb1a0_carve" or name in IN_ROW:
        continue
    # Y markers: the Spec-level base (0x7930), the row-block sizes (19456, merged 19480),
    # and HfAssemble's internal layout, which places Y at `arg0` (Y1).
    if "carve" in text and re.search(r"0x7930|19456|19480|\barg0\b", text):
        if "a2_row_spill" in text:
            print(f"ok a2: {name} cites a2_row_spill")
        else:
            print(f"FAIL a2: {name} carves the Y block without a2_row_spill (add it, or prove in-row and list in IN_ROW)")
            rc = 1
sys.exit(rc)
