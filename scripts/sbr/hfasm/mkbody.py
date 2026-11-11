#!/usr/bin/env python3
"""Emit the Lean `body` text for sbr_hf_assemble with cut labels."""
import re, sys

import os
SRC = os.path.join(os.environ.get("HFASM_PROG_DIR", "."), "sbr_hf_assemble.s")   # the disassembly; output: body.s on stdout
P = "sbr_hf_assemble"
lines = open(SRC).read().split("\n")

# extra cut labels: source line number (1-indexed) -> label (placed before that line)
CUTS = {
    10: "p1", 22: "p2", 33: "r0",
    49: "r1", 58: "r2", 67: "r3", 76: "r4", 85: "r5", 94: "r6", 103: "r7", 112: "r8",
    48: "r0c", 57: "r1c", 66: "r2c", 75: "r3c", 84: "r4c", 93: "r5c", 102: "r6c", 111: "r7c",
    1145: None,
}
# e-copy loops: setup / call2 / tail / restore for k = 0..7
loop_heads = [155, 194, 233, 272, 311, 350, 389, 428]  # label lines (.La970 ...)
for k, h in enumerate(loop_heads):
    CUTS[h - 12 if k < 7 else h - 13] = f"s{k}"
    CUTS[h + 6] = f"c{k}"      # after first call
    CUTS[h + 10] = f"d{k}"     # after second call
    if k < 7:
        CUTS[h + 17] = f"x{k}"  # restore after loop
# fix the setups: compute exactly from text below instead
CUTS = {k: v for k, v in CUTS.items() if v}
MORE = {
    460: "m1", 473: "m2", 489: "m3",
    564: "g1", 603: "n2", 647: "a1",
    690: "v1", 701: "v2", 720: "w1", 732: "w2",
    753: "y1", 765: "y2", 778: "y3", 790: "y4", 796: "y5", 808: "y6", 814: "y7",
    826: "y8", 832: "y9", 844: "y10", 850: "y11", 862: "y12", 868: "y13", 880: "y14",
}
CUTS.update(MORE)

RIP = {470: "LCPI17_12", 521: "LCPI17_11"}
for base in (489, 590, 650):
    for j, l in enumerate(["LCPI17_6", "LCPI17_7", "LCPI17_8", "LCPI17_9", "LCPI17_10"] * 2):
        RIP[base + j] = l

out = []
for n, ln in enumerate(lines, 1):
    if n in CUTS:
        out.append(f"{P}.{CUTS[n]}:")
    s = ln
    m = re.match(r"^(\.L[0-9a-f]+):$", s)
    if m:
        out.append(f"{P}.{m.group(1)[1:]}:")
        continue
    if s == "start:":
        out.append(f"{P}:")
        continue
    if s == "done:":
        break
    s = re.sub(r"\s\.L([0-9a-f]+)$", lambda mm: f" {P}.L{mm.group(1)}", s)
    if n in RIP:
        assert "0x0(%rip)" in s, (n, s)
        s = s.replace("0x0(%rip)", f"{RIP[n]}(%rip)")
    if s.strip() == "jmp done":
        out.append(f"{P}.done:")
        s = "    ret"
    out.append(s)
while out and out[-1].strip() in ("", "int3"):
    out.pop()
print("\n".join(out))
