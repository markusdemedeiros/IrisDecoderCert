#!/usr/bin/env python3
"""Labelled program text of `read_sbr_grid` for `Grid.lean`.

Input: the `to_program` text of `read_sbr_grid` (aacsbr.rela.o) and the GNU objdump listing
of the same range (for the instruction addresses). Output (stdout): the body of the Lean
`parse(...)`, one block per label:

  * labels `.LXXXX` become `read_sbr_grid.LXXXX` (XXXX = address in aacsbr.rela.o);
  * extra labels at the jump-table targets and at the cut points CUTS;
  * `0x0(%rip)` operands get their symbol (relocations listed in NOTES below);
  * the `ret` is kept in place, behind the label `read_sbr_grid.done`; the trailing
    `done: nop` of `to_program` is dropped.

Usage: gen.py PROG.s OBJDUMP.txt [CUT...] > body.s   (no CUT: DEFAULT_CUTS)
"""
import re
import sys

P = "read_sbr_grid"
BASE = 0x4400
# rip-relative operands, by address (aacsbr.rela.o), from the relocations.
RIP = {
    0x447b: "read_sbr_grid_jt",   # .rodata+0x0: the switch's jump table (no symbol)
    0x44d7: "L_str_25", 0x45cd: "ceil_log2", 0x4762: "L_str_26", 0x4875: "ceil_log2",
    0x4c55: "ceil_log2", 0x4ebd: "L_str_28", 0x5073: "L_str_29", 0x50e8: "L_str_3",
    0x50ef: "L_str_27", 0x50f6: "L_str_5",
}
# jump-table targets (the four frame classes) and cut points.
JT = [0x448b, 0x4773, 0x44e3, 0x46a2]
# the cut points of the proof (block entries that get their own assertion): the loop heads and
# the blocks whose verification conditions are too large otherwise.
DEFAULT_CUTS = """
440b 4419 4422 442b 4434 443a 4478 4ddd 4ed3 510e
450e 4539 4548 4556 45a5 45bf 45d8 460b 4621 4662 4694 46cd 4701 4726 474b 4798 47bd 47d3
47ea 47fb 4806 483b 484f 486a 4880 48b3 48f3 4905 4948 4979 499b 49cf 49e9 4a1d 4a37 4a6b
4a85 4ab9 4ad3 4b07 4b21 4b55 4b6b 4b9f 4bdb 4be6 4c1b 4c2f 4c53 4c5c 4c93 4cfb 4d08 4d15
4d24 4d37 4d4a 4d59 4d6b 4d80 4db6 4dbf 4dcb 4e32 4e64 4f11 4f22 4f27 4f93 4fed 5002 5018
502d 5043 5058 506a
""".split()
CUTS = [int(x, 16) for x in (sys.argv[3:] or DEFAULT_CUTS)]


def main():
  prog = [l.rstrip("\n") for l in open(sys.argv[1])]
  dump = []
  for l in open(sys.argv[2]):
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m:
      dump.append((int(m[1], 16), m[2].strip()))
  out, k = [], 0
  extra = set(JT) | set(CUTS)
  for l in prog:
    if not l.strip():
      continue
    if not l.startswith(" "):
      lab = l[:-1]
      if lab == "done":
        break
      out.append((None, f"{P}:" if lab == "start" else f"{P}.{lab[1:]}:" if lab.startswith(".L")
                  else f"{P}.{lab}:"))
      continue
    a, t = dump[k]
    k += 1
    ins = l.strip()
    if a in extra and not (out and out[-1][0] is None and out[-1][1] == f"{P}.L{a:x}:"):
      out.append((None, f"{P}.L{a:x}:"))
    if a in RIP:
      ins = ins.replace("0x0(%rip)", f"{RIP[a]}(%rip)")
    if ins == "jmp done":
      out.append((None, f"{P}.done:"))
      ins = "ret"
    ins = re.sub(r"\.L([0-9a-f]+)\b", lambda m: f"{P}.L{m[1]}", ins)
    out.append((a, "    " + ins))
  for a, t in out:
    print(t)


main()
