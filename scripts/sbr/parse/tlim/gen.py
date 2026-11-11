#!/usr/bin/env python3
"""Labelled program text of `sbr_make_f_tablelim` for `TlimText.lean`.

Input: the `to_program` text of `sbr_make_f_tablelim` (aacsbr.rela.o) and the GNU objdump listing
of the same range (for the instruction addresses). Output (stdout): the body of the Lean
`parse(...)`, one block per label:

  * labels `.LXXXX` become `sbr_make_f_tablelim.LXXXX` (XXXX = address in aacsbr.rela.o);
  * extra labels at the cut points CUTS;
  * `0x0(%rip)` operands get their symbol (relocations listed in NOTES below);
  * the `ret` is kept in place, behind the label `sbr_make_f_tablelim.done`; the trailing
    `done: nop` of `to_program` is dropped.

Usage: gen.py PROG.s OBJDUMP.txt > body.s
"""
import re
import sys

P = "sbr_make_f_tablelim"
BASE = 0x3f10
# rip-relative operands, by address (aacsbr.rela.o), from the relocations.
RIP = {
    0x3f3a: "sbr_make_f_tablelim_bw",   # .rodata+0x70: bands_warped[3] (no symbol)
}
JT = []
# cut points: every conditional exit of the unrolled patch-border chain, after each call,
# and the heads of the code after the checks.
DEFAULT_CUTS = [0x3f22, 0x3f31, 0x3f3a, 0x3f59, 0x3f65, 0x3f77, 0x3f89, 0x3f9b, 0x3fad, 0x3fbf,
                0x3ff5, 0x4000, 0x400a, 0x4020, 0x403f, 0x40c3, 0x40c9, 0x4105, 0x4110, 0x4199,
                0x41ca, 0x4211, 0x421b, 0x425a, 0x42b6, 0x42bc, 0x42fa, 0x4312, 0x4317, 0x4323,
                0x4338, 0x4340, 0x435b, 0x4363, 0x4398, 0x43a4]
CUTS = DEFAULT_CUTS + [int(x, 16) for x in sys.argv[3:]]


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
