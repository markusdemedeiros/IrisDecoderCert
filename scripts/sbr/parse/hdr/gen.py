#!/usr/bin/env python3
"""Labelled program text of `read_sbr_header` / `read_sbr_invf` for `HdrText.lean` /
`InvfText.lean`.

Input: the `to_program` text of the routine (aacsbr.rela.o) and the GNU objdump listing of
the same symbol (for the instruction addresses). Output (stdout): the body of the Lean
`parse(...)`, one block per label:

  * labels `.LXXXX` become `SYM.LXXXX` (XXXX = address in aacsbr.o);
  * extra labels at the cut points CUTS;
  * the `ret` is kept in place, behind the label `SYM.done`; the trailing `done: nop` of
    `to_program` is dropped; the `int3` padding after the last instruction is kept.

Usage: gen.py SYM PROG.s OBJDUMP.txt CUT... > body.s
"""
import re
import sys

P = sys.argv[1]
CUTS = [int(x, 16) for x in sys.argv[4:]]


def main():
  prog = [l.rstrip("\n") for l in open(sys.argv[2])]
  dump = []
  for l in open(sys.argv[3]):
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m:
      dump.append((int(m[1], 16), m[2].strip()))
  out, k = [], 0
  extra = set(CUTS)
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
    ins = l.strip()
    a = None
    if k < len(dump):
      a, t = dump[k]
      k += 1
      # the listing and the program text must agree on the mnemonic
      assert t.split()[0] == ins.split()[0] or ins == "jmp done", (hex(a), t, ins)
    else:
      assert ins == "int3", ins
    if a in extra and not (out and out[-1][0] is None and out[-1][1] == f"{P}.L{a:x}:"):
      out.append((None, f"{P}.L{a:x}:"))
    if ins == "jmp done":
      out.append((None, f"{P}.done:"))
      ins = "ret"
    ins = re.sub(r"\.L([0-9a-f]+)\b", lambda m: f"{P}.L{m[1]}", ins)
    out.append((a, "    " + ins))
  for a, t in out:
    print(t)


main()
