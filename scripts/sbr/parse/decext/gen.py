#!/usr/bin/env python3
"""Labelled program text of `ff_aac_sbr_decode_extension` for `DecExtText.lean`.

Input: the `to_program` text of `ff_aac_sbr_decode_extension` (aacsbr.rela.o, where the routine
is at .text+0) and the GNU objdump listing of the same range (for the instruction addresses).
Output (stdout): the body of the Lean `parse(...)`, one block per label:

  * labels `.LXXX` become `ff_aac_sbr_decode_extension.LXXX` (XXX = address);
  * extra labels after every `call` and at the cut points CUTS (command line, hex);
  * `0x0(%rip)` operands get their symbol (relocations in RIP below);
  * the `ret` is kept in place, behind the label `ff_aac_sbr_decode_extension.done`; the trailing
    `done: nop` of `to_program` is dropped.

Usage: gen.py PROG.s OBJDUMP.txt [CUT...] > body.s
"""
import re
import sys

P = "ff_aac_sbr_decode_extension"
# rip-relative operands, by address, from the relocations.
RIP = {
    0x46b: "L_str_21", 0x510: "L_str", 0xc6f: "L_str_24", 0xca8: "L_str_22", 0xcc0: "L_str_23",
}
CUTS = [int(x, 16) for x in sys.argv[3:]]


def main():
  prog = [l.rstrip("\n") for l in open(sys.argv[1])]
  dump = []
  for l in open(sys.argv[2]):
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m:
      dump.append((int(m[1], 16), m[2].strip()))
  # the address after every call
  extra = set(CUTS)
  for i, (a, t) in enumerate(dump):
    if t.startswith("call") and i + 1 < len(dump):
      extra.add(dump[i + 1][0])
  out, k = [], 0
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
    if a in extra and not (out and out[-1][0] is None):
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
