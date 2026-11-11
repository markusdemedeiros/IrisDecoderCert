#!/usr/bin/env python3
"""Labelled program text of `read_sbr_noise` / `read_sbr_dtdf` for `NoiseText.lean` /
`DtdfText.lean`.

Input: the `to_program` text of the routine (aacsbr.rela.o) and the llvm-objdump listing of
the same symbol with relocations (`llvm-objdump -d -r --no-show-raw-insn
--disassemble-symbols=SYM aacsbr.rela.o`), for the instruction addresses and the symbols of
the rip-relative operands. Output (stdout): the body of the Lean `parse(...)`, one block per
label:

  * labels `.LXXXX` become `SYM.LXXXX` (XXXX = address in aacsbr.rela.o);
  * extra labels at the cut points (hex addresses after the two files);
  * `0x0(%rip)` operands get the symbol of their relocation (`.L.str.N` becomes `L_str_N`);
  * each `jmp done` becomes `ret` behind the label `SYM.done` (one return label; a second
    `jmp done` becomes `jmp SYM.done`); the trailing `done: nop` of `to_program` is dropped.

Usage: gen.py SYM PROG.s OBJDUMP.txt [CUT...] > body.s
"""
import re
import sys

P = sys.argv[1]
CUTS = {int(x, 16) for x in sys.argv[4:]}


def main():
  prog = [l.rstrip("\n") for l in open(sys.argv[2])]
  dump, rel = [], {}
  for l in open(sys.argv[3]):
    m = re.match(r"^\s+([0-9a-f]+):\s+R_X86_64_\w+\s+(\S+?)(-0x4)?$", l)
    if m:
      rel[int(m[1], 16)] = m[2]
      continue
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m:
      dump.append((int(m[1], 16), m[2].strip()))
  # the relocation sits inside the instruction: attach it to the instruction before it
  addrs = [a for a, _ in dump]
  rip = {}
  for r, s in rel.items():
    a = max(x for x in addrs if x <= r)
    rip[a] = s.replace(".L.str.", "L_str_")
  out, k, done = [], 0, False
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
    if a in CUTS and not (out and out[-1][0] is None and out[-1][1] == f"{P}.L{a:x}:"):
      out.append((None, f"{P}.L{a:x}:"))
    if a in rip and "0x0(%rip)" in ins:
      ins = ins.replace("0x0(%rip)", f"{rip[a]}(%rip)")
    if ins == "jmp done":
      if not done:
        out.append((None, f"{P}.done:"))
        ins, done = "ret", True
      else:
        ins = f"jmp {P}.done"
    ins = re.sub(r"\.L([0-9a-f]+)\b", lambda m: f"{P}.L{m[1]}", ins)
    out.append((a, "    " + ins))
  for a, t in out:
    print(t)


main()
