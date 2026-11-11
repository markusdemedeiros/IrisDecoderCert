#!/usr/bin/env python3
"""Labelled program text of `sbr_reset` for `ResetBlocks.lean`.

Inputs: the `to_program` text of `sbr_reset` (aacsbr.rela.o), its notes (stderr of
`to_program`, which lists the relocation of every rip-relative operand), and the llvm-objdump
listing of the same symbol (for the instruction addresses). Output (stdout): the body of the
Lean `parse(...)`, one block per label:

  * labels `.LXXXX` become `sbr_reset.LXXXX` (XXXX = address in aacsbr.rela.o);
  * extra labels at the cut points given on the command line (hex addresses);
  * `0x0(%rip)` operands get their symbol: `.rodata+0x10+16*r` is row `r` of `sbr_offset`
    (`sbr_offset_r`), `.LCPI5_n` is `LCPI5_n`, `.L.str.n` is `L_str_n`;
  * the `ret` is kept in place, behind the label `sbr_reset.done`; the trailing
    `done: nop` of `to_program` is dropped.

Usage: gen.py PROG.s PROG.notes OBJDUMP.txt [CUT ...] > body.s
"""
import re
import sys

P = "sbr_reset"


def sym_of(target):
  m = re.match(r"^\.rodata\+0x([0-9a-f]+)$", target)
  if m:
    off = int(m[1], 16)
    assert 0x10 <= off < 0x70 and (off - 0x10) % 16 == 0, target
    return f"sbr_offset_{(off - 0x10) // 16}"
  m = re.match(r"^\.LCPI(\d+)_(\d+)\+0x0$", target)
  if m:
    return f"LCPI{m[1]}_{m[2]}"
  m = re.match(r"^\.L\.str\.(\d+)\+0x0$", target)
  if m:
    return f"L_str_{m[1]}"
  raise SystemExit(f"unknown relocation target {target}")


def main():
  prog = [l.rstrip("\n") for l in open(sys.argv[1])]
  rip = {}
  for l in open(sys.argv[2]):
    m = re.match(r"^warning: 0x([0-9a-f]+): `[^`]*\(%rip\)[^`]*` has relocation \S+ \S+; "
                 r"the operand addresses (\S+) ", l)
    if m:
      rip[int(m[1], 16)] = sym_of(m[2])
  dump = []
  for l in open(sys.argv[3]):
    if "R_X86_64" in l:
      continue
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m:
      dump.append((int(m[1], 16), m[2].strip()))
  cuts = {int(x, 16) for x in sys.argv[4:]}
  out, k = [], 0
  for l in prog:
    if not l.strip():
      continue
    if not l.startswith(" "):
      lab = l[:-1]
      if lab == "done":
        break
      out.append(f"{P}:" if lab == "start" else f"{P}.{lab[1:]}:" if lab.startswith(".L")
                 else f"{P}.{lab}:")
      continue
    a, _ = dump[k]
    k += 1
    ins = l.strip()
    if a in cuts and out[-1] != f"{P}.L{a:x}:":
      out.append(f"{P}.L{a:x}:")
    if "0x0(%rip)" in ins:
      ins = ins.replace("0x0(%rip)", f"{rip[a]}(%rip)")
    if ins == "jmp done":
      out.append(f"{P}.done:")
      ins = "ret"
    ins = re.sub(r"\.L([0-9a-f]+)\b", lambda m: f"{P}.L{m[1]}", ins)
    out.append("    " + ins)
  assert k == len(dump) or all(t.startswith("int3") or t.startswith("nop") for _, t in dump[k:]), \
      (k, len(dump))
  for t in out:
    print(t)


main()
