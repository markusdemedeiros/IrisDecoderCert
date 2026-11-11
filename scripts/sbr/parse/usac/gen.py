#!/usr/bin/env python3
"""Labelled program text of `ff_aac_sbr_decode_usac_data` / `ff_aac_sbr_config_usac`.

Input: the `to_program` text of the routine (aacsbr.rela.o) and the GNU objdump listing of
the same range (for the instruction addresses). Output (stdout): the body of the Lean
`parse(...)`, one block per label:

  * labels `.LXXXX` become `P.LXXXX` (XXXX = address in aacsbr.rela.o), `start` becomes `P`;
  * extra labels at the cut points CUTS (addresses, hex);
  * the `ret` is kept in place, behind the label `P.done`; the trailing `done: nop` of
    `to_program` is dropped;
  * the routine has no rip-relative operand; the calls name the callee symbols.

Usage: gen.py SYMBOL PROG.s OBJDUMP.txt [CUT ...] > body.s
"""
import re
import sys

P = sys.argv[1]
CUTS = set(int(x, 16) for x in sys.argv[4:])


def main():
  prog = [l.rstrip("\n") for l in open(sys.argv[2])]
  dump = []
  inside = False
  for l in open(sys.argv[3]):
    m = re.match(r"^[0-9a-f]+ <(.*)>:$", l)
    if m:
      inside = m[1] == P
      continue
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m and inside:
      dump.append((int(m[1], 16), m[2].strip()))
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
    m0 = ins.split()[0]
    t0 = t.split()[0]
    if not (m0 == t0 or m0[:3] == t0[:3]
            or (m0 == "nop" and (t0.startswith("nop") or t == "xchg   %ax,%ax"))
            or (m0 == "jmp" and t0 == "ret") or m0.startswith("j") and t0.startswith("j")
            or m0.startswith("ud1") or m0.startswith("cmov") or m0.startswith("set")):
      sys.exit(f"mismatch at {a:x}: {ins!r} vs {t!r}")
    if a in CUTS and not (out and out[-1][0] is None and out[-1][1] == f"{P}.L{a:x}:"):
      out.append((None, f"{P}.L{a:x}:"))
    if ins == "jmp done":
      out.append((None, f"{P}.done:"))
      ins = "ret"
    ins = re.sub(r"\.L([0-9a-f]+)\b", lambda m: f"{P}.L{m[1]}", ins)
    out.append((a, "    " + ins))
  for a, t in out:
    print(t)


main()
