#!/usr/bin/env python3
"""Labelled program text of `read_sbr_envelope` for `EnvText.lean`.

Input: the `to_program` text of `read_sbr_envelope` (aacsbr.rela.o) and an objdump listing of
the same symbol (for the instruction addresses). Output (stdout): the body of the Lean
`parse(...)`, one block per label:

  * labels `.LXXXX` become `read_sbr_envelope.LXXXX` (XXXX = address in aacsbr.rela.o);
  * extra labels at the cut points CUTS (addresses);
  * `0x0(%rip)` operands get their symbol (relocations, by address, in RIP below);
  * the `ret` (`jmp done` in the `to_program` text) is a `ret` behind the label
    `read_sbr_envelope.done`; the trailing `done: nop` is dropped.

Usage: gen.py PROG.s OBJDUMP.txt [--annotate] > body.s
"""
import re
import sys

P = "read_sbr_envelope"
# rip-relative operands, by address (aacsbr.rela.o), from the relocations.
RIP = {
    0x5802: "ff_aac_sbr_vlc",
    0x585b: "ff_aac_sbr_vlc",
    0x5862: "ff_aac_sbr_vlc+0x20",
    0x6050: "L_str_30",
}
CUTS = [
    0x57c1, 0x57c9, 0x57ef,                  # prologue; channel / coupling / table selection
    0x58a4, 0x58c5, 0x58e6, 0x58f1,          # the frame stores after .L5893
    0x590d, 0x5930,                          # envelope loop head
    0x595a, 0x5998, 0x5a38,                  # time delta, same resolution (walk at .L5940)
    0x5a95, 0x5ae4, 0x5b25, 0x5bc7,          # frequency delta (walk at .L5ad0)
    0x5bf6, 0x5c26, 0x5c5e,                  # time delta, low resolution, first band
    0x5ced, 0x5cfd, 0x5d35, 0x5dd7,          # time delta, high resolution (walk at .L5cd0)
    0x5e4b, 0x5e8d, 0x5eca, 0x5f6e,          # time delta, low resolution (walk at .L5e70)
    0x5fac, 0x5fdd, 0x5fe9,                  # USAC temp_shape
    0x6063,                                  # after the call of av_log
]


def main():
  annotate = "--annotate" in sys.argv
  args = [a for a in sys.argv[1:] if not a.startswith("--")]
  prog = [l.rstrip("\n") for l in open(args[0])]
  dump = []
  for l in open(args[1]):
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m:
      dump.append((int(m[1], 16), m[2].strip()))
  out, k = [], 0
  extra = set() if "--nocuts" in sys.argv else set(CUTS)
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
    print(f"{a:x}  {t}" if annotate and a is not None else t)


main()
