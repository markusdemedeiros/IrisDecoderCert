#!/usr/bin/env python3
"""Labelled program text of `ff_ps_read_data` for `PsText.lean`.

Input: the `to_program` text of `ff_ps_read_data` (from the merged object of
`libavcodec/aacps_common.c`, where the routine starts at `.text+0`) and an objdump listing of
the same range (for the instruction addresses). Output (stdout): the body of the Lean
`parse(...)`, one block per label:

  * labels `.LXXXX` become `ff_ps_read_data.LXXXX` (XXXX = offset in the routine);
  * extra labels at the cut points CUTS (offsets, hexadecimal, on the command line);
  * `0x0(%rip)` operands get their symbol (relocations listed in RIP below); the GOT slot of
    `ff_log2_tab` is the label `ff_log2_tab_got`;
  * the `ret` is kept in place, behind the label `ff_ps_read_data.done`; the trailing
    `done: nop` of `to_program` is dropped.

Usage: gen.py PROG.s OBJDUMP.txt [CUT ...] > body.s
"""
import re
import sys

P = "ff_ps_read_data"
# rip-relative operands, by offset, from the relocations (symbol + addend + 4).
RIP = {
    0xaa: "L_str", 0xc7: "nr_iidicc_par_tab", 0xe5: "nr_iidopd_par_tab", 0x148: "L_str_1",
    0x15c: "nr_iidicc_par_tab", 0x1ff: "num_env_tab", 0x23f: "ff_log2_tab_got",
    0x297: "L_str_2", 0x7b8: "huff_iid", 0x7c2: "vlc_ps", 0xad5: "vlc_ps", 0xc7a: "L_str_7",
    0xe3a: "vlc_ps", 0xf4e: "vlc_ps", 0x10cf: "L_str_8", 0x132a: "L_str_5", 0x1410: "L_str_6",
    0x1459: "L_str_3", 0x14cc: "L_str_4",
    0x3ad: "LCPI0_0", 0x3bc: "LCPI0_1", 0x3c8: "LCPI0_2", 0x3d4: "LCPI0_3", 0x417: "LCPI0_4",
    0x423: "LCPI0_5", 0x42f: "LCPI0_6", 0x43b: "LCPI0_7", 0x47d: "LCPI0_8", 0x489: "LCPI0_9",
    0x495: "LCPI0_10", 0x4a1: "LCPI0_11", 0x4ea: "LCPI0_12", 0x4f6: "LCPI0_13",
    0x502: "LCPI0_14", 0x50e: "LCPI0_15", 0x553: "LCPI0_16", 0x55f: "LCPI0_17",
    0x56b: "LCPI0_18", 0x577: "LCPI0_19", 0x5c0: "LCPI0_20", 0x5cc: "LCPI0_21",
    0x5d8: "LCPI0_22", 0x5e4: "LCPI0_23", 0x625: "LCPI0_24", 0x631: "LCPI0_25",
    0x63d: "LCPI0_26", 0x649: "LCPI0_27", 0x6ab: "LCPI0_28", 0x6c0: "LCPI0_30",
}
CUTS = [int(x, 16) for x in sys.argv[3:]]


def main():
  prog = [l.rstrip("\n") for l in open(sys.argv[1])]
  dump = []
  for l in open(sys.argv[2]):
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", l)
    if m:
      dump.append((int(m[1], 16), m[2].strip()))
  out, k = [], 0
  extra = set(CUTS)
  used = set()
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
      assert "0x0(%rip)" in ins, (hex(a), ins)
      ins = ins.replace("0x0(%rip)", f"{RIP[a]}(%rip)")
      used.add(a)
    if ins == "jmp done":
      out.append((None, f"{P}.done:"))
      ins = "ret"
    ins = re.sub(r"\.L([0-9a-f]+)\b", lambda m: f"{P}.L{m[1]}", ins)
    out.append((a, "    " + ins))
  assert used == set(RIP), sorted(set(RIP) - used)
  for a, t in out:
    print(t)


main()
