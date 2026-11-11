#!/usr/bin/env python3
"""Count the x86-64 instructions of the proved program texts, twice, independently.

1. Lean side: the program texts as exported from the built oleans by `tv/Export.lean`
   (`$SBR_OUT/tv/lean/<text>.txt`, one instruction per line).
2. Object side: llvm-objdump's linear sweep of the objects, without using the Lean texts
   or tv.py. A text's range is its entry symbol's ELF size if nonzero (compiled C), else up to
   the next global function symbol in the same section that is not one of the text's
   own labels (NASM sets no sizes); trailing padding is dropped. The text's labels are
   used only for this boundary, never for the count.
   The objects' STT_OBJECT symbols in code (NASM's `.end` markers) are removed from a
   copy first, so that llvm-objdump does not print code as data.

On both sides alignment padding is not counted: `nop` forms anywhere, and `int3` runs
after a text's last instruction (clang pads between functions with `int3`; the Lean
texts include that padding so that tv can check coverage). An `int3` inside a text
would be counted. Exit status 1 if any text's two counts differ, or if a text's entry
symbol is not found.

Usage: count_instr.py [LEAN_EXPORT_DIR] [OBJ_DIR]
  (defaults: $SBR_OUT/tv/lean, $SBR_OBJ_DIR; llvm from $LLVM_BIN)
"""
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
LLVM = os.environ.get("LLVM_BIN", "/usr/lib/llvm-21/bin")
OUT = os.environ.get("SBR_OUT") or os.path.join(ROOT, ".lake", "sbr-ci")
OBJS = ["aacsbr.rela.o", "aacps_common.rela.o", "sbrdsp.o", "float_dsp.o"]
NOP = re.compile(r"^(?:(?:data16|cs|ds)\s+)*(?:nop[wlq]?\b.*|xchg\s+ax,\s*ax)$")


def tool(name, *args):
  return subprocess.run([os.path.join(LLVM, name), *args], check=True,
                        capture_output=True, text=True).stdout


def lean_text(path):
  """(entry label, its labels, non-padding instruction count) of an exported text."""
  entry, labels, ins = None, set(), []
  for line in open(path, encoding="utf-8"):
    if re.match(r"^\S.*:\s*$", line):
      entry = entry or line.strip()[:-1]
      labels.add(line.strip()[:-1])
      continue
    t = line.split(";;")[0].strip()
    if t and not t.startswith(".nops") and not NOP.match(t):
      ins.append(t)
  while ins and ins[-1] == "int3":
    ins.pop()
  return entry, labels, len(ins)


def object_code(obj, tmp):
  """{symbol: (section, address)} for code symbols, and [(section, address, text)]."""
  size, glob = {}, set()
  for line in tool("llvm-nm", "--defined-only", "-S", obj).split("\n"):
    f = line.split()
    if len(f) == 4:
      size[f[3]] = int(f[1], 16)
      if f[2] == "T":
        glob.add(f[3])
  # STT_OBJECT symbols in code: llvm-readelf lists type OBJECT with a code section index.
  xsec = set()
  for line in tool("llvm-readelf", "-SW", obj).split("\n"):
    m = re.match(r"^\s*\[\s*(\d+)\]\s+(\S+)\s+\S+\s+\S+\s+\S+\s+\S+\s+\S+\s+(\S*)", line)
    if m and "X" in m[3]:
      xsec.add(m[1])
  strip = []
  for line in tool("llvm-readelf", "-sW", obj).split("\n"):
    f = line.split()
    if len(f) >= 8 and f[3] == "OBJECT" and f[6] in xsec:
      strip.append(f[7])
  copy = os.path.join(tmp, os.path.basename(obj))
  shutil.copyfile(obj, copy)
  if strip:
    subprocess.run([os.path.join(LLVM, "llvm-objcopy")] + [a for s in strip for a in ("-N", s)]
                   + [copy], check=True)
  dis = tool("llvm-objdump", "-d", "--no-show-raw-insn", "-M", "intel", copy)
  syms, insns, sec = {}, [], None
  for line in dis.split("\n"):
    m = re.match(r"^Disassembly of section (\S+):", line)
    if m:
      sec = m[1]
      continue
    m = re.match(r"^([0-9a-f]+) <([^>]+)>:", line)
    if m:
      syms[m[2]] = (sec, int(m[1], 16))
      continue
    m = re.match(r"^\s+([0-9a-f]+):\s+(.*)$", line)
    if m and sec:
      insns.append((sec, int(m[1], 16), m[2].strip()))
  return syms, insns, size, glob


def main():
  lean_dir = sys.argv[1] if len(sys.argv) > 1 else os.path.join(OUT, "tv", "lean")
  obj_dir = sys.argv[2] if len(sys.argv) > 2 else os.environ.get("SBR_OBJ_DIR", "")
  if not os.path.isdir(lean_dir) or not os.path.isdir(obj_dir):
    sys.exit("count_instr: need the tv export dir and SBR_OBJ_DIR (run tv/tv.sh first)")
  texts = []
  for f in sorted(os.listdir(lean_dir)):
    if f.endswith(".txt"):
      texts.append(lean_text(os.path.join(lean_dir, f)))
  tmp = tempfile.mkdtemp()
  code = {o: object_code(os.path.join(obj_dir, o), tmp) for o in OBJS}
  shutil.rmtree(tmp)
  where = {}
  for entry, _, _ in texts:
    for o, (syms, _, _, _) in code.items():
      if entry in syms:
        where[entry] = (o,) + syms[entry]
        break
  bad, tl, to = 0, 0, 0
  print(f"{'text':32s} {'lean':>6s} {'object':>6s}")
  for entry, labels, n in texts:
    if entry not in where:
      print(f"{entry:32s} {n:6d}      ?  entry symbol not found")
      bad += 1
      continue
    o, sec, start = where[entry]
    syms, insns, size, glob = code[o]
    if size.get(entry):
      end = start + size[entry]
    else:
      # A text may hold several entry points and a shared body (hf_apply_noise_0..3 and
      # apply_noise_main): its own labels do not end it.
      nexts = [a for e, (s2, a) in syms.items()
               if e in glob and e not in labels and s2 == sec and a > start]
      end = min(nexts) if nexts else float("inf")
    rng = [t for s, a, t in insns if s == sec and start <= a < end]
    while rng and (NOP.match(rng[-1]) or rng[-1] == "int3"):
      rng.pop()
    m = sum(1 for t in rng if not NOP.match(t))
    mark = "" if m == n else "  MISMATCH"
    bad += m != n
    tl, to = tl + n, to + m
    print(f"{entry:32s} {n:6d} {m:6d}{mark}")
  print(f"{'TOTAL (' + str(len(texts)) + ' texts)':32s} {tl:6d} {to:6d}")
  print("count_instr: " + ("ok" if bad == 0 else f"FAIL ({bad} texts)"))
  sys.exit(1 if bad else 0)


if __name__ == "__main__":
  main()
