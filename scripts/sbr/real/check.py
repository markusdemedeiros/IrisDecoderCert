#!/usr/bin/env python3
"""Check the elaborated real image `Real.rCE 0` against the linked binary.

usage: check.py BINARY OUTDIR      (OUTDIR holds cells.txt, texts.txt from RealExport.lean)
Env: LLVM_BIN; SBR_OBJ_DIR (optional: compare the constants with the objects).

Input: every cell of the image with the address and size `Real.rLayout 0` gives it.
 1. The cells are contiguous from `rStart`.
 2. Code: each maximal run of label/instruction cells is re-assembled with llvm-mc, each
    instruction placed by `.org` at its Lean address and the run's labels at theirs. The
    relocations llvm-mc leaves (references to labels outside the run) are resolved against
    the LEAN addresses of those labels. Each instruction must give exactly the binary's
    bytes at its address (no masking), and its cell size must be the length of the binary
    instruction there (the binary's linear sweep has an instruction boundary at every cell
    and none inside). Allowed, as in tv.py: a Lean `.nops n` on binary padding of n bytes
    (or an unsized `.nops 1` on any padding instruction), and an encoding that differs but
    decodes to the same instruction with the same targets.
 3. Labels: each text of `Real.rTexts` starts at its entry symbol (in the aacsbr.c STT_FILE
    scope for the C procedures); each label named after a binary symbol unique in its scope
    sits at it; the `<sym>.L<hex>` labels of each text sit at one common offset from <hex>
    (the `<sym>.L<hex>_<k>` labels, blocks split off inside it, behind that address).
    Every other label of the image other than a `gap_*` label is referenced by an
    instruction of the image (so step 2 pins its address to the binary's encoding).
 4. Data: the constants of `CstW` hold at their Lean addresses the values the statement
    names (`LCPI14_4` = 1E20, `LCPI17_11` = {0x1ff, 3, 0, 0}) and, with SBR_OBJ_DIR, the
    same bytes as in the objects (aacsbr.rela.o, sbrdsp.o, float_dsp.o).
Exit status 1 on any FINDING.
"""
import os
import re
import struct
import subprocess
import sys

import real_lib as R
tv = R.tv

CST_SIZES = {
    "LCPI14_0": 4, "LCPI14_5": 4, "LCPI14_6": 4, "LCPI14_9": 4, "LCPI14_10": 4, "LCPI14_11": 4,
    "LCPI14_12": 4, "LCPI14_13": 4, "LCPI14_14": 4, "LCPI14_15": 4, "LCPI14_16": 4,
    "LCPI14_17": 4, "LCPI14_3": 8, "LCPI14_1": 16, "LCPI14_2": 16, "LCPI14_8": 16,
    "exp2_tab": 16, "bw_tab": 16, "limgain": 16, "sbr_qmf_window_ds": 1280, "ff_ps_neg": 16,
    "ps_mask": 16, "LCPI19_0": 4, "LCPI19_1": 4, "LCPI19_2": 16, "ps_mask3": 16,
    "sbr_qmf_window_us": 2560, "LCPI15_1": 4, "ps_mask2": 16, "ff_sbr_noise_table": 4160,
    "ps_noise0": 16, "ps_noise13": 48, "ps_noise2": 16, "LCPI17_6": 4, "LCPI17_7": 4,
    "LCPI17_8": 4, "LCPI17_9": 4, "LCPI17_10": 4, "LCPI17_12": 4, "LCPI14_4": 8,
    "LCPI17_11": 16, "pd_reverse": 32}
CST_VALUES = {"LCPI14_4": struct.pack("<d", 1e20), "LCPI17_11": (0x3000001ff).to_bytes(16, "little")}

findings, notes = [], []


def finding(m):
  findings.append(m)


def read_cells(path):
  cells = []
  for line in open(path):
    line = line.rstrip("\n")
    if not line:
      continue
    a, z, k, *rest = line.split(" ", 3)
    cells.append(dict(addr=int(a, 16), size=int(z), kind=k, text=rest[0] if rest else ""))
  return cells


def apply_relocs(gb, grel, base, labaddr, got):
  """Resolve llvm-mc's relocations against the Lean label addresses."""
  gb = bytearray(gb)
  for off, (typ, sym, add) in grel.items():
    P = base + off
    if typ == "R_X86_64_GOTPC32":
      v, w = got + add - P, 4
    elif typ in ("R_X86_64_PC32", "R_X86_64_PLT32"):
      if sym not in labaddr:
        raise KeyError(f"relocation against `{sym}`, which is not a label of the image")
      v, w = labaddr[sym] + add - P, 4
    elif typ == "R_X86_64_GOTOFF64":
      v, w = labaddr[sym] + add - got, 8
    else:
      raise KeyError(f"unexpected relocation {typ} {sym}")
    gb[off:off + w] = (v % 2 ** (8 * w)).to_bytes(w, "little")
  return bytes(gb)


def mc_decode(bs, addr, work, tag):
  """Decode bytes at an address (objdump on a one-section object, VMA adjusted)."""
  raw = os.path.join(work, tag + ".bin")
  obj = os.path.join(work, tag + ".o")
  open(raw, "wb").write(bs)
  R.run([tv.tool("llvm-objcopy"), "-I", "binary", "-O", "elf64-x86-64",
         "--rename-section=.data=.text,code", raw, obj])
  out = R.run([tv.tool("llvm-objdump"), "-d", "-z", "-M", "intel", "--no-show-raw-insn",
               f"--adjust-vma={addr:#x}", obj])
  res = []
  for line in out.splitlines():
    m = re.match(r"^\s*([0-9a-f]+):\s+(.*)$", line)
    if m:
      res.append((int(m[1], 16), tv.norm(m[2])))
  return res


def check_run(B, run, labaddr, got, work, stats, referenced):
  base = run[0]["addr"]
  insns = [c for c in run if c["kind"] == "I"]
  if not insns:
    return
  stop = run[-1]["addr"] + run[-1]["size"]
  bins = {a: t for a, t in B.disasm(base, stop)}
  asm = [".intel_syntax noprefix", ".text"]
  run_labels = set()
  for i, c in enumerate(run):
    asm.append(f".org {c['addr'] - base:#x}")
    if c["kind"] == "L":
      asm.append(f"{c['text']}:")
      run_labels.add(c["text"])
    elif c["kind"] == "I":
      for (l, off, rk) in R.refs(c["text"]):
        referenced.add(l)
      if c["text"].startswith(".nops"):
        continue
      asm.append(tv.to_mc(c["text"]))
      asm.append(f"__real_end_{i}:")
  tag = f"run_{base:x}"
  sfile, ofile = os.path.join(work, tag + ".s"), os.path.join(work, tag + ".o")
  open(sfile, "w").write("\n".join(asm) + "\n")
  r = subprocess.run([tv.tool("llvm-mc"), "-triple=x86_64", "-filetype=obj", "-o", ofile, sfile],
                     capture_output=True, text=True)
  if r.returncode != 0:
    finding(f"run {base:#x}: llvm-mc failed: {r.stderr[:2000]}")
    return
  g = tv.Elf(ofile)
  ends = {s["name"]: s["value"] for s in g.syms if s["name"].startswith("__real_end_")}
  gt = g.sec(".text")
  try:
    gb = apply_relocs(g.data[gt["off"]: gt["off"] + gt["size"]], tv.relocs(ofile), base, labaddr, got)
  except KeyError as e:
    finding(f"run {base:#x}: {e}")
    return
  for i, c in enumerate(run):
    if c["kind"] != "I":
      continue
    a, z = c["addr"], c["size"]
    # the binary has an instruction at a, of length z
    if a not in bins:
      finding(f"{a:#x}: no binary instruction starts at the Lean cell `{c['text']}`")
      continue
    inside = [x for x in bins if a < x < a + z]
    if inside or (a + z not in bins and a + z != stop):
      finding(f"{a:#x}: cell size {z} is not the binary instruction's length")
      continue
    bt = tv.norm(bins[a])
    ob = B.bytes(a, z)
    if c["text"].startswith(".nops"):
      n = int(c["text"].split()[1])
      if not tv.PAD_RE.match(bt):
        finding(f"{a:#x}: Lean `{c['text']}` on binary `{bt}`")
      elif n == z:
        stats["ident"] += 1
      elif n == 1:
        stats["nop_unsized"] += 1
      else:
        finding(f"{a:#x}: Lean `{c['text']}` on binary padding of {z} bytes")
      continue
    off = a - base
    glen = ends[f"__real_end_{i}"] - off
    lb = gb[off: off + glen]
    if glen == z and lb == ob:
      stats["ident"] += 1
      continue
    # different encoding: both must decode to the same instruction, with the same targets
    lt = mc_decode(lb, a, work, f"g_{a:x}")
    btd = mc_decode(ob, a, work, f"b_{a:x}")
    if len(lt) == 1 and len(btd) == 1 and lt[0][1] == btd[0][1]:
      stats["diffenc"] += 1
      notes.append(f"{a:#x}: same instruction, other encoding: `{bt}` [{ob.hex()}] vs [{lb.hex()}]")
      continue
    if bt in ("rep ret", "repz ret") and ob == b"\xf3\xc3" and lt and lt[0][1] == "ret":
      stats["rep_ret"] += 1
      continue
    finding(f"{a:#x}: binary `{bt}` [{ob.hex()}] vs Lean `{c['text']}` -> "
            f"{[t for _, t in lt]} [{lb.hex()}]")


def main():
  if len(sys.argv) != 3:
    sys.exit(__doc__)
  binary, outdir = sys.argv[1:]
  work = os.path.join(outdir, "work")
  os.makedirs(work, exist_ok=True)
  B = R.Binary(binary, work)
  cells = read_cells(os.path.join(outdir, "cells.txt"))
  entries = [l.strip() for l in open(os.path.join(outdir, "texts.txt")) if l.strip()]
  # 1. contiguity
  for c, d in zip(cells, cells[1:]):
    if c["addr"] + c["size"] != d["addr"]:
      finding(f"cells not contiguous at {c['addr']:#x}")
  for c in cells:
    if (c["kind"] == "L") != (c["size"] == 0):
      finding(f"{c['addr']:#x}: label/size mismatch `{c['text']}` {c['size']}")
  labaddr = {}
  for c in cells:
    if c["kind"] == "L":
      if c["text"] in labaddr:
        finding(f"label {c['text']} twice")
      labaddr[c["text"]] = c["addr"]
  got = labaddr.get(R.GOT)
  if got is None:
    finding("no _GLOBAL_OFFSET_TABLE_ label")
  # 2. code runs
  runs, cur = [], []
  for c in cells:
    if c["kind"] == "B":
      if cur:
        runs.append(cur)
      cur = []
    else:
      cur.append(c)
  if cur:
    runs.append(cur)
  stats = dict(ident=0, nop_unsized=0, diffenc=0, rep_ret=0)
  referenced = set()
  for run in runs:
    check_run(B, run, labaddr, got, work, stats, referenced)
  ninsn = sum(1 for c in cells if c["kind"] == "I")
  # 3. labels
  scopes = {e: s for _, e, s in R.TEXTS}
  if entries != [e for _, e, _ in R.TEXTS]:
    finding(f"Real.rTexts entries {entries} differ from real_lib.TEXTS")
  for e in entries:
    try:
      s = B.sym(e, scopes.get(e))
    except KeyError as ex:
      finding(str(ex))
      continue
    if labaddr.get(e) != s["value"]:
      finding(f"text {e} at {labaddr.get(e, 0):#x}, binary symbol at {s['value']:#x}")
    # C procedures: the text covers the symbol's extent
    if s["size"]:
      run = [r for r in runs if r[0]["addr"] <= s["value"] < r[-1]["addr"] + r[-1]["size"]]
      if not run or run[0][-1]["addr"] + run[0][-1]["size"] < s["value"] + s["size"]:
        finding(f"text {e}: the image does not cover the symbol's {s['size']} bytes")
  insn_labels = set()
  for run in runs:
    if any(c["kind"] == "I" for c in run):
      insn_labels |= {c["text"] for c in run if c["kind"] == "L"}
  sym_checked, deltas, sub = 0, {}, []
  for l, a in labaddr.items():
    cands = B.syms_named(l)
    if l in insn_labels:
      scope = next((s for _, e, s in R.TEXTS if l == e or l.startswith(e + ".")), None)
      cs = [s for s in cands if scope is None or s["scope"] == scope]
      if len(cs) == 1:
        sym_checked += 1
        if cs[0]["value"] != a:
          finding(f"label {l} at {a:#x}, binary symbol at {cs[0]['value']:#x}")
      m = re.match(r"^(.*)\.L([0-9a-f]+)(_\d+)?$", l)
      if m and not m[3]:
        deltas.setdefault(m[1], set()).add(a - int(m[2], 16))
      elif m:
        sub.append((m[1], l, a - int(m[2], 16)))
    elif not l.startswith("gap_"):
      if l not in referenced:
        finding(f"label {l} is referenced by no instruction of the image")
      if len(cands) == 1:
        sym_checked += 1
        if cands[0]["value"] != a:
          finding(f"label {l} at {a:#x}, binary symbol at {cands[0]['value']:#x}")
  for p, ds in deltas.items():
    if len(ds) != 1:
      finding(f"labels {p}.L<hex>: not at one common offset ({len(ds)} offsets)")
  # `<sym>.L<hex>_<k>`: a block split off inside the block at <hex>, so behind it
  for p, l, d in sub:
    if p in deltas and len(deltas[p]) == 1 and d <= next(iter(deltas[p])):
      finding(f"label {l} not behind {p}.L<hex>'s address")
  # 4. data
  objs = os.environ.get("SBR_OBJ_DIR")
  oelf = {}
  if objs and os.path.exists(os.path.join(objs, "aacsbr.rela.o")):
    oelf = {k: tv.Elf(os.path.join(objs, f)) for k, f in
            (("aacsbr", "aacsbr.rela.o"), ("sbrdsp", "sbrdsp.o"), ("float_dsp", "float_dsp.o"))}
  data_ok, data_obj = 0, 0
  for l, n in CST_SIZES.items():
    a = labaddr.get(l)
    if a is None:
      finding(f"constant {l} not in the image")
      continue
    bb = B.bytes(a, n)
    if l in CST_VALUES:
      if bb != CST_VALUES[l]:
        finding(f"constant {l} at {a:#x} is {bb.hex()}, the statement says {CST_VALUES[l].hex()}")
      else:
        data_ok += 1
    for key in ("aacsbr", "sbrdsp", "float_dsp"):
      if key not in oelf:
        continue
      sec, off = tv.resolve(oelf[key], l, 0, True)
      if sec is None or str(sec).startswith("AMBIGUOUS") or sec == l:
        continue
      s = oelf[key].sec(sec)
      ob = oelf[key].data[s["off"] + off - s["addr"]: s["off"] + off - s["addr"] + n]
      if ob != bb:
        finding(f"constant {l}: binary {bb[:16].hex()}… differs from {key} {ob[:16].hex()}…")
      else:
        data_obj += 1
      break
  print(f"cells {len(cells)}, runs {len(runs)}, instructions {ninsn}: {stats}")
  print(f"labels {len(labaddr)}: {sym_checked} at their binary symbols, "
        f"{len(deltas)} texts with .L<hex> labels at a common offset "
        f"({sum(1 for _ in sub)} .L<hex>_<k> labels behind theirs)")
  print(f"constants: {data_ok} values as stated, {data_obj} equal to the objects"
        + ("" if oelf else " (SBR_OBJ_DIR not set: object comparison skipped)"))
  for n in notes[:20]:
    print("  note:", n)
  for f in findings:
    print("  FINDING:", f)
  print(f"check.py: {'exit 1' if findings else 'exit 0'}")
  sys.exit(1 if findings else 0)


if __name__ == "__main__":
  main()
