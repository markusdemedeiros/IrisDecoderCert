#!/usr/bin/env python3
"""Translation validation, part 2: which object, and the data the proofs assume.

A. Object identity: the six C procedures in `aacsbr.rela.o` (the object tv.py
   compares against; `ld -r` merge of the `-ffunction-sections` build) against
   `aacsbr.pic.o` and `aacsbr.g.o` (one section per function): same bytes outside
   relocation fields, same relocation types, same resolved targets (symbol name
   or section+offset mapped to the symbol at that place).
B. Data: every `lab "X"` region of the proofs' footprints (sizes as stated in
   the Lean files, copied below) is resolved in the objects: inside its section,
   pairwise disjoint within each footprint (the separating conjunction is
   unsatisfiable otherwise), alignment facts the specs assume (`LayoutC`,
   `isAligned`), and the values the proofs assume (`LCPI14_4 = 1E20`,
   `LCPI17_11 = 0x3000001ff` as 16 little-endian bytes).
C. read_sbr_grid's jump table against `Grid.JtC`.
D. Every constant byte list the top theorems place at a label (printed from the elaborated
   closures by `ExportData.lean`), against the bytes of the object that holds the label.
Exit 1 on any mismatch.
"""
import os
import struct
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from tv import Elf, relocs, OBJDIR, ROOT, tool, LEAN_ALIAS  # noqa: E402

bad = []


def say(ok, msg):
  print(("ok    " if ok else "FAIL  ") + msg)
  if not ok:
    bad.append(msg)


# ------------------------------------------------------------- A ---------

def func_view(elf, rels, name):
  s = elf.sym(name)
  sec = elf.secs[s["shndx"]]
  b = elf.data[sec["off"] + s["value"] - sec["addr"]: sec["off"] + s["value"] - sec["addr"] + s["size"]]
  out = {}
  for o, (t, symidx, ad) in rels.get(sec["idx"], {}).items():
    if s["value"] <= o < s["value"] + s["size"]:
      # resolve to the symbol at the target (section-relative or named)
      rs = elf.syms[symidx]
      if rs["type"] == 3:  # STT_SECTION: find the symbol covering the target
        shndx = rs["shndx"]
        probe = ad + (4 if t != "R_X86_64_GOTOFF64" else 0)
        cands = sorted(x["name"] for x in elf.syms if x["shndx"] == shndx
                       and x["type"] in (0, 1, 2) and x["value"] <= probe < x["value"] + max(x["size"], 1))
        if cands:
          x = next(y for y in elf.syms if y["name"] == cands[0] and y["shndx"] == shndx)
          tgt = f"{cands[0]}{ad - x['value']:+#x}"
        else:
          tgt = f"{elf.secname(shndx)}+{ad:#x}"
      else:
        tgt = f"{rs['name']}{ad:+#x}"
      out[o - s["value"]] = (t, tgt)
  return b, out


def all_relocs(path):
  """target section index -> {offset: (type, symbol, addend)} (llvm-readelf -r,
  which reads CREL; the relocation section is identified by its file offset,
  since `-ffunction-sections` objects have many sections of one name)."""
  import re
  import subprocess
  e = Elf(path)
  outp = subprocess.run([tool("llvm-readelf"), "-r", path], capture_output=True,
                        text=True, check=True).stdout
  res, sec = {}, None
  for line in outp.splitlines():
    m = re.match(r"^Relocation section '(.+)' at offset (0x[0-9a-f]+) contains", line)
    if m:
      rs = next(s for s in e.secs if s["off"] == int(m[2], 16) and s["name"] == m[1])
      sec = rs["info"]
      res.setdefault(sec, {})
      continue
    m = re.match(r"^([0-9a-f]{16})\s+([0-9a-f]{16})\s+(R_\S+)\s+[0-9a-f]+\s+(\S+)\s*([+-])\s*([0-9a-f]+)$",
                 line)
    if m:
      ad = int(m[6], 16) * (-1 if m[5] == "-" else 1)
      res[sec][int(m[1], 16)] = (m[3], int(m[2], 16) >> 32, ad)
  return res


def part_a():
  print("== A. object identity (rela.o vs pic.o, g.o)")
  for base, funcs in OBJ_FUNCS:
    part_a_obj(base, funcs)


# The C procedures tv.py compares, per object: apply's cluster and the session's parser.
OBJ_FUNCS = [
    ("aacsbr", ("ff_aac_sbr_apply", "sbr_qmf_synthesis", "sbr_lf_gen", "sbr_hf_inverse_filter",
                "sbr_x_gen", "sbr_hf_assemble",
                "ff_aac_sbr_decode_extension", "ff_aac_sbr_decode_usac_data",
                "ff_aac_sbr_config_usac", "ff_aac_sbr_ctx_alloc_init", "read_sbr_header",
                "sbr_reset", "sbr_make_f_tablelim", "read_sbr_grid", "read_sbr_dtdf",
                "read_sbr_invf", "read_sbr_envelope", "read_sbr_noise")),
    ("aacps_common", ("ff_ps_read_data",)),
]


def part_a_obj(base, funcs):
  ref = os.path.join(OBJDIR, base + ".rela.o")
  e0, r0 = Elf(ref), all_relocs(ref)
  for other in (base + ".pic.o", base + ".g.o"):
    p = os.path.join(OBJDIR, other)
    e1, r1 = Elf(p), all_relocs(p)
    for f in funcs:
      b0, x0 = func_view(e0, r0, f)
      b1, x1 = func_view(e1, r1, f)
      mask = set()
      for o, (t, _) in list(x0.items()) + list(x1.items()):
        mask.update(range(o, o + (8 if t.endswith("64") else 4)))
      same = len(b0) == len(b1) and all(b0[i] == b1[i] for i in range(len(b0)) if i not in mask)
      # pic.o calls other functions through relocations; rela.o (merged .text)
      # may have resolved some of them: compare only common offsets' targets,
      # and require the same offsets.
      diffs = [(hex(o), x0.get(o), x1.get(o)) for o in sorted(set(x0) | set(x1))
               if x0.get(o) != x1.get(o)]
      say(same and not diffs, f"{f}: rela.o vs {other}: {len(b0)} bytes, {len(x0)} relocs, "
          f"bytes {'equal' if same else 'DIFFER'}, reloc diffs {diffs[:4]}")


# ------------------------------------------------------------- B ---------

# Footprints, alignments and values are DERIVED from the Lean text (so they
# cannot go stale): every `(lab "X", N)` / `N ?@ lab "X"` region, every valued
# cell `Int.toBytes K V =@ lab "X"`, every `isAligned A (lab "X")`.
# Groups: the `def CstW` block of each Apply source (a single separating
# conjunction: strictly disjoint), and per file the union of all lab regions.
import glob
import re

SBR = os.path.join(ROOT, "Kraken/X64/Examples/Sbr")
# Apply's spec sources: ApplySpec.lean (with its part of SessionSpec.lean), plus optional
# extra files with a `def CstW` block (TV_APPLY_TEMPLATES, ':'-separated; e.g. a staged generator template).
APPLY_SRCS = [os.path.join(SBR, "ApplySpec.lean")] + [
    p for p in os.environ.get("TV_APPLY_TEMPLATES", "").split(":") if p and os.path.exists(p)]


def lean_texts():
  """{path: text} of the Lean files under Sbr, with `SessionSpec.lean` dealt back to the
  modules it gathers: each of its sections (`## §N. …`, `Lemmas about these: `<path>`.`) is
  appended to the text of `<path>`, so every group below is what it was per module."""
  out = {}
  for f in sorted(glob.glob(os.path.join(SBR, "**/*.lean"), recursive=True)):
    out[f] = open(f).read()
  spec = out.pop(os.path.join(SBR, "SessionSpec.lean"), "")
  parts = re.split(r"^/-! ## §\d+\. .*\n\nLemmas about these: `([\w/]+\.lean)`\. -/$", spec,
                   flags=re.M)
  for path, text in zip(parts[1::2], parts[2::2]):
    f = os.path.join(SBR, path)
    out[f] = out.get(f, "") + "\n" + text
  return out


def src_text(p):
  """The text of `p`, with its part of `SessionSpec.lean` (`lean_texts`)."""
  return lean_texts().get(p) or open(p).read()

NUM = r"(0x[0-9a-fA-F_]+|\d+)"
RE_REG = re.compile(r'\(lab "([\w.]+)",\s*' + NUM + r"\)")
RE_RES = re.compile(NUM + r'\s*\?@\s*\(?lab "([\w.]+)"\)?')
RE_VAL = re.compile(r"Int\.toBytes\s+" + NUM + r"\s+(\(?[\w.#]+\)?)\s*=@\s*\(?lab \"([\w.]+)\"")
RE_ALN = re.compile(r'isAligned\s+' + NUM + r'\s+\(lab "([\w.]+)"\)')


def num(s):
  return int(s.replace("_", ""), 0)


def bv_consts():
  """`def NAME : BitVec 64 := 0x...#64` anywhere under Sbr (e.g. dbl1E20)."""
  out = {}
  for f in glob.glob(os.path.join(SBR, "**/*.lean"), recursive=True):
    for m in re.finditer(r"def (\w+) : BitVec (\d+) := " + NUM + r"#\d+", open(f).read()):
      out[m[1]] = (num(m[3]), int(m[2]))
  return out


def value_bytes(k, expr, consts):
  e = expr.strip("()")
  m = re.fullmatch(r"(\w+)\.toInt", e)
  if m and m[1] in consts:
    v, bits = consts[m[1]]
    v = v - (1 << bits) if v >> (bits - 1) else v  # toInt
  else:
    v = num(e)
  return (v % (1 << (8 * k))).to_bytes(k, "little")


def scan(text, consts):
  regs, vals, aln = {}, {}, {}
  for m in RE_REG.finditer(text):
    regs[m[1]] = max(regs.get(m[1], 0), num(m[2]))
  for m in RE_RES.finditer(text):
    regs[m[2]] = max(regs.get(m[2], 0), num(m[1]))
  for m in RE_VAL.finditer(text):
    k = num(m[1])
    vals[m[3]] = value_bytes(k, m[2], consts)
    regs[m[3]] = max(regs.get(m[3], 0), k)
  for m in RE_ALN.finditer(text):
    aln[m[2]] = max(aln.get(m[2], 0), num(m[1]))
  return regs, vals, aln


def cstw_block(text):
  i = text.index("def CstW")
  j = text.find("\n\n", i)
  return text[i: j if j > 0 else len(text)]


def footprints():
  consts = bv_consts()
  fps = []  # (name, regs, vals, aln)
  for p in APPLY_SRCS:
    t = src_text(p)
    blk = cstw_block(t)
    if p.endswith("ApplySpec.lean"):  # alignments: the spec and the generated table
      t += open(os.path.join(SBR, "ApplyTable.lean")).read()
    r, v, _ = scan(blk, consts)
    # completeness: every label CstW mentions must have been parsed as a region
    missed = sorted(set(re.findall(r'lab "([\w.]+)"', blk)) - set(r))
    say(not missed, f"CstW of {os.path.relpath(p, ROOT)}: every label parsed as a region "
        f"({len(r)}); unparsed: {missed}")
    _, _, a = scan(t, consts)
    fps.append((f"Apply.CstW ({os.path.relpath(p, ROOT)})", r, v, a))
  for f, text in sorted(lean_texts().items()):
    if f.endswith(("ApplySpec.lean", "ApplyTable.lean")):
      continue
    r, v, a = scan(text, consts)
    if r or a:
      fps.append((f"{os.path.relpath(f, ROOT)} (all lab regions)", r, v, a))
  return fps


def find(label):
  if label in LEAN_ALIAS:  # a Lean name for unnamed data (tv.py): target symbol/section + offset
    tgt, extra = LEAN_ALIAS[label]
    e = Elf(os.path.join(OBJDIR, "aacsbr.rela.o"))
    secs = [x for x in e.secs if x["name"] == tgt]
    if secs:
      return "aacsbr.rela.o", e, dict(name=f"{tgt}+{extra:#x}", shndx=secs[0]["idx"],
                                      value=secs[0]["addr"] + extra)
    objn, e, s = find(tgt)
    if s is None:
      return None, None, None
    return objn, e, dict(s, name=f"{s['name']}+{extra:#x}", value=s["value"] + extra)
  for objn in ("aacsbr.rela.o", "aacps_common.rela.o", "sbrdsp.o", "float_dsp.o"):
    e = Elf(os.path.join(OBJDIR, objn))
    c = [x for x in e.syms if x["shndx"] and x["type"] != 3 and
         (x["name"] in (label, "." + label) or x["name"].endswith("." + label)
          or x["name"].lstrip(".").replace(".", "_") == label)]
    if c:
      return objn, e, c[0]
  return None, None, None


def part_b():
  print("== B. data (derived from the Lean text)")
  fps = footprints()
  if not fps or not fps[0][1]:
    say(False, "no CstW regions found in the Apply sources")
  for fp, regs, vals, aln in fps:
    placed = []
    for lab in sorted(set(regs) | set(aln)):
      n = regs.get(lab, 0)
      objn, e, s = find(lab)
      if s is None:
        print(f"ok    {fp}: {lab} ({n} B) is external (not in these objects; checked at link)")
        continue
      sec = e.secs[s["shndx"]]
      off = s["value"] - sec["addr"]
      say(off + n <= sec["size"], f"{fp}: {lab} = {s['name']} @ {objn}:{sec['name']}+{off:#x}, "
          f"{n} B inside {sec['name']} ({sec['size']:#x} B, align {sec['align']})")
      if n:
        placed.append((objn, sec["name"], off, n, lab))
      if lab in aln:
        a = aln[lab]
        say(sec["align"] >= a and off % a == 0, f"{fp}: {lab} aligned {a} (section align "
            f"{sec['align']}, offset {off:#x})")
      if lab in vals:
        got = e.data[sec["off"] + off: sec["off"] + off + len(vals[lab])]
        say(got == vals[lab], f"{fp}: {lab} value {got.hex()} expected {vals[lab].hex()}")
    nbad = len(bad)
    for i in range(len(placed)):
      for j in range(i + 1, len(placed)):
        a, b = placed[i], placed[j]
        if a[:2] == b[:2] and a[2] < b[2] + b[3] and b[2] < a[2] + a[3]:
          say(False, f"{fp}: {a[4]} and {b[4]} overlap in {a[0]}:{a[1]}")
    if len(bad) == nbad:
      print(f"ok    {fp}: {len(regs)} regions ({len(placed)} in these objects) pairwise disjoint, "
            f"{len(aln)} alignments, {len(vals)} values")
    for lab in aln:
      if find(lab)[2] is None:
        print(f"note  {fp}: {lab} external; alignment {aln[lab]} must come from its defining object at link")


# ------------------------------------------------------------- C ---------

def part_c():
  """read_sbr_grid's jump table (`Grid.JtC`, a hypothesis of the session): entry k of
  `read_sbr_grid_jt` (`.rodata`+4k of aacsbr.rela.o, filled by an R_X86_64_PC32 relocation
  against `.text`) holds the offset of the k-th label of `Grid.JtW` from the table. The
  labels `read_sbr_grid.L<hex>` sit at <hex> (tv.py checks)."""
  print("== C. read_sbr_grid jump table (Grid.JtC)")
  txt = src_text(os.path.join(SBR, "Parse/GridSpec.lean"))
  jtw = txt[txt.index("def JtW"): txt.index("def JtC")]
  ents = [(int(m[1] or "0"), m[2]) for m in
          re.finditer(r'cell4 \(?JT(?: \+ (\d+)#64)?\)? \(jtOff "(read_sbr_grid\.L[0-9a-f]+)"\)', jtw)]
  jtc = txt[txt.index("def JtC"): txt.index("\n\n", txt.index("def JtC"))]
  say(len(ents) == 4 and sorted(set(re.findall(r'jtOff "([^"]+)"', jtc))) == sorted(l for _, l in ents),
      f"Grid.JtW entries {ents}, the labels of Grid.JtC")
  path = os.path.join(OBJDIR, "aacsbr.rela.o")
  e, rel = Elf(path), all_relocs(path)
  tgt, extra = LEAN_ALIAS["read_sbr_grid_jt"]
  rod = next(x for x in e.secs if x["name"] == tgt)
  text = next(x for x in e.secs if x["name"] == ".text")
  r = rel.get(rod["idx"], {})
  for off, lab in ents:
    want = int(lab.rsplit(".L", 1)[1], 16)
    o = extra + off
    got = r.get(o)
    stored = e.data[rod["off"] + o: rod["off"] + o + 4]
    ok = (got is not None and got[0] == "R_X86_64_PC32" and e.syms[got[1]]["type"] == 3
          and e.syms[got[1]]["shndx"] == text["idx"] and got[2] - o == want and stored == bytes(4))
    # PC32 at P = table + o: S + A - P = .text + want + o - (table + o) = want - table
    say(ok, f"jt entry +{off}: {got and (got[0], e.secname(e.syms[got[1]]['shndx']), hex(got[2]))} "
        f"= {lab} - table")


# ------------------------------------------------------------- D ---------

# Objects that hold data the texts reach only through the GOT (no relocation in a text names
# the table itself): the label, the object, why.
DATA_OBJS = {
    # `ff_ps_read_data` loads `ff_log2_tab` through its GOT slot `ff_log2_tab_got`;
    # `libavutil/log2_tab.c` of the same build (the -g variant, as aacsbr.g.o).
    "ff_log2_tab": "log2_tab.g.o",
}


def text_objects():
  """label -> object, from tv.py's report: the object of the program whose relocation
  resolved the Lean label."""
  import json
  tvout = os.path.join(os.path.abspath(os.environ.get("SBR_OUT") or os.path.join(ROOT, ".lake", "sbr-ci")),
                       "tv")
  rep = json.load(open(os.path.join(tvout, "tv.json")))
  objof = {r["prog"]: r["obj"] for r in rep["results"]}
  out = {}
  for r in rep["relocs"]:
    l = r.get("lean_sym")
    if l and r.get("ok"):
      out.setdefault(l, set()).add(objof[r["prog"]])
  return out, tvout


def lookup(objn, label):
  """(elf, section, offset) of a Lean label in one object (aliases as tv.py)."""
  e = Elf(os.path.join(OBJDIR, objn))
  if label in LEAN_ALIAS:
    tgt, extra = LEAN_ALIAS[label]
    secs = [x for x in e.secs if x["name"] == tgt]
    if secs:
      return e, secs[0], extra
    r = lookup(objn, tgt)
    return (r[0], r[1], r[2] + extra) if r else None
  c = [x for x in e.syms if x["shndx"] and x["type"] != 3 and
       (x["name"] in (label, "." + label) or x["name"].endswith("." + label)
        or x["name"].lstrip(".").replace(".", "_") == label)]
  if len(c) != 1:
    return None
  sec = e.secs[c[0]["shndx"]]
  return e, sec, c[0]["value"] - sec["addr"]


def part_d():
  """Every constant byte list the two top theorems place at a label (`ExportData.lean`,
  from the elaborated closures) against the object's bytes there."""
  print("== D. placed constants (ExportData.lean) vs the objects")
  where, tvout = text_objects()
  path = os.environ.get("TV_DATA") or os.path.join(tvout, "data.txt")
  lines = [l.split() for l in open(path) if l[:2] in ("V ", "S ")]
  say(any(l[0] == "V" for l in lines), f"{path}: {sum(l[0] == 'V' for l in lines)} constants")
  for l in lines:
    if l[0] == "S":
      print(f"note  {l[1]}+{l[2]} ({l[3]}): symbolic contents (link/run time), "
            f"not object data")
      continue
    _, lab, off, hx, decl = l
    want = bytes.fromhex(hx)
    objs = where.get(lab, set())
    if lab in DATA_OBJS:
      objs = objs | {DATA_OBJS[lab]}
    if len(objs) != 1:
      say(False, f"{lab} ({decl}): in which object? {sorted(objs) or 'not referenced by a text'}")
      continue
    objn = objs.pop()
    r = lookup(objn, lab)
    if r is None:
      say(False, f"{lab} ({decl}): no unique symbol in {objn}")
      continue
    e, sec, o = r
    o += int(off)
    nobits = sec["type"] == 8
    got = b"" if nobits else e.data[sec["off"] + o: sec["off"] + o + len(want)]
    say(not nobits and not sec["flags"] & 1 and got == want,
        f"{lab}+{off} ({decl}) = {objn}:{sec['name']}+{o:#x}"
        f"{' (writable!)' if sec['flags'] & 1 else ''}: {len(want)} B "
        f"{'equal' if got == want else f'DIFFER: object {got.hex()} vs Lean {hx}'}")


if __name__ == "__main__":
  part_a()
  part_b()
  part_c()
  part_d()
  sys.exit(1 if bad else 0)
