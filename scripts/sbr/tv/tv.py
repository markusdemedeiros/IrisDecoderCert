#!/usr/bin/env python3
"""Translation validation of the SBR proofs' programs against the object code.

Input: `$SBR_OUT/tv/lean/<prog>.txt`, printed by `Export.lean` from the elaborated
`Program` terms (Intel syntax, `Kraken/X64/PrintIntel.lean`), and the objects.

For each program:
 1. Instruction boundaries of the object (llvm-objdump linear sweep of the
    routine, on a copy whose STT_OBJECT symbols in code are removed so that
    llvm-objdump does not print NASM's `.end` labels as data).
 2. Lean instructions are matched 1:1, in order, to the object instructions
    starting at the entry symbol (a Lean `nop` must meet an object padding
    instruction).
 3. The Lean text is re-assembled with llvm-mc, each instruction placed by
    `.org` at its object address (relative to the entry), with its labels in
    front of it, so that label addresses, and hence branch displacements, are
    those the Lean text implies. An end marker after each instruction gives its
    length.
 4. Per instruction: bytes compared with the object (relocation fields masked),
    relocation targets compared after resolution to (section, offset) or
    (external symbol, addend). If bytes differ, both encodings are decoded and
    the decoded texts compared ("different encoding").
 5. Coverage: the object instructions behind the last Lean instruction, up to
    the routine's end, must be padding. Labels named like an object symbol must
    sit at that symbol's address; labels `<sym>.L<hex>` at address <hex>.
 Relocation targets: Lean labels resolve to the object symbol of that name, or by
 LEAN_ALIAS (data the object has no symbol for), or `<sym>_got` to `<sym>`'s GOT slot.
Exit status 1 on any FINDING.
"""
import json
import os
import re
import struct
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("SBR_ROOT") or os.path.abspath(os.path.join(HERE, "..", "..", ".."))
# Output: $SBR_OUT/tv (default <repo>/.lake/sbr-ci/tv).
TVOUT = os.path.join(os.path.abspath(os.environ.get("SBR_OUT") or os.path.join(ROOT, ".lake", "sbr-ci")), "tv")
OBJDIR = os.environ.get("SBR_OBJ_DIR", "")
if not OBJDIR:
  sys.exit("tv: SBR_OBJ_DIR is not set (directory holding aacsbr.rela.o, aacsbr.pic.o, "
           "aacsbr.g.o, aacps_common.{rela,pic,g}.o, sbrdsp.o and float_dsp.o; see scripts/sbr/README.md)")
OBJS = {"sbrdsp": os.path.join(OBJDIR, "sbrdsp.o"), "float_dsp": os.path.join(OBJDIR, "float_dsp.o"),
        "aacps": os.path.join(OBJDIR, "aacps_common.rela.o"),
        "aacsbr": os.path.join(OBJDIR, "aacsbr.rela.o")}
WORK = os.path.join(TVOUT, "work")
LEANDIR = os.environ.get("TV_LEANDIR") or os.path.join(TVOUT, "lean")


def tool(name):
  """An llvm tool: from $LLVM_BIN if set, else from PATH."""
  if os.environ.get("LLVM_BIN"):
    return os.path.join(os.environ["LLVM_BIN"], name)
  import shutil
  t = shutil.which(name)
  if not t:
    sys.exit(f"tv: {name} not found on PATH (set LLVM_BIN to the llvm bin directory)")
  return t


def run(cmd, **kw):
  r = subprocess.run(cmd, capture_output=True, text=True, **kw)
  if r.returncode != 0:
    raise RuntimeError(f"{' '.join(cmd)} failed:\n{r.stderr}")
  return r.stdout


# ---------------------------------------------------------------- ELF ----

class Elf:
  def __init__(self, path):
    self.path = path
    data = open(path, "rb").read()
    self.data = data
    (shoff,) = struct.unpack_from("<Q", data, 0x28)
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 0x3a)
    secs = []
    for i in range(shnum):
      name, typ, flags, addr, off, size, link, info, align, entsize = struct.unpack_from(
          "<IIQQQQIIQQ", data, shoff + i * shentsize)
      secs.append(dict(name_off=name, type=typ, flags=flags, addr=addr, off=off, size=size,
                       link=link, info=info, align=align, entsize=entsize, idx=i))
    strtab = secs[shstrndx]
    for s in secs:
      s["name"] = self._str(strtab, s["name_off"])
    self.secs = secs
    self.syms = []
    for s in secs:
      if s["type"] == 2:  # SYMTAB
        st = secs[s["link"]]
        for j in range(s["size"] // 24):
          nm, info, other, shndx, value, size = struct.unpack_from("<IBBHQQ", data, s["off"] + j * 24)
          self.syms.append(dict(name=self._str(st, nm), type=info & 0xf, bind=info >> 4,
                                shndx=shndx, value=value, size=size))

  def _str(self, sec, off):
    o = sec["off"] + off
    e = self.data.index(b"\0", o)
    return self.data[o:e].decode()

  def sec(self, name):
    return next(s for s in self.secs if s["name"] == name)

  def secname(self, idx):
    return self.secs[idx]["name"] if 0 < idx < len(self.secs) else None

  def bytes_at(self, secname, addr, n):
    s = self.sec(secname)
    return self.data[s["off"] + addr - s["addr"]: s["off"] + addr - s["addr"] + n]

  def sym(self, name):
    c = [s for s in self.syms if s["name"] == name and s["shndx"] != 0]
    return c[0] if c else None


def relocs(path, section=".text"):
  """offset -> (type, symbol, addend), read by llvm-objdump (reads CREL)."""
  out = run([tool("llvm-objdump"), "-r", path])
  res, sec = {}, None
  for line in out.splitlines():
    m = re.match(r"^RELOCATION RECORDS FOR \[(.+)\]:$", line)
    if m:
      sec = m[1]
      continue
    m = re.match(r"^([0-9a-f]+)\s+(R_\S+)\s+(\S+)$", line)
    if m and sec == section:
      t = re.match(r"^(.+?)([+-]0x[0-9a-f]+)?$", m[3])
      res[int(m[1], 16)] = (m[2], t[1], int(t[2] or "0", 16))
  return res


def disasm(path, start, stop, adjust=0, section=".text"):
  """[(addr, text)] by llvm-objdump (Intel)."""
  cmd = [tool("llvm-objdump"), "-d", "-M", "intel", "--no-show-raw-insn", "-j", section,
         f"--start-address={start - adjust:#x}", f"--stop-address={stop - adjust:#x}", path]
  if adjust:
    cmd.insert(1, f"--adjust-vma={adjust:#x}")
  out = run(cmd)
  res = []
  for line in out.splitlines():
    m = re.match(r"^\s*([0-9a-f]+):\s+(.*)$", line)
    if m:
      res.append((int(m[1], 16), m[2]))
  return res


def norm(text):
  t = text.split("#", 1)[0]
  t = re.sub(r"<[^>]*>", "", t)
  return re.sub(r"\s+", " ", t).strip()


PAD_RE = re.compile(r"^(?:(?:data16|cs|ds) )*(?:nop[wlq]?\b.*|xchg ax, ax)$")

_STRIPPED = {}


def boundaries_obj(key):
  """A copy of the object without STT_OBJECT symbols in code (so llvm-objdump
  disassembles behind NASM's `.end` labels)."""
  if key in _STRIPPED:
    return _STRIPPED[key]
  path = OBJS[key]
  e = Elf(path)
  bad = [s["name"] for s in e.syms
         if s["type"] == 1 and s["shndx"] and e.secs[s["shndx"]]["flags"] & 4]
  out = os.path.join(WORK, os.path.basename(path) + ".nodata.o")
  cmd = [tool("llvm-objcopy")] + [f"--strip-symbol={n}" for n in bad] + [path, out]
  run(cmd)
  _STRIPPED[key] = (out, bad)
  return _STRIPPED[key]


# -------------------------------------------------------------- Lean -----

def read_lean(prog):
  items = []
  for line in open(os.path.join(LEANDIR, prog + ".txt")):
    line = line.rstrip("\n")
    if not line:
      continue
    if not line.startswith(" "):
      assert line.endswith(":"), line
      items.append(("label", line[:-1]))
    else:
      txt, _, meta = line.strip().partition(" ;; ")
      items.append(("insn", txt, meta))
  return items


def to_mc(txt):
  """Kraken's Intel print -> llvm-mc Intel input (only cosmetic rewrites)."""
  t = txt.replace("+-", "-")
  # `movsx r64, r/m32` is spelled movsxd by llvm-mc.
  m = re.match(r"^movsx (r\w+), (e\w+|r\d+d|DWORD PTR .*)$", t)
  if m:
    t = f"movsxd {m[1]}, {m[2]}"
  # Kraken's `imm = lab X - lab _GLOBAL_OFFSET_TABLE_` is the assembler's
  # `X@GOTOFF` (R_X86_64_GOTOFF64, value S + A - GOT), a 64-bit immediate.
  m = re.match(r"^mov (r\w+), \((\S+) - _GLOBAL_OFFSET_TABLE_\)$", t)
  if m:
    t = f"movabs {m[1]}, offset {m[2]}@GOTOFF"
  return t


RELSIZE = {"R_X86_64_PC32": 4, "R_X86_64_PLT32": 4, "R_X86_64_GOTPC32": 4, "R_X86_64_GOTOFF64": 8,
           "R_X86_64_GOTPCREL": 4, "R_X86_64_GOTPCRELX": 4, "R_X86_64_REX_GOTPCRELX": 4}
GOTREL = ("R_X86_64_GOTPCREL", "R_X86_64_GOTPCRELX", "R_X86_64_REX_GOTPCRELX")

# Lean labels for data without an object symbol of that name, as (target, offset): the target
# is an object symbol (resolved as the Lean names are) or a section name. Each is a separate
# label of the proofs (its own footprint region), placed where the object has the data.
#  * `sbr_offset_<k>`: row k of `static const int8_t sbr_offset[6][16]` (sbr_reset);
#  * `sbr_make_f_tablelim_bw`: the function-local `bands_warped[3]` of sbr_make_f_tablelim;
#  * `read_sbr_grid_jt`: read_sbr_grid's switch jump table, at the start of `.rodata` (no
#    symbol; its entries are checked by tv_data.py).
LEAN_ALIAS = dict({f"sbr_offset_{k}": ("sbr_offset", 16 * k) for k in range(6)},
                  sbr_make_f_tablelim_bw=("sbr_make_f_tablelim.bands_warped", 0),
                  read_sbr_grid_jt=(".rodata", 0))
# A Lean label `<sym>_got` is the GOT slot of `<sym>`: the proofs assume it holds `lab "<sym>"`
# (ff_ps_read_data: `PsSpec`), and the object loads it through a GOTPCREL-type relocation.


# ----------------------------------------------------------- compare -----

def resolve(elf, sym, addend, lean_side):
  """Canonical (base, offset) of a relocation target S + A."""
  s = None
  if lean_side and sym in LEAN_ALIAS:
    tgt, extra = LEAN_ALIAS[sym]
    if any(x["name"] == tgt for x in elf.secs):
      return (tgt, extra + addend)
    b, o = resolve(elf, tgt, extra + addend, True)
    return (b, o)
  if lean_side:
    # Kraken label names: `.LCPI14_4` -> `LCPI14_4`, `.L.str.1` -> `L_str_1`,
    # function-local statics `sbr_dequant.exp2_tab` -> `exp2_tab`.
    def mangle(n):
      return n.lstrip(".").replace(".", "_")
    cands = [x for x in elf.syms if x["shndx"] and x["type"] != 3 and
             (x["name"] in (sym, "." + sym) or x["name"].endswith("." + sym)
              or mangle(x["name"]) == sym)]
    if len(cands) > 1:
      exact = [x for x in cands if x["name"] in (sym, "." + sym)]
      cands = exact or cands
    if len(cands) == 1:
      s = cands[0]
    elif cands:
      return ("AMBIGUOUS:" + sym, addend)
  else:
    secs = [x for x in elf.secs if x["name"] == sym]
    if secs:
      return (sym, addend)
    s = elf.sym(sym)
  if s is None:
    return (sym, addend)  # external
  return (elf.secname(s["shndx"]), s["value"] + addend)


def obj_symname(elf, base, off):
  names = [x["name"] for x in elf.syms if x["shndx"] and elf.secname(x["shndx"]) == base
           and x["value"] == off and x["type"] in (0, 1, 2)]
  return names


def check(prog, report):
  items = read_lean(prog)
  entry = items[0][1]
  key = next((k for k in ("sbrdsp", "float_dsp", "aacps") if Elf(OBJS[k]).sym(entry)), "aacsbr")
  path = OBJS[key]
  elf = Elf(path)
  esym = elf.sym(entry)
  esec = elf.secname(esym["shndx"])
  base = esym["value"]
  bpath, _ = boundaries_obj(key)
  secend = elf.sec(esec)["addr"] + elf.sec(esec)["size"]
  oins = disasm(bpath, base, secend, section=esec)
  orel = relocs(path, esec)
  findings, notes, allowed, diffenc, link = [], [], [], [], []
  end = secend  # refined after matching
  # --- 2. match
  plan, k, pending = [], 0, []
  for it in items:
    if it[0] == "label":
      pending.append(it[1])
      continue
    # object padding the Lean text leaves out (NASM alignment between entries)
    if not it[1].startswith(".nops"):
      skipped = []
      while k < len(oins) and PAD_RE.match(norm(oins[k][1])):
        skipped.append(oins[k])
        k += 1
      if skipped:
        prev = plan[-1]["lean"] if plan else None
        gap = (skipped[0][0], oins[k][0] if k < len(oins) else end)
        report["gaps"].append(dict(prog=prog, start=gap[0], stop=gap[1], prev=prev,
                                   labels_after=pending))
        if pending and prev is not None:
          # PlacedIn.next demands that the block before `pending[0]` end at its address
          link.append(f"{gap[0]:#x}..{gap[1]:#x}: {len(skipped)} padding instruction(s) of the "
                      f"object are not in the Lean text, between `{prev}` and label {pending[0]}: "
                      f"Program.PlacedIn.next requires the block before {pending[0]} to end at "
                      f"{pending[0]}'s address; in the object it ends at {gap[0]:#x}, not {gap[1]:#x}")
        else:
          findings.append(f"{gap[0]:#x}: object padding not in Lean text, not before a label")
    if k >= len(oins):
      findings.append(f"Lean instruction `{it[1]}` beyond the object's code")
      break
    plan.append(dict(lean=it[1], meta=it[2], addr=oins[k][0], otext=oins[k][1], labels=pending,
                     olen=(oins[k + 1][0] if k + 1 < len(oins) else secend) - oins[k][0]))
    pending, k = [], k + 1
  if pending:
    findings.append(f"labels at the end of the text, behind every instruction: {pending}")
  last_end = plan[-1]["addr"] + plan[-1]["olen"]
  # routine end: the entry's st_size when set (C), else the next function symbol
  # behind the last Lean instruction (NASM symbols have size 0)
  if esym["size"]:
    end = base + esym["size"]
  else:
    nxt = [s["value"] for s in elf.syms if s["shndx"] == esym["shndx"] and s["type"] == 2
           and s["value"] >= last_end]
    end = min(nxt) if nxt else secend
  # coverage behind the last Lean instruction
  tail = [(a, t) for a, t in oins[k:] if a < end]
  bad_tail = [(a, t) for a, t in tail if not (PAD_RE.match(norm(t)) or norm(t) == "int3")]
  if bad_tail:
    findings.append(f"object instructions behind the Lean text not covered: "
                    f"{[(hex(a), norm(t)) for a, t in bad_tail[:5]]} ({len(bad_tail)})")
  if last_end < end and tail:
    notes.append(f"{len(tail)} padding instruction(s) behind the text up to {end:#x} not in Lean")
  # --- 3. assemble
  asm = [".intel_syntax noprefix", ".text"]
  lean_labels = set(it[1] for it in items if it[0] == "label")
  for i, p in enumerate(plan):
    asm.append(f".org {p['addr'] - base:#x}")
    for l in p["labels"]:
      asm.append(f"{l}:")
    if p["lean"].startswith(".nops"):
      p["pad"] = True
      continue
    if norm(p["otext"]) == "ret" and p["lean"].startswith("jmp "):
      # object `ret`, Lean `jmp <block>`: the block must be a lone `ret` (checked below,
      # ret_targets). Assembled as `ret` so that the 2-byte `jmp` does not run into the
      # next instruction's `.org` (when the object has more code or padding behind it).
      p["retjmp"] = True
      asm.append("ret")
    else:
      asm.append(to_mc(p["lean"]))
    asm.append(f"__tv_end_{i}:")
  os.makedirs(WORK, exist_ok=True)
  sfile = os.path.join(WORK, prog + ".s")
  ofile = os.path.join(WORK, prog + ".o")
  open(sfile, "w").write("\n".join(asm) + "\n")
  r = subprocess.run([tool("llvm-mc"), "-triple=x86_64", "-filetype=obj", "-o", ofile, sfile],
                     capture_output=True, text=True)
  if r.returncode != 0:
    findings.append("llvm-mc failed on the Lean text:\n" + r.stderr[:4000])
    return dict(prog=prog, obj=os.path.basename(path), findings=findings, notes=notes, n=len(plan))
  gelf = Elf(ofile)
  grel = relocs(ofile)
  gends = {s["name"]: s["value"] for s in gelf.syms if s["name"].startswith("__tv_end_")}
  gtext = gelf.sec(".text")
  gb = gelf.data[gtext["off"]: gtext["off"] + gtext["size"]]
  gins = None
  ident = 0
  # --- 4. compare
  for i, p in enumerate(plan):
    a, off = p["addr"], p["addr"] - base
    ot = norm(p["otext"])
    if p.get("pad"):
      mn = re.match(r"^\.nops (\d+)$", p["lean"].strip())
      if not PAD_RE.match(ot):
        findings.append(f"{a:#x}: Lean `nop` but object `{ot}`")
      elif not mn:
        findings.append(f"{a:#x}: Lean padding `{p['lean']}` not of the form `.nops n`")
      elif int(mn[1]) == p["olen"]:
        ident += 1  # a sized Lean `nop n` on object padding of exactly n bytes
      elif int(mn[1]) == 1:
        # an unsized Lean `nop` (the parser gives `.nop 1`) on multi-byte object padding
        allowed.append(("padding", a, ot, p["lean"]))
      else:
        findings.append(f"{a:#x}: Lean nop {mn[1]} B but object padding `{ot}` is {p['olen']} B")
      continue
    if p.get("retjmp"):
      allowed.append(("ret->jmp done", a, ot, p["lean"]))
      notes.append(f"{a:#x}: object `ret`, Lean `{p['lean']}` (checked: see ret_targets)")
      report.setdefault("ret_targets", []).append((prog, a, p["lean"].split()[1]))
      continue
    glen = gends[f"__tv_end_{i}"] - off
    ob = elf.bytes_at(esec, a, p["olen"])
    lb = gb[off: off + glen]
    # relocation fields in range
    ofields = {o: v for o, v in orel.items() if a <= o < a + p["olen"]}
    gfields = {o + base: v for o, v in grel.items() if off <= o < off + glen}
    mask = set()
    for o, v in list(ofields.items()) + list(gfields.items()):
      if v[0] not in RELSIZE:
        findings.append(f"{a:#x}: unexpected relocation type {v}")
      mask.update(range(o, o + RELSIZE.get(v[0], 4)))
    for o in set(ofields) & set(gfields):
      if ofields[o][0] != gfields[o][0]:
        notes.append(f"{a:#x}: relocation type object {ofields[o][0]} vs Lean {gfields[o][0]}")
    same_bytes = glen == p["olen"] and all(
        ob[j] == lb[j] for j in range(glen) if a + j not in mask)
    # relocation targets
    rel_ok, rel_desc = True, []
    for o in sorted(set(ofields) | set(gfields)):
      if o in ofields:
        t, s, ad = ofields[o]
        oc = ("GOT:" + s, ad) if t in GOTREL else resolve(elf, s, ad, False)
      else:  # resolved by the assembler: S + A = disp + P
        disp = struct.unpack_from("<i", ob, o - a)[0]
        oc = (esec, disp + o)
      if o in gfields:
        t, s, ad = gfields[o]
        lc = (("GOT:" + s[:-4], ad) if s.endswith("_got") and t == "R_X86_64_PC32"
              else resolve(elf, s, ad, True))
        lsym = s
      else:
        disp = struct.unpack_from("<i", lb, o - a)[0] if o - a + 4 <= len(lb) else None
        lc = (esec, None if disp is None else disp + o)
        lsym = None
      ok = oc == lc
      rel_ok &= ok
      on = obj_symname(elf, oc[0], oc[1] + 4) if isinstance(oc[1], int) else []
      rel_desc.append(dict(addr=a, field=o, obj=list(oc), lean=list(lc), lean_sym=lsym,
                           obj_sym_at_target_plus4=on, ok=ok))
    for d in rel_desc:
      report["relocs"].append(dict(prog=prog, **d))
    if not rel_ok:
      findings.append(f"{a:#x}: relocation target mismatch {rel_desc}")
    if same_bytes:
      ident += 1
      continue
    # decode both and compare
    if gins is None:
      gins = {ad: t for ad, t in disasm(ofile, base, base + len(gb), adjust=base)}
    lt = norm(gins.get(a, "?"))
    if lt == ot:
      diffenc.append((a, ot, ob.hex(), lb.hex()))
      continue
    # `rep ret` (f3 c3, NASM's RET macro for AMD predictors): the F3 prefix has no
    # defined effect on `ret`; Kraken's parser reads it as `ret`.
    if ot in ("rep ret", "repz ret", "rep ret") and lt == "ret" and ob == b"\xf3\xc3":
      allowed.append(("rep ret = ret", a, ot, p["lean"]))
      continue
    # ret <-> jmp to a block that is just `ret`
    if ot == "ret" and p["lean"].startswith("jmp "):
      allowed.append(("ret->jmp done", a, ot, p["lean"]))
      notes.append(f"{a:#x}: object `ret`, Lean `{p['lean']}` (checked: see ret_targets)")
      report.setdefault("ret_targets", []).append((prog, a, p["lean"].split()[1]))
      continue
    findings.append(f"{a:#x}: object `{ot}` [{ob.hex()}] vs Lean `{p['lean']}` -> `{lt}` [{lb.hex()}]")
  # --- 5. labels
  symaddr = {s["name"]: s["value"] for s in elf.syms if s["shndx"] == esym["shndx"]}
  labaddr = {}
  for p in plan:
    for l in p["labels"]:
      labaddr[l] = p["addr"]
  for l, ad in labaddr.items():
    if l in symaddr and symaddr[l] != ad:
      findings.append(f"label {l} at {ad:#x} but object symbol {l} at {symaddr[l]:#x}")
    m = re.match(r"^.*\.L([0-9a-f]+)(_\d+)?$", l)
    if m and int(m[1], 16) != ad and l not in symaddr:
      # `<sym>.L<hex>` names the object address <hex> (tv_data.py relies on it for the jump
      # table); `<sym>.L<hex>_<n>` is a later cut in the block that starts there.
      (notes if m[2] else findings).append(f"label {l} sits at {ad:#x} (name says {m[1]})")
  # ret_targets: the jump target block must be a lone `ret`
  for (pg, a, tgt) in report.get("ret_targets", []):
    if pg != prog:
      continue
    idx = [i for i, p in enumerate(plan) if tgt in p["labels"]]
    if not idx or norm(plan[idx[0]]["lean"]) != "ret":
      findings.append(f"{a:#x}: object ret, Lean jmp {tgt}, but {tgt} is not a lone ret")
  return dict(prog=prog, obj=os.path.basename(path), entry=f"{entry}@{base:#x}", end=hex(end),
              last=hex(last_end), n=len(plan), ident=ident, diffenc=diffenc, allowed=allowed,
              findings=findings, notes=notes, link=link,
              labels_checked=sum(1 for l in labaddr if l in symaddr))


def main():
  progs = sys.argv[1:] or sorted(f[:-4] for f in os.listdir(LEANDIR))
  os.makedirs(WORK, exist_ok=True)
  report = {"relocs": [], "gaps": []}
  results = []
  bad = 0
  for prog in progs:
    res = check(prog, report)
    results.append(res)
    bad += len(res["findings"]) + len(res.get("link", []))
    print(f"{prog:32} {res.get('entry','')} n={res['n']} ident={res.get('ident')} "
          f"diffenc={len(res.get('diffenc', []))} allowed={len(res.get('allowed', []))} "
          f"findings={len(res['findings'])} link={len(res.get('link', []))}")
    for f in res["findings"]:
      print("  FINDING:", f)
    for f in res.get("link", []):
      print("  LINK:", f)
  report["results"] = results
  json.dump(report, open(os.path.join(os.environ.get("TV_JSON_DIR") or TVOUT, "tv.json"), "w"), indent=1)
  sys.exit(1 if bad else 0)


if __name__ == "__main__":
  main()
