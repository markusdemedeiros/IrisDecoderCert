"""Shared helpers of `gen.py` and `check.py` (placement in the linked binary).

The binary is an FFmpeg 8.1 `ffmpeg` PIE (opt build, the same compilation as the objects of
`../baseline/objects.sha256`). `TEXTS` lists the proved texts that the real image places, in
the order of `Real.rTexts` (KrakenSbrReal/Real.lean): adding a text is one entry
here and one in `rTexts`.
"""
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "tv"))
# tv.py reads SBR_OBJ_DIR at import; the real-binary tools need it only for `objcmp`.
os.environ.setdefault("SBR_OBJ_DIR", os.environ.get("SBR_OBJ_DIR") or "/nonexistent")
import tv  # noqa: E402  (Elf, relocs, to_mc, norm, PAD_RE, tool)

# (export name = tv/Export.lean program name, entry symbol, STT_FILE scope or None)
TEXTS = [
    ("ff_sbr_neg_odd_64_sse", "ff_sbr_neg_odd_64_sse", None),
    ("ff_sbr_sum64x5_sse", "ff_sbr_sum64x5_sse", None),
    ("ff_sbr_sum_square_sse", "ff_sbr_sum_square_sse", None),
    ("ff_sbr_qmf_pre_shuffle_sse2", "ff_sbr_qmf_pre_shuffle_sse2", None),
    ("ff_sbr_qmf_post_shuffle_sse", "ff_sbr_qmf_post_shuffle_sse", None),
    ("ff_sbr_qmf_deint_neg_sse", "ff_sbr_qmf_deint_neg_sse", None),
    ("ff_sbr_qmf_deint_bfly_sse2", "ff_sbr_qmf_deint_bfly_sse2", None),
    ("ff_sbr_autocorrelate_sse", "ff_sbr_autocorrelate_sse", None),
    ("ff_sbr_autocorrelate_sse3", "ff_sbr_autocorrelate_sse3", None),
    ("ff_sbr_hf_gen_sse", "ff_sbr_hf_gen_sse", None),
    ("ff_sbr_hf_g_filt_sse", "ff_sbr_hf_g_filt_sse", None),
    ("ff_sbr_hf_apply_noise", "ff_sbr_hf_apply_noise_0_sse2", None),
    ("sbr_qmf_synthesis", "sbr_qmf_synthesis", "aacsbr.c"),
    ("sbr_lf_gen", "sbr_lf_gen", "aacsbr.c"),
    ("sbr_hf_inverse_filter", "sbr_hf_inverse_filter", "aacsbr.c"),
    ("sbr_x_gen", "sbr_x_gen", "aacsbr.c"),
    ("sbr_hf_assemble", "sbr_hf_assemble", "aacsbr.c"),
    ("ff_aac_sbr_apply", "ff_aac_sbr_apply", None),
    ("ff_vector_fmul_sse", "ff_vector_fmul_sse", None),
    ("ff_vector_fmul_avx", "ff_vector_fmul_avx", None),
    ("ff_vector_fmul_add_sse", "ff_vector_fmul_add_sse", None),
    ("ff_vector_fmul_add_avx", "ff_vector_fmul_add_avx", None),
    ("ff_vector_fmul_add_fma3", "ff_vector_fmul_add_fma3", None),
    ("ff_vector_fmul_reverse_sse", "ff_vector_fmul_reverse_sse", None),
    ("ff_vector_fmul_reverse_avx", "ff_vector_fmul_reverse_avx", None),
    ("ff_vector_fmul_reverse_avx2", "ff_vector_fmul_reverse_avx2", None),
]

# Labels the statements name that must sit at their real address (CstW, LabAligned).
STMT_LABELS = [
    "LCPI14_0", "LCPI14_5", "LCPI14_6", "LCPI14_9", "LCPI14_10", "LCPI14_11", "LCPI14_12",
    "LCPI14_13", "LCPI14_14", "LCPI14_15", "LCPI14_16", "LCPI14_17", "LCPI14_3", "LCPI14_1",
    "LCPI14_2", "LCPI14_8", "exp2_tab", "bw_tab", "limgain", "sbr_qmf_window_ds", "ff_ps_neg",
    "ps_mask", "LCPI19_0", "LCPI19_1", "LCPI19_2", "ps_mask3", "sbr_qmf_window_us", "LCPI15_1",
    "ps_mask2", "ff_sbr_noise_table", "ps_noise0", "ps_noise13", "ps_noise2", "LCPI17_6",
    "LCPI17_7", "LCPI17_8", "LCPI17_9", "LCPI17_10", "LCPI17_12", "LCPI14_4", "LCPI17_11",
    "pd_reverse"]

GOT = "_GLOBAL_OFFSET_TABLE_"


def run(cmd):
  r = subprocess.run(cmd, capture_output=True, text=True)
  if r.returncode != 0:
    raise RuntimeError(f"{' '.join(cmd)} failed:\n{r.stderr[:2000]}")
  return r.stdout


class Binary:
  """The linked binary: sections, symbols (with their STT_FILE scope), bytes at addresses,
  and a linear-sweep disassembly of a range (on a copy without STT_OBJECT symbols in code,
  so that llvm-objdump does not dump behind NASM's `.end`/`.loop` object labels as data)."""

  def __init__(self, path, work):
    self.path = path
    self.elf = tv.Elf(path)
    self.work = work
    scope = None
    self.syms = []
    for s in self.elf.syms:
      if s["type"] == 4:
        scope = s["name"]
        continue
      self.syms.append(dict(s, scope=scope if s["bind"] == 0 else None))
    self._nodata = None

  def sym(self, name, scope=None):
    c = [s for s in self.syms if s["name"] == name and s["shndx"] != 0 and s["type"] in (0, 1, 2)
         and (scope is None or s["scope"] == scope)]
    if scope is None and len(c) > 1:
      g = [s for s in c if s["bind"] != 0]
      c = g or c
    if len(c) != 1:
      raise KeyError(f"symbol {name} (scope {scope}): {len(c)} candidates")
    return c[0]

  def syms_named(self, name):
    return [s for s in self.syms if s["name"] == name and s["shndx"] != 0]

  def bytes(self, addr, n):
    for s in self.elf.secs:
      if s["type"] == 1 and s["addr"] <= addr and addr + n <= s["addr"] + s["size"]:
        return self.elf.data[s["off"] + addr - s["addr"]: s["off"] + addr - s["addr"] + n]
    raise KeyError(f"{addr:#x}+{n}: not in a PROGBITS section")

  def section_of(self, addr):
    for s in self.elf.secs:
      if s["addr"] and s["addr"] <= addr < s["addr"] + s["size"]:
        return s
    return None

  def nodata(self):
    if self._nodata is None:
      os.makedirs(self.work, exist_ok=True)
      bad = sorted({s["name"] for s in self.syms if s["type"] == 1 and s["shndx"]
                    and s["shndx"] < len(self.elf.secs) and self.elf.secs[s["shndx"]]["flags"] & 4})
      out = os.path.join(self.work, "bin.nodata")
      lst = os.path.join(self.work, "bin.nodata.syms")
      open(lst, "w").write("\n".join(bad) + "\n")
      run([tv.tool("llvm-objcopy"), f"--strip-symbols={lst}", self.path, out])
      self._nodata = out
    return self._nodata

  def disasm(self, start, stop):
    """[(addr, text)] (Intel, objdump's `# 0x... <sym>` comments kept)."""
    out = run([tv.tool("llvm-objdump"), "-d", "-z", "-M", "intel", "--no-show-raw-insn",
               f"--start-address={start:#x}", f"--stop-address={stop:#x}", self.nodata()])
    res = []
    for line in out.splitlines():
      m = re.match(r"^\s*([0-9a-f]+):\s+(.*)$", line)
      if m:
        res.append((int(m[1], 16), m[2]))
    return res


def read_export(leandir, prog):
  """Cells of an exported text (tv/Export.lean): ("label", name) or ("insn", intel text)."""
  items = []
  for line in open(os.path.join(leandir, prog + ".txt")):
    line = line.rstrip("\n")
    if not line:
      continue
    if not line.startswith(" "):
      assert line.endswith(":"), line
      items.append(("label", line[:-1]))
    else:
      items.append(("insn", line.strip().partition(" ;; ")[0]))
  return items


# Label references of a Kraken Intel instruction text: (label, offset, kind)
REF_RES = [
    (re.compile(r"\[rip\+\(([A-Za-z_.][\w.]*) \+ (\d+)\)\]"), "rip"),
    (re.compile(r"\[rip\+([A-Za-z_.][\w.]*)\]"), "rip"),
    (re.compile(r"^(?:call|jmp|j[a-z]+) ([A-Za-z_.][\w.]*)$"), "branch"),
    (re.compile(r"\(([A-Za-z_.][\w.]*) - " + GOT + r"\)"), "gotoff"),
]


REG_RE = re.compile(r"^(?:[re]?[abcd]x|[re]?[sd]il?|[re]?[sb]pl?|r\d+[dwb]?|[abcd][lh])$")


def refs(txt):
  out = []
  for rx, kind in REF_RES:
    for m in rx.finditer(txt):
      if REG_RE.match(m[1]):
        continue
      off = int(m[2]) if kind == "rip" and m.lastindex == 2 else 0
      out.append((m[1], off, kind))
  return out


def target_of(kind, btext):
  """The address the binary instruction encodes for a reference of this kind."""
  if kind in ("rip", "branch"):
    m = re.search(r"# 0x([0-9a-f]+)", btext) if kind == "rip" else \
        re.match(r"^\S+\s+0x([0-9a-f]+)", btext)
    return int(m[1], 16) if m else None
  if kind == "gotoff":
    m = re.match(r"^movabs\s+\w+,\s+(-?0x[0-9a-f]+|-?\d+)$", btext)
    return int(m[1], 0) if m else None
  return None
