#!/usr/bin/env python3
"""Generates Kraken/X64/Examples/Sbr/Parse/InitLink.lean: the element after a successful
`ff_aac_sbr_ctx_alloc_init` (ElemS at evInit) as the session's description of the element.

The session's cells (groups) are listed with offsets from the element `p`; the element's cells
(ElemS) are cut at the group boundaries. A group is `same` (the element's cell is the session's
cell) or `raw` (the element's cells become one raw block).

Usage: link.py > Kraken/X64/Examples/Sbr/Parse/InitLink.lean
"""

S = 0x28920          # sbr
D0 = S + 0x80        # sbr->data[0]
D1 = S + 0x15B40     # sbr->data[1]
PS = S + 0x2B600     # sbr->ps
TB = S + 0x4C1E0     # the frequency tables

# ---- the element's cells (ElemS at evInit, zero values as zero runs) ----
# (offset, size, expr or None for zero)
elem = [
  (0x0, 0x9E40, None),
  (0x9E40, 8, "Int.toBytes 8 (r.p + 0x1e120#64).toInt"),
  (0x9E48, 0x9DB8, None),
  (0x13C00, 8, "Int.toBytes 8 (r.p + 0x23520#64).toInt"),
  (0x13C08, 0x14D1C, None),
  (0x28924, 8, None),                       # start, ready (zero)
  (0x2892C, 4, "Int.toBytes 4 id.toInt"),
  (0x28930, 4, None),                       # usac (zero)
  (0x28934, 8, None),
  (0x2893C, 4, "Int.toBytes 4 (-1)"),
  (0x28940, 2, "Int.toBytes 2 (-1)"),
  (0x28942, 0x32, None),
  (0x28974, 4, None),                       # kx[0] (zero)
  (0x28978, 4, "Int.toBytes 4 32"),
  (0x2897C, 4, None),
  (0x28980, 4, None),                       # m[1] (zero)
  (0x28984, 0x391C, None),
  (0x2C2A0, 4, "Int.toBytes 4 0x480"),
  (0x2C2A4, 4, None),
  (0x2C2A8, 4, "Int.toBytes 4 (-1)"),
  (0x2C2AC, 0x15AB4, None),
  (0x41D60, 4, "Int.toBytes 4 0x480"),
  (0x41D64, 4, None),
  (0x41D68, 4, "Int.toBytes 4 (-1)"),
  (0x41D6C, 0x32D4C, None),
  (0x74AB8, 0x40, "r.psd"),
  (0x74AF8, 0x13FE8, None),
  (0x88AE0, 8, "Int.toBytes 8 r.anaCtx.toInt"),
  (0x88AE8, 8, "fb r.anaFn"),
  (0x88AF0, 8, "Int.toBytes 8 r.synCtx.toInt"),
  (0x88AF8, 8, "fb r.synFn"),
]
SLOTS = ["sum64x5", "sumSquare", "negOdd64", "preShuffle", "postShuffle", "deintNeg",
         "deintBfly", "autocorr", "hfGen", "gfilt", "noise0", "noise1", "noise2", "noise3"]
for i, f in enumerate(SLOTS):
  elem.append((0x88B00 + 8 * i, 8, f"fb r.sl.{f}"))
elem += [
  (0x88B70, 8, 'fb (entry "sbr_lf_gen")'),
  (0x88B78, 8, 'fb (entry "sbr_hf_assemble")'),
  (0x88B80, 8, 'fb (entry "sbr_x_gen")'),
  (0x88B88, 8, 'fb (entry "sbr_hf_inverse_filter")'),
  (0x88B90, 0x10, None),
]
# lengths of the value cells (for raw groups)
VLEN = {"r.psd": "hpsd"}

# ---- the session's cells ----
groups = []  # (offset, size, kind)
def g(o, n, k="same"):
  groups.append((o, n, k))

g(0, S, "raw")
for o, n, k in [(0x0, 4, "same"), (0x4, 4, "same"), (0x8, 4, "same"), (0xC, 4, "same"),
                (0x10, 4, "same"), (0x14, 4, "same"), (0x18, 4, "same"), (0x1C, 4, "same"),
                (0x20, 2, "same"), (0x22, 2, "raw"), (0x24, 4, "same"), (0x28, 4, "raw"),
                (0x2C, 4, "same"), (0x30, 4, "same"), (0x34, 4, "same"), (0x38, 4, "same"),
                (0x3C, 4, "same"), (0x40, 4, "same"), (0x44, 16, "raw"), (0x54, 4, "same"),
                (0x58, 4, "same"), (0x5C, 4, "same"), (0x60, 4, "same"), (0x64, 4, "same"),
                (0x68, 0x18, "raw")]:
  g(S + o, n, k)
DATA = [(0, 4, "raw"), (4, 4, "raw"), (8, 4, "same"), (0xC, 9, "same"), (0x15, 3, "raw"),
        (0x18, 4, "same"), (0x1C, 11, "raw"), (0x27, 10, "same"), (0x31, 48, "raw"),
        (0x61, 3, "raw"), (0x64, 4, "raw"), (0x68, 0x3898, "raw"), (0x3900, 4, "same"),
        (0x3904, 4, "raw"), (0x3908, 4, "raw"), (0x390C, 0x4014, "raw"), (0x7920, 4, "same"),
        (0x7924, 0xE178, "raw"), (0x15A9C, 10, "same"), (0x15AA6, 3, "same"),
        (0x15AA9, 3, "raw"), (0x15AAC, 8, "same"), (0x15AB4, 12, "raw")]
for d in (D0, D1):
  for o, n, k in DATA:
    g(d + o, n, k)
g(PS, 764)
g(PS + 764, 4, "raw"); g(PS + 768, 133200, "raw"); g(PS + 133968, 68); g(PS + 134036, 76, "raw")
for o, n, k in [(0, 4, "same"), (4, 4, "same"), (8, 4, "same"), (0xC, 4, "same"),
                (0x10, 98, "raw"), (0x72, 50, "same"), (0xA4, 98, "same"), (0x106, 12, "same"),
                (0x112, 60, "same"), (0x14E, 2, "raw"), (0x150, 4, "same"), (0x154, 6, "same"),
                (0x15A, 6, "same")]:
  g(TB + o, n, k)
for o, n in [(0x4C340, 10240), (0x4EB40, 20480), (0x53B40, 0x4C00), (0x58740, 0x4C00),
             (0x5D340, 512), (0x5D540, 512), (0x5D740, 1536), (0x5DD40, 1536), (0x5E340, 384),
             (0x5E4C0, 1536), (0x5EAC0, 1536), (0x5F0C0, 1536), (0x5F6C0, 1536), (0x5FCC0, 1280)]:
  g(S + o, n, "raw")
for i in range(4):
  g(S + 0x601C0 + 8 * i, 8)
for i in range(14):
  g(S + 0x601E0 + 8 * i, 8)
for i in range(4):
  g(S + 0x60250 + 8 * i, 8)
g(S + 0x60270, 0x10, "raw")

# ---- checks ----
END = 0x88BA0
pos = 0
for o, n, _ in elem:
  assert o == pos, hex(o)
  pos += n
assert pos == END
pos = 0
for o, n, _ in groups:
  assert o == pos, (hex(o), hex(pos))
  pos += n
assert pos == END

# ---- cut the element's cells at the group boundaries ----
bounds = sorted({o for o, _, _ in groups} | {END})
pieces = []   # (offset, size, expr or None)
splits = []   # (offset, n, k, N) zero-run splits, in order
for o, n, e in elem:
  if e is not None:
    pieces.append((o, n, e))
    continue
  cur, rem = o, n
  while True:
    nxt = min(b for b in bounds if b > cur)
    if nxt >= cur + rem:
      pieces.append((cur, rem, None))
      break
    k = nxt - cur
    splits.append((cur, k, rem - k, rem))
    pieces.append((cur, k, None))
    cur, rem = nxt, rem - k

def addr(o):
  return "p" if o == 0 else f"(p + 0x{o:x}#64)"

def atom(pc):
  o, n, e = pc
  return f"zs {n} =@ {addr(o)}" if e is None else f"{e} =@ {addr(o)}"

def nest(xs):
  if len(xs) == 1:
    return xs[0]
  return f"{xs[0]} ⋆ ({nest(xs[1:])})"

def pieces_in(o, n):
  ps = [pc for pc in pieces if o <= pc[0] < o + n]
  assert all(pc[0] + pc[1] <= o + n for pc in ps), hex(o)
  assert sum(pc[1] for pc in ps) == n
  return ps

flat_g, flat_r, ents = [], [], []
for o, n, k in groups:
  ps = pieces_in(o, n)
  if k == "same":
    assert len(ps) == 1, hex(o)
    flat_g.append(atom(ps[0]))
    flat_r.append(atom(ps[0]))
    ents.append("(Mem.Entails.refl _)")
  else:
    flat_g.append(f"({nest([atom(pc) for pc in ps])})")
    flat_r.append(f"{n} ?@ {addr(o)}")
    def lenpf(pc):
      _, m, e = pc
      if e is None:
        return f"(zs_len {m})"
      if e in VLEN:
        return VLEN[e]
      return "(Int.toBytes_length _ _)"
    def ent(i):
      po, pn, pe = ps[i]
      if i == len(ps) - 1:
        return f"(vraw {lenpf(ps[i])} (by decide))"
      rest = sum(pc[1] for pc in ps[i + 1:])
      nxt = ps[i + 1][0]
      hb = "rfl" if po == 0 else f"(addr_step p 0x{po:x} {pn} 0x{nxt:x} rfl)"
      return (f"(raw_cons (n := {pn}) (k := {rest}) {lenpf(ps[i])} {hb} (by decide)\n"
              f"      {ent(i + 1)})")
    ents.append(ent(0))

def nest_ent(xs):
  if len(xs) == 1:
    return xs[0]
  return f"sep_mono' {xs[0]}\n    ({nest_ent(xs[1:])})"

out = []
w = out.append
w("""import Kraken.X64.Examples.Sbr.Parse.InitLinkBase

/-!
# `ff_aac_sbr_ctx_alloc_init`: the element after a successful run as the session's element

Generated by `scripts/sbr/parse/init/link.py`. `elem_flat` cuts the element's cells (`ElemS` at
`evInit`) at the boundaries of the session's cells, `elem_ent` forgets the cells the session
owns raw, and `init_sessW` regroups them, with the caller's parts (`*ac`, the `float_dsp` slots,
the `av_tx` contexts and tables, the PS tables, `Ext`, the constants, the parser's static data
`P`), as the session's description of the element (`DecExt.SbrF` at values `d` with the values
of `xInit`, `PsRestI`, `ArrW`, `DspW`, `FnW`, `AcW`, `CstW`, `P`) and the rest `InitGap`.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.Session (zs InitIn xInit dvInit)

namespace Kraken.Examples.Sbr.Init

variable [CodeEnv]

/-- The element's cells cut at the session's cells. -/
abbrev ElemG (p : BitVec 64) (id : BitVec 32) (r : IR) : Mem 64 → Prop :=""")
w("  " + nest(flat_g))
w("""
/-- … with the cells the session owns raw forgotten. -/
abbrev ElemR (p : BitVec 64) (id : BitVec 32) (r : IR) : Mem 64 → Prop :=""")
w("  " + nest(flat_r))
w("""
theorem elem_flat (p : BitVec 64) (id : BitVec 32) (r : IR) :
    ElemS p (evInit id r) = ElemG p id r := by
  simp only [ElemS, evInit, toB8_0, toB4_0]
  rw [slots_split]""")
for (o, k, rest, N) in splits:
  if o == 0:
    w(f"  rw [zsS0 p {k} {rest} {N} rfl (by decide)]")
  else:
    w(f"  rw [zsS p 0x{o:x} {k} {rest} {N} 0x{o + k:x} rfl rfl (by decide)]")
w("""  unfold ElemG
  ac_rfl
""")
w("""theorem elem_ent (p : BitVec 64) (id : BitVec 32) (r : IR) (hpsd : r.psd.length = 64) :
    Mem.Entails (ElemG p id r) (ElemR p id r) :=""")
w("  " + nest_ent(ents))
print("\n".join(out))

TAIL = r'''
omit [CodeEnv] in
theorem z32 : (0 : BitVec 32).toInt = 0 := by decide
omit [CodeEnv] in
theorem z64 : (0 : BitVec 64).toInt = 0 := by decide
omit [CodeEnv] in
theorem n0 : ((0 : Nat) : Int) = 0 := rfl
omit [CodeEnv] in
theorem n32 : ((32 : Nat) : Int) = 32 := rfl

/-- **The element after a successful run as the session's element.** The element at `r.p`
with the values `evInit` (InitPost), with the caller's parts (the `*ac` fields at `xInit`, the
`float_dsp` slots, the two `av_tx` contexts, the `av_tx` and PS tables, `Ext`, the constants and
`P`), is the session's description at the parameters `envOf e₀ r` and the values
`xInit (inOf r …)` (`d` presents them with zero `usac`, `inter_tes`, `bs_amp_res_header`,
`bs_limiter_bands` and `spectrum_params` all ones), and the rest `InitGap r.p`. -/
theorem init_sessW {e₀ : Env} {r : IR} {id : BitVec 32} {R : Mem 64 → Prop}
    {avctx fdsp : BitVec 64} {extRate ps : BitVec 32} {d : DecExt.DS} {t : MachineData}
    {m : Mem 64} {P F : Mem 64 → Prop} (hp : arg1 t = r.p) (hpsd : r.psd.length = 64)
    (hd : d.a = xInit (inOf r id R avctx fdsp extRate ps)) (hu : d.usac = 0) (hi : d.it = 0)
    (ha : d.amp = 0) (hl : d.h.lb = 0)
    (hs : d.sp = spB (xInit (inOf r id R avctx fdsp extRate ps)))
    (h : m =⋆ ElemS r.p (evInit id r) ⋆ (e₀.Ctx r.anaCtx ⋆ (e₀.Ctx r.synCtx
      ⋆ (AcW (xInit (inOf r id R avctx fdsp extRate ps)) t ⋆ (FdspW e₀ fdsp ⋆ (e₀.TxTab
      ⋆ (e₀.PsTab ⋆ (e₀.Ext ⋆ (CstW ⋆ (P ⋆ F)))))))))) :
    m =⋆ (DecExt.SbrF d (sbrA t) ⋆ (PsRestI (xInit (inOf r id R avctx fdsp extRate ps)) t
      ⋆ (ArrW t ⋆ (DspW (envOf e₀ r) t
      ⋆ (FnW (envOf e₀ r) (xInit (inOf r id R avctx fdsp extRate ps)) t
      ⋆ (AcW (xInit (inOf r id R avctx fdsp extRate ps)) t ⋆ (CstW ⋆ P)))))))
      ⋆ (InitGap r.p ⋆ F) := by
  rw [elem_flat] at h
  have h1 := sep_mono' (elem_ent r.p id r hpsd) (Mem.Entails.refl _) m h
  clear h
  simp only [ElemR, DecExt.SbrF, DecExt.SbrS, DecExt.DataF, DecExt.TabF, PsRestI, ArrW, DspW, FnW,
    InitGap, FdspW, Blocks, xInit, dvInit, inOf, envOf, fsOf, spB, sbrA, hp, cell4, c4, FnCell,
    Apply.c8, fb, BitVec.add_assoc, BitVec.reduceAdd, z32, z64, n0, n32, toB4_0, toB8_0,
    allOnes32, allOnes16, vOff_init, sp_split, hd, hu, hi, ha, hl, hs] at h1 ⊢
  exact Mem.ac h1

end Kraken.Examples.Sbr.Init'''
print(TAIL)
