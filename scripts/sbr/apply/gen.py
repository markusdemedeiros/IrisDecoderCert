#!/usr/bin/env python3
"""M4 generator: ff_aac_sbr_apply proof skeleton (owner: apply).

Outputs (default into the Kraken tree, override with APPLY_OUT=<dir>):
  ApplyText.lean          the text (B.<id> per block, labelList, blocks, body); parser and
                          machine model imports only
  ApplyTable.lean         CFG lemmas, footprint, frames, table
  Apply/<File>.lean       blk_<id> theorems of one shard file (imports ApplyTable only)
  Apply.lean              of_cfg_post_pre assembly

Inputs: body.s and blocks.json (cut.py's output: the blocks of the text), templates/*.lean.in.
Hooks (all optional, in this directory):
  spec/<File>.py          `def define(g)`: g.entry(id, lean_text) sets E.<id> (a Prop in
                          k e x ra t₀ s); g.frame(name, {slot: value}) defines a frame view;
                          g.var_text overrides var.
  override/<id>.lean      full text of `theorem blk_<id> ...` (replaces the sorry default)
  lemmas/<File>.lean      inserted after the header of Apply/<File>.lean
  lemmas/_table.lean      inserted into ApplyTable.lean before BlockOb
  ../baseline/hb_table.txt  lines `<id> <heartbeats>`: per-block maxHeartbeats (default 400000)
Env:
  APPLY_OUT=<dir>         output root (files keep their relative names)
  APPLY_FILES=F1,F2       only (re)write these shard files (a split shard: all parts, or one part MapB2) (+ Table/Main unless APPLY_NOTABLE=1)
  APPLY_DEV=id1,id2       only these blocks keep their override proofs, the rest sorry
  APPLY_OVR=<dir>         override directory (default ./override)
  APPLY_SPECDIR=<dir>     private spec/<File>.py files (take precedence over ./spec)
  APPLY_LEMDIR=<dir>      private lemmas/<File>.lean (take precedence over ./lemmas)
  APPLY_HB=<file>         private `<id> <heartbeats>` lines, override hb_table.txt
  APPLY_INLINELEM=1       split shards: inline lemmas/<Shard>.lean into each part (single-file checks)
  APPLY_PARTS=MapB:5,EnvA:2  override PARTS
"""
import glob, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", ".."))   # repository root (scripts/sbr/apply)
OUT = os.environ.get("APPLY_OUT", os.path.join(ROOT, "Kraken/X64/Examples/Sbr"))
OVR = os.environ.get("APPLY_OVR", os.path.join(HERE, "override"))
NS = "Kraken.Examples.Sbr.Apply"
MOD = "Kraken.X64.Examples.Sbr"
PROC = "ff_aac_sbr_apply"
DEFAULT_HB = 400000

# shard files: name -> phases (cut.py phase names)
FILES = [
    ("Trap", ["Trap", "Abort"]),
    ("EntrySyn", ["Entry", "Setup", "Syn"]),
    ("DqCpl", ["DqCplEnv", "DqCplNoise"]),
    ("DqSce", ["DqSce"]),
    ("AnaHf", ["Ana", "Chirp", "HfGen"]),
    ("MapA", ["Map:A"]),
    ("MapB", ["Map:B"]),
    ("EnvA", ["Env:A"]),
    ("EnvB", ["Env:B"]),
    ("GainAsm", ["Gain", "Asm"]),
]
# module split for memory (peak RSS accumulates per file): shard -> number of parts.
# Parts are contiguous runs of the shard's blocks, files <Shard>1..<Shard>N, lemmas/<Shard>.lean becomes module Apply/<Shard>Lem.lean, imported by the parts.
PARTS = {"MapB": 13, "EnvA": 3, "EnvB": 3, "MapA": 5}
# extra imports of a shard module (its lemmas live in another shard), e.g. GainAsm uses DqCpl's dq_* tactics
IMPORTS = {"GainAsm": ["DqCpl"]}
if os.environ.get("APPLY_PARTS"):
    PARTS = {a.split(":")[0]: int(a.split(":")[1]) for a in os.environ["APPLY_PARTS"].split(",")}
# Map / Env are split at these labels (first block of the B half, text order)
SPLIT = {"Map": "L8009", "Env": None}

# frame slots (name, offset below rbp, size); rbp = rsp0 - 8. See DESIGN.md (c).
SLOTS = [
    ("tmp30", 0x30, 8), ("che", 0x38, 8), ("nch2", 0x39, 1), ("dch", 0x48, 8), ("s50", 0x50, 8),
    ("s58", 0x58, 8), ("s60", 0x60, 8), ("s68", 0x68, 8), ("xh150", 0x70, 8), ("s78", 0x78, 8),
    ("s80", 0x80, 8), ("lim0", 0x82, 2), ("ac", 0x90, 8), ("s98", 0x98, 8), ("idaac", 0x9c, 4),
    ("X", 0xa8, 8), ("sbr", 0xb0, 8), ("Xh", 0xb8, 8), ("Xl", 0xc0, 8), ("sc8", 0xc8, 8),
    ("eom", 0xd0, 8), ("sd8", 0xd8, 8), ("se0", 0xe0, 8), ("se8", 0xe8, 8), ("sf0", 0xf0, 8),
    ("sf4", 0xf4, 4), ("ch0", 0xf8, 4), ("gain", 0x100, 8), ("qm", 0x108, 8), ("ea", 0x110, 8),
    ("qfs", 0x118, 8), ("dsp", 0x120, 8), ("R", 0x128, 8), ("L", 0x130, 8), ("d0", 0x138, 8),
    ("a1", 0x140, 8), ("a0", 0x148, 8), ("ds", 0x150, 8), ("gain4", 0x158, 8), ("sim1", 0x160, 8),
    ("spp", 0x168, 8), ("sm", 0x170, 8), ("ecur", 0x178, 8), ("ah1", 0x180, 8), ("qmap", 0x188, 8),
    ("xh10", 0x190, 8), ("fth4", 0x198, 8), ("ch", 0x1a0, 8), ("smap", 0x1a8, 8), ("ftl", 0x1b0, 8),
    ("fth", 0x1b8, 8),
]
SAVED = [("rbx", 0x30), ("r12", 0x28), ("r13", 0x20), ("r14", 0x18), ("r15", 0x10), ("rbp", 0x8)]
FRAME_LO, FRAME_HI = 0x1c8, 0x30   # own slot area [rsp0 - 0x1c8, rsp0 - 0x30)
R0 = "t₀.regs.get64 .rsp"


def ident(lab):
    return "start" if lab == PROC else lab[len(PROC) + 1:]


def read_blocks():
    bl, cur = [], None
    for line in open(os.path.join(HERE, "body.s")):
        m = re.match(r"^(%s[\w.]*):\s*$" % PROC, line)
        if m:
            cur = [m.group(1), []]
            bl.append(cur)
        elif line.strip():
            cur[1].append(line.rstrip())
    meta = json.load(open(os.path.join(HERE, "blocks.json")))
    assert len(meta) == len(bl)
    out = []
    half = {}
    for (lab, body), mt in zip(bl, meta):
        i = ident(lab)
        assert (mt["label"] or "start") == i, (mt["label"], i)
        ph = mt["phase"]
        if ph in SPLIT:
            if ph not in half:
                half[ph] = "A"
            if SPLIT[ph] and i.split("_")[0] == SPLIT[ph]:
                half[ph] = "B"
            ph = f"{ph}:{half[ph]}"
        out.append(dict(lab=lab, id=i, body=body, phase=ph, kind=mt["kind"], line=mt["line"]))
    # Env split by half of its blocks when no label given
    envs = [b for b in out if b["phase"].startswith("Env")]
    for j, b in enumerate(envs):
        b["phase"] = "Env:A" if j < (len(envs) + 1) // 2 else "Env:B"
    return out


class G:
    """What spec hooks see."""
    def __init__(self, blocks):
        self.blocks = blocks
        self.ids = [b["id"] for b in blocks]
        self.ENTRY = {}
        self.FRAMES = {}
        self.MEASURE = {}
        self.DIGITS = {}
        self.var_text = None
        self.slots = SLOTS

    def entry(self, i, text):
        assert i in self.ids, i
        self.ENTRY[i] = text

    def frame(self, name, vals, saved=True, params=""):
        """A frame view `name x t₀ <params> Kt`; `params` are extra binders, e.g.
        "(ch : Nat) (c0 : BitVec 32)", usable in the slot values."""
        cur = getattr(self, "cur_file", None)
        owner = getattr(self, "FRAME_OWNER", {})
        self.FRAME_OWNER = owner
        if name in self.FRAMES and owner.get(name) != cur \
                and self.FRAMES[name] != (vals, saved, params):
            raise SystemExit(f"gen.py: frame {name} defined in both "
                             f"{owner.get(name)} and {cur} (rename one)")
        owner[name] = cur
        self.FRAMES[name] = (vals, saved, params)

    def measure(self, i, ms):
        """Loop measures of label i, outermost enclosing loop first (Lean terms in `s`)."""
        assert i in self.ids, i
        self.MEASURE[i] = list(ms)

    def digits(self, i, ds):
        """Override the whole digit list of label i (padded with 0): for backward-in-text jumps
        that are not loop edges at their level (the laminar loop merge folds them into an outer
        loop, e.g. L99cf -> L9146 inside the channel loop)."""
        assert i in self.ids, i
        self.DIGITS[i] = list(ds)


def slot_cells(vals):
    """(offset below rsp0, size, value or None) covering the own slot area, address order."""
    cells = []
    pos = FRAME_LO  # offset below rsp0, decreasing
    for o, size, name in sorted(((off + 8, size, name) for name, off, size in SLOTS), reverse=True):
        assert pos >= o, f"slot {name} overlaps"
        if pos > o:
            cells.append((pos, pos - o, None))
        cells.append((o, size, vals.get(name)))
        pos = o - size
    if pos > FRAME_HI:
        cells.append((pos, pos - FRAME_HI, None))
    return cells


def cell_text(o, size, v):
    a = f"(r - {o:#x}#64)"
    if v is None:
        return f"{size} ?@ {a}"
    if isinstance(v, tuple) and v[0] == "cells":   # custom cells covering the slot, e.g. split
        return v[1]
    return f"c8 {a} ({v})" if size == 8 else f"Int.toBytes {size} ({v}) =@ {a}"


def chain(cs, tail):
    s = cs[0]
    for c in cs[1:]:
        s += f"\n    ⋆ ({c}"
    return s + f" ⋆ {tail}" + ")" * (len(cs) - 1)


def frame_text(vals, saved=True, tail="Kt"):
    """Cells covering the own frame, address-ordered; unset slots / gaps raw."""
    cells = [cell_text(*c) for c in slot_cells(vals)]
    for reg, off in SAVED:
        cells.append(f"c8 (r - {off:#x}#64) (t₀.regs.get64 .{reg})" if saved else f"8 ?@ (r - {off:#x}#64)")
    return chain(cells, tail)


def frame_split_lemma():
    """0x198 raw bytes = the raw slot cells."""
    cells = slot_cells({})
    rhs = chain([cell_text(*c) for c in cells], "K")
    steps = []
    rem = FRAME_LO - FRAME_HI
    for o, size, _ in cells[:-1]:
        rest = rem - size
        steps.append(f"  rw [show ({rem} ?@ (r - {o:#x}#64) : Mem 64 → Prop) = ({size} + {rest}) ?@ (r - {o:#x}#64) from rfl,\n"
                     f"    Block.split (r - {o:#x}#64) {size} {rest} (by decide), "
                     f"show r - {o:#x}#64 + BitVec.ofNat 64 {size} = r - {o - size:#x}#64 by bv_omega, Std.ExtHashMap.sep_assoc]")
        rem = rest
    return (f"omit [CodeEnv] in\n/-- The own slot area as its slots. -/\n"
            f"theorem frame_split (r : BitVec 64) (K : Mem 64 → Prop) :\n"
            f"    {FRAME_LO - FRAME_HI:#x} ?@ (r - {FRAME_LO:#x}#64) ⋆ K =\n    {rhs} := by\n"
            f"  rw [show ({FRAME_LO - FRAME_HI:#x} ?@ (r - {FRAME_LO:#x}#64) : Mem 64 → Prop) = {FRAME_LO - FRAME_HI} ?@ (r - {FRAME_LO:#x}#64) from rfl]\n"
            + "\n".join(steps) + "\n")


def entry_text(g, b):
    i = b["id"]
    if i in g.ENTRY:
        return g.ENTRY[i]
    if i == "start":
        return "s = t₀ ∧ ApplyPre k e x ra t₀"
    if b["phase"] in ("Trap", "Abort") or b["kind"] == "abort":
        return "False"
    return "Inv k e x ra t₀ s"


def edges(bl):
    """(source index, target index) of every jump and fallthrough."""
    idx = {b["lab"]: j for j, b in enumerate(bl)}
    out = []
    for j, b in enumerate(bl):
        for l in b["body"]:
            m = re.search(r"\bj[a-z]+\s+(%s[\w.]*)" % PROC, l)
            if m and m.group(1) in idx:
                out.append((j, idx[m.group(1)]))
        last = b["body"][-1].split()[0] if b["body"] else ""
        if j + 1 < len(bl) and last not in ("jmp", "ret", "ud1"):
            out.append((j, j + 1))
    return out


def loops(bl):
    """Laminar text intervals [s, e] of the loops (merged back-edge intervals), sorted."""
    iv = sorted({(t, u) for u, t in edges(bl) if t <= u})
    changed = True
    while changed:
        changed = False
        iv = sorted(set(iv))
        for a in range(len(iv)):
            for b in range(len(iv)):
                (s1, e1), (s2, e2) = iv[a], iv[b]
                if a != b and s1 <= s2 <= e1 < e2 or (a != b and s1 == s2 and e1 != e2 and False):
                    iv[a] = (s1, e2); iv[b] = (s1, e2); changed = True
        iv = sorted(set(iv))
        # same start, different end: keep both (nested)
    return iv


def var_digits(g):
    """Per block: the digit terms [ph0, m1, ph1, ...] (padded) and missing-measure notes."""
    bl = g.blocks
    lp = loops(bl)
    def parent(L):
        cs = [M for M in lp if M != L and M[0] <= L[0] and L[1] <= M[1]]
        return max(cs, key=lambda M: M[0] - M[1]) if cs else None   # innermost
    kids = {}
    for L in lp:
        kids.setdefault(parent(L), []).append(L)
    def chain(i):
        return sorted([L for L in lp if L[0] <= i <= L[1]], key=lambda L: (L[0], -L[1]))
    depth = max((len(chain(i)) for i in range(len(bl))), default=0)
    width = 2 * depth + 1
    out, missing = [], []
    for i, b in enumerate(bl):
        ch = chain(i)
        ms = g.MEASURE.get(b["id"])
        if ch and (ms is None or len(ms) != len(ch)) and entry_text(g, b) != "False":
            missing.append((b["id"], len(ch)))
        ds = []
        for d in range(len(ch) + 1):
            par = ch[d - 1] if d > 0 else None
            sib = kids.get(par, [])
            pos = ch[d][0] if d < len(ch) else i
            strict = d < len(ch)
            ds.append(str(sum(1 for M in sib if M[0] > pos)))
            if d < len(ch):
                m = ms[d] if ms is not None and len(ms) == len(ch) else "0"
                ds.append(f"({m})")
        if b["id"] in g.DIGITS:
            ds = list(g.DIGITS[b["id"]])
        ds += ["0"] * (width - len(ds))
        out.append(ds)
    return out, missing, lp


def var_text(g):
    bl = g.blocks
    ds, missing, lp = var_digits(g)
    t = ["/-! ## The variant (lexicographic: per loop level a phase and the loop's measure) -/\n",
         f"-- loops (text-index intervals): {lp}", "namespace VD"]
    for b, d in zip(bl, ds):
        t.append(f"/-- {b['lab']} -/\nabbrev {b['id']} (s : MachineData) : List Nat := [{', '.join(d)}]")
    t.append("end VD\n")
    t.append("def VAR : List (MachineData → List Nat) := [\n  " + ",\n  ".join(f"VD.{b['id']}" for b in bl) + "]\n")
    t.append("/-- The variant: `lex` of the label's digits. -/\n"
             "def var (l : Label) (s : MachineData) : Nat :=\n"
             "  lex ((VAR[labelList.idxOf l]?.getD (fun _ => [])) s)\n\nnamespace V")
    for j, (b, d) in enumerate(zip(bl, ds)):
        t.append(f"@[lex_var] theorem {b['id']} {{s : MachineData}} : var \"{b['lab']}\" s = lex [{', '.join(d)}] := by\n"
                 f"  rw [var, Program.idxOf_of_getElem? labelList_nodup (i := {j}) rfl]; rfl")
    t.append("end V\n\nnamespace I")
    for j, b in enumerate(bl):
        t.append(f"@[lex_var] theorem {b['id']} : Program.blockIdx body \"{b['lab']}\" = {j} := blockIdx_at L.{b['id']}")
    t.append("end I\n")
    return "\n".join(t), missing


def file_of(phase):
    for f, phs in FILES:
        if phase in phs:
            return f
    raise KeyError(phase)


def text_file(g):
    """ApplyText.lean: the program text only (imports the parser and the machine model)."""
    bl = g.blocks
    t = [open(os.path.join(HERE, "templates/head_text.lean.in")).read()]
    t.append("namespace B\n")
    for b in bl:
        t.append(f'set_option maxRecDepth 20000 in\n/-- asm line {b["line"]} ({b["phase"]}, {b["kind"]}) -/\n'
                 f'def {b["id"]} : Program := parse("\n' + "\n".join(b["body"]) + '\n")\n')
    t.append("end B\n")
    t.append("/-- The labels, in order. -/\ndef labelList : List Label := [\n  " +
             ",\n  ".join(f'"{b["lab"]}"' for b in bl) + "]\n")
    t.append("/-- The blocks, in order. -/\ndef blocks : List (Label × Program) := [\n  " +
             ",\n  ".join(f'("{b["lab"]}", B.{b["id"]})' for b in bl) + "]\n")
    t.append(f"""
/-- The text of `{PROC}`: the blocks glued with their labels. -/
def body : Program := blocks.flatMap Program.blockCells

end {NS}
""")
    return "\n".join(t)


def table_file(g):
    bl = g.blocks
    t = [open(os.path.join(HERE, "templates/head_table.lean.in")).read()]  # imports ApplyText, SessionSpec
    t.append(f"""/-! ## The control flow of the text (`ApplyText.lean`) -/

set_option maxRecDepth 200000 in
theorem blocks_free : ∀ lb ∈ blocks, ∀ d ∈ lb.2, d.isLabel = false := by decide +kernel

theorem view_body : Program.view body = ([], blocks) := Program.view_flatMap blocks blocks_free

set_option maxRecDepth 200000 in
theorem labels_body : Program.labels body = labelList := by
  rw [Program.labels_eq_view, view_body]; rfl

/-- A key per label (distinct keys, distinct labels: `labelList_nodup`). -/
def labelKey (s : String) : Nat := s.toList.foldl (fun n c => n * 256 + c.toNat) 0

set_option maxRecDepth 200000 in
theorem labelList_nodup : labelList.Nodup :=
  (List.pairwise_map.mp (show (labelList.map labelKey).Nodup by decide +kernel)).imp
    fun h e => h (congrArg labelKey e)

theorem body_wf : Program.WF body := ⟨labels_body ▸ labelList_nodup⟩

/-- The label questions of a jump to the `i`-th label. -/
theorem blockIdx_at {{i : Nat}} {{l : Label}} (h : labelList[i]? = some l) : Program.blockIdx body l = i :=
  Program.blockIdx_of_getElem? body_wf (labels_body ▸ h)

theorem isSome_at {{i : Nat}} {{l : Label}} (h : labelList[i]? = some l) :
    (Program.blockAt body l).isSome = true :=
  Program.isSome_blockAt_of_getElem? (labels_body ▸ h)

/-! ## Frames -/

{frame_split_lemma()}

/-- The frame with every slot raw. -/
abbrev FrRaw (t₀ : MachineData) (Kt : Mem 64 → Prop) : Mem 64 → Prop :=
  let r := {R0}
  {frame_text({})}
""")
    for nm, (vals, saved, params) in g.FRAMES.items():
        ps = f" {params}" if params else ""
        t.append(f"abbrev {nm} (x : Args) (t₀ : MachineData){ps} (Kt : Mem 64 → Prop) : Mem 64 → Prop :=\n"
                 f"  let r := {R0}\n  {frame_text(vals, saved)}\n")
    t.append(open(os.path.join(HERE, "templates/mid.lean.in")).read())
    t.append("/-! ## The table -/\n\nnamespace E\n")
    sig = "(k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) : MachineData → Prop"
    for b in bl:
        i = b["id"]
        txt = entry_text(g, b)
        t.append(f"/-- {b['lab']} -/\nabbrev {i} {sig} :=\n  fun s => {txt}")
    t.append("end E\n")
    t.append("def ENT (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) :\n"
             "    List (MachineData → Prop) := [\n  " +
             ",\n  ".join(f"E.{b['id']} k e x ra t₀" for b in bl) + "]\n")
    t.append("""
set_option maxRecDepth 100000

/-- The table: the entry of the `i`-th label is `ENT[i]`. -/
def table (k : Nat) (e : Env) (x : Args) (ra : Int64) (t₀ : MachineData) (l : Label)
    (s : MachineData) : Prop :=
  Program.LTable labelList (ENT k e x ra t₀) l s

namespace T
""")
    for j, b in enumerate(bl):
        t.append(f"theorem {b['id']} {{k e x ra t₀ s}} : table k e x ra t₀ \"{b['lab']}\" s ↔ E.{b['id']} k e x ra t₀ s :=\n"
                 f"  Program.LTable.iff labelList_nodup (i := {j}) rfl rfl")
    t.append("end T\n\nnamespace L\n")
    for j, b in enumerate(bl):
        t.append(f"theorem {b['id']} : labelList[{j}]? = some \"{b['lab']}\" := rfl")
    t.append("end L\n")
    lt = os.path.join(HERE, "lemmas/_table.lean")
    if os.path.exists(lt):
        t.append(open(lt).read())
    vt, missing = var_text(g)
    g.missing_measures = missing
    t.append(open(os.path.join(HERE, "templates/tail.lean.in")).read()
             .replace("abbrev var : Label → MachineData → Nat := fun _ _ => 0", vt))
    t.append(f"end {NS}\n")
    return "\n".join(t)


# the entry's stack headroom (`CallPre.le` of `ApplyPre`), a hypothesis of every block
HST = "applyNeed k ≤ (t₀.regs.get64 .rsp).toNat"


def blk_head(b, nxt):
    return (f"theorem blk_{b['id']} (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env) (hc : ApplyCallees k e)\n"
            f"    (x : Args) (ra : Int64) (t₀ : MachineData) (hSt : {HST}) :\n"
            f"    BlockOb k e x ra t₀ \"{b['lab']}\" ⟨\"{b['lab']}\", B.{b['id']}, {nxt}⟩ := by\n")


def modules():
    """(module file name, shard name) in order."""
    return [(m, f) for f, _ in FILES for m in ([f] if f not in PARTS else [f"{f}{i}" for i in range(1, PARTS[f] + 1)])]


def part_of(g, b):
    """Module name of block b."""
    f = file_of(b["phase"])
    if f not in PARTS:
        return f
    ids = [c["id"] for c in g.blocks if file_of(c["phase"]) == f]
    n = PARTS[f]
    j = ids.index(b["id"])
    return f"{f}{j * n // len(ids) + 1}"


HIDE = ["hm", "hm0", "hm00"]   # the big separation hypotheses, PLift-hidden around vcgen (hbopt F4);
# hm/hm0 always, other names only in blocks that mention them
VCGEN = re.compile(r"^(all_goals )?vcgen( \[.*\])?$")
F1_RFL = re.compile(r"^(all_goals try \(simp only \[.*\]; )rfl\)$")
# blocks whose register closer needs the default-transparency `rfl`: it closes goals that
# `with_reducible rfl` leaves open (L8a50_3: `ofNat 64 a + 1 = ofNat 64 (a + 1)`; L914e_3)
F1_KEEP = {"L8a50_3", "L914e_3"}

# F8 (px-apgen; `APPLY_F8=0` turns it off): emit the LD loop once. The override proofs repeat the
# per-load pass (`… at ldK` normalisation + `try (revert ldK; sep_mem h; …)` for K = 1..n, then the
# goal-level simps) twice in a row. A second copy is dropped when it is an immediate (tandem) repeat
# of the first INSIDE ONE SCOPE: every line of both copies is an `all_goals …` line at the same
# indentation (so a `·` bullet or `case` never falls inside; the ch=0/ch=1 bullets differ in text
# anyway), and the window contains an LD `revert ldK; sep_mem` step. F8_KEEP: blocks that need the
# second pass (measured).
F8 = os.environ.get("APPLY_F8", "1") != "0"
# measured (px-apgen batch 2026-10-11): these fail without the second pass (a load the first pass
# leaves is closed only after the `sep_vals` between the passes)
F8_KEEP = {"L7db0", "L7db0_1", "L7eb6", "L8009", "L814a", "L828a", "L83ca", "L85cd_1", "L862d_1", "L8740"} \
    | (set(os.environ.get("APPLY_F8_KEEP", "").split(",")) - {""})
F8_LD = re.compile(r"revert ld\d+; sep_mem")


def ld_dedupe(L):
    """drop tandem repeats L[i:i+n] == L[i+n:i+2n] of same-indent `all_goals` lines with an LD step."""
    def ok(l, ind):
        t = l.strip()
        return t.startswith("all_goals ") and len(l) - len(l.lstrip()) == ind
    out, i = [], 0
    while i < len(L):
        l = L[i]
        ind = len(l) - len(l.lstrip())
        best = 0
        if ok(l, ind):
            # longest run of scope lines from i
            j = i
            while j < len(L) and ok(L[j], ind):
                j += 1
            for n in range((j - i) // 2, 2, -1):
                if L[i:i + n] == L[i + n:i + 2 * n] and any(F8_LD.search(x) for x in L[i:i + n]):
                    best = n
                    break
        if best:
            out.extend(L[i:i + best])
            i += 2 * best
        else:
            out.append(l)
            i += 1
    return out


# F6 (px-apgen prototype; `APPLY_F6=id1,id2` turns it on for those blocks): slot-read facts.
# A block's loads are numbered ld1, ld2, … in instruction order (`env_name`/`mapb_name` rename the
# load hyps in context order, i.e. along the path, and a block is straight-line code with exits).
# For a load from a frame slot `-o(%rbp)` before any store of the block, the entry frame says
# what the slot holds:
#   * an unknown cell (`n ?@ a`): the LD step `try (… revert ldK; sep_mem h; …)` can never rewrite
#     the load, so it (and its `… at ldK` normalisation) is dropped;
#   * a value cell (`c8 a v` / `Int.toBytes n v =@ a`) of the load's size: a read fact `hRo` is
#     stated ONCE before `vcgen` (by `sep_mem` in the single pre-vcgen goal) and each goal uses
#     `rw [hRo] at ldK` instead of searching the ~150-cell fact again.
F6 = set(os.environ.get("APPLY_F6", "").split(",")) - {""}
F6_UNK = os.environ.get("APPLY_F6_UNK", "1") != "0"
F6_READ = os.environ.get("APPLY_F6_READ", "1") != "0"
_SLOT_MEM = re.compile(r"^(-?)0x([0-9a-f]+)\(%rbp\)$")


def block_loads(body):
    """[(kind, rbp offset or None, size or None)] per load instruction in order; kind 'slot'/'other'.
    None if the block has instructions F6 does not model (push/pop/call/ret/rep, string ops)."""
    out, stored = [], False
    for line in body:
        t = line.strip()
        if not t or t.endswith(":"):
            continue
        op = t.split()[0]
        args = t[len(op):].strip()
        if op.startswith(("push", "pop", "call", "ret", "rep", "stos", "movs", "leave")) and not op.startswith(("movsl", "movsb", "movsw", "movss", "movsd", "movsx")):
            return None
        if "(" not in t or op.startswith(("j", "lea", "nop")):
            continue
        ops = [a.strip() for a in re.split(r",(?![^(]*\))", args)]
        mem = [k for k, a in enumerate(ops) if "(" in a]
        if not mem:
            continue
        k = mem[0]
        is_dst = k == len(ops) - 1
        is_mov = op in ("mov", "movl", "movq", "movb", "movw", "vmovss", "vmovsd", "vmovq", "vmovd",
                        "vmovdqa", "vmovdqu", "vmovaps", "vmovups", "movss", "movsd")
        if is_dst and is_mov and not op.startswith(("cmp", "test")):
            stored = True
            continue
        size = None
        if op in ("vmovss", "movss") or op.endswith("l") and op.startswith(("mov", "add", "sub", "cmp", "and", "or", "xor", "imul")) and not op.startswith(("movzbl", "movzwl", "movsbl", "movswl")):
            size = 4
        if op in ("mov", "cmp", "add", "sub", "and", "or", "xor", "test", "imul"):
            # size from the register operand
            r = [a for a in ops if a.startswith("%")]
            if r:
                rr = r[0][1:]
                size = 8 if rr.startswith("r") and not rr.endswith(("d", "w", "b")) else 4 if rr.startswith("e") or rr.endswith("d") else None
        if op in ("vmovsd", "movsd", "vmovq"):
            size = 8
        if op.startswith(("movzbl", "movsbl", "movzbq", "movsbq")):
            size = 1
        if op.startswith(("movzwl", "movswl", "movzwq", "movswq")):
            size = 2
        m = _SLOT_MEM.match(ops[k])
        if m and m.group(1) and not stored and size:
            out.append(("slot", int(m.group(2), 16), size))   # bytes below rbp
        else:
            out.append(("other", None, None))
        if is_dst:
            stored = True   # read-modify-write
    return out


def frame_cell(g, frame, rsp_off, size):
    """the entry frame's cell covering [rsp0 - rsp_off, rsp0 - rsp_off + size): ('unk',) /
    ('val', value text, cell size) / None (custom cells or not exactly one cell)."""
    if frame not in g.FRAMES:
        return None
    vals, saved, params = g.FRAMES[frame]
    for o, sz, v in slot_cells(vals):
        if o >= rsp_off and rsp_off - size >= o - sz:
            if v is None:
                return ("unk",)
            if isinstance(v, tuple):
                parts = [p.strip() for p in v[1].split("⋆")]
                return ("unk",) if all(re.match(r"^\d+ \?@ ", p) for p in parts) else None
            return ("val", v, sz)
    for reg, off in SAVED:
        if off == rsp_off and size == 8:
            return ("val", f"t₀.regs.get64 .{reg}", 8) if saved else ("unk",)
    return None


# F9 (px-apgen; P5 of hbopt/b MEASURE.md): `all_goals try have hNk := mapb_noise hC hst k (by omega)`
# (k a literal) and its `all_goals try simp only [...] at hNk` depend only on the entry facts, but run
# after vcgen in every goal (omega over the goal's whole context, 60-70k per line). They move to just
# before the scope's `vcgen` (before any PLift hiding), so they run once per pre-vcgen goal.
# On by default (`APPLY_F9=0` off); `APPLY_F9_KEEP=ids` adds opt-outs.
F9 = os.environ.get("APPLY_F9", "1") != "0"
F9_ON = set(os.environ.get("APPLY_F9_ON", "").split(",")) - {""}
F9_KEEP = {"L8480", "L8480_1", "L8009", "L814a", "L828a", "L83ca", "L8740"} | (set(os.environ.get("APPLY_F9_KEEP", "").split(",")) - {""})   # measured: slower (L8480*, L8740) or failing (L8009 L814a L828a L83ca)
_NOISE = re.compile(r"^all_goals try have (hN\d+) := mapb_noise \S+ \S+ \d+ \(by omega\)$")


def noise_hoist(L):
    vc = [i for i, l in enumerate(L) if VCGEN.match(l.strip())]
    if not vc:
        return L
    L = list(L)
    for a, z in reversed(list(zip(vc, vc[1:] + [len(L)]))):
        ind = len(L[a]) - len(L[a].lstrip())
        move, keep = [], []
        names = set()
        for j in range(a + 1, z):
            t = L[j].strip()
            m = _NOISE.match(t)
            if m and len(L[j]) - len(L[j].lstrip()) == ind:
                names.add(m.group(1))
                move.append(L[j])
                continue
            m2 = re.match(r"^all_goals try simp only \[[^\]]*\] at (hN\d+)$", t)
            if m2 and m2.group(1) in names and len(L[j]) - len(L[j].lstrip()) == ind:
                move.append(L[j])
                continue
            keep.append(L[j])
        if not move:
            continue
        q = a
        while q > 0 and "PLift" in L[q - 1]:
            q -= 1
        L = L[:q] + move + L[q:a + 1] + keep + L[z:]
    return L


def f6_plan(g, b):
    """{K: ('unk',) | ('val', fact name, `have` text)} for the slot loads of block b."""
    m = re.search(r"\((Fr\w*) x t₀", g.ENTRY.get(b["id"], ""))
    ls = block_loads(b["body"]) if m else None
    if not ls:
        return None
    plan = {}
    for K, (kind, o, n) in enumerate(ls, 1):
        if kind != "slot":
            continue
        c = frame_cell(g, m.group(1), o + 8, n)
        if c is None:
            continue
        if c[0] == "unk" and F6_UNK:
            plan[K] = ("unk",)
        elif c[0] == "val" and c[2] == n and F6_READ:
            nm = f"hR{o:x}"
            plan[K] = ("val", nm, f"have {nm} := (show s₀.dmem.loadInt (t₀.regs.get64 .rsp - {o + 8}#64) {n} = _ by sep_mem hm; try rfl)")
    return plan or None


def opt_proof(txt, bid="", f6=None):
    """hbopt generator defaults, applied to every override proof (opt out: a `-- gen:raw` line
    in the override, or APPLY_NOOPT=1). Proof scripts only; the statement is untouched.
    F4: around every `vcgen` / `all_goals vcgen [..]` line, PLift-hide `hm`/`hm0` (vcgen otherwise
        pays for the ~150-cell memory hypotheses in every goal) and restore them after. Each step
        is under `try`, so blocks without these names, or with them already hidden, are unchanged.
    F1: the register closer `all_goals try (simp only [...]; rfl)` closes with `with_reducible rfl`
        (a failing default-transparency `rfl` unfolds machine states: 1.6M hb in L89f3_1)."""
    if os.environ.get("APPLY_NOOPT") == "1" or "-- gen:raw" in txt:
        return txt
    k = txt.find("theorem blk_")   # helper lemmas before the block theorem stay verbatim
    if k > 0:
        return txt[:k] + opt_proof(txt[k:], bid, f6)
    out = []
    L = txt.split("\n")
    if F8 and bid not in F8_KEEP:
        L = ld_dedupe(L)
    if (F9 or bid in F9_ON) and bid not in F9_KEEP:
        L = noise_hoist(L)
    if f6:
        L2 = []
        for l in L:
            t = l.strip()
            m = re.search(r"\brevert ld(\d+); sep_mem", t) or re.match(r"^all_goals try .* at ld(\d+)$", t)
            K = int(m.group(1)) if m else None
            if K in f6 and f6[K][0] == "unk":
                continue   # the step can never rewrite a load of an unknown cell
            if K in f6 and f6[K][0] == "val" and "sep_mem" in t:
                sp = l[:len(l) - len(t)]
                L2.append(f"{sp}all_goals try (rw [{f6[K][1]}] at ld{K}; simp only [Option.some.injEq] at ld{K}; subst ld{K})")
            L2.append(l)
        L = L2
    for i, l in enumerate(L):
        t = l.strip()
        sp = l[:len(l) - len(t)] if t else ""
        m = VCGEN.match(t)
        prev = "\n".join(L[max(0, i - 3):i])
        if m and f6:
            # read facts, once, in the pre-vcgen goal(s), before any PLift hiding of hm
            q = len(out)
            while q > 0 and "PLift" in out[q - 1]:
                q -= 1
            facts = [f"{sp}{m.group(1) or ''}try {v[2]}" for K, v in sorted(f6.items()) if v[0] == "val"]
            out[q:q] = facts
        if m and "PLift" not in prev:
            ag = m.group(1) or ""
            hs = [h for h in HIDE if h in ("hm", "hm0") or re.search(rf"\b{h}\b", txt)]
            for h in hs:
                out.append(f"{sp}{ag}try (have p_{h} : PLift _ := ⟨{h}⟩; clear {h})")
            out.append(l)
            for h in hs:
                out.append(f"{sp}all_goals try (have {h} := p_{h}.down; clear p_{h})")
            continue
        m = F1_RFL.match(t)
        if m and bid not in F1_KEEP:
            out.append(f"{sp}{m.group(1)}with_reducible rfl)")
            continue
        if F5:
            l = F5_LD.sub(r"try (hb_used \1; revert \1; sep_mem", l)
        if F7:
            l = F7_SIMP.sub(lambda m: m.group(0).replace("simp", "simp -implicitDefEqProofs", 1)
                            if F7_LEM.search(m.group(2)) else m.group(0), l)
        out.append(l)
    if f6:
        # drop the read facts after their last use: later closers see the old context
        for v in f6.values():
            if v[0] != "val":
                continue
            starts = [j for j, x in enumerate(out) if f"have {v[1]} :=" in x] + [len(out)]
            for a, z in reversed(list(zip(starts, starts[1:]))):
                last = max((j for j in range(a, z) if f"rw [{v[1]}]" in out[j]), default=None)
                if last is not None:
                    sp = out[last][:len(out[last]) - len(out[last].lstrip())]
                    out.insert(last + 1, f"{sp}all_goals try clear {v[1]}")
    return "\n".join(out)


# F5 (Kraken/Rules/HbOptApply.lean; `APPLY_F5=0` turns it off): the LD loop step
# `try (revert ldK; sep_mem h; …)` runs only in goals where ldK's value is used (`hb_used ldK`).
# Measured and dropped (no gain on MapB3/MapB8/EnvA2): `hb_mem_guard` before `try sep_mem h`
# (those goals do contain loads), and clearing hm/hm0 before the omega closers.
F5 = os.environ.get("APPLY_F5", "1") != "0"
F5_LD = re.compile(r"try \(revert (ld\d+); sep_mem")
# F7 (from fx-f7; `APPLY_F7=0` turns it off): a `simp … only [...]` whose list has the rfl-lemmas
# BitVec.toNat_add/_sub/_mul/_ofNat gets `-implicitDefEqProofs`. Otherwise simp emits
# defeq (`id`) steps, and the kernel re-checks `(r + c₁ + c₂).toNat ≡ …` by unary Nat.add/Nat.ble
# (MapB12 L8740: kernel 37 s → 2.2 s, peak 8.0 → 2.6 GB).
F7 = os.environ.get("APPLY_F7", "1") != "0"
F7_SIMP = re.compile(r"\bsimp( \(disch := [^()]*\))? only \[([^\]]*)\]")
F7_LEM = re.compile(r"\bBitVec\.toNat_(add|sub|mul|ofNat)\b")


def shard_file(mname, g, hb, dev):
    bl = g.blocks
    fname = mname.rstrip("0123456789") if mname.rstrip("0123456789") in PARTS else mname
    out = [f"import {MOD}.ApplyTable\n\n/-! # `{PROC}`: blocks of shard `{mname}` -/\n\n"
           f"open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem\n"
           f"open scoped Kraken.FrameLemmas.Int32Nat\nset_option mvcgen.warning false\n"
           f"set_option grind.warning false\n\nnamespace {NS}\n\nvariable [CodeEnv]\n"]
    if F5 and os.environ.get("APPLY_NOOPT") != "1":
        out[0] = "import Kraken.Rules.HbOptApply\n" + out[0]
    out[0] = "import Kraken.InfoOff\n" + out[0]
    lf = os.path.join(HERE, "lemmas", fname + ".lean")
    if os.environ.get("APPLY_LEMDIR") and os.path.exists(os.path.join(os.environ["APPLY_LEMDIR"], fname + ".lean")):
        lf = os.path.join(os.environ["APPLY_LEMDIR"], fname + ".lean")   # private lemmas take precedence
    for imp in IMPORTS.get(fname, []):   # single-file checks (INLINELEM): inline its lemmas instead
        if os.environ.get("APPLY_INLINELEM") == "1":
            out.append(open(os.path.join(HERE, "lemmas", imp + ".lean")).read())
        else:
            out[0] = out[0].replace(f"import {MOD}.ApplyTable\n", f"import {MOD}.ApplyTable\nimport {MOD}.Apply.{imp}\n")
    if os.path.exists(lf):
        if fname in PARTS and os.environ.get("APPLY_INLINELEM") != "1":   # shared by the parts: module Apply/<Shard>Lem.lean
            out[0] = out[0].replace(f"import {MOD}.ApplyTable\n", f"import {MOD}.Apply.{fname}Lem\n")
            # `open` does not cross module boundaries: replay the lemma file's own top-level opens
            # (e.g. EnvB's `namespace EnvBL ... end EnvBL / open EnvBL`) in each part
            hdr = out[0].split("namespace", 1)[0]
            ops = [l for l in open(lf).read().splitlines()
                   if l.startswith("open ") and not l.rstrip().endswith(" in") and l not in hdr]
            if ops:
                out[0] = out[0].replace("variable [CodeEnv]\n", "variable [CodeEnv]\n" + "".join(o + "\n" for o in ops), 1)
        else:
            out.append(open(lf).read())
    for j, b in enumerate(bl):
        if part_of(g, b) != mname:
            continue
        nxt = f'some "{bl[j + 1]["lab"]}"' if j + 1 < len(bl) else "none"
        f = os.path.join(OVR, b["id"] + ".lean")
        use = os.path.exists(f) and (dev is None or b["id"] in dev)
        h = hb.get(b["id"], DEFAULT_HB)
        pre = f"set_option maxRecDepth 100000 in\nset_option maxHeartbeats {h} in\n"
        if use:
            # the statement is the generator's, not the override's: Apply.lean's cfg rule needs
            # BlockOb's `next` = the text successor (helper tables once wrote `none` after a `jmp`)
            txt = opt_proof(open(f).read().rstrip(), b["id"], f6_plan(g, b) if b["id"] in F6 or "all" in F6 else None) + "\n"
            txt, nsub = re.subn(r'(BlockOb k e x ra t₀ "[^"]+" ⟨"[^"]+", B\.\S+, )(none|some "[^"]+")⟩',
                                lambda m: m.group(1) + nxt + "⟩", txt, count=1)
            assert nsub == 1, b["id"]
            out.append(pre + txt)
        elif entry_text(g, b) == "False":
            out.append(pre + blk_head(b, nxt) +
                       f"  intro n\n  refine Triple.pin fun s₀ hs₀ => ?_\n  exact (T.{b['id']}.mp hs₀.1).elim\n")
        else:
            out.append(pre + blk_head(b, nxt) + "  sorry\n")
    out.append(f"end {NS}\n")
    return info_off("\n".join(out))


# first tactic of every block proof: stop info-tree collection (Kraken/InfoOff.lean; px-ci)
INFO_OFF = re.compile(r"^(theorem blk_\w+\b.*?:= by\n)", re.M | re.S)


def info_off(txt):
    if os.environ.get("NO_INFO_OFF") == "1" or "  info_off\n" in txt:
        return txt
    return INFO_OFF.sub(r"\1  info_off\n", txt)


def lem_file(fname):
    """Apply/<Shard>Lem.lean: lemmas/<Shard>.lean of a split shard, imported by all its parts."""
    return (f"import {MOD}.ApplyTable\n\n/-! # `{PROC}`: helper lemmas of shard `{fname}` -/\n\n"
            f"open Kraken Kraken.X64.Parser Std.WP MachineWP Kraken.SysV Mem\n"
            f"open scoped Kraken.FrameLemmas.Int32Nat\nset_option mvcgen.warning false\n"
            f"set_option grind.warning false\n\nnamespace {NS}\n\nvariable [CodeEnv]\n"
            + open(lemma_path(fname)).read() + f"\nend {NS}\n")


def lemma_path(fname):
    d = os.environ.get("APPLY_LEMDIR")
    if d and os.path.exists(os.path.join(d, fname + ".lean")):
        return os.path.join(d, fname + ".lean")
    return os.path.join(HERE, "lemmas", fname + ".lean")


def main_file(g):
    bl = g.blocks
    chain = "".join(f"\n      (.cons (blk_{b['id']} k hk e hc x ra t₀ hSt)" for b in bl) + \
        " (.nil _)" + ")" * len(bl)
    imps = "\n".join(f"import {MOD}.Apply.{m}" for m, _ in modules())
    return f"""{imps}

/-!
# `{PROC}` (`libavcodec/aacsbr_template.c`): memory safety

The blocks (`Apply/*.lean`) assembled by `ProcSpec.of_cfg_post_pre` over the block list
(`Program.forall_blockAt`, `view_body`), with `body_wf` for the label uniqueness.

M4-F1 (closed): `sbr_hf_gen`'s read of `bw_array[g]` is inside the 20-byte `bw_array`
block. The noise-band search ends with `g ≤ n_q - 1 ≤ 4` by the `TabWF` facts F1–F5
(`ApplyTable.lean`, with their `aacsbr_template.c` citations).
-/

open Kraken Std.WP MachineWP Kraken.SysV

namespace {NS}

variable [CodeEnv]

set_option maxRecDepth 200000 in
/-- `ff_aac_sbr_apply` is memory safe (`ApplySpec`) with its callees at `k` bytes of stack.
Every access lies in the bytes it owns (`ApplyF ⋆ x.R`). On return it gives back the same
groups at new values `y`, and `x.KeepD y` holds (INV-D5): `bs_num_env`, `t_env`, `bs_freq_res`,
`t_q` of both channels, `ps->common`, `k[0]` and the frequency tables are unchanged, and `start`
is unchanged or cleared (`sbr_turnoff`).

**The synthesis window (D2).** `qmfVSize` gives `sbr_qmf_synthesis` either 9216 or 11264
bytes from `v0`, depending on `div` and `vOff`. In the larger case the call site carves the
extra 2048 bytes from `analysis_filterbank_samples` with `a3_overread_carve`.

**The `sbr_hf_assemble` footprint.** `HfAssembleSpec`'s footprint includes the 24 bytes
after Y[Ypos] (see `HfData`, `a2_row_spill`):
- For Ypos = 0, the theorem bounds the access to Y[1] by those 24 bytes.
- For Ypos = 1, those bytes belong to `g_temp`, which hf_assemble owns anyway. There the
  24-byte bound rests on `a2_row_spill` and the row-crossing discipline (`HfAssemble`
  crosses a row of `Y` only through `a2_row_spill`; checked by tv.sh), not on the footprint.

**Granularity (ruling (A)).** A procedure theorem bounds the procedure's accesses by the
union of the bytes it owns. Reads and writes are not distinguished. Unions are exact only at
procedure boundaries: this theorem and each callee contract. Inside one proof, splitting an
owned union into objects or rows does not change what is proved, so the per-object layout of
`ApplyF` is presentation and object/row boundaries inside it are not theorem facts. A row
may be crossed only through `a2_row_spill`.

**Trusted.**
- Assumed, never proved:
  - `ff_ps_apply` (`PsApplySpec`): memory safe given `PsWF`, `top ≤ 64` and 16-alignment,
    and preserves W6.
  - `av_tx` with its tables `TxTab` (`TxSpec`, also inside `QmfSynthesisSpec`).
  - `float_dsp` for `1 ≤ len < 2^30` (`VectorFmulRevSpec`, and `vector_fmul` and
    `vector_fmul_add` inside `QmfSynthesisSpec`).
  - `memcpy`, `memset`, `av_log` (`MemcpySpec`, `MemsetSpec`, `AvLogSpec`).
  - `AbortSpec` holds of any code, since its precondition is `False`.
- Hypotheses here, each proved separately; composing them is checked at link:
  - the `SBRDSPContext` leaf contracts (`Dsp/*`);
  - `LfGenSpec`, `HfInverseFilterSpec`, `HfAssembleSpec`, `XGenSpec`, `QmfSynthesisSpec`
    (the `spec` theorems of their modules).
- The float model is not an assumption. `DequantFloatModel`, the `1E20` compare of
  `sbr_dequant`, is proved (`dequantFloatModel_holds`) and used directly.
- Also trusted: the placement of the text (`Program.PlacedIn`). tv.sh compares every Lean text
  with the object (exit 0, no open link items; the `hf_apply_noise` entry padding is in the
  Lean text as sized `nop`s). Also the x86 dsp initialisation (which procedures the `sbr->dsp` and
  `sbr->c` slots hold, set by cpu flags). -/
theorem spec (hpl : Program.PlacedIn body) (k : Nat) (hk : k ≤ 2 ^ 32) (e : Env)
    (hc : ApplyCallees k e) : ApplySpec k e := by
  refine Kraken.Executable.ProcSpec.of_cfg_post_pre (p := body) (table k e) (Post' k e) var
    (hblocks := ?_) (hpre := ?_) (hpost := ?_) (hwf := body_wf)
  · intro x ra t₀ hp
    have hSt := CallPre.le hp.1
    refine Program.forall_blockAt ?_
    rw [view_body]
    exact {chain}
  · intro x ra t ht
    exact (T.start).mpr ⟨rfl, ht⟩
  · intro x ra t₀ s _ h; exact h

end {NS}
"""


def main():
    bl = read_blocks()
    g = G(bl)
    for f in ["_frames"] + [f for f, _ in FILES]:   # shared frame dicts first
        sp = os.path.join(HERE, "spec", f + ".py")
        if os.environ.get("APPLY_SPECDIR"):  # private spec files take precedence
            sp2 = os.path.join(os.environ["APPLY_SPECDIR"], f + ".py")
            if os.path.exists(sp2):
                sp = sp2
        if os.path.exists(sp):
            ns = {"__file__": sp}   # spec files may import siblings (MapA imports MapB)
            g.cur_file = f
            exec(open(sp).read(), ns)
            ns["define"](g)
    hb = {}
    for hbf in [os.path.join(HERE, "..", "baseline", "hb_table.txt")] + ([os.environ["APPLY_HB"]] if os.environ.get("APPLY_HB") else []):
        if os.path.exists(hbf):   # APPLY_HB (private) entries override the shared table
            for line in open(hbf):
                p = line.split()
                if len(p) >= 2:
                    hb[p[0]] = int(p[1])
    dev = set(os.environ["APPLY_DEV"].split(",")) if os.environ.get("APPLY_DEV") else None
    only = set(os.environ["APPLY_FILES"].split(",")) if os.environ.get("APPLY_FILES") else None
    os.makedirs(os.path.join(OUT, "Apply"), exist_ok=True)

    def write(rel, txt):
        p = os.path.join(OUT, rel)
        if os.path.exists(p) and open(p).read() == txt:
            return  # keep mtime: lake does not rebuild
        open(p, "w").write(txt)

    if os.environ.get("APPLY_NOTABLE") != "1":
        write("ApplyText.lean", text_file(g))
        write("ApplyTable.lean", table_file(g))
        write("Apply.lean", main_file(g))
    for f in PARTS:
        if os.path.exists(lemma_path(f)) and (only is None or f in only):
            write(f"Apply/{f}Lem.lean", lem_file(f))
    for m, f in modules():
        if only is None or f in only or m in only:
            write(f"Apply/{m}.lean", shard_file(m, g, hb, dev))
    from collections import Counter
    print("blocks", len(bl), Counter(part_of(g, b) for b in bl))
    if os.environ.get("APPLY_VARINFO"):
        ds, missing, lp = var_digits(g)
        print("loops", len(lp), lp)
        for b, d in zip(bl, ds):
            if d[1] != "0" or any(x != "0" for x in d[1:]) or True:
                pass
        mf = sorted({file_of(b["phase"]) for b in bl if b["id"] in dict(missing)})
        print("labels in loops without measures:", len(missing), "files:", mf)


if __name__ == "__main__":
    main()
