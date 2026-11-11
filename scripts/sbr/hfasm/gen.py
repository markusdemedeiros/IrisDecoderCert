#!/usr/bin/env python3
"""Generate the text of the sbr_hf_assemble proof (build.sh assembles and splits it into
Kraken/X64/Examples/Sbr/HfAssemble.lean and HfAssemble/{Base,Part1,Part2}.lean).
Inputs: body.s (mkbody.py's output), spec_hf.py (+ mregion.py, skel.py), override/<blk>.lean
(block proofs), override/_lemmas.lean, lb01d_dev.lean, dev2.lean, hb_table.txt."""
import subprocess, sys, os, re
import re as _re
HERE = os.path.dirname(os.path.abspath(__file__))
P = "sbr_hf_assemble"
R = "t₀.regs.get64 .rsp"

# frame slots: (name, offset below rsp0, size)
SLOTS = [("gtab", 0x288, 192), ("qtab", 0x1c8, 192), ("vec", 0x108, 16), ("mm1", 0xf8, 8),
         ("sm", 0xf0, 8), ("qh", 0xe8, 8), ("ykx8", 0xe0, 8), ("m4", 0xd8, 8), ("m16", 0xd0, 8),
         ("xkx", 0xc8, 8), ("mz", 0xc0, 8), ("qb", 0xb8, 8), ("sme", 0xb0, 8), ("u1", 0xa8, 4),
         ("kx1", 0xa4, 4), ("gh", 0xa0, 8), ("ea", 0x98, 8), ("kx", 0x90, 8), ("y", 0x88, 8),
         ("m", 0x80, 8), ("xv", 0x78, 16), ("u2", 0x68, 12), ("sm4", 0x5c, 4), ("s50", 0x58, 8),
         ("s48", 0x50, 8), ("sbr", 0x48, 8), ("s38", 0x40, 8), ("ch", 0x38, 8)]
SAVED = [("rbx", 0x30), ("r12", 0x28), ("r13", 0x20), ("r14", 0x18), ("r15", 0x10), ("rbp", 0x8)]


def cell(name, off, size, v):
    a = f"(r - {off:#x}#64)"
    if v == "OMIT":
        return []
    if v is None:
        if name == "s38":
            return ["4 ?@ (r - 0x40#64)", "4 ?@ (r - 0x3c#64)"]
        return [f"{size} ?@ {a}"]
    if name == "s38" and isinstance(v, tuple):
        # split variants
        kind, val = v
        if kind == "b":   # 1 + 3 + 4
            c1 = "1 ?@ (r - 0x40#64)" if val is None else f"Int.toBytes 1 {val} =@ (r - 0x40#64)"
            return [c1, "3 ?@ (r - 0x3f#64)", "4 ?@ (r - 0x3c#64)"]
        if kind == "q":   # one qword
            return ["8 ?@ (r - 0x40#64)" if val is None else f"c8 (r - 0x40#64) ({val})"]
        if kind == "d":   # 4 + 4
            c1 = "4 ?@ (r - 0x40#64)" if val is None else f"Int.toBytes 4 {val} =@ (r - 0x40#64)"
            return [c1, "4 ?@ (r - 0x3c#64)"]
    if size == 8:
        return [f"c8 {a} ({v})"]
    return [f"Int.toBytes {size} {v} =@ {a}"]


def frame(vals, saved_val=True, tail="Kt"):
    cs = []
    for name, off, size in SLOTS:
        cs += cell(name, off, size, vals.get(name))
    for reg, off in SAVED:
        if saved_val:
            cs.append(f"c8 (r - {off:#x}#64) (t₀.regs.get64 .{reg})")
        else:
            cs.append(f"8 ?@ (r - {off:#x}#64)")
    s = cs[0]
    for c in cs[1:]:
        s += f"\n    ⋆ ({c}"
    s += f" ⋆ {tail}" + ")" * (len(cs) - 1)
    return s


FRAMES = {}
EXIT_FRAMES = []


def defframe(nm, vals, saved_val=True, params=""):
    FRAMES[nm] = (vals, saved_val, params)


# ---- frames ----



OUT = []


def emit(s):
    OUT.append(s)


def frames_text():
    out = []
    for nm, (vals, sv, params) in FRAMES.items():
        out.append(f"abbrev {nm} (x : HfArgs) (t₀ : MachineData){params} (Kt : Mem 64 → Prop) : Mem 64 → Prop :=\n"
                   f"  let r := {R}\n  {frame(vals, sv)}\n")
    return "\n".join(out)


# ---------------- per-block pre/post lemmas ----------------
GROUPS = {
    "Sc": ["Int.toBytes 4 x.reset.toInt =@ (arg2 t₀ + 0x18#64)",
           "Int.toBytes 4 x.smooth.toInt =@ (arg2 t₀ + 0x38#64)",
           "Int.toBytes 4 (x.kx : Int) =@ (arg2 t₀ + 0x58#64)",
           "Int.toBytes 4 (x.m : Int) =@ (arg2 t₀ + 0x60#64)"],
    "Te": ["Int.toBytes 4 (x.nenv : Int) =@ (arg3 t₀ + 0x8#64)"] +
          [f"Int.toBytes 1 (x.te {k} : Int) =@ (arg3 t₀ + {0x15a9c + k:#x}#64)" for k in range(10)],
    "Ea": ["Int.toBytes 4 x.ea0.toInt =@ arg4 t₀", "Int.toBytes 4 x.ea1.toInt =@ (arg4 t₀ + 4#64)"],
    "Fn": [f"Int.toBytes 8 fs.{n}.toBitVec.toInt =@ (arg2 t₀ + {o:#x}#64)" for n, o in
           [("gfilt", 0x60228), ("noise0", 0x60230), ("noise1", 0x60238), ("noise2", 0x60240), ("noise3", 0x60248)]],
}
GDEF = {"Sc": "ScW x t₀", "Fn": "FnW fs t₀", "Te": "TeW x t₀", "Ea": "EaW x t₀", "Data": "DataW x t₀"}


def chain(cs, tail):
    if not cs:
        return tail
    s = cs[0]
    for c in cs[1:]:
        s += f" ⋆ ({c}"
    return s + f" ⋆ {tail}" + ")" * (len(cs) - 1)


def frame_cells(vals, saved_val):
    """list of (slotname, cellstring) in chain order, with r expanded."""
    out = []
    for name, off, size in SLOTS:
        for c in cell(name, off, size, vals.get(name)):
            out.append((name, c.replace("(r -", f"({R} -")))
    for reg, off in SAVED:
        c = f"c8 ({R} - {off:#x}#64) (t₀.regs.get64 .{reg})" if saved_val else f"8 ?@ ({R} - {off:#x}#64)"
        out.append((reg, c))
    return out


def tparts(IC):
    """the T prefix parts (name, string) before the frame."""
    return [("slot", f"8 ?@ ({R} - 0x290#64)"), ("res", f"Reserve k ({R} - 0x290#64)"),
            ("Data", "DataW x t₀"), ("Sc", "ScW x t₀"), ("Fn", "FnW fs t₀"), ("Te", "TeW x t₀"),
            ("Ea", "EaW x t₀"), ("IC", IC)]


def view(fr, IC, touched, args=None):
    return subst(view0(fr, IC, touched), fr, args)


def view0(fr, IC, touched):
    vals, sv, params = FRAMES[fr]
    front, rest = [], []
    for nm, c in tparts(IC):
        if nm in touched:
            front += GROUPS.get(nm, [c]) if nm in GROUPS else [c]
        else:
            rest.append(c)
    for nm, c in frame_cells(vals, sv):
        (front if nm in touched else rest).append(c)
    return chain(front + [f"Hid ({chain(rest, f'Rest x.R ra t₀')})"], "").rstrip(" ⋆ ") if False else \
        chain(front, f"Hid ({chain(rest, 'Rest x.R ra t₀')})")


import re as _re


def pnames(fr):
    if fr not in FRAMES:
        return []
    params = FRAMES[fr][2]
    return [p.split(":")[0].strip(" (") for p in params.split(")") if p.strip()] if params else []


def frame_app(fr, args=None):
    args = pnames(fr) if args is None else args
    return f"({fr} x t₀{''.join(' (' + a + ')' for a in args)})"


def subst(txt, fr, args):
    if args is None:
        return txt
    for p, a in zip(pnames(fr), args):
        txt = _re.sub(r"\b" + p + r"\b", "(" + a + ")", txt)
    return txt


def view_lemma(name, fr, IC, touched):
    vals, sv, params = FRAMES[fr]
    unf = "T, Hid, " + ", ".join(FRAMES.keys()) + ", " + ", ".join(
        {"Sc": "ScW, HfSc", "Te": "TeW, HfTe", "Ea": "EaW, HfEa", "Fn": "FnW, HfFn, FnCell"}[g] for g in GROUPS if g in touched) if any(g in touched for g in GROUPS) else "T, Hid, " + ", ".join(FRAMES.keys())
    return (f"theorem {name} (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData){params} :\n"
            f"    T k fs x ra t₀ ({IC}) {frame_app(fr)} =\n      {view(fr, IC, touched)} := by\n"
            f"  simp only [{unf}, Std.ExtHashMap.sep_assoc]\n  all_goals ac_rfl\n")


# ---------------- table ----------------
ENTRY = {}   # label -> (facts list, frame, IC)
VAR = {}     # label -> var expression (Lean, in s)


def entry(l, facts, fr, IC="IdxC x t₀", var="0", args=None):
    ENTRY[l] = (facts, fr, IC, args)
    VAR[l] = var


def lab(l):
    return P if l == "" else f"{P}.{l}"


def mem_of(l):
    facts, fr, IC, args = ENTRY[l]
    return f"(s.dmem =⋆ T k fs x ra t₀ ({IC}) {frame_app(fr, args)})"


def facts_of(l):
    return ENTRY[l][0]


def table_text():
    out = ["/-- The invariant table. -/",
           "abbrev table (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData) :",
           "    Label → MachineData → Prop"]
    for l, (facts, fr, IC, args) in ENTRY.items():
        body = " ∧ ".join([f"({f})" for f in facts] + [mem_of(l)])
        if l == "":
            body = f"s = t₀ ∧ HfC x t₀ ∧ (t₀.dmem =⋆ T k fs x ra t₀ ({IC}) {frame_app(fr, args)})"
        out.append(f"  | \"{lab(l)}\", s => {body}")
    out.append("  | _, _ => False\n")
    out.append("/-- The variant. -/\nabbrev var : Label → MachineData → Nat")
    for l in ENTRY:
        out.append(f"  | \"{lab(l)}\", s => {VAR[l]}")
    out.append("  | _, _ => 0\n")
    return "\n".join(out)


def tbl_lemma(name, l, view_name, touched):
    facts, fr, IC, args = ENTRY[l]
    hyp = " ∧ ".join([f"({f})" for f in facts] + [f"(s.dmem =⋆ {view(fr, IC, touched, args)})"])
    shown = " ∧ ".join([f"({f})" for f in facts] + [mem_of(l)])
    return (f"theorem {name} (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ s : MachineData) :\n"
            f"    ({hyp}) →\n    table k fs x ra t₀ \"{lab(l)}\" s := by\n"
            f"  intro h\n  show {shown}\n  rw [{view_name}]\n  exact h\n")


FORGETS = set()


def forget_tbl_lemma(name, l, view_name, via, touched, vargs=None):
    facts, fr, IC, args = ENTRY[l]
    vapp = "" if vargs is None else " " + " ".join(f"({a})" for a in vargs)
    hyp = " ∧ ".join([f"({f})" for f in facts] + [f"(s.dmem =⋆ {view(via, IC, touched, vargs)})"])
    n = len(facts)
    hs = ", ".join(f"h{i}" for i in range(n))
    return (f"theorem {name} (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ s : MachineData) :\n"
            f"    ({hyp}) →\n    table k fs x ra t₀ \"{lab(l)}\" s := by\n"
            f"  rintro ⟨{hs}, hm⟩\n  rw [← {view_name}] at hm\n"
            f"  exact ⟨{hs}, T_forget k fs x ra t₀ _ _ _ ({via}_to_{fr} x t₀{vapp}) _ hm⟩\n")


def forget_lemma(a, b):
    va, _, _ = FRAMES[a]
    vb, _, _ = FRAMES[b]
    ca, cb = [], []
    for name, off, size in SLOTS:
        ca += cell(name, off, size, va.get(name))
        cb += cell(name, off, size, vb.get(name))
    join = False
    if "8 ?@ (r - 0x40#64)" in cb and "8 ?@ (r - 0x40#64)" not in ca and not any(c.startswith("c8 (r - 0x40#64)") for c in ca):
        i = cb.index("8 ?@ (r - 0x40#64)")
        cb = cb[:i] + ["4 ?@ (r - 0x40#64)", "4 ?@ (r - 0x3c#64)"] + cb[i + 1:]
        join = "s38_join8"
    elif len(ca) == len(cb) + 1:
        # A has the byte-split s38 ([1][3][4]), B the dword-split ([4][4])
        i = cb.index("4 ?@ (r - 0x40#64)")
        cb = cb[:i] + ["1 ?@ (r - 0x40#64)", "3 ?@ (r - 0x3f#64)"] + cb[i + 1:]
        join = True
    assert len(ca) == len(cb), (a, b)
    term = "Mem.Entails.refl _"
    for x, y in reversed(list(zip(ca, cb))):
        if x == y:
            term = f"Mem.Entails.sep_left ({term})"
        else:
            assert "?@" in y, (x, y)
            if x.startswith("c8 "):
                term = f"Mem.Entails.forget8 _ _ ({term})"
            else:
                term = f"Mem.Entails.forget (Mem.Split.here _ _) ({term}) (by simp [Int.toBytes_length]) (by decide)"
    return f"""omit [CodeEnv] in
theorem {a}_to_{b} (x : HfArgs) (t₀ : MachineData){FRAMES[a][2]} (K : Mem 64 → Prop) :
    Mem.Entails ({frame_app(a)[1:-1]} K) ({frame_app(b)[1:-1]} K) := by
  simp only [{a}, {b}, c8]
{("  rw [" + (join if isinstance(join, str) else "s38_join") + "]") if join else ""}
  exact {term}
"""


def exit_tbl_lemma(name, l, view_name, via, touched, vargs=None):
    facts, fr, IC, args = ENTRY[l]
    params = FRAMES[via][2]
    hyp = " ∧ ".join([f"({f})" for f in facts] + [f"(s.dmem =⋆ {view(via, 'IdxC x t₀', touched, vargs)})"])
    n = len(facts)
    hs = ", ".join(f"h{i}" for i in range(n))
    vapp = "" if vargs is None else " " + " ".join(f"({a})" for a in vargs)
    return (f"theorem {name} (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ s : MachineData){params} :\n"
            f"    ({hyp}) →\n    table k fs x ra t₀ \"{lab(l)}\" s := by\n"
            f"  rintro ⟨{hs}, hm⟩\n  rw [← {view_name}{vapp}] at hm\n"
            f"  exact ⟨{hs}, T_exit k fs x ra t₀ _ ({via}_exit x t₀{vapp}) _ hm⟩\n")


# ---------------- blocks ----------------
BLOCKS = []   # (label, kind, data)
LEMMAS = []


def nfacts(l):
    return len(ENTRY[l][0])


def pat(l):
    if l == "":
        return "hs, hC"
    out = []
    for i, f in enumerate(ENTRY[l][0]):
        if f == "Base t₀ s":
            out.append("⟨hrsp, hrbp⟩")
        elif f == "ArgRegs t₀ s":
            out.append("⟨ha0, ha1, ha2, ha3, ha4⟩")
        else:
            out.append(f"h{i}")
    return ", ".join(out)


def hyps(l):
    out = ""
    for f in ENTRY[l][0]:
        if f == "Base t₀ s":
            out += ", hrsp, hrbp"
        elif f == "ArgRegs t₀ s":
            out += ", ha0, ha1, ha2, ha3, ha4"
    return out


_DONE_TBL = set()


def front_cells(fr, IC, touched, args=None):
    """the cells `view0` puts in front of `Hid`, in order (after `subst`)."""
    vals, sv, params = FRAMES[fr]
    front = []
    for nm, c in tparts(IC):
        if nm in touched:
            front += GROUPS.get(nm, [c]) if nm in GROUPS else [c]
    for nm, c in frame_cells(vals, sv):
        if nm in touched:
            front.append(c)
    return [subst(c, fr, args) for c in front]


def slot_reads(fr, IC, touched, args=None):
    """F6: one closed read fact per value cell in front of `Hid` (explicit `Split` path), stated
    before `vcgen`; the generated `simp … at *` normalises them with the load hypotheses."""
    out, names = [], []
    for i, c in enumerate(front_cells(fr, IC, touched, args)):
        if "?@" in c:
            continue
        p = "Mem.Split.here _ _"
        for _ in range(i):
            p = f"Mem.Split.right ({p}) _"
        names.append(f"hR{i}")
        out.append(f"    have hR{i} := Mem.Val.loadInt hm ({p}) (Int.toBytes_length _ _) (by decide)\n")
    return "".join(out), names


SLOT_ROUND = """    all_goals try simp only [{hs}, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
"""
# two rounds: a load whose address is a loaded value (`mov -0x30(%rbp),%r8; mov 0x8(%r8),%edx`)
# matches its read fact only once the first value is in
SLOT_SIMP = SLOT_ROUND + SLOT_ROUND


def _mem_ops():
    """label -> (stores, loads) of its instructions in body.s (memory operands)."""
    import re as _r
    out, lab = {}, None
    for line in open(os.path.join(HERE, "body.s")):
        m = _r.match(r"^sbr_hf_assemble\.?([\w.]*):", line)
        if m:
            lab = m.group(1)
            out[lab] = [0, 0]
            continue
        t = line.strip()
        if lab is None or not t or "(" not in t:
            continue
        op, args = t.split()[0], t[len(t.split()[0]):].strip()
        if op.startswith(("j", "call", "lea", "nop")):
            continue
        if op.startswith(("cmp", "test")) or "," not in args or "(" not in args.split(",")[-1]:
            out[lab][1] += 1
        else:
            out[lab][0] += 1
    return out


MEMOPS = _mem_ops()

_R64 = {"rax", "rbx", "rcx", "rdx", "rsi", "rdi", "rbp", "rsp"} | {f"r{i}" for i in range(8, 16)}
_R32 = {"eax", "ebx", "ecx", "edx", "esi", "edi", "ebp", "esp"} | {f"r{i}d" for i in range(8, 16)}


def _insns():
    """label -> list of ('S', off below rsp0 or None, size or None) / ('L',) / ('X',) in order."""
    import re as _r
    out, lab = {}, None
    for line in open(os.path.join(HERE, "body.s")):
        m = _r.match(r"^sbr_hf_assemble\.?([\w.]*):", line)
        if m:
            lab = m.group(1)
            out[lab] = []
            continue
        t = line.strip()
        if lab is None or not t:
            continue
        op = t.split()[0]
        args = t[len(op):].strip()
        if op.startswith(("push", "call", "rep")) or (op.startswith(("stos", "movs")) and not args):
            out[lab].append(("X",))
            continue
        if "(" not in t or op.startswith(("j", "lea", "nop")):
            continue
        if op.startswith(("cmp", "test")) or "," not in args or "(" not in args.split(",")[-1]:
            out[lab].append(("L",))
            continue
        src, dst = args[:args.rindex(",")], args.split(",")[-1].strip()
        if op not in ("mov", "vmovdqa", "vmovq"):
            out[lab].append(("L",))   # read-modify-write: load first
        md = _r.match(r"^-0x([0-9a-f]+)\(%rbp\)$", dst)
        size = None
        s = src.strip().lstrip("%")
        if op == "vmovdqa":
            size = 16
        elif op == "vmovq":
            size = 8
        elif s in _R64:
            size = 8
        elif s in _R32:
            size = 4
        if md and int(md.group(1), 16) in RBP_OFFS and size:
            out[lab].append(("S", int(md.group(1), 16) + 8, size))
        else:
            out[lab].append(("S", None, None))
    return out


INSNS = None
SC_TEXT = {}   # block -> store-chain text (for porting into override/ blocks)


def _path(i):
    p = "Mem.Split.here _ _"
    for _ in range(i):
        p = f"Mem.Split.right ({p}) _"
    return p


def _cell_info(c):
    """(kind 'B'/'V', size, rsp offset or None) of a front cell string, or None."""
    import re as _r
    m = _r.match(r"^(\d+) \?@ \(t₀\.regs\.get64 \.rsp - 0x([0-9a-f]+)#64\)$", c)
    if m:
        return ("B", int(m.group(1)), int(m.group(2), 16))
    m = _r.match(r"^(\d+) \?@ ", c)
    if m:
        return ("B", int(m.group(1)), None)
    m = _r.match(r"^c8 \(t₀\.regs\.get64 \.rsp - 0x([0-9a-f]+)#64\) ", c)
    if m:
        return ("V", 8, int(m.group(1), 16))
    if c.startswith("c8 "):
        return ("V", 8, None)
    m = _r.match(r"^Int\.toBytes (\d+) .* =@ \(t₀\.regs\.get64 \.rsp - 0x([0-9a-f]+)#64\)$", c)
    if m:
        return ("V", int(m.group(1)), int(m.group(2), 16))
    m = _r.match(r"^Int\.toBytes (\d+) .* =@ ", c)
    if m:
        return ("V", int(m.group(1)), None)
    return None


def store_chain(l, fr, IC, touched, args=None):
    """Stage 2 (store threading): isSome facts for every front cell, a position-keeping store chain
    `hS<k>` (stops at the first store it cannot map to a front cell), and read facts for the valued
    cells after each prefix of the chain that is followed by a load (`hR<i>` before any store,
    `hL<k>_<i>` after k stores). Returns (text, simp names, nstores threaded)."""
    global INSNS
    if INSNS is None:
        INSNS = _insns()
    cells = front_cells(fr, IC, touched, args)
    info = [_cell_info(c) for c in cells]
    out, names = [], []
    for i, ci in enumerate(info):
        if ci is None:
            continue
        if ci[0] == "B":
            out.append(f"    have hB{i} := Mem.Block.loadInt_isSome_at hm ({_path(i)})\n")
        else:
            out.append(f"    have hB{i} := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm ({_path(i)}) (Int.toBytes_length _ _) (by decide)⟩\n")
    at = {ci[2]: i for i, ci in enumerate(info) if ci is not None and ci[2] is not None}
    kind = [ci[0] if ci else None for ci in info]
    k, done_reads = 0, set()

    def reads(k):
        if k in done_reads:
            return
        done_reads.add(k)
        vs = " ".join(f"(v{j} : Int)" for j in range(1, k + 1))
        pv = " ".join(f"v{j}" for j in range(1, k + 1))
        for i, kd in enumerate(kind):
            if kd != "V":
                continue
            if k == 0:
                nm = f"hR{i}"
                out.append(f"    have {nm} := Mem.Val.loadInt hm ({_path(i)}) (Int.toBytes_length _ _) (by decide)\n")
            else:
                nm = f"hL{k}_{i}"
                out.append(f"    have {nm} := fun {vs} => Mem.Val.loadInt (hS{k} {pv}) ({_path(i)}) (Int.toBytes_length _ _) (by decide)\n")
            names.append(nm)

    for ins in INSNS.get(l, []):
        if ins[0] == "L":
            reads(k)
            continue
        if ins[0] == "X" or ins[1] is None or ins[1] not in at:
            break
        i = at[ins[1]]
        if info[i][1] != ins[2]:
            break
        k += 1
        prev = "hm" if k == 1 else f"(hS{k - 1} {' '.join(f'v{j}' for j in range(1, k))})"
        vs = " ".join(f"(v{j} : Int)" for j in range(1, k + 1))
        if kind[i] == "B":
            term = f"store_keep {prev} ({_path(i)}) ({_path(i)}) (v := v{k})"
        else:
            term = f"store_keep_val {prev} ({_path(i)}) (Int.toBytes_length _ _) ({_path(i)}) (v := v{k})"
        out.append(f"    have hS{k} := fun {vs} => {term}\n")
        kind[i] = "V"
    if k > 1:
        out.append("    clear " + " ".join(f"hS{j}" for j in range(1, k)) + "\n")
    return "".join(out), names, k


STORE_CLOSE = "    all_goals first | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | close_cell\n"
# auto-slot opt-outs: slower with slots (full-run measurement) or broken (g1: simp maxRecDepth;
# a1: grouped front cells, the positional Split paths are wrong)
# store-chain opt-outs (stage 2)
NO_STORE = {"r0", "m2"}  # whnf timeouts with the chain
NO_SLOTS = {"La8ea", "La9c2", "Laa62", "Lab02", "Laba2", "Lac42", "Lace2", "Lad82", "Lae0d",
            "g1", "a1"}


def plain_block(l, touched, succs, hb=1000000, extra_simp="", pre_tac="", slots=None):
    """succs: list of (succ label, how) with how in {'fall','jump'}"""
    nm = (l or "start")
    _, fr, IC, args = ENTRY[l]
    if slots is None:  # F6 by default on the blocks that load but do not store
        st, ld = MEMOPS.get(l, [0, 0])
        slots = st == 0 and ld > 0 and nm not in NO_SLOTS
    sr, srn = slot_reads(fr, IC, touched, args) if slots else ("", [])
    closer = "    all_goals close_cell\n"
    st, ld = MEMOPS.get(l, [0, 0])
    if st > 0 and l != "" and nm not in NO_STORE and not slots:
        sr, srn, _k = store_chain(l, fr, IC, touched, args)
        closer = STORE_CLOSE
        SC_TEXT[nm] = (sr, srn, _k)
    LEMMAS.append(view_lemma(f"{nm}_pre", fr, IC, touched))
    tacs = []
    for sc in succs:
        sl, how = sc[0], sc[1]
        sfr = ENTRY[sl][1]
        vname = f"{nm}_post_{sl or 'start'}"
        tname = f"{sl or 'start'}_tbl_{nm}"
        if sfr != "FZ" and len(sc) > 2:
            via = sc[2]
            LEMMAS.append(view_lemma(vname, via, ENTRY[sl][2], touched))
            LEMMAS.append(forget_tbl_lemma(tname, sl, vname, via, touched, sc[3] if len(sc) > 3 else None))
            FORGETS.add((via, sfr))
        elif sfr == "FZ":
            via = sc[2]
            vargs = sc[3] if len(sc) > 3 else None
            LEMMAS.append(view_lemma(vname, via, "IdxC x t₀", touched))
            LEMMAS.append(exit_tbl_lemma(tname, sl, vname, via, touched, vargs))
        else:
            if tname not in _DONE_TBL:
                _DONE_TBL.add(tname)
                LEMMAS.append(view_lemma(vname, sfr, ENTRY[sl][2], touched))
                LEMMAS.append(tbl_lemma(tname, sl, vname, touched))
        hl = ["?_"] * (nfacts(sl) + 1)
        if ENTRY[sl][0] and ENTRY[sl][0][0] == "HfC x t₀" and l != "" and ENTRY[l][0] and ENTRY[l][0][0] == "HfC x t₀":
            hl[0] = "h0"
        holes = ", ".join(hl)
        if how == "fall":
            tacs.append(f"    all_goals try refine ⟨{tname} _ _ _ _ _ _ ⟨{holes}⟩, ?_⟩")
        else:
            tacs.append(f"    all_goals try (left; refine Table.ofLabels_at (l := \"{lab(sl)}\") ⟨by decide, {tname} _ _ _ _ _ _ ⟨{holes}⟩, ?_⟩)")
    start = "    subst hs\n" if l == "" else ""
    BLOCKS.append((l, f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats {hb} in
theorem blk_{nm} (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "{lab(l)}" := by
  clear hc
  cfg_block
  measure_hb "{nm}"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨{pat(l)}, hm⟩, hn⟩ := hs₀
{start}    rw [{nm}_pre] at hm
{sr}{pre_tac}    vcgen
""" + "\n".join(tacs) + f"""
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd{RBPO}{hyps(l)}{extra_simp},
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
""" + (SLOT_SIMP.format(hs=", ".join(srn)) if srn else "") + closer))


def sorry_block(l):
    nm = (l or "start")
    BLOCKS.append((l, f"""theorem blk_{nm} (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "{lab(l)}" := by
  sorry
"""))


BLOCKOB = """

macro "grind_cells'" : tactic =>
  `(tactic| ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); grind (ematch := 400) (gen := 400) (instances := 20000) (mbtc := false) [-BitVec.toInt_eq_toNat_of_msb, -BitVec.toInt_eq_toNat_bmod, hf_ofBytes1_mod]))

omit [CodeEnv] in
theorem hf_add_congr {a b c d : BitVec 64} (h1 : a = c) (h2 : b = d) : a + b = c + d := by subst h1 h2; rfl

omit [CodeEnv] in
theorem hf_ofNat_congr {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by subst h; rfl

macro "close_part" : tactic =>
  `(tactic| first | grind_cells' | (refine hf_ofNat_congr ?_; grind_cells'))

/-- The read-only `.LCPI17_*` float constants are 4-byte blocks of `DataW`. -/
theorem hf_lcpi4 {x : HfArgs} {t : MachineData} {R : Mem 64 → Prop} {m : Mem 64} {l : Label}
    (hl : l = "LCPI17_6" ∨ l = "LCPI17_7" ∨ l = "LCPI17_8" ∨ l = "LCPI17_9" ∨ l = "LCPI17_10"
      ∨ l = "LCPI17_12")
    (h : m =⋆ DataW x t ⋆ R) : (m.loadInt (lab l) 4).isSome = true := by
  rw [DataW] at h
  simp only [Blocks, Std.ExtHashMap.sep_assoc] at h
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl <;> grind_cells'

/-- `hf_lcpi4` with `DataW` anywhere in the tree (`find_split`). -/
theorem hf_lcpi4_split {x : HfArgs} {t : MachineData} {R H : Mem 64 → Prop} {m : Mem 64} {l : Label}
    (hl : l = "LCPI17_6" ∨ l = "LCPI17_7" ∨ l = "LCPI17_8" ∨ l = "LCPI17_9" ∨ l = "LCPI17_10"
      ∨ l = "LCPI17_12")
    (h : m =⋆ H) (hs : Mem.Split (DataW x t) R H) : (m.loadInt (lab l) 4).isSome = true := by
  unfold Mem.Split at hs; rw [hs] at h; exact hf_lcpi4 hl h

set_option hygiene false in
/-- A `.LCPI17_*` load behind stores, from `DataW` anywhere in `hm`'s tree. -/
macro "cell_lcpi_raw" : tactic =>
  `(tactic| ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); (find_split hm DataW); with_reducible exact hf_lcpi4_split (by simp) hm hsplit))

/-- `cell_lcpi_raw` under a 20k-heartbeat `cell_guard`. -/
macro "cell_lcpi" : tactic => `(tactic| cell_guard 20000 cell_lcpi_raw)

/-- A value goal after `cell_reads` replaced the loaded values by the cells' bytes. -/
macro "cell_val_raw" : tactic =>
  `(tactic| (simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] <;> first | with_reducible rfl | omega))

/-- `cell_val_raw` under a 20k-heartbeat `cell_guard`. -/
macro "cell_val" : tactic => `(tactic| cell_guard 20000 cell_val_raw)

/-- The generic closer. The cell closers (`Cells.lean`) come before `grind`: a failing `grind`
over the full frame costs 0.1-1M heartbeats, the cell closers fail in a few hundred. -/
macro "close_cell" : tactic =>
  `(tactic| first | omega | with_reducible assumption | cell_some | cell_lcpi | cell_val | grind_cells' | (refine hf_add_congr ?_ ?_ <;> close_part) | (refine hf_xb ?_ ?_ <;> first | with_reducible assumption | with_reducible rfl))

abbrev BlockOb (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ : MachineData) (l : Label) : Prop :=
  ∀ blk, Program.blockAt body l = some blk → ∀ n : Nat,
    ⦃ fun s => table k fs x ra t₀ l s ∧ var l s = n ⦄ blk.body
    ⦃ (match blk.next with
       | some l' => fun _ s => table k fs x ra t₀ l' s ∧ var l' s ≤ n
       | none => fun _ _ => False);
      fun a s => Table.ofLabels (fun l' s => (Program.blockAt body l').isSome
          ∧ table k fs x ra t₀ l' s ∧ Program.EdgeLt body var l n l' s) a s
        ∨ (a = ra ∧ Post' k fs x ra t₀ s) ⦄
"""

PREAMBLE = """
/-! ## NEW LIBRARY CANDIDATES (hfasm) -/

omit [CodeEnv] in
/-- A byte stored and loaded back, modulo 256 (for `movzbl` of a stored byte). -/
theorem hf_ofBytes1_mod (v : Int) : Int.ofBytes (Int.toBytes 1 v) % 256 = v % 256 := by
  have := BitVec.ofInt8_ofBytes_toBytes1 v
  have h3 := congrArg BitVec.toNat this
  simp [BitVec.toNat_ofInt] at h3
  omega


omit [CodeEnv] in
theorem sext_ofInt32_nat (n : Nat) (h : n < 2 ^ 31) :
    (BitVec.ofInt 32 (n : Int)).signExtend 64 = BitVec.ofNat 64 n := by
  rw [BitVec.signExtend_eq_setWidth_of_msb_false]
  · apply BitVec.eq_of_toNat_eq; simp; omega
  · simp [BitVec.msb_eq_decide]; omega

omit [CodeEnv] in
/-- A store into an unknown cell, read back as the view with that cell known, in place
(`ht` uses the same `Split` path as `hs`). -/
theorem store_keep {m : Mem 64} {H H' R : Mem 64 → Prop} {a : BitVec 64} {n : Nat} {v : Int}
    (h : m =⋆ H) (hs : Mem.Split (n ?@ a) R H) (ht : Mem.Split (Int.toBytes n v =@ a) R H') :
    m.storeInt a n v =⋆ H' := by
  unfold Mem.Split at ht; rw [ht]; exact Mem.Block.storeInt_val h hs v

omit [CodeEnv] in
/-- A store over a known cell, in place. -/
theorem store_keep_val {m : Mem 64} {H H' R : Mem 64 → Prop} {a : BitVec 64} {bs : List UInt8}
    {n : Nat} {v : Int} (h : m =⋆ H) (hs : Mem.Split (bs =@ a) R H) (hlen : bs.length = n)
    (ht : Mem.Split (Int.toBytes n v =@ a) R H') : m.storeInt a n v =⋆ H' := by
  unfold Mem.Split at ht; rw [ht]; exact Mem.Val.storeInt h hs hlen v

abbrev ArgRegs (t₀ s : MachineData) : Prop :=
  s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rsi = arg1 t₀ ∧ s.regs.get64 .rdx = arg2 t₀
    ∧ s.regs.get64 .rcx = arg3 t₀ ∧ s.regs.get64 .r8 = arg4 t₀
"""


SETE = """
omit [CodeEnv] in
theorem add_zero64 (a : BitVec 64) : a + 0 = a := BitVec.add_zero a

omit [CodeEnv] in
/-- Low byte of `sete` after `test v, v` (32-bit). -/
theorem sete_z_low (r : BitVec 64) (v : BitVec 32) (af : Bool) :
    (r.replaceLow (BitVec.ofNat 8 (CondCode.z.interp (StatusFlags.from_result
        (v &&& v) { cf := false, af := af, of := false })).toNat)).toNat % 256
      = if v = 0 then 1 else 0 := by
  rw [BitVec.toNat_replaceLow8_mod]
  simp [CondCode.interp, StatusFlags.from_result, BitVec.and_self]
  by_cases h : v = 0#32
  · simp [h]
  · have : (v == 0#32) = false := by simpa using h
    simp [this, h]
"""

RBP_OFFS = [0x30, 0x38, 0x40, 0x48, 0x50, 0x54, 0x70, 0x78, 0x80, 0x88, 0x90, 0x98, 0x9c, 0xa8, 0xb0,
            0xb8, 0xc0, 0xc8, 0xd0, 0xd8, 0xe0, 0xe8, 0xf0, 0x100, 0x1c0, 0x280]


def rbpo_text():
    out = ["/-! `rbp`-relative frame addresses (`rbp = rsp₀ - 8`). -/"]
    for o in RBP_OFFS:
        out.append(f"""omit [CodeEnv] in
theorem rbpo_{o:x} (a : BitVec 64) : a - 8#64 + Int64.toBitVec (-{o}) = a - {o + 8:#x}#64 := by
  rw [show Int64.toBitVec (-{o}) = {(2**64 - o):#x}#64 from rfl]; bv_omega
""")
    return "\n".join(out)


RBPO = ", add_zero64, Int64.toBitVec_ofNat_norm" + "".join(f", rbpo_{o:x}" for o in RBP_OFFS)


NOIDP_SKIP = ["Lb01d"]

# override/ blocks that get the stage-2 store chain spliced in (after `rw [<b>_pre] at hm`, and the
# read-fact simp + isSome closer after the `dsimp only at hn hm ⊢` line)
PORT_OVR = {"r0", "La8f6", "m1", "m2", "m3"}
STORE_TRY = "    all_goals try ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption)\n"


def port_store(nm, txt):
    if nm not in PORT_OVR or nm not in SC_TEXT or nm in NO_STORE:
        return txt
    sr, srn, _k = SC_TEXT[nm]
    a = f"    rw [{nm}_pre] at hm\n"
    d = "    all_goals try dsimp only at hn hm ⊢\n"
    assert txt.count(a) == 1 and txt.count(d) == 1, nm
    txt = txt.replace(a, a + sr, 1)
    txt = txt.replace(d, d + (SLOT_SIMP.format(hs=", ".join(srn)) if srn else "") + STORE_TRY, 1)
    return txt


def main():
    import spec_hf  # noqa: the label specification
    spec_hf.define(sys.modules[__name__])
    import skel
    g = sys.modules[__name__]
    out = [frames_text(), PREAMBLE, SETE, rbpo_text(), skel.lemmas(g), skel.exit_lemmas(g, EXIT_FRAMES), table_text(), skel.POST, BLOCKOB]
    out += [forget_lemma(a, b) for (a, b) in sorted(FORGETS)]
    out += LEMMAS
    have = {l: b for l, b in BLOCKS}
    ovr = os.environ.get("HFASM_OVR", os.path.join(HERE, "override"))
    import glob
    for f in sorted(glob.glob(os.path.join(HERE, "extra", "*.lean"))) + [os.path.join(ovr, "_lemmas.lean")]:
        if os.path.exists(f):
            out.append(open(f).read())
    for l in skel.labels():
        f = os.path.join(ovr, (l or "start") + ".lean")
        fd = os.path.join(HERE, "override_dev", (l or "start") + ".lean")
        if os.environ.get("HFASM_DEV") and os.path.exists(fd):
            f = fd
        if (l in have or l in ENTRY) and os.path.exists(f):
            out.append(port_store(l or "start", open(f).read()))
        elif l in have:
            out.append(have[l])
        elif l in ENTRY:
            sorry_block(l)
            out.append(BLOCKS[-1][1])
        else:
            out.append(skel.false_block(l))
    out.append(skel.spec(g))
    out.append("end Kraken.Examples.Sbr.HfAssemble\n")
    txt = "\n".join(out)
    txt = info_off(txt)
    # per-block budgets = ~2x measured (hb_table.txt from hb.py); on by default (the committed
    # files), HFASM_HB=0 keeps the generous generated budgets (development)
    hbf = os.path.join(HERE, "hb_table.txt")
    if os.environ.get("HFASM_HB", "1") == "1" and os.path.exists(hbf):
        tab = {l.split()[0]: l.split()[2] for l in open(hbf) if l.strip()}
        txt = _re.sub(r"set_option maxHeartbeats \d+ in\ntheorem blk_(\w+)",
                      lambda m: f"set_option maxHeartbeats {tab.get(m.group(1), m.group(0).split()[2])} in\ntheorem blk_{m.group(1)}"
                      if m.group(1) in tab else m.group(0), txt)
        # 200000 is Lean's default maxHeartbeats: omit the option line
        txt = txt.replace("set_option maxHeartbeats 200000 in\n", "")
    # fx-f7 kernel fix: explicit (non-defeq) simp proofs, so the kernel does not re-check
    # `BitVec.toNat_*` rfl-rewrites by whnf on `x + <big literal>` (unary Nat.add)
    if os.environ.get("HFASM_NOIDP", "1") == "1":
        txt = _re.sub(r"\bsimp only \[", "simp -implicitDefEqProofs only [", txt)
        txt = _re.sub(r"\bsimp (\(disch := [^)]*\)) only \[", r"simp -implicitDefEqProofs \1 only [", txt)
        for b in NOIDP_SKIP:   # blocks whose later `rw … at` needs the old simp proof shape
            i = txt.index(f"theorem blk_{b} ")
            j = txt.index("\ntheorem ", i + 1) if "\ntheorem " in txt[i + 1:] else len(txt)
            txt = txt[:i] + txt[i:j].replace("simp -implicitDefEqProofs ", "simp ") + txt[j:]
    with open(os.path.join(os.environ.get("HFASM_WORK", HERE), "store_chain.txt"), "w") as f:   # debug listing (untracked)
        for b, (t, ns, kk) in SC_TEXT.items():
            f.write(f"== {b} (stores threaded: {kk}; simp names: {', '.join(ns)})\n{t}\n")
    print(txt)


# first tactic of every block proof: stop info-tree collection (Kraken/InfoOff.lean; px-ci)
INFO_OFF = re.compile(r"^(theorem blk_\w+\b.*?:= by\n)", re.M | re.S)


def info_off(txt):
    if os.environ.get("NO_INFO_OFF") == "1" or "  info_off\n" in txt:
        return txt
    return INFO_OFF.sub(r"\1  info_off\n", txt)


if __name__ == "__main__":
    main()
