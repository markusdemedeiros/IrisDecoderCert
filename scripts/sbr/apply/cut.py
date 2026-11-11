#!/usr/bin/env python3
"""Cut ff_aac_sbr_apply.s into blocks and emit body.s (labels prefixed with the symbol).

Rules (DESIGN.md §a):
  R1 every original label starts a block;
  R2 a call ends its block (a free label after it);
  R3 a call block holds no store: if the block has a store before the call, cut right
     before the call's argument set-up (the run of reg/lea/load moves before `call`);
  R4 at most MAXN (15) instructions per block; a long block is cut before a load that
     follows a store, else after a store, else at MAXN;
  R5 a run of stores followed by a load in the same block is cut after the stores;
  R6 at most 8 stores per block.
  RIP: `0x0(%rip)` operands get their symbol from the .notes relocations;
       the GOTOFF pair becomes `_GLOBAL_OFFSET_TABLE_` / `sbr_qmf_window_ds-_GLOBAL_OFFSET_TABLE_`.
  The final `jmp done` becomes `ff_aac_sbr_apply.done: ret`.
Outputs: body.s, blocks.json (label, phase, instrs, kind, succs).
"""
import json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
SCR = os.environ.get("APPLY_PROG_DIR", ".") + "/"   # directory with ff_aac_sbr_apply.s and .notes
SRC = SCR + "ff_aac_sbr_apply.s"
NOTES = SCR + "ff_aac_sbr_apply.notes"
P = "ff_aac_sbr_apply"
MAXN = 15
MANUAL = {}   # source line -> label name (extra cuts), filled below

# ---- relocations from the notes, by address order of `0x0(%rip)` / call operands ----
relocs = []
for l in open(NOTES):
    m = re.search(r"0x([0-9a-f]+): `([^`]*)` has relocation (\S+) (\S+)", l)
    if m:
        relocs.append((int(m.group(1), 16), m.group(2), m.group(3), m.group(4)))

def sym_of(rel, target):
    s = target.split("-0x")[0].split("+0x")[0]
    s = s.lstrip(".")
    return s

lines = open(SRC).read().split("\n")
rip_sites = [i for i, l in enumerate(lines) if "0x0(%rip)" in l or l.strip().startswith("movabs $0x0")]
rip_rel = [r for r in relocs if "0x0(%rip)" in r[1] or r[1].startswith("movabs $0x0")]
assert len(rip_sites) == len(rip_rel), (len(rip_sites), len(rip_rel))
RIP = {}
for i, r in zip(rip_sites, rip_rel):
    _, ins, kind, tgt = r
    assert ins.split()[0] == lines[i].split()[0], (ins, lines[i])
    if kind == "R_X86_64_GOTPC32":
        RIP[i] = lines[i].replace("0x0(%rip)", "_GLOBAL_OFFSET_TABLE_(%rip)")
    elif kind == "R_X86_64_GOTOFF64":
        RIP[i] = lines[i].replace("$0x0", "$sbr_qmf_window_ds-_GLOBAL_OFFSET_TABLE_")
    else:
        s = sym_of(kind, tgt)
        s = s.replace("sbr_dequant.", "").replace("sbr_chirp.", "").replace("sbr_gain_calc.", "")
        s = s.replace(".", "_")
        RIP[i] = lines[i].replace("0x0(%rip)", f"{s}(%rip)")

def is_store(t):
    m = re.match(r"^(\w+)\s+(.*)$", t)
    if not m:
        return False
    op, args = m.groups()
    if op.startswith(("cmp", "test", "vucomis", "j", "call", "lea", "push", "pop", "nop", "ud1")):
        return False
    depth, parts, cur = 0, [], ""
    for ch in args:
        depth += (ch == "(") - (ch == ")")
        if ch == "," and depth == 0:
            parts.append(cur); cur = ""
        else:
            cur += ch
    parts.append(cur)
    last = parts[-1].strip()
    if op.startswith("set"):
        return "(" in last
    return "(" in last and "(%rip)" not in last and len(parts) >= 2

def is_load(t):
    if t.startswith(("lea", "nop", "j", "ud1", "call", "push", "pop")):
        return False
    m = re.match(r"^(\w+)\s+(.*)$", t)
    if not m:
        return False
    args = m.group(2)
    srcs = args.rsplit(",", 1)[0] if is_store(t) else args
    if is_store(t) and t.split()[0].startswith(("add", "sub", "inc", "dec", "and", "or", "xor", "neg", "not")):
        return True   # read-modify-write
    return "(" in srcs and "(%rip)" not in srcs

# ---- pass 1: items ----
items = []   # (srcline, kind, text)  kind: 'label' or 'ins'
for i, l in enumerate(lines):
    s = l.strip()
    if not s:
        continue
    if s.endswith(":"):
        items.append((i + 1, "label", s[:-1]))
    else:
        items.append((i + 1, "ins", RIP.get(i, l).strip()))

def lname(orig):
    if orig == "start":
        return ""
    if orig == "done":
        return "done"
    return orig[1:] if orig.startswith(".") else orig

# ---- pass 2: blocks with automatic cuts ----
out = []          # list of (label, [(srcline, text)])
cur = None
counter = {}

def newblock(name):
    global cur
    cur = [name, []]
    out.append(cur)

def fresh(base):
    counter[base] = counter.get(base, 0) + 1
    return f"{base or 'start'}_{counter[base]}"

base = None
for (ln, k, t) in items:
    if k == "label":
        if t == "done":
            break
        base = lname(t)
        newblock(base)
        continue
    if ln in MANUAL:
        newblock(MANUAL[ln])
    if t == "jmp done":
        newblock("done")
        cur[1].append((ln, "ret"))
        continue
    body = cur[1]
    real = [x for x in body if x[1] != "nop" and not x[1].startswith("int3")]
    closed = real and (real[-1][1].startswith(("jmp", "ud1", "ret")))
    if t == "nop" or t.startswith("int3"):
        if not closed:
            body.append((ln, t))
        else:
            body.append((ln, t))
        continue
    if closed:
        # unreachable tail after jmp (only nops expected)
        assert False, (ln, t)
    nst = sum(1 for x in real if is_store(x[1]))
    last_store = bool(real) and is_store(real[-1][1])
    cut = False
    if len(real) >= MAXN:
        cut = True
    elif is_load(t) and nst and any(is_store(x[1]) for x in real[-3:]):
        cut = True        # R5 load after a recent store
    elif is_store(t) and nst >= 8:
        cut = True        # R6
    if t.startswith("call") and nst:
        # R3: move the argument set-up with the call
        j = len(body)
        while j > 0 and not is_store(body[j - 1][1]) and not body[j - 1][1].startswith(("j", "cmp", "test")):
            j -= 1
        tail = body[j:]
        del body[j:]
        newblock(fresh(base))
        cur[1].extend(tail)
        cur[1].append((ln, t))
        newblock(fresh(base))
        continue
    if cut:
        newblock(fresh(base))
    cur[1].append((ln, t))
    if t.startswith("call"):
        newblock(fresh(base))

# drop empty blocks created by a call at the very end before a label
blocks = []
for name, body in out:
    real = [x for x in body if x[1] != "nop" and not x[1].startswith("int3")]
    if not body and blocks:
        # an empty cut block right before a label: drop it
        continue
    blocks.append((name, body))

# ---- phases by source line ----
PHASES = [
    (1, 89, "Entry"), (90, 207, "DqCplEnv"), (208, 489, "DqCplNoise"), (490, 508, "Entry"),
    (509, 851, "DqSce"), (852, 915, "Setup"), (916, 1012, "Ana"), (1013, 1143, "Chirp"),
    (1144, 1256, "HfGen"), (1257, 1909, "Map"), (1910, 2475, "Env"), (2476, 2892, "Gain"),
    (2893, 2960, "Asm"), (2961, 3038, "Syn"), (3039, 3128, "Trap"),
]
def phase(ln):
    for a, b, p in PHASES:
        if a <= ln <= b:
            return p
    return "?"
# fix-ups: blocks physically inside other ranges
OVR_PHASE = {"L8b4f": "HfGen", "L879e": "Map", "L99c6": "Env", "L99cf": "Env", "L9a02": "Syn",
             "L9a69": "Syn", "L9a7d": "Syn", "L9a85": "Syn", "L9b24": "Syn", "L9b2b": "Syn",
             "done": "Syn", "L9b9a": "Abort", "L9bd4": "Abort", "L6ff7": "Trap", "L6ffc": "DqSce",
             "L7007": "DqSce", "L700e": "DqSce", "L7020": "DqSce", "L74de": "Setup", "L6f32": "Entry",
             "L6fbe": "DqSce", "L6fca": "DqSce", "L6abf": "DqCplNoise", "L6a90": "DqCplEnv"}

res = []
for name, body in blocks:
    real = [x for x in body if x[1] != "nop" and not x[1].startswith("int3")]
    ln = body[0][0] if body else 0
    root = name.split("_")[0] if name not in ("", "done") else name
    ph = OVR_PHASE.get(name) or OVR_PHASE.get(root) or phase(ln)
    if real and len(real) == 1 and real[0][1].startswith("ud1"):
        ph = "Trap"
    calls = [x[1] for x in real if x[1].startswith("call")]
    st = sum(1 for x in real if is_store(x[1]))
    ld = sum(1 for x in real if is_load(x[1]))
    vec = sum(1 for x in real if x[1].startswith("v"))
    kind = "straight"
    if real and real[-1][1].startswith("ud1") and len(real) == 1:
        kind = "trap"
    elif any("abort" in c for c in calls):
        kind = "abort"
    elif any("av_log" in c for c in calls):
        kind = "call_avlog"
    elif any(c.startswith("call *") for c in calls):
        kind = "call_ind"
    elif any(c in ("call memcpy", "call memset") for c in calls):
        kind = "call_mem"
    elif any(c in ("call ff_ps_apply",) for c in calls):
        kind = "call_ps"
    elif any(c in ("call sbr_qmf_synthesis",) for c in calls):
        kind = "call_qmf"
    elif name == "done" or (real and real[-1][1] == "ret"):
        kind = "ret"
    elif any(x[1].startswith("ud1") for x in real):
        kind = "straight+ud1"
    elif st >= 6:
        kind = "store_run"
    elif vec >= 8:
        kind = "vector"
    jumps = [x[1].split()[1] for x in real if x[1].startswith("j")]
    res.append({"label": name, "phase": ph, "line": ln, "n": len(real), "st": st, "ld": ld,
                "vec": vec, "kind": kind, "calls": calls, "jumps": jumps})

json.dump(res, open(os.path.join(HERE, "blocks.json"), "w"), indent=0)

with open(os.path.join(HERE, "body.s"), "w") as f:
    for name, body in blocks:
        f.write(f"{P}:\n" if name == "" else f"{P}.{name}:\n")
        for ln, t in body:
            t = re.sub(r"(\s)\.L([0-9a-f]+)$", lambda mm: f"{mm.group(1)}{P}.L{mm.group(2)}", t)
            f.write(f"    {t}\n")

if __name__ == "__main__":
    from collections import Counter
    print("blocks", len(res), "instr", sum(b["n"] for b in res))
    print("by phase", Counter(b["phase"] for b in res))
    print("by kind", Counter(b["kind"] for b in res))
    print("max n", max(b["n"] for b in res))
    for b in res:
        if "-v" in sys.argv:
            print(f"{b['line']:5} {b['label'] or 'start':12} {b['phase']:10} {b['kind']:12} n={b['n']:2} st={b['st']} ld={b['ld']} {' '.join(b['calls'])}")
