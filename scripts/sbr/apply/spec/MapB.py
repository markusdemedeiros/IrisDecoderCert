# entries / frames of shard MapB (sbr_mapping, second half) — helper apply-mapb, DRAFT v2
#
# Logical variables of the mapping loop (existential in every entry):
#   ch  channel (< 2), slot `ch` (rbp-0x1a0) = ch
#   j   envelope index e (< bs_num_env ≤ 8); slot s68 = j+1 after L7e90
# Frames (parametrised, gen "FrM (ch j : Nat)" hack):
#   FrM0 : loop-invariant slots (valid at L7db0)
#   FrM  : + kx30 = kx1, s50 = ilim, s68 = j+1       (L7e90 .. L8740)
#   FrMs : + s78 = -kx1 (u32)                        (L86d7 .. L86b0_1)
#   FrMn : FrM with s58 already advanced to row j+1  (L8740_1)

def u8(bs, i):
    return f"u8 {bs} ({i})"


MFR0 = "u8 (x.d ch).freqRes (j + 1) = 0"
TAB = f"(if {MFR0} then x.ftLow else x.ftHigh)"
ILIM = f"(if {MFR0} then x.n0 else x.n1)"
TABA = f"(if {MFR0} then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64)"


def fN(i):
    return f"u16 x.ftNoise ({i})"


def fH(i):
    return f"u16 x.ftHigh ({i})"


def tb(i):
    return f"u16 {TAB} ({i})"


def row(base, sz, idx):
    return f"{base} + BitVec.ofNat 64 ({sz} * {idx})"


QROW = lambda j: row("sbrA t₀ + 0x5dd40#64", "0xc0", j)   # q_mapped[j]
EROW = lambda j: row("sbrA t₀ + 0x5d740#64", "0xc0", j)   # e_origmapped[j]
PROW = lambda j: row("arg1 t₀", "0xc0", j)                # q_mapped[j] - 0x86660
SIROW = lambda j: row("dA t₀ ch + 0x15030#64", "48", j)   # s_indexmapped[j]
SMROW = lambda j: row("sbrA t₀ + 0x5e340#64", "48", j)    # s_mapped[j]

BASE0 = {   # Map-local slots on top of g.FR_CH (shared channel-level frame, W/spec/_frames.py)
    "dch": "dA t₀ ch",
    "s98": "BitVec.ofNat 64 (0x15ac0 * ch)",
    "s58": QROW("j"),
    "s60": PROW("j"),
    "s80": "dA t₀ ch + 0x15030#64",
    "sd8": "dA t₀ ch + 0x15a60#64",
    "se0": "dA t₀ ch + 0x15390#64",
    "se8": "dA t₀ ch + 0x32#64",
}
FRM = dict(BASE0, **{"tmp30": ("cells", "Int.toBytes 4 (BitVec.ofNat 32 x.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)"), "s50": f"BitVec.ofNat 64 {ILIM}", "s68": "BitVec.ofNat 64 (j + 1)"})
FRMS = dict(FRM, **{"s78": "BitVec.ofNat 64 ((2 ^ 32 - x.kx1) % 2 ^ 32)"})
FRMN = dict(FRM, **{"s58": QROW("(j + 1)")})


def R(r, v):
    return f"s.regs.get64 .{r} = {v}"


def ofn(v):
    return f"BitVec.ofNat 64 ({v})"


MAPC = "x.start ≠ 0 ∧ ch < 2 ∧ j < (x.d ch).nenv"
LOOPREGS = [R("r12", EROW("j")), R("r15", TABA)]
NOISE = [R("rax", ofn("j")), R("rcx", ofn("x.nq")), "kk ≤ 2",
         R("rdx", row("dA t₀ ch + 0x15a60#64", "20", "kk"))]


LAST = {}
ENTF = {}


def yy(f):
    return f.replace("x.", "y.")


def ent(ex, facts, fr="FrMb", mapc=None, keep="y"):
    mapc = MAPC if mapc is None else mapc
    # owner's channel-loop shape (05:16): ApplyC x ∧ Base ∧ ∃ y …, x.Keep y ∧ ApplyC y t₀ ∧ facts(y) ∧ Mm … y
    facts = [yy(f) for f in facts]
    LAST["v"] = (ex.split(), list(facts), fr)
    mem = f"(s.dmem =⋆ Mm k e y ra t₀ ({fr} x t₀ ch c0 y j))"
    body = " ∧ ".join([f"(x.Keep {keep} ∧ ChLive t₀ ch y)", "ApplyC y t₀", "c0.getLsbD 0 = decide (ch = 0)", yy(mapc)] + facts + [mem])
    return f"ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j{(' ' + ex) if ex else ''}, {body}"


ENT = {}


def define(g):
    P = g.FR_CH_PARAMS + " (y : Args) (j : Nat)"
    for nm, d in (("FrM0", BASE0), ("FrMb", FRM), ("FrMs", FRMS), ("FrMn", FRMN)):
        g.frame(nm, dict(g.FR_CH, **{k: ((v[0], yy(v[1])) if isinstance(v, tuple) else yy(v)) for k, v in d.items()}), params=P)
    E = lambda i, t: (g.entry(i, t), ENT.__setitem__(i, t), ENTF.__setitem__(i, LAST['v']))
    # ---- noise mapping (q_mapped[j][m - kx1] = noise_facs[kk][i]), stages i = 1..4
    # (start, end register, row-pointer register / counter / remaining-count register of the main loop)
    stages = [("L8009", "rsi", "rdi", "rbx", "r14", "rsi", 1, "L8050", "L8077", "L8077_1", "L80c0", "L80c0_1"),
              ("L814a", "rdi", "rsi", "rbx", "r14", "rdi", 2, "L8190", "L81b7", "L81b7_1", "L8200", "L8200_1"),
              ("L828a", "rsi", "rdi", "rbx", "r14", "rsi", 3, "L82d0", "L82f7", "L82f7_1", "L8340", "L8340_1"),
              ("L83ca", "rdi", "rsi", "rsi", "rbx", "rdi", 4, "L8410", "L8437", "L8437_1", "L8480", "L8480_1")]
    for head, st, en, rb, ctr, cnt, i, pre, mid, mid1, loop, loop1 in stages:
        E(head, ent("kk", NOISE + LOOPREGS + [f"{i} ≤ x.nq", R(st, ofn(fN(i)))]))
        c = f"({fN(i + 1)} - {fN(i)})"
        band = [f"{i + 1} ≤ x.nq", f"x.kx1 ≤ {fN(i)}", f"{fN(i)} < {fN(i + 1)}", f"{fN(i + 1)} ≤ x.kx1 + 48"]
        keep_en = [R(en, ofn(fN(i + 1)))]
        E(pre, ent("kk t", NOISE + LOOPREGS + band + [f"t < {c} % 4", R(st, ofn(fN(i)))] + keep_en + [
            R("r8", ofn(c)), R("r9", f"0#64 - {ofn(c + ' % 4')}"), R("r11", f"0#64 - {ofn('t')}"),
            R("r10", ofn(f"{fN(i)} + t - x.kx1"))]))
        m0 = f"({fN(i)} + {c} % 4)"
        E(mid, ent("kk", NOISE + LOOPREGS + band + [R(st, ofn(m0))] + keep_en + [R("r8", ofn(c))]))
        a = f"({m0} - x.kx1)"
        P = PROW("j")
        ptrs = [R(rb, f"{P} + {ofn('4 * ' + a)}"), R("r11", f"{P} + {ofn('4 * (' + a + ' + 1)')}"),
                R("r10", f"{P} + {ofn('4 * (' + a + ' + 2)')}"), R("r9", f"{P} + {ofn('4 * (' + a + ' + 3)')}")]
        common = NOISE + LOOPREGS + band + [f"{m0} + 4 ≤ {fN(i + 1)}", R("r8", ofn(a)),
                                             R(cnt, f"{ofn(m0)} - {ofn(fN(i + 1))}")] + ptrs
        if i < 4:
            common += keep_en
        E(mid1, ent("kk", common))
        lp = common + [f"{m0} + 4 * t + 4 ≤ {fN(i + 1)}", R(ctr, f"0x21998#64 + {ofn('4 * t')}")]
        E(loop, ent("kk t", lp))
        E(loop1, ent("kk t", lp))
    E("L8509", ent("kk", NOISE + LOOPREGS + ["5 ≤ x.nq"]))
    # ---- harmonic map: s_indexmapped[j+1][mid(i) - kx1]
    E("L8520", ent("", [R("r8", "arg1 t₀"), R("rax", ofn("j"))] + LOOPREGS))
    H = [R("rax", ofn("j")), R("r11", "0#64"), R("rbx", "dA t₀ ch"), R("r14", "dA t₀ ch + 0x15030#64"),
         R("r13", "dA t₀ ch + 0x32#64"), R("rcx", SIROW("(j + 1)"))]
    HI = H + ["i % 2 = 0", "i < x.n1", R("rdi", ofn("i")), R("rdx", ofn("i + 1")),
              R("rsi", "sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i)")]
    E("L8570", ent("i", HI + LOOPREGS))
    for l in ("L8570_1", "L85c0", "L85cd"):
        E(l, ent("i v", HI + LOOPREGS + ["v < 48", R("r10", ofn("v"))]))
    E("L85cd_1", ent("i", HI + LOOPREGS))
    HI2 = HI + ["i + 1 < x.n1", "v < 48"]
    E("L85cd_2", ent("i v", HI2 + LOOPREGS + [R("r8", ofn("v"))]))
    E("L8620", ent("i v", HI2 + LOOPREGS + [R("r10", ofn("v"))]))
    E("L862d", ent("i v", HI2 + LOOPREGS + [R("r8", ofn("v"))]))
    E("L862d_1", ent("i", H + ["i % 2 = 0", "i + 2 ≤ x.n1", R("rdi", ofn("i + 2")), R("rdx", ofn("i + 1")),
                               R("rsi", "sbrA t₀ + 0x4c288#64 + BitVec.ofNat 64 (2 * i)")] + LOOPREGS))
    # ---- s_mapped[j][table[i] - kx1 ..] = sinusoid flag of band i
    E("L8660", ent("", [R("rax", ofn("j"))] + LOOPREGS))
    S = [R("rbx", SIROW("(j + 1)")), R("r14", SMROW("j"))] + LOOPREGS
    E("L86d7", ent("i", S + [f"i < {ILIM}", R("r13", ofn("i"))], fr="FrMs"))
    E("L86b0_1", ent("i", S + [f"i ≤ {ILIM}", R("r13", ofn("i"))], fr="FrMs"))
    BAND = S + [f"i < {ILIM}", R("r13", ofn("i")), f"x.kx1 ≤ {tb('i')}", f"{tb('i')} ≤ {tb('i + 1')}",
                f"{tb('i + 1')} ≤ x.kx1 + 48", R("rax", ofn(tb("i"))), R("rcx", ofn(tb("i + 1")))]
    E("L8700", ent("i t", BAND + [f"{tb('i')} + t < {tb('i + 1')}", R("rsi", ofn(f"{tb('i')} + t - x.kx1")),
                                  R("rdx", ofn(f"{tb('i + 1')} - {tb('i')} - t"))], fr="FrMs"))
    E("L8720", ent("i", BAND, fr="FrMs"))
    E("L86a0", ent("i", BAND, fr="FrMs"))
    E("L86b0", ent("i", BAND + [R("rdx", ofn(f"{tb('i')} - x.kx1"))], fr="FrMs"))
    # ---- next envelope
    E("L8740", ent("", [R("r12", EROW("j"))]))
    E("L8740_1", ent("", ["j + 1 < (x.d ch).nenv", R("rdx", ofn("j + 1")), R("rcx", ofn("j + 2")),
                          R("rbx", "dA t₀ ch"), R("r8", "arg1 t₀"), R("r12", EROW("(j + 1)"))], fr="FrMn"))
    # ---- error exit (kx[1] != table[0]) and the empty-envelope entry: boundary proposals
    # L8790 (nenv = 0, from L7ce4_2): shared FrC + dch/s98 (FrA1-less), rbx/r8/r10 as at L7ce4_2
    g.frame("FrZ", dict(g.FR_CH, dch=BASE0["dch"], s98=BASE0["s98"]), params=g.FR_CH_PARAMS + " (y : Args) (j : Nat)")
    E("L8790", ent("", [R("rbx", "dA t₀ ch"), R("r8", "arg1 t₀"), R("r10", "dA t₀ ch + 0x15030#64")], "FrZ",
                   "x.start ≠ 0 ∧ ch < 2 ∧ j = 0 ∧ (x.d ch).nenv = 0"))
    # L879e (kx1 ≠ table[0], from L7db0 after tmp30 := kx1): call_avlog; L879e_1/_2 reset stores -> owner
    # (mapb 08:20) av_log, then the turnoff stores; the 4-byte tmp30 store at L7db0 stays inside FrM0's 8 ?@.
    E("L879e", ent("", [R("rbx", "dA t₀ ch")], "FrM0"))
    E("L879e_1", ent("", [R("rbx", "dA t₀ ch")], "FrM0"))
    # after the sbr-side stores y is already turned off (start = 0): only ch < 2 survives of MAPC;
    # the spectrum_params memset (this block's two stores) is still to come: `Keep` holds of y.spSet
    E("L879e_2", ent("", [R("rbx", "dA t₀ ch")], "FrM0", "ch < 2", keep="y.spSet"))


if __name__ == "__main__":
    class G:
        blocks = []
        FR_CH = {}; FR_CH_PARAMS = "(ch : Nat) (c0 : BitVec 32)"
        def entry(self, i, t): pass
        def frame(self, *a, **k): pass
    define(G())
    for k, v in ENT.items():
        print(k, ":", v, "\n")


# ---- variant measures (one per enclosing loop: channel, [L7cbf..L8b4f], [L7ce4..L8b4f], e loop, inner)
MCH = "2 - (slot64 s 0x1a0).toNat"
ME = "9 - (slot64 s 0x68).toNat"
OUT3 = [MCH, "0", "0"]


def reg(r):
    return f"(s.regs.get64 .{r})"


INNER = {}
for l in ("L8050", "L8190", "L82d0", "L8410"):
    INNER[l] = f"({reg('r11')} - {reg('r9')}).toNat"
for ls, a, b in ((("L80c0", "L80c0_1"), "rsi", "r14"), (("L8200", "L8200_1"), "rdi", "r14"),
                 (("L8340", "L8340_1"), "rsi", "r14"), (("L8480", "L8480_1"), "rdi", "rbx")):
    for l in ls:
        INNER[l] = f"(0x21998#64 - ({reg(a)} + {reg(b)})).toNat"
for l in ("L8570", "L8570_1", "L85c0", "L85cd", "L85cd_1", "L85cd_2", "L8620", "L862d"):
    INNER[l] = f"50 - {reg('rdi')}.toNat"
INNER["L862d_1"] = f"51 - {reg('rdi')}.toNat"
for l, c in (("L86a0", 1), ("L86b0", 1), ("L86d7", 3), ("L86b0_1", 3), ("L8700", 2), ("L8720", 2)):
    INNER[l] = f"4 * (48 - {reg('r13')}.toNat) + {c}"

_define = define


def define(g):
    _define(g)
    for b in g.blocks:
        if b["phase"] != "Map:B":
            continue
        i = b["id"]
        if i in ("L8790", "L879e", "L879e_1", "L879e_2"):
            g.measure(i, OUT3)
        elif i == "L8700":
            g.measure(i, OUT3 + [ME, INNER[i], f"{reg('rdx')}.toNat"])
        elif i in INNER:
            g.measure(i, OUT3 + [ME, INNER[i]])
        else:
            g.measure(i, OUT3 + [ME])
