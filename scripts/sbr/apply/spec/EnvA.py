# entries / frames / measures of shards EnvA + EnvB (sbr_env_estimate, inlined) — helper apply-env, DRAFT v1
#
# C: aacsbr_template.c sbr_env_estimate. Two branches:
#  * bs_interpol_freq != 0 (L881c_1 ..): the e-loop is UNROLLED (e = 0..7, e = 8 is ud1 at L99cf);
#    per e: head (load t_env[e], recip -> tmp30), first sum_square call (m = 0), m-loop
#    [store e_curr[e][m]; m++; m < m1 ? call : exit], exit (reload nenv, flag = (m1 == 0)).
#  * bs_interpol_freq == 0 (L8947 ..): e-loop L8970..L8b00, p-loop L89e0..L8ad0_1,
#    k-loop L8a50..L8a50_2 (sum_square), store loop L8ad0..L8ad0_1.
# Logical variables (existential): ch (< 2), y (the evolved Args, x.Keep y), j (envelope),
# m (m index), p (band), q (k index), c (e_curr column).
# With y.start ≠ 0 (TabWF y): 1 ≤ nenv ≤ 8, 1 ≤ m1, so: the m1 == 0 flag paths (L8b6b, the
# `jne` on the flag in every head) and nenv == 0 exits (L98e0) are refuted; ilb ≥ 40 exits refuted
# (t_env ≤ 16); the only real exit is L9146 (e == nenv), entered with rax = nenv.

D = "(y.d ch)"
N = f"{D}.nenv"
K = "y.kx1"
M = "y.m1"
XH = "(sbrA t₀ + 0x4eb40#64)"


def T(i):
    return f"u8 {D}.te ({i})"


def FR(i):
    return f"u8 {D}.freqRes ({i})"


def ofn(v):
    return f"BitVec.ofNat 64 ({v})"


def R(r, v):
    return f"s.regs.get64 .{r} = {v}"


def FLAG(r):   # low byte of r is zero (sete on m1 != 0) -- spelling to be checked against `test %sil,%sil`
    return f"(s.regs.get64 .{r}).toNat % 256 = 0"


def MFR0(j):
    return f"{FR(f'{j} + 1')} = 0"


def TAB(j):
    return f"(if {MFR0(j)} then y.ftLow else y.ftHigh)"


def ILIM(j):
    return f"(if {MFR0(j)} then y.n0 else y.n1)"


def TABA(j):
    return f"(if {MFR0(j)} then sbrA t₀ + 0x4c252#64 else sbrA t₀ + 0x4c284#64)"


def tb(j, i):
    return f"u16 {TAB(j)} ({i})"


# ---- frames (slot names: gen.SLOTS). Channel constants used here (owner: add the rest of the
# channel-level constant slots so they thread through to GainAsm).
# Frames extend the owner's channel frame g.FR_CH (spec/_frames.py, params "(ch : Nat) (c0 : BitVec 32)")
# with params + " (y : Args)" [+ loop variables]; the abbrev's own `x` is the original Args.
KX30 = ("cells", "Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)")
RAW30 = ("cells", "4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)")
EA = {"ea": "dA t₀ ch + 0x3904#64"}
DY = "(y.d ch)"


def frames(FR_CH):
    O = dict(FR_CH, dch="dA t₀ ch", s98="BitVec.ofNat 64 (0x15ac0 * ch)", tmp30=KX30)
    # FrO (L881c), FrO8 (L8818), FrX (L9146) are in the shared spec/_frames.py (owner, 05:24)
    F = {
        # after L881c's `mov %rcx,-0x110(%rbp)` (e_a pointer)
        "FrE1": dict(O, **EA),
        # interpol, e = 0: s50 = &X_high[kx1]
        "FrI0": dict(O, tmp30=RAW30, s50=f"{XH} + BitVec.ofNat 64 (320 * y.kx1)", **EA),
        # interpol, e >= 1: s50 = 320 * kx1 (L8b77 `mov %r14,-0x50(%rbp)`)
        "FrI1": dict(O, tmp30=RAW30, s50="BitVec.ofNat 64 (320 * y.kx1)", **EA),
        # non-interpol: s60 = kx1
        "FrN0": dict(O, tmp30=RAW30, s60="BitVec.ofNat 64 y.kx1", **EA),
    }
    FRN = dict(F["FrN0"], s68="BitVec.ofNat 64 (j + 1)", s78="arg1 t₀ + BitVec.ofNat 64 (0xc0 * j)",
               s80=f"sbrA t₀ + 0x4eb50#64 + BitVec.ofNat 64 (16 * u8 {DY}.te j)")
    FRNP = dict(FRN, s58="BitVec.ofNat 64 p")
    return F, FRN, FRNP


LAST = {}
ENT = {}


def ent(ex, facts, fr):
    mem = f"(s.dmem =⋆ Mm k e y ra t₀ ({fr}))"
    body = " ∧ ".join(["(x.Keep y ∧ ChLive t₀ ch y)", "ApplyC y t₀", "c0.getLsbD 0 = decide (ch = 0)", "y.start ≠ 0", "ch < 2"]
                      + facts + [mem])
    return f"ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0{(' ' + ex) if ex else ''}, {body}"


def fE0(): return "FrO x t₀ ch c0 y"
def fE1(): return "FrE1 x t₀ ch c0 y"
def fI0(): return "FrI0 x t₀ ch c0 y"
def fI1(): return "FrI1 x t₀ ch c0 y"
def fN0(): return "FrN0 x t₀ ch c0 y"
def fN(): return "FrN x t₀ ch c0 y j"
def fNP(): return "FrNP x t₀ ch c0 y j p"
def fX(): return "FrX x t₀ ch c0 y"


# interpol unrolled chain: e -> (head, head_1 (call), head_2, loop, loop_1, loop_2, exit, flagreg)
# head = block with `cmp $e+1,%ecx` (none for e = 0 / 1), call block, after-call block,
# m-loop store block, m-loop call block, m-loop latch, m-loop exit block.
CHAIN = [
    # e, head, call, after, L, L_1, L_2, exit, flag tested at head, e_curr row offset
    (0, "L881c_2", "L881c_3", "L881c_4", "L8900", "L8900_1", "L8900_2", "L8b2a", None),
    (1, "L8b77", "L8b77_1", "L8b77_2", "L8bf0", "L8bf0_1", "L8bf0_2", "L8c33", "rsi"),
    (2, "L8c4c", "L8c4c_1", "L8c4c_2", "L8cc9", "L8cc9_1", "L8cc9_2", "L8d0c", "rdx"),
    (3, "L8d26", "L8d26_1", "L8d26_2", "L8da3", "L8da3_1", "L8da3_2", "L8de6", "rsi"),
    (4, "L8dff", "L8dff_1", "L8dff_2", "L8e7c", "L8e7c_1", "L8e7c_2", "L8ebf", "rdx"),
    (5, "L8ed9", "L8ed9_1", "L8ed9_2", "L8f56", "L8f56_1", "L8f56_2", "L8f93", "rsi"),
    (6, "L8fa4", "L8fa4_2", "L8fa4_3", "L9026", "L9026_1", "L9026_2", "L9070", "rdx"),
    (7, "L907f", "L907f_2", "L907f_3", "L90f9", "L90f9_1", "L90f9_2", "L99c6", "rsi"),
]
# register holding `che` across the m-loop of e (call *0x88b08(%reg)) and the head's `rdi`/`r14` roles
CHE_REG = {0: "r13", 1: "r13", 2: "r13", 3: "r13", 4: "r13", 5: "r13", 6: "r13", 7: "r14"}


def define(g):
    P = g.FR_CH_PARAMS + " (y : Args)"
    F, FRN, FRNP = frames(g.FR_CH)
    for nm, vals in F.items():
        g.frame(nm, vals, params=P)
    g.frame("FrN", FRN, params=P + " (j : Nat)")
    g.frame("FrNP", FRNP, params=P + " (j p : Nat)")
    E = lambda i, t: (g.entry(i, t), ENT.__setitem__(i, t))

    XK = f"{XH} + {ofn('320 * ' + K)}"     # &X_high[kx1]
    def ROW(e, extra):                      # &X_high[kx1 + extra] + ilb(e) = X_high + 16 + 16 t_env[e] + 320 (kx1 + extra)
        return f"{XH} + {ofn(f'16 + 16 * {T(e)} + 320 * ({K} + {extra})')}"
    def ENVSZ(e):
        e1 = e + 1 if isinstance(e, int) else f"{e} + 1"
        return ofn(f"2 * ({T(e1)} - {T(e)})")

    # ---------------- IN boundary + dispatch
    # L8818 / L881c / L9146 entries: shared spec/_frames.py (agreed with mapb / owner)
    IN = [R("rbx", "dA t₀ ch"), R("rax", ofn(N)), R("r8", "arg1 t₀")]
    E("L881c_1", ent("", IN + [R("rcx", ofn(N))], fE1()))
    E("L8b6b", "False")     # m1 == 0: refuted (TabWF: 1 ≤ m1)

    # ---------------- interpol chain
    for (j, head, call, after, L, L1, L2, ex, flag) in CHAIN:
        nxt = CHAIN[j + 1] if j + 1 < len(CHAIN) else None
        last = j == 7
        fr = fI0() if j == 0 else fI1()
        lo = f"{j + 1} ≤ {N}"   # envelope j exists
        # head (entry of the block that loads t_env[j])
        if j == 0:
            E(head, ent("", [R("rbx", "dA t₀ ch"), R("rax", ofn(N)), R("rcx", ofn(N)), R("r8", "arg1 t₀"),
                             R("r12", ofn(T(0))), R("r14", ofn("320 * " + K)), R("rdi", XK)], fE1()))
        else:
            # j = 1: L8b2a checked nenv ≥ 2; j ≥ 2: the head itself does `cmp $j+1,%ecx`
            hf = [f"{j + 1 if j == 1 else j} ≤ {N}", R("rax", ofn(N)), R("rcx", ofn(N)), FLAG(flag)]
            if j < 7:
                hf += [R("rbx", "dA t₀ ch"), R("rdi", XK)]
            else:
                hf += [R("r14", XK)]       # L907f: rdi is dead (clobbered by the m-loop calls)
            if j == 1:
                hf += [R("r8", "arg1 t₀"), R("r14", ofn("320 * " + K))]
                E(head, ent("", hf, fI0()))
            else:
                if j < 6:
                    hf += [R("r8", "arg1 t₀")]
                E(head, ent("", hf, fr))
        # call block: rdi = &X_high[kx1], rax = 2 t_env[j], r15 = env size (doubled at the call block
        # start for j >= 2, already doubled for j = 0, 1)
        dbl = j <= 1
        TJ = "rbx" if j == 7 else "r12"    # L907f keeps t_env[7] in ebx
        r15 = ENVSZ(j) if dbl else ofn(f"{T(j + 1)} - {T(j)}")
        cf = [lo, R("rdi" if j < 6 else "r14", XK), R("rax", ofn(f"2 * {T(j)}")), R("r15", r15), R(TJ, ofn(T(j)))]
        if j == 0:
            cf += [R("r14", ofn("320 * " + K))]
        if j < 6:
            cf += [R("r8", "arg1 t₀")]
        E(call, ent("", cf, fr))
        # after-call block
        af = [lo, R(CHE_REG[j], "arg1 t₀"), R(TJ, ofn(T(j))), R("r15", ENVSZ(j))]
        af += [R("r14", ofn("320 * " + K))] if j == 0 else ([R("r14", XK)] if j < 7 else [])
        E(after, ent("", af, fr))
        # m loop
        keep = [lo, R(CHE_REG[j], "arg1 t₀"), R("r15", ENVSZ(j))]
        keep += [R("r14", ofn("320 * " + K))] if j == 0 else ([R("r14", XK)] if j < 7 else [])
        E(L, ent("m", keep + [f"m < {M}", "m < 48", R("rbx", ofn("m")), R("r12", ROW(j, "m + 1"))], fr))
        E(L1, ent("m", keep + ["1 ≤ m", f"m ≤ {M}", R("rbx", ofn("m")), R("r12", ROW(j, "m"))], fr))
        E(L2, ent("m", keep + ["1 ≤ m", f"m < {M}", R("rbx", ofn("m")), R("r12", ROW(j, "m"))], fr))
        # m-loop exit
        xf = [lo, R("rax", ofn(M))]
        xf += [R("r14", ofn("320 * " + K))] if j == 0 else ([R("r14", XK)] if j < 7 else [])
        if j < 5:      # L8f56_1 / L9026_1 / L90f9_1 do not copy r13 to r8
            xf += [R("r8", "arg1 t₀")]
        E(ex, ent("", xf, fr))
    # the interpol-chain blocks between head and call for j = 6, 7 (L8fa4_1, L907f_1: recip store)
    E("L8fa4_1", ent("", ["7 ≤ " + N, R("r14", XK), R("rax", ofn(f"2 * {T(6)}")),
                          R("r15", ofn(f"{T(7)} - {T(6)}")), R("r12", ofn(T(6)))], fI1()))
    E("L907f_1", ent("", ["8 ≤ " + N, R("r14", XK), R("rax", ofn(f"2 * {T(7)}")),
                          R("r15", ofn(f"{T(8)} - {T(7)}")), R("rbx", ofn(T(7)))], fI1()))
    # e = 8 head: ud1 unless nenv < 9
    E("L99cf", ent("", ["8 ≤ " + N, R("rcx", ofn(N)), R("rax", ofn(N))], fI1()))
    # exits to L9146 through L9063 / L913a
    E("L9063", ent("", [R("rax", ofn(N)), R("rbx", "dA t₀ ch")], fI1()))
    E("L913a", ent("", [R("rax", ofn(N))], fI1()))

    # ---------------- non-interpol
    E("L8947", ent("", [R("rbx", "dA t₀ ch"), R("rax", ofn(N))], fE1()))
    E("L8947_1", ent("", [R("rbx", "dA t₀ ch"), R("rcx", ofn("1"))], fN0()))
    E("L8970", ent("j", [f"j < {N}", R("rbx", "dA t₀ ch"), R("r8", ofn("j")), R("rcx", ofn("j + 1")),
                         R("rsi", "arg1 t₀"), R("rdi", f"arg1 t₀ + {ofn('0xc0 * j')}")], fN0()))
    E("L8970_1", ent("j", [f"j < {N}", R("r8", ofn("j + 1")), R("rdx", ofn(T("j"))), R("r12", ofn(T("j + 1"))),
                           R("r14", TABA("j")), R("rcx", ofn(FR("j + 1"))), R("rsi", "arg1 t₀"),
                           R("rdi", f"arg1 t₀ + {ofn('0xc0 * j')}")], fN0()))
    PL = [f"j < {N}", R("rsi", "arg1 t₀"), R("r14", TABA("j")), R("r12", ENVSZ("j")), R("r8", ofn("j + 1")),
          R("rdi", f"arg1 t₀ + {ofn('0xc0 * j')}")]
    E("L89f3", ent("j p", PL + [f"p ≤ {ILIM('j')}", R("rbx", ofn("p")), R("rcx", ofn(FR("j + 1")))], fN()))
    E("L89e0", ent("j p", PL + [f"p ≤ {ILIM('j')}", R("rbx", ofn("p"))], fN()))
    KL = [f"j < {N}", R("r14", TABA("j")), R("r12", ENVSZ("j")), f"p < {ILIM('j')}", R("rbx", ofn("p + 1")),
          f"{tb('j', 'p')} < {tb('j', 'p + 1')}"]
    E("L89f3_1", ent("j p", KL + [R("r13", ofn(tb("j", "p"))), R("r15", ofn(f"4 * {tb('j', 'p')}"))], fNP()))
    QF = [f"{tb('j', 'p')} ≤ q", f"q < {tb('j', 'p + 1')}", R("r13", ofn("q")),
          R("r15", f"{XH} + {ofn(f'16 + 16 * {T(chr(106))} + 320 * q')}")]
    E("L8a50", ent("j p q", KL + QF, fNP()))
    E("L8a50_1", ent("j p q", KL + QF + [R("rdi", f"{XH} + {ofn(f'16 + 16 * {T(chr(106))} + 320 * q')}"),
                                         R("rsi", ENVSZ("j"))], fNP()))
    E("L8a50_2", ent("j p q", KL + QF, fNP()))
    SL = [f"j < {N}", R("rsi", "arg1 t₀"), R("r14", TABA("j")), R("r12", ENVSZ("j")), R("r8", ofn("j + 1")),
          R("rdi", f"arg1 t₀ + {ofn('0xc0 * j')}"), f"p < {ILIM('j')}", R("rbx", ofn("p + 1")),
          f"{tb('j', 'p')} < {tb('j', 'p + 1')}"]
    E("L8a50_3", ent("j p", SL + ["s.status.cf = true", R("rax", ofn(tb("j", "p"))), R("rcx", ofn(tb("j", "p + 1")))], fNP()))
    CL = SL + ["c < 48", R("rcx", ofn("c")), R("rax", ofn(f"{K} + c + 1")), f"{K} + c < {tb('j', 'p + 1')}"]
    E("L8ad0", ent("j p c", CL, fNP()))
    E("L8ad0_1", ent("j p c", CL, fNP()))
    E("L8b00", ent("j", [f"j < {N}", R("r8", ofn("j + 1")), R("rsi", "arg1 t₀"),
                         R("rdi", f"arg1 t₀ + {ofn('0xc0 * j')}")], fN()))

    # ---------------- variant measures
    MCH = "2 - (slot64 s 0x1a0).toNat"
    rg = lambda r: f"(s.regs.get64 .{r}).toNat"
    for b in g.blocks:
        if not b["phase"].startswith("Env"):
            continue
        i = b["id"]
        idx = g.ids.index(i)
        early = idx <= g.ids.index("L8b2a")      # inside the text-order loops (164,259), (166,259)
        ms = [MCH, "0", "0"] if early else [MCH]
        heads = [c[4] for c in CHAIN]
        if i in heads:
            ms.append(f"2 * (48 - {rg('rbx')})")
        elif any(i in (c[5], c[6]) for c in CHAIN):
            ms.append(f"2 * (48 - {rg('rbx')}) + 1")
        elif i == "L8970":
            ms.append(f"2 * (9 - {rg('r8')})")
        elif i == "L8970_1":   # r8 = j + 1 here: equal to L8970's (r8 = j) value, then blockIdx
            ms.append(f"2 * (9 - {rg('r8')}) + 2")
        elif i in ("L8b00",):
            ms.append("2 * (9 - (slot64 s 0x68).toNat) + 1")
        elif i in ("L89e0", "L89f3"):
            ms += ["2 * (9 - (slot64 s 0x68).toNat) + 1", f"2 * (50 - {rg('rbx')})"]
        elif i in ("L89f3_1", "L8a50_3"):
            ms += ["2 * (9 - (slot64 s 0x68).toNat) + 1", f"2 * (50 - {rg('rbx')}) + 1"]
        elif i in ("L8a50", "L8a50_1", "L8a50_2"):
            ms += ["2 * (9 - (slot64 s 0x68).toNat) + 1", f"2 * (50 - {rg('rbx')}) + 1", f"64 - {rg('r13')}"]
        elif i in ("L8ad0", "L8ad0_1"):
            ms += ["2 * (9 - (slot64 s 0x68).toNat) + 1", f"2 * (50 - {rg('rbx')}) + 1", f"48 - {rg('rcx')}"]
        g.measure(i, ms)


if __name__ == "__main__":
    class G0:
        blocks = []
        ids = []
        def entry(self, i, t): pass
        def frame(self, *a, **k): pass
        def measure(self, *a): pass
    define(G0())
    for k, v in ENT.items():
        print(k, ":", v, "\n")
