# entries / frames / measures of shard GainAsm (sbr_gain_calc inlined + hf_assemble / x_gen tail)
# owner of this file: apply-dqcpl (helper). IN: L9146 (shared, from Env), L9927 / L9934 (shared, from
# anahf / mapb). OUT: L7682 (channel loop head), L9a02 (Syn). Traps False.
#
# C (aacsbr_template.c sbr_gain_calc): e-loop (r12 = e < nenv) x k-loop (rdx = k < n_lim) x m-loops over
# [ml, mh) = [f_tablelim[k] - kx1, f_tablelim[k+1] - kx1) (TabWF: kx1 <= f_tablelim[i] <= kx1 + m1 <= kx1 + 48).
# The e/k loops are merged by the generator into one phase (318, 368) with measure EK.

D = "(y.d ch)"
N = f"{D}.nenv"
K = "y.kx1"
NL = "y.nlim"


def FL(i):
    return f"u16 y.ftLim ({i})"


ML = f"({FL('kk')} - {K})"
MH = f"({FL('kk + 1')} - {K})"


def ofn(v):
    return f"BitVec.ofNat 64 ({v})"


def R(r, v):
    return f"s.regs.get64 .{r} = {v}"


def PE(base, e="ee"):
    return f"sbrA t₀ + {base}#64 + BitVec.ofNat 64 (0xc0 * {e})"


S98 = "dA t₀ ch + 0x15030#64 + BitVec.ofNat 64 (0x30 * (ee + 1))"
ENT = {}


def ent(ex, facts, fr):
    mem = f"(s.dmem =⋆ Mm k e y ra t₀ ({fr}))"
    body = " ∧ ".join(["(x.Keep y ∧ ChLive t₀ ch y)", "ApplyC y t₀", "c0.getLsbD 0 = decide (ch = 0)", "y.start ≠ 0", "ch < 2"]
                      + facts + [mem])
    return f"ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0{(' ' + ex) if ex else ''}, {body}"


def define(g):
    P = g.FR_CH_PARAMS + " (y : Args)"
    ch = g.FR_CH
    X = dict(ch, ea="dA t₀ ch + 0x3904#64", tmp30=("cells", "4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)"))
    G1 = dict(X, s78=ofn(NL))
    G2 = dict(G1, lim0=f"(({FL(0)} : Nat) : Int)")
    E0 = dict(G2, sf4=f"(-(BitVec.ofNat 32 {K})).toInt", s98=S98)
    E1 = dict(E0, s60=PE("0x5d740"))
    E2 = dict(E1, se8=PE("0x5eac0"))
    E3 = dict(E2, se0=PE("0x5f0c0"))
    E4 = dict(E3, sd8=PE("0x5e4c0"))
    E5 = dict(E4, s80=PE("0x5f6c0"))
    FK = dict(E5, s58=ofn("ee"))
    FB = dict(FK, s50=ofn("kk"))
    FB68 = dict(FB, s68=ofn(ML))
    FA = {kk: v for kk, v in X.items() if kk != "s98"}
    g.frame("FrGa1", G1, params=P)
    g.frame("FrGa2", G2, params=P)
    g.frame("FrGA", FA, params=P)
    for nm, d in [("FrGe0", E0), ("FrGe1", E1), ("FrGe2", E2), ("FrGe3", E3), ("FrGe4", E4), ("FrGe5", E5),
                  ("FrGk", FK)]:
        g.frame(nm, d, params=P + " (ee : Nat)")
    g.frame("FrGb", FB, params=P + " (ee kk : Nat)")
    g.frame("FrGb68", FB68, params=P + " (ee kk : Nat)")
    E = lambda i, t: (g.entry(i, t), ENT.__setitem__(i, t))

    RB = R("rbx", "dA t₀ ch")
    RC = R("rcx", ofn(K))
    REG = [RC, R("r10", f"arg1 t₀ + {ofn('0x30 * ee')}"), R("r11", PE("0x5f6c0")), R("r9", PE("0x5d740")),
           R("r8", PE("0x5eac0")), R("rdi", PE("0x5f6c4"))]
    EL = [f"ee < {N}", f"1 ≤ {NL}"]

    E("L914e", ent("", [RB], "FrX x t₀ ch c0 y"))
    E("L914e_1", ent("", [RB, f"1 ≤ {NL}"], "FrGa1 x t₀ ch c0 y"))
    E("L914e_2", ent("", [RB, f"1 ≤ {NL}", R("r10", "arg1 t₀"), RC], "FrGa2 x t₀ ch c0 y"))
    E("L914e_3", ent("", [RB, f"1 ≤ {NL}", R("r10", "arg1 t₀"), RC], "FrGe0 x t₀ ch c0 y 0"))
    for i in ["L91f7", "L9206", "L9215"]:
        E(i, ent("ee", EL + [RB, R("r12", ofn("ee"))] + REG, "FrGe0 x t₀ ch c0 y ee"))
    RSI = R("rsi", ofn("0xc0 * ee"))
    for i, fr in [("L9215_1", "FrGe1"), ("L9215_2", "FrGe2"), ("L9215_3", "FrGe3"), ("L9215_4", "FrGe4")]:
        E(i, ent("ee", EL + [RB, R("r12", ofn("ee")), RSI] + REG, f"{fr} x t₀ ch c0 y ee"))
    E("L9215_5", ent("ee", EL + [RB, R("r12", ofn("ee"))] + REG, "FrGe5 x t₀ ch c0 y ee"))
    KL = [f"ee < {N}", f"kk < {NL}"]
    E("L929e", ent("ee kk", KL + [R("r12", ofn("ee")), R("rdx", ofn("kk")), R("rsi", ofn(FL("kk")))] + REG,
                   "FrGk x t₀ ch c0 y ee"))
    FBt = "FrGb x t₀ ch c0 y ee kk"
    FB68t = "FrGb68 x t₀ ch c0 y ee kk"
    BODY = KL + [R("rdx", ofn("kk + 1"))] + REG
    RSI1 = R("rsi", ofn(FL("kk + 1")))
    R12 = R("r12", ofn("ee"))
    R13 = R("r13", ofn(ML))
    LT = f"{ML} < {MH}"
    E("L929e_1", ent("ee kk", BODY + [R12, R13], FBt))
    M1 = [f"{ML} ≤ mm", f"mm < {MH}", R("rbx", ofn("48")), R("r12", S98), R13]
    for i in ["L9300", "L9300_1"]:
        E(i, ent("ee kk mm", BODY + M1 + [R("rax", ofn("mm")), RSI1], FBt))
    # L9300_1 clobbers rsi (movzbl s_indexmapped byte); L9386_1 reloads f_tablelim[k+1]
    for i in ["L9300_2", "L9370", "L9386"]:
        E(i, ent("ee kk mm", BODY + M1 + [R("rax", ofn("mm"))], FBt))
    E("L9386_1", ent("ee kk mm", BODY + M1 + [R("rax", ofn("mm + 1"))], FBt))
    E("L93d0", ent("ee kk", BODY + [f"{MH} ≤ {ML}", R12, R13, RSI1], FBt))
    E("L93f0", ent("ee kk", BODY + [LT, R("r14", ofn(MH)), R("r15", ofn(FL("kk + 1"))), RSI1], FBt))
    E("L93f0_1", ent("ee kk", BODY + [LT, R("rbx", ofn(ML)), R("r12", ofn(f"{MH} - {ML}")), R("r14", ofn(MH)),
                                    R("r15", ofn(FL("kk + 1"))), R13, RSI1], FBt))
    E("L9440", ent("ee kk jj cc", BODY + [LT, "1 ≤ cc", f"jj + cc = {ML} + ({MH} - {ML}) % 8", f"{ML} ≤ jj",
                                      R("rbx", ofn("jj")), R("r12", ofn("cc")), R("r14", ofn(MH)),
                                      R("r15", ofn(FL("kk + 1"))), R13, RSI1], FB68t))
    E("L9458", ent("ee kk", BODY + [LT, R("rbx", ofn(f"{ML} + ({MH} - {ML}) % 8")), R("r14", ofn(MH)),
                                  R("r15", ofn(FL("kk + 1"))), R13, RSI1], FB68t))
    for i in ["L9470", "L9470_1"]:
        E(i, ent("ee kk jj", BODY + [LT, f"{ML} ≤ jj", f"jj < {MH}", f"({MH} - jj) % 8 = 0", R("rbx", ofn("jj")),
                                  R("r15", ofn(MH)), R13, RSI1], FB68t))
    E("L9504", ent("ee kk", BODY + [LT, R13, RSI1], FB68t))
    E("L9520", ent("ee kk", BODY + [R13, RSI1], FBt))
    E("L952c", ent("ee kk", BODY + [R13, RSI1], FBt))
    E("L9530", ent("ee kk", BODY + [R12, R13, RSI1], FBt))
    E("L9530_1", ent("ee kk", BODY + [R12, R13, LT, RSI1], FBt))
    M3 = [R12, R13, LT, f"{ML} ≤ mm", f"mm < {MH}", R("r14", ofn("48"))]
    for i in ["L95a0", "L95a0_1"]:
        E(i, ent("ee kk mm", BODY + M3 + [R("rax", ofn("mm")), RSI1], FBt))
    E("L95a0_2", ent("ee kk mm", BODY + M3 + [R("rax", ofn("mm + 1"))], FBt))
    E("L9600", ent("ee kk", BODY + [R12, LT, R("rbx", ofn(MH)), RSI1], FBt))
    E("L9617", ent("ee kk", BODY + [R12, R13, R("rbx", ofn(MH)), f"({LT} → {R('rax', ofn(FL('kk')))})", RSI1], FBt))
    E("L9617_1", ent("ee kk", BODY + [LT, R13, R("r12", ofn(MH)), RSI1], FBt))
    E("L968d", ent("ee kk", BODY + [LT, f"({MH} - {ML}) % 2 = 1", R("rax", ofn(ML)), R("r12", ofn(MH)), R13, RSI1], FBt))
    E("L96d3", ent("ee kk", BODY + [LT, R("rax", ofn(ML)), R("rbx", ofn(f"{ML} + ({MH} - {ML}) % 2")),
                                  R("r12", ofn(MH)), R13, RSI1], FBt))
    E("L96e1", ent("ee kk", BODY + [LT, R("rax", ofn(ML)), R13, RSI1], FBt))
    for i in ["L9720", "L9731", "L9731_1", "L97b7", "L97f0"]:
        E(i, ent("ee kk jj", BODY + [LT, f"{ML} ≤ jj", f"jj + 2 ≤ {MH}", f"({MH} - jj) % 2 = 0", R("rbx", ofn("jj")),
                                  R("r12", ofn(MH)), R("rax", ofn(ML)), R13, RSI1], FBt))
    E("L9820", ent("ee kk", BODY + [R12, R13, f"{MH} ≤ {ML}", RSI1], FBt))
    E("L983f", ent("ee kk", BODY + [LT, R12, R("rax", ofn(ML)), RSI1], FBt))
    M6 = [LT, R12, f"{ML} ≤ mm", f"mm < {MH}", R("rbx", ofn("48"))]
    for i in ["L9860", "L9860_1", "L9860_2"]:
        E(i, ent("ee kk mm", BODY + M6 + [R("rax", ofn("mm")), RSI1], FBt))
    E("L9860_3", ent("ee kk mm", BODY + M6 + [R("rax", ofn("mm + 1"))], FBt))
    E("L9290", ent("ee kk", BODY + [R12, RSI1], FBt))
    E("L91c0", ent("ee kk", [f"ee < {N}", f"1 ≤ {NL}", RB, R12] + REG, FBt))
    E("L98bc", "False")
    E("L98e0", ent("", [RB], "FrGA x t₀ ch c0 y"))
    CHC = "ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0)"
    QFS = R("r12", "sbrA t₀ + 0x5fcc0#64")
    # L9934_1: before the x_gen call (rsi = X[ch], rdi = &data[ch].Y, rcx = 1 - ypos, eax = ypos, r9 = ch)
    E("L9934_1", f"∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ {CHC} ∧ {QFS} ∧ {R('r9', ofn('ch'))}"
                 f" ∧ {R('rsi', 'sbrA t₀ + 0x53b40#64 + ' + ofn('0x4c00 * ch'))} ∧ {R('rdi', 'dA t₀ ch + 0x7930#64')} ∧ (s.regs.get64 .rbx).toNat % 256 = (if BitVec.setWidth 32 (arg2 t₀) = 1#32 then 1 else 0)"
                 " ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.regs.get64 .rax).toNat % 2^32 = (y.d ch).ypos"
                 f" ∧ {R('rcx', ofn('1 - (y.d ch).ypos'))} ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))")
    # L9934_2: after x_gen (r14 = che from the -0x38 slot)
    E("L9934_2", f"∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ {CHC} ∧ {QFS} ∧ {R('r14', 'arg1 t₀')}"
                 " ∧ (s.regs.get64 .rbx).toNat % 256 = (if BitVec.setWidth 32 (arg2 t₀) = 1#32 then 1 else 0)"
                 " ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))")
    # L9a02 (Syn IN): text agreed with apply (identical in apply's next EntrySyn.py; keep it here until then)
    E("L9a02", "∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀"
               " ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64"
               " ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))")

    # ---------------- variant measures
    MCH = "2 - (slot64 s 0x1a0).toNat"
    rg = lambda r: f"(s.regs.get64 .{r}).toNat"
    E8 = "(8 - (slot64 s 0x58).toNat)"
    K50 = "(30 - (slot64 s 0x50).toNat)"
    body = f"128 * {E8} + 4 * {K50} + 2"
    ms = {}
    for i in ["L9146", "L914e", "L914e_1", "L914e_2", "L914e_3", "L98e0", "L9927", "L9934", "L9934_1", "L9934_2"]:
        ms[i] = [MCH]
    for i in ["L91f7", "L9206", "L9215", "L9215_1", "L9215_2", "L9215_3", "L9215_4", "L9215_5"]:
        ms[i] = [MCH, f"128 * (8 - {rg('r12')}) + 127"]
    ms["L91c0"] = [MCH, f"128 * (8 - {rg('r12')}) + 1"]
    ms["L929e"] = [MCH, f"128 * {E8} + 4 * (30 - {rg('rdx')}) + 3"]
    ms["L9290"] = [MCH, f"128 * {E8} + 4 * {K50} + 1"]
    for i in ["L929e_1", "L93d0", "L93f0", "L93f0_1", "L9458", "L9504", "L9520", "L952c", "L9530", "L9530_1",
              "L9600", "L9617", "L9617_1", "L968d", "L96d3", "L9820", "L983f"]:
        ms[i] = [MCH, body]
    for i in ["L9300", "L9300_1", "L9300_2", "L9370", "L9386", "L95a0", "L95a0_1", "L9860", "L9860_1", "L9860_2"]:
        ms[i] = [MCH, body, f"2 * (64 - {rg('rax')}) + 1"]
    for i in ["L9386_1", "L95a0_2", "L9860_3"]:
        ms[i] = [MCH, body, f"2 * (64 - {rg('rax')}) + 3"]
    ms["L9440"] = [MCH, body, rg("r12")]
    for i in ["L9470", "L9470_1"]:
        ms[i] = [MCH, body, f"64 - {rg('rbx')}"]
    ms["L96e1"] = [MCH, body, "0"]
    ms["L9720"] = [MCH, body, f"3 * (64 - {rg('rbx')}) + 1"]
    for i in ["L9731", "L9731_1"]:
        ms[i] = [MCH, body, f"3 * (64 - {rg('rbx')})", "0"]
    for i in ["L97b7", "L97f0"]:
        ms[i] = [MCH, body, f"3 * (64 - {rg('rbx')}) + 2", "0"]
    for i, m in ms.items():
        g.measure(i, m)


if __name__ == "__main__":
    class G0:
        blocks = []
        ids = []
        FR_CH = {}
        FR_CH_PARAMS = ""
        def entry(self, i, t): pass
        def frame(self, *a, **k): pass
        def measure(self, *a): pass
    define(G0())
    for kk, v in ENT.items():
        print(kk, ":", v, "\n")
