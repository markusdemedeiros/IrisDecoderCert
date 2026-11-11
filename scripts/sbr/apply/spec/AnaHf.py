# entries / frames / measures of shard AnaHf (Ana, Chirp, HfGen) — helper apply-anahf, DRAFT v1
#
# Entry shape (owner convention, 05:16):
#   ∃ <vars>, ApplyC x t₀ ∧ Base t₀ s ∧ <regs/pure> ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ <facts y>
#     ∧ (s.dmem =⋆ Mm k e y ra t₀ (Fr… x t₀ …))
# Frames: FrL (loop head, shared), FrAn1..FrA6 (Ana store stages), FrH (HfGen: tmp30 = bs_num_env).
# Boundary: IN L7682 (owner-accepted text), OUT L9934 (Syn, owner), L7ce4 (mapb), traps False.

Z = "sbrA t₀ + 0x5fcc0#64"
CHE = "arg1 t₀"
DCH = "dA t₀ ch"
C0F = "c0.getLsbD 0 = decide (ch = 0)"


def R(r, v):
    return f"s.regs.get64 .{r} = {v}"


def ofn(v):
    return f"BitVec.ofNat 64 ({v})"


def PS(j):
    """Σ_{j ≤ i < npatch} patch_num_subbands[i]."""
    return f"((List.range' ({j}) (y.npatch - ({j}))).map (fun i => u8 y.pnum i)).sum"


def ent(exs, outer, yfacts, fr):
    head = ["ApplyC x t₀", "Base t₀ s"] + outer
    y = " ∧ ".join(["(x.Keep y ∧ ChLive t₀ ch y)", "ApplyC y t₀"] + yfacts + [f"(s.dmem =⋆ Mm k e y ra t₀ ({fr}))"])
    body = " ∧ ".join(head + [f"∃ y : Args, {y}"])
    return f"∃ {exs}, {body}" if exs else body


MCH0 = "2 - (s.regs.get64 .rdx).toNat"
MCH = "2 - (slot64 s 0x1a0).toNat"
M_ANA = "4096 - (s.regs.get64 .r13).toNat"
M_J = "6 - (s.regs.get64 .r15).toNat"
M_X = "256 - (s.regs.get64 .r14).toNat"
M_G = "(s.regs.get64 .rcx).toNat - (s.regs.get64 .rdx).toNat"

P3 = "(e : Env) (ch : Nat) (c0 : BitVec 32)"


def define(g):
    FL = {k: v for k, v in g.FR_CH.items() if k not in ("ch", "ch0", "dch", "s98")}
    A1 = dict(FL, tmp30="x.fdsp")
    A2 = dict(A1, s58="x.anaCtx")
    A3 = dict(A2, s50="e.fs.mdctAna.toBitVec", ch0="c0.toInt")
    A4 = dict(A3, s68="if ch = 0 then arg3 t₀ else arg4 t₀", ch="BitVec.ofNat 64 ch")
    A5 = dict(A4, dch=DCH, s78="dA t₀ ch + 0x3920#64")
    A6 = dict(A5, s98="BitVec.ofNat 64 (0x15ac0 * ch)")
    H = dict(A6, tmp30="BitVec.ofNat 64 ne")
    g.frame("FrAn1", A1)
    g.frame("FrA2", A2)
    g.frame("FrA3", A3, params=P3)
    g.frame("FrA4", A4, params=P3)
    g.frame("FrA5", A5, params=P3)
    g.frame("FrA6", A6, params=P3)
    g.frame("FrH", H, params=P3 + " (ne : Nat)")
    F = lambda n: f"{n} x t₀ e ch c0"
    FH = "FrH x t₀ e ch c0 ne"

    # ---------------- Ana (sbr_qmf_analysis + lf_gen + hf_inverse_filter) ----------------
    RCX = "(s.regs.get64 .rcx).getLsbD 0 = decide (ch = 0)"
    base0 = ["ch < 2", R("r9", CHE), R("r12", Z), R("rdx", ofn("ch")), RCX]
    g.entry("L7682", ent("ch", base0, [], "FrL x t₀"))           # IN (owner-accepted)
    g.entry("L7682_1", ent("ch", base0 + [R("r14", Z)], [], "FrAn1 x t₀"))
    g.entry("L7682_2", ent("ch", base0 + [R("r14", Z)], [], "FrA2 x t₀"))
    g.entry("L7682_3", ent("ch c0", ["ch < 2", C0F, R("r9", CHE), R("r14", Z), R("rdx", ofn("ch")),
                                     "s.status.zf = decide (ch ≠ 0)"], [], F("FrA3")))
    S98 = ofn("0x15ac0 * ch")
    b4 = ["ch < 2", C0F, R("r9", CHE), R("r14", Z), R("r13", S98)]
    g.entry("L7682_4", ent("ch c0", b4, [], F("FrA4")))
    g.entry("L7682_5", ent("ch c0", b4 + [R("rcx", "sbrA t₀ + 0x80#64"), R("rdi", "dA t₀ ch + 0x2480#64")],
                           [], F("FrA5")))
    XB = "dA t₀ ch + 0x2480#64"
    YP = ofn("(y.d ch).ypos")
    b6 = ["ch < 2", C0F, R("r14", Z), R("r12", XB), R("rbx", CHE)]
    g.entry("L7682_6", ent("ch c0", b6 + [R("r13", S98)], [R("r15", YP)], F("FrA5")))
    g.entry("L7682_7", ent("ch c0", b6 + [R("r13", S98)], [R("r15", YP)], F("FrA6")))
    g.entry("L7682_8", ent("ch c0", b6, [R("r15", YP)], F("FrA6")))
    loop = ["ch < 2", C0F, "i < 32", R("r12", XB), R("r13", ofn("128 * i")), R("r14", Z), R("rbx", CHE)]
    WR = R("r15", "dA t₀ ch + 0x3920#64 + BitVec.ofNat 64 (8192 * (y.d ch).ypos + 256 * i)")
    for l in ("L7750", "L7750_1", "L7750_2", "L7750_3", "L7750_4", "L7750_5"):
        g.entry(l, ent("ch c0 i", loop, [WR], F("FrA6")))
        g.measure(l, [MCH, M_ANA])
    b7 = ["ch < 2", C0F, R("r14", Z), R("r15", DCH), R("rbx", CHE)]
    g.entry("L7750_6", ent("ch c0", b7, [], F("FrA6")))
    g.entry("L7750_7", ent("ch c0", b7, ["(s.regs.get64 .rax).toNat % 2^32 = (y.d ch).ypos"], F("FrA6")))
    g.entry("L7750_8", ent("ch c0", ["ch < 2", C0F], ["y.start ≠ 0"], F("FrA6")))

    # ---------------- Chirp (sbr_chirp, unrolled 5x) ----------------
    cb = ["ch < 2", C0F, R("r8", CHE), R("rbx", DCH)]
    NQ = R("rax", ofn("y.nq"))
    for l in ("L7866", "L7884", "L7884_1", "L78f2", "L7910", "L7910_1", "L797e", "L799c",
              "L799c_1", "L7a0a", "L7a28"):
        g.entry(l, ent("ch c0", cb, ["y.start ≠ 0", NQ], F("FrA6")))
    for l in ("L7a28_1", "L7a96", "L7ab4"):
        g.entry(l, ent("ch c0", cb, ["y.start ≠ 0", NQ, "5 ≤ y.nq"], F("FrA6")))

    # ---------------- HfGen (sbr_hf_gen) ----------------
    g.entry("L7b00", ent("ch c0", cb, ["y.start ≠ 0"], F("FrA6")))
    NE = "ne = (y.d ch).nenv"
    g.entry("L7b00_1", ent("ch c0 ne", cb, ["y.start ≠ 0", NE], FH))
    jb = cb + [R("r15", ofn("j")), R("r12", ofn("kk"))]
    jy = ["y.start ≠ 0", NE, "j < y.npatch"]
    g.entry("L7b2d", ent("ch c0 ne j kk g", jb + [R("r13", ofn("g"))],
                         jy + [R("rax", ofn("y.npatch")), "g ≤ y.nq", f"kk + {PS('j')} ≤ y.kx1 + y.m1"], FH))
    g.entry("L7c5d", ent("ch c0 ne j kk g", jb + [R("r13", ofn("g"))],
                         jy + [R("rax", ofn("y.npatch")), "g ≤ y.nq", f"kk + {PS('j + 1')} ≤ y.kx1 + y.m1"], FH))
    xb = jb + [R("r14", ofn("xx"))]
    xy = jy + ["xx < u8 y.pnum j", f"kk + (u8 y.pnum j - xx) + {PS('j + 1')} ≤ y.kx1 + y.m1"]
    PST = R("rax", ofn("u8 y.pstart j"))
    g.entry("L7b50", ent("ch c0 ne j kk g xx", xb + [R("r13", ofn("g"))], xy + ["g ≤ y.nq"], FH))
    g.entry("L7b80", ent("ch c0 ne j kk xx gg", xb + [R("rdx", ofn("gg")), R("rsi", "6#64")],
                         xy + [PST, "gg < y.nq + 1", R("rcx", ofn("y.nq + 1")), R("r13", ofn("y.nq + 1"))], FH))
    g.entry("L7bb0", ent("ch c0 ne j kk xx gg", xb + [R("rdx", ofn("gg"))],
                         xy + [PST, "gg < y.nq + 1"], FH))
    g.entry("L7bb3", ent("ch c0 ne j kk g xx", xb + [R("r13", ofn("g"))], xy + [PST, "g ≤ y.nq"], FH))
    P = "(u8 y.pstart j + xx)"
    g.entry("L7bb3_1", ent("ch c0 ne j kk g xx", xb + [R("r13", ofn("g"))],
                           xy + ["g < y.nq", R("rax", ofn(P)),
                                 R("rdi", "sbrA t₀ + 0x4eb40#64 + BitVec.ofNat 64 (320 * kk) + 16#64"),
                                 R("rsi", f"sbrA t₀ + 0x4c340#64 + BitVec.ofNat 64 (320 * {P}) + 16#64")], FH))
    g.entry("L7bb3_2", ent("ch c0 ne j kk g xx",
                           ["ch < 2", C0F, R("rbx", CHE), R("r15", ofn("j")), R("r12", ofn("kk")),
                            R("r14", ofn("xx")), R("r13", ofn("g"))],
                           xy + ["g < y.nq"], FH))
    for l in ("L7b2d", "L7c5d"):
        g.measure(l, [MCH, M_J])
    for l in ("L7b50", "L7bb0", "L7bb3", "L7bb3_1", "L7bb3_2"):
        g.measure(l, [MCH, M_J, M_X])
    g.measure("L7b80", [MCH, M_J, M_X, M_G])
    # error exit (no noise band), the tail memset, the exit to sbr_mapping
    g.entry("L7c80", ent("ch c0 ne", ["ch < 2", C0F, R("rbx", DCH)], ["y.start ≠ 0", NE], FH))
    g.entry("L7c80_1", ent("ch c0 ne", ["ch < 2", C0F, R("rbx", DCH)], ["y.start ≠ 0", NE], FH))
    g.entry("L7cb0", ent("ch c0 ne", cb, ["y.start ≠ 0", NE, R("r12", ofn("y.kx1"))], FH))
    g.entry("L8b4f", ent("ch c0 ne kk", cb + [R("r12", ofn("kk"))], ["y.start ≠ 0", NE, "kk ≤ 64"], FH))
    g.entry("L7cbf", ent("ch c0 ne kk cnt", ["ch < 2", C0F, R("rbx", DCH), R("r12", ofn("kk")),
                                             R("rax", ofn("cnt"))],
                         ["y.start ≠ 0", NE, "kk + cnt ≤ 64"], FH))
    g.entry("L7ce0", ent("ch c0 ne", ["ch < 2", C0F, R("rbx", DCH)], ["y.start ≠ 0", NE], FH))
    g.measure("L7cbf", [MCH, "0"])
    g.measure("L7ce0", [MCH, "0"])
    g.measure("L8b4f", [MCH, "1", "0"])

    # channel measure for every other label of the shard
    for l in ("L7682", "L7682_1", "L7682_2", "L7682_3"):
        g.measure(l, [MCH0])
    for b in g.blocks:
        if b["phase"] in ("Ana", "Chirp", "HfGen") and b["id"] not in g.MEASURE:
            g.measure(b["id"], [MCH])
