# entries / frames / measures of shard DqSce (sbr_dequant, single-channel / non-coupled branch)
# Frames take parameters by the name hack "FrX (ch nch : Nat)" (gen.py inserts the name verbatim).
FRD = {"R": "arg4 t₀", "L": "arg3 t₀", "che": "arg1 t₀", "ac": "arg0 t₀",
       "idaac": "(BitVec.setWidth 32 (arg2 t₀)).toInt",
       "sf0": ("cells", "Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)")}
P = "(ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀"


def R(r):
    return f"s.regs.get64 .{r}"


def mem(fr):
    return f"(s.dmem =⋆ Mm k e x ra t₀ ({fr}))"


# loops (text order): A=[L6ffc,L7495_1] B=[L7007,L7495_1] C=[L700e,L7495] D=[L7020,L7370]
# E=[L7070,L71b0] F=[L7090,L717f] G=[L70bf,L717f]. Only A, E, F carry real measures:
#   mA = 4*(2-ch) + stage (stage 3 env loop/noise row 1, 2 noise row 2, 0 tail L6ffc..L7020)
#   mE = 9 - e (r15),  mF = 3*(48 - k) + t (t 2 before the store/compare, 1 av_log path, 0 L70bf)
CHR = "(if s.regs.get64 .r13 - s.regs.get64 .r9 = 0x289a0#64 then 8 else 4)"
CHS = "(if s.regs.get64 .r13 - slot64 s 0x38 = 0x289a0#64 then 8 else 4)"   # r9 clobbered
ME = "9 - (s.regs.get64 .r15).toNat"


def MF(t):
    return f"3 * (48 - (s.regs.get64 .rbx).toNat) + {t}"


def define(g):
    g.frame("FrS0 (nch : Nat)", dict(FRD, sc8="BitVec.ofNat 64 nch"))
    base = dict(FRD, sc8="BitVec.ofNat 64 nch", s58="dA t₀ 0")
    g.frame("FrM (ch nch : Nat)", dict(base, s50="dA t₀ ch + 0x15210#64", dch="dA t₀ ch + 0x15450#64"))
    g.frame("FrDq (ch nch : Nat)", dict(base, s50="dA t₀ ch + 0x15210#64", dch="dA t₀ ch + 0x15450#64",
                                       tmp30="BitVec.ofNat 64 ch"))
    g.frame("FrL1 (ch nch : Nat)", dict(base, s50="dA t₀ (ch + 1) + 0x15210#64",
                                        dch="dA t₀ ch + 0x15450#64", tmp30="BitVec.ofNat 64 ch"))
    g.frame("FrL2 (ch nch : Nat)", dict(base, s50="dA t₀ (ch + 1) + 0x15210#64",
                                        dch="dA t₀ (ch + 1) + 0x15450#64", tmp30="BitVec.ofNat 64 ch"))
    CH = "∃ ch nch : Nat, ch < nch ∧ nch ≤ 2"
    # boundary IN labels
    g.entry("L6fbe", f"{P} ∧ {mem('FrD x t₀')}")
    g.entry("L6fca", f"{P} ∧ ∃ nch : Nat, (nch = 1 ∨ nch = 2) ∧ {mem('FrS0 nch x t₀')}")
    # channel loop
    g.entry("L7044", f"{P} ∧ {CH} ∧ {R('rax')} = BitVec.ofNat 64 ch ∧ {mem('FrM ch nch x t₀')}")
    g.measure("L7044", ["(if s.regs.get64 .rax = 0#64 then 8 else 4) + 3", "0", "0", "0"])
    g.entry("L7044_1", f"{P} ∧ {CH} ∧ {R('rax')} = BitVec.ofNat 64 (0x15ac0 * ch)"
            f" ∧ {mem('FrDq ch nch x t₀')}")
    g.measure("L7044_1", ["(if s.regs.get64 .rax = 0#64 then 8 else 4) + 3", "0", "0", "0"])
    D = f"{R('r13')} = dA t₀ ch"
    # envelope loop: e in r15, r14 = &env_facs_q[e], r12 = &env_facs[e]
    EL = (f"{CH} ∧ {D} ∧ ∃ j : BitVec 64, {R('r15')} = j ∧ 1 ≤ j.toNat ∧ j.toNat ≤ (x.d ch).nenv"
          f" ∧ {R('r14')} = dA t₀ ch + 0x151e0#64 + 0x30#64 * j"
          f" ∧ {R('r12')} = dA t₀ ch + 0x15390#64 + 0xc0#64 * j")
    FR = "BitVec.ofNat 64 (u8 (x.d ch).freqRes j.toNat)"
    K48 = f"({R('rbx')}).toNat < 48"
    ml = mem("FrDq ch nch x t₀")
    g.entry("L7070", f"{P} ∧ {EL} ∧ {ml}")
    g.measure("L7070", [f"{CHR} + 3", "0", "0", "0", ME])
    g.entry("L71b0", f"{P} ∧ {EL} ∧ {ml}")
    g.measure("L71b0", [f"{CHR} + 3", "0", "0", "0", ME])
    g.entry("L70ca", f"{P} ∧ {EL} ∧ {R('rax')} = {FR} ∧ {ml}")
    g.measure("L70ca", [f"{CHR} + 3", "0", "0", "0", ME, MF(2), "0"])
    for i in ["L70ca_1", "L70bf"]:
        g.entry(i, f"{P} ∧ {EL} ∧ {R('rax')} = {FR} ∧ {K48} ∧ {ml}")
    g.measure("L70ca_1", [f"{CHR} + 3", "0", "0", "0", ME, MF(2), "0"])
    g.measure("L70bf", [f"{CHR} + 3", "0", "0", "0", ME, MF(0), "0"])
    for i in ["L7120", "L7140", "L7166", "L717f"]:
        g.entry(i, f"{P} ∧ {EL} ∧ {R('rax')} = {FR} ∧ {K48} ∧ {ml}")
        g.measure(i, [f"{CHR} + 3", "0", "0", "0", ME, MF(2), "0"])
    # av_log path: r9/rax clobbered by the call, r9 reloaded in L7090_1
    g.entry("L7090", f"{P} ∧ {EL} ∧ {K48} ∧ {ml}")
    g.measure("L7090", [f"{CHR} + 3", "0", "0", "0", ME, MF(1)])
    g.entry("L7090_1", f"(ApplyC x t₀ ∧ IdLive t₀ x) ∧ Base t₀ s ∧ {EL} ∧ {K48} ∧ {ml}")
    g.measure("L7090_1", [f"{CHS} + 3", "0", "0", "0", ME, MF(1)])
    g.entry("L7090_2", f"{P} ∧ {EL} ∧ {K48} ∧ {ml}")
    g.measure("L7090_2", [f"{CHR} + 3", "0", "0", "0", ME, MF(1)])
    # noise part
    g.entry("L71e0", f"{P} ∧ {CH} ∧ {D} ∧ {ml}")
    g.measure("L71e0", [f"{CHR} + 3", "0", "0", "0"])
    NZ = (f"{CH} ∧ {D} ∧ 1 ≤ (x.d ch).nnoise ∧ {R('rax')} = BitVec.ofNat 64 (x.d ch).nnoise"
          f" ∧ {R('rdx')} = BitVec.ofNat 64 x.nq")
    groups1 = [(1, ["L71e0_1", "L7226", "L723c"]), (2, ["L723c_1", "L7270", "L7286"]),
               (3, ["L7286_1", "L72ba", "L72d0"]), (4, ["L72d0_1", "L7304", "L731a"]),
               (5, ["L731a_1", "L734a", "L7360"])]
    for q, ids in groups1:
        for i in ids:
            g.entry(i, f"{P} ∧ {NZ} ∧ {q} ≤ x.nq ∧ {ml}")
            g.measure(i, [f"{CHR} + 3", "0", "0", "0"])
    g.entry("L7370", f"{P} ∧ {NZ} ∧ 1 ≤ x.nq ∧ {ml}")
    g.measure("L7370", [f"{CHR} + 3", "0", "0", "0"])
    N2 = (f"{CH} ∧ {D} ∧ (x.d ch).nnoise = 2 ∧ {R('rax')} = 3#64"
          f" ∧ {R('rdx')} = BitVec.ofNat 64 x.nq")
    groups2 = [(1, ["L73a1", "L73b7"]), (2, ["L73b7_1", "L73eb", "L7401"]),
               (3, ["L7401_1", "L7435", "L744b"]), (4, ["L744b_1", "L747f", "L7495"]),
               (5, ["L7495_1"])]
    for q, ids in groups2:
        for i in ids:
            g.entry(i, f"{P} ∧ {N2} ∧ {q} ≤ x.nq ∧ {ml}")
            g.measure(i, [f"{CHR} + 2", "0", "0"])
    g.measure("L7495_1", [f"{CHR} + 2", "0"])
    # L7495_1 clobbers edx (byte load): the row tail keeps only rax = 3
    for i in ["L6ffc", "L7007"]:
        g.entry(i, f"{P} ∧ {CH} ∧ {D} ∧ {R('rax')} = 3#64 ∧ {ml}")
    g.measure("L6ffc", [f"{CHR} + 0"])
    g.measure("L7007", [f"{CHR} + 0", "0"])
    g.entry("L700e", f"{P} ∧ {CH} ∧ {D} ∧ {R('rax')} = 3#64 ∧ {ml}")
    g.measure("L700e", [f"{CHR} + 0", "0", "0"])
    g.entry("L7020", f"{P} ∧ {CH} ∧ {D} ∧ {ml}")
    g.measure("L7020", [f"{CHR} + 0", "0", "0", "0"])
    CH1 = "(if s.regs.get64 .rax = 1#64 then 4 else 0) + 3"
    g.entry("L7020_1", f"{P} ∧ {CH} ∧ {R('rax')} = BitVec.ofNat 64 (ch + 1) ∧ {mem('FrL1 ch nch x t₀')}")
    g.measure("L7020_1", [CH1, "0", "0", "0"])
    g.entry("L7020_2", f"{P} ∧ {CH} ∧ {R('rax')} = BitVec.ofNat 64 (ch + 1) ∧ {mem('FrL2 ch nch x t₀')}")
    g.measure("L7020_2", [CH1, "0", "0", "0"])

# env loop (r14 = &env_facs_q[e]) and its head L71e0 (sets r14 = 0 inside): plain Base
NOT_Z = {"L7070", "L7090", "L7090_1", "L7090_2", "L70bf", "L70ca", "L70ca_1", "L7120", "L7140",
         "L7166", "L717f", "L71b0", "L71e0"}

# ---- apply (push/BaseZ rebuild): the dequant runs on x.push; r14 = 0 (BaseZ) where noted ----
_define_dq = define


def define(g):
    orig = g.entry

    def ent(i, text):
        text = text.replace("Mm k e x ra", "Mm k e x.push ra")
        if i not in NOT_Z:
            text = text.replace("Base t₀ s", "BaseZ t₀ s", 1)
        orig(i, text)
    g.entry = ent
    try:
        _define_dq(g)
    finally:
        del g.entry
