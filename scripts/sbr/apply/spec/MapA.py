# entries / frames of shard MapA (sbr_mapping, first half) — helper apply-mapb, DRAFT v1 (paper, 05:20)
#
# Boundary IN  L7ce4 (agreed with anahf 05:18):
#   ∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0) ∧ rbx = dA t₀ ch ∧ r8 = arg1 t₀
#     ∧ ∃ y, x.Keep y ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrA x t₀ ch c0))
# NOTE: frames below are still written in the old "(ch j)" style; they get the owner's
#       params mechanism (ch c0 y j) once it lands. FrA = owner's channel-level dict.
#
# Block semantics (rbx = dA ch, r8 = arg1 = che, sbr = arg1 + 0x28920):
#   L7ce4/_1   zero s_indexmapped rows 1..7 (dA+0x15060 .. +0x151b0), r10 = dA+0x15030
#   L7ce4_2    nenv = 0 -> L8790 ; se0 = dA+0x15390 (env_facs), sd8 = dA+0x15a60 (noise_facs)
#   L7ce4_3    r11 = ah1 + s98 = dA+0x32 ; rcx = 1 ; s60 = arg1 (= PROW 0)
#   L7ce4_4    s58 = qmap (= QROW 0)
#   L7ce4_5    r12 = eom (= EROW 0) ; rax = 0 ; s80 = r10 ; se8 = r11
#   L7db0      e loop head (rax = e = j, rcx = j+1): freqRes[j+1] < 2 (else trap L9b77);
#              r15 = table; tmp30 = kx1; kx1 ≠ table[0] -> L879e (error exit)
#   L7db0_1    s50 = n[res]; = 0 -> L7e90 ; rcx = env_facs[j+1]; rdx = 0; -> L7e29
#   L7e20/L7e29/L7e60/L7e60_1  e_origmapped[j][m - kx1] = env_facs[j+1][i]  (traps L9b5e/L99e9)
#   L7e90      s68 = j+1 ; rdx = 1
#   L7e90_1    kk = (bs_num_noise ≥ 2 ∧ t_env[j] ≥ t_q[1]) ? 2 : 1  (cmp te / sbb)
#   L7eb6      nq = 0 -> L8520 ; rdx = noise_facs[kk] ; band 0 = [ftNoise[0], ftNoise[1]) ;
#              empty -> L8009 ; r8 = c, r9 = c & 3
#   L7eb6_1    c % 4 = 0 -> L7f36 (ZF of the `and`) ; head loop L7f10 (stage 0 "pre")
#   L7f36/_1   4-way loop L7f80/_1 (stage 0 "mid"/"mid1"/"loop"), falls through to L8009
import os, sys
sys.path.insert(0, os.environ.get("APPLY_SPECDIR") or os.path.dirname(os.path.abspath(globals().get("__file__", "."))))
from MapB import (BASE0, FRM, R, ofn, row, tb, fN, ILIM, TABA, EROW, QROW, PROW, MAPC, NOISE,
                  LOOPREGS, LAST, yy, OUT3)
from MapB import ME as ME0

ENTF = {}
ENT = {}

LOC = {k: v for k, v in BASE0.items() if k in ("dch", "s98")}   # on top of g.FR_CH (= FrC)
FA1 = dict(LOC, se0=BASE0["se0"], sd8=BASE0["sd8"])
FA2 = dict(FA1, s60=PROW("j"))
FA3 = dict(FA2, s58=QROW("j"))
FRB = dict(BASE0, tmp30=FRM["tmp30"])
FRE = dict(FRB, s50=FRM["s50"])

ENVROW = row("dA t₀ ch + 0x15390#64", "192", "(j + 1)")
KX0 = f"x.kx1 = {tb('0')}"


def ent(ex, facts, fr, mapc=MAPC):
    facts = [yy(f) for f in facts]
    LAST["v"] = (ex.split(), list(facts), fr)
    frt = f"{fr} x t₀ ch c0" if fr == "FrC" else f"{fr} x t₀ ch c0 y j"
    mem = f"(s.dmem =⋆ Mm k e y ra t₀ ({frt}))"
    body = " ∧ ".join(["(x.Keep y ∧ ChLive t₀ ch y)", "ApplyC y t₀", "c0.getLsbD 0 = decide (ch = 0)", yy(mapc)] + facts + [mem])
    return f"ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0 j{(' ' + ex) if ex else ''}, {body}"


def define(g):
    P = g.FR_CH_PARAMS + " (y : Args) (j : Nat)"
    for nm, d in (("FrMA1", FA1), ("FrMA2", FA2), ("FrMA3", FA3), ("FrMB", FRB), ("FrME", FRE)):
        g.frame(nm, dict(g.FR_CH, **{k: ((v[0], yy(v[1])) if isinstance(v, tuple) else yy(v)) for k, v in d.items()}), params=P)
    # L7ce4 entry lives in shared W/spec/_frames.py
    E = lambda i, t: (g.entry(i, t), ENT.__setitem__(i, t), ENTF.__setitem__(i, LAST['v']))
    C0 = "x.start ≠ 0 ∧ ch < 2 ∧ j = 0"
    RB = [R("rbx", "dA t₀ ch"), R("r8", "arg1 t₀")]
    R10 = [R("r10", "dA t₀ ch + 0x15030#64")]
    # L7ce4 (IN boundary) is the agreed text above; inner prefix blocks:
    E("L7ce4_1", ent("", RB + R10, "FrC", C0))
    E("L7ce4_2", ent("", RB + R10, "FrC", C0))
    C1 = C0 + " ∧ 0 < (x.d ch).nenv"
    E("L7ce4_3", ent("", RB + R10, "FrMA1", C1))
    R11 = [R("r11", "dA t₀ ch + 0x32#64"), R("rcx", "1#64")]
    E("L7ce4_4", ent("", RB + R10 + R11, "FrMA2", C1))
    E("L7ce4_5", ent("", RB + R10 + R11, "FrMA3", C1))
    # e loop
    BASE = [R("rax", ofn("j")), R("rbx", "dA t₀ ch"), R("r12", EROW("j"))]
    E("L7db0", ent("", BASE + [R("rcx", ofn("j + 1")), R("r8", "arg1 t₀")], "FrM0"))
    MFR = "u8 (x.d ch).freqRes (j + 1)"
    B1 = BASE + [R("r14", ofn("j + 1")), R("r15", TABA), KX0]
    E("L7db0_1", ent("", B1 + [f"{MFR} < 2", R("rcx", ofn(MFR)), R("r8", "arg1 t₀"), R("rdi", ofn(tb("0")))], "FrMB"))
    B2 = B1 + [R("rcx", ENVROW)]
    E("L7e29", ent("i", B2 + [f"i < {ILIM}", R("rdx", ofn("i")), R("rdi", ofn(tb("i")))], "FrME"))
    E("L7e20", ent("i", B2 + [f"1 ≤ i", f"i ≤ {ILIM}", R("rdx", ofn("i")), R("r9", ofn(tb("i")))], "FrME"))
    BV = B2 + [f"i < {ILIM}", R("rsi", ofn("i")), R("rdx", ofn("i + 1")), R("r9", ofn(tb("i + 1"))),
               f"{tb('i')} ≤ v", f"v < {tb('i + 1')}", "x.kx1 ≤ v", "v < x.kx1 + 48",
               R("r8", ofn("v - x.kx1")), R("rdi", ofn("v + 1"))]
    E("L7e60", ent("i v", BV, "FrME"))
    E("L7e60_1", ent("i v", BV, "FrME"))
    B3 = [R("rax", ofn("j")), R("rbx", "dA t₀ ch")] + LOOPREGS + [R("r14", ofn("j + 1"))]
    E("L7e90", ent("", B3, "FrME"))
    E("L7e90_1", ent("", B3 + [R("rdx", "1#64")], "FrMb"))
    E("L7eb6", ent("kk", B3 + ["1 ≤ kk", "kk ≤ 2", R("rdx", ofn("kk"))], "FrMb"))
    # noise stage 0 (band [ftNoise[0], ftNoise[1]), start reg rdi, end reg rsi) — same shapes as MapB stages
    c = f"({fN(1)} - {fN(0)})"
    band = ["1 ≤ x.nq", f"x.kx1 ≤ {fN(0)}", f"{fN(0)} < {fN(1)}", f"{fN(1)} ≤ x.kx1 + 48"]
    N0 = NOISE + LOOPREGS + band + [R("rsi", ofn(fN(1)))]
    E("L7eb6_1", ent("kk", N0 + [R("rdi", ofn(fN(0))), R("r8", ofn(c)), R("r9", ofn(f"{c} % 4")),
                                 f"s.status.zf = decide ({c} % 4 = 0)"], "FrMb"))
    E("L7f10", ent("kk t", N0 + [f"t < {c} % 4", R("rdi", ofn(fN(0))), R("r8", ofn(c)),
                                 R("r9", f"0#64 - {ofn(c + ' % 4')}"), R("r11", f"0#64 - {ofn('t')}"),
                                 R("r10", ofn(f"{fN(0)} + t - x.kx1"))], "FrMb"))
    m0 = f"({fN(0)} + {c} % 4)"
    E("L7f36", ent("kk", N0 + [R("rdi", ofn(m0)), R("r8", ofn(c))], "FrMb"))
    a = f"({m0} - x.kx1)"
    P = PROW("j")
    ptrs = [R("rbx", f"{P} + {ofn('4 * ' + a)}"), R("r11", f"{P} + {ofn('4 * (' + a + ' + 1)')}"),
            R("r10", f"{P} + {ofn('4 * (' + a + ' + 2)')}"), R("r9", f"{P} + {ofn('4 * (' + a + ' + 3)')}")]
    common = N0 + [f"{m0} + 4 ≤ {fN(1)}", R("r8", ofn(a)), R("rdi", f"{ofn(m0)} - {ofn(fN(1))}")] + ptrs
    # rbx is the row pointer here (not dA ch): drop the B3 rbx fact
    common = [f for f in common if not f.startswith('s.regs.get64 .rbx = dA')]
    E("L7f36_1", ent("kk", common, "FrMb"))
    lp = common + [f"{m0} + 4 * t + 4 ≤ {fN(1)}", R("r14", f"0x21998#64 + {ofn('4 * t')}")]
    E("L7f80", ent("kk t", lp, "FrMb"))
    E("L7f80_1", ent("kk t", lp, "FrMb"))


# measures: channel, [L7cbf loop], [L7ce4 loop] (owner (a): 0 at all Map labels), e loop, inner
INNER = {}
for l in ("L7e29", "L7e20", "L7e60", "L7e60_1"):
    INNER[l] = "50 - (s.regs.get64 .rdx).toNat"     # band index; inner store loop uses rdi below
for l in ("L7e60", "L7e60_1"):   # rdx = i+1 here (apply-anahf 10:32): 51 - rdx = 50 - i, so L7e60_1 -> L7e20 (rdx = i+1) decreases
    INNER[l] = "51 - (s.regs.get64 .rdx).toNat"
INNER["L7f10"] = "((s.regs.get64 .r11) - (s.regs.get64 .r9)).toNat"
for l in ("L7f80", "L7f80_1"):
    INNER[l] = "(0x21998#64 - ((s.regs.get64 .rdi) + (s.regs.get64 .r14))).toNat"
ME_PRE = {"L7db0": "9 - (s.regs.get64 .rcx).toNat"}
for _l in ("L7db0_1", "L7e20", "L7e29", "L7e60", "L7e60_1", "L7e90"):
    ME_PRE[_l] = "9 - (s.regs.get64 .r14).toNat"
_define = define


def define(g):
    _define(g)
    for b in g.blocks:
        if b["phase"] != "Map:A":
            continue
        i = b["id"]
        # e-loop variant before the -0x68 slot store at L7e90: slot still holds the old
        # index there, so read j+1 from a register (rcx at L7db0, r14 after) instead.
        ME = ME_PRE.get(i, ME0)
        if i.startswith("L7ce4"):
            g.measure(i, OUT3)
        elif i in ("L7e60", "L7e60_1"):
            # store loop nested in band loop: rdx = i+1 here, so band part = 49 - i; then 64 - rdi
            g.measure(i, OUT3 + [ME, INNER[i], "2 ^ 16 + 64 - (s.regs.get64 .rdi).toNat"])
        elif i in INNER:
            g.measure(i, OUT3 + [ME, INNER[i]])
        else:
            g.measure(i, OUT3 + [ME])


if __name__ == "__main__":
    class G:
        blocks = []
        def entry(self, i, t): pass
        FR_CH = {}; FR_CH_PARAMS = '(ch : Nat) (c0 : BitVec 32)'
        def frame(self, *a, **k): pass
    define(G())
    for k, v in ENT.items():
        print(k, ":", v, "\n")
