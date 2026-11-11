# shared frame dicts (loaded by gen.py before the shard specs; owner: apply)
# FR_CH: the channel-level frame = all Setup slots (set in L74e9_*) + per-channel slots.
# Extend in shard specs with  g.frame("FrX", dict(g.FR_CH, s58="…"), params=g.FR_CH_PARAMS + " (y : Args)")
SB = "sbrA t₀ + {}#64"
def define(g):
    ch = {k: SB.format(v) for k, v in [
        ("d0", "0x80"), ("dsp", "0x601e0"), ("Xl", "0x4c340"), ("a0", "0x5d340"), ("a1", "0x5d540"),
        ("Xh", "0x4eb40"), ("fth", "0x4c284"), ("ftl", "0x4c252"), ("eom", "0x5d740"),
        ("qmap", "0x5dd40"), ("smap", "0x5e340"), ("spp", "0x1c"), ("ecur", "0x5e4c0"),
        ("qm", "0x5eac0"), ("sm", "0x5f0c0"), ("gain", "0x5f6c0"), ("X", "0x53b40"),
        ("fth4", "0x4c288"), ("ah1", "0xb2"), ("xh150", "0x4ec90"), ("xh10", "0x4eb50"),
        ("sim1", "0x150e0"), ("gain4", "0x5f6c4"), ("sc8", "0x5fdc0"), ("qfs", "0x5fcc0")]}
    ch.update({"che": "arg1 t₀", "ac": "arg0 t₀", "R": "arg4 t₀", "L": "arg3 t₀", "sbr": "sbrA t₀",
               "sf0": 'lab "sbr_qmf_window_ds"',
               # owner slots (TENTATIVE spelling, fixed against vcgen output after the R1 rebuild)
               "idaac": "(BitVec.setWidth 32 (arg2 t₀)).toInt",
               "ds": "BitVec.ofNat 64 (dsN x)",
               # per-channel (anahf)
               "ch": "BitVec.ofNat 64 ch", "ch0": "c0.toInt",
               "dch": "dA t₀ ch", "s98": "BitVec.ofNat 64 (0x15ac0 * ch)"})
    g.FR_CH = ch
    g.FR_CH_PARAMS = "(ch : Nat) (c0 : BitVec 32)"
    g.frame("FrC", ch, params=g.FR_CH_PARAMS)
    # channel-loop head L7682: the per-channel slots are not valid on the first pass
    g.frame("FrL", {k: v for k, v in ch.items() if k not in ("ch", "ch0", "dch", "s98")})
    # ---- agreed boundary entries between shards (owner: apply) ----
    P = g.FR_CH_PARAMS + " (y : Args)"
    fo = dict(ch, tmp30=("cells", "Int.toBytes 4 (BitVec.ofNat 32 y.kx1).toInt =@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)"))
    g.frame("FrO", fo, params=P)
    g.frame("FrO8", dict(fo, s80="dA t₀ ch + 0x15030#64"), params=P)
    CHC = "ch < 2 ∧ c0.getLsbD 0 = decide (ch = 0)"
    # Ana/HfGen IN (anahf): channel-loop head
    g.entry("L7682", "∃ ch, ApplyC x t₀ ∧ Base t₀ s ∧ ch < 2 ∧ s.regs.get64 .r9 = arg1 t₀"
            " ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .rdx = BitVec.ofNat 64 ch"
            " ∧ (s.regs.get64 .rcx).getLsbD 0 = decide (ch = 0)"
            " ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrL x t₀))")
    # Map IN (mapb + anahf)
    g.entry("L7ce4", f"∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ {CHC}"
            " ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀"
            " ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ y.start ≠ 0 ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrC x t₀ ch c0))")
    # Env:A IN (mapb + env)
    ENVO = ("ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0)"
            " ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rbx = dA t₀ ch ∧ s.regs.get64 .r8 = arg1 t₀")
    g.entry("L881c", ENVO + " ∧ s.regs.get64 .r10 = dA t₀ ch + 0x15030#64"
            " ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.d ch).nenv ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrO x t₀ ch c0 y))")
    g.entry("L8818", ENVO + " ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.d ch).nenv"
            " ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrO8 x t₀ ch c0 y))")
    # after gain_calc slot -0x98 holds an env pointer (dqcpl 07:38): s98 raw from L9927 on
    g.frame("FrCs", {k: v for k, v in ch.items() if k != "s98"}, params=g.FR_CH_PARAMS)
    # Syn: after hf_assemble (anahf) or the reset error path (mapb, y := y.turnoff)
    g.entry("L9927", f"ApplyC x t₀ ∧ Base t₀ s ∧ ∃ ch c0, {CHC} ∧ s.regs.get64 .rbx = dA t₀ ch"
            " ∧ ∃ y, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))")
    g.entry("L9934", f"∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ {CHC}"
            " ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64"
            " ∧ ∃ y : Args, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ (s.regs.get64 .rax).toNat % 2^32 = (y.d ch).ypos"
            " ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))")
    # Env OUT -> GainAsm IN (env): the only real exit of Env
    g.frame("FrX", dict(ch, ea="dA t₀ ch + 0x3904#64",
                        tmp30=("cells", "4 ?@ (r - 0x38#64) ⋆ 4 ?@ (r - 0x34#64)")), params=P)
    g.entry("L9146", "ApplyC x t₀ ∧ Base t₀ s ∧ ∃ y ch c0, (x.Keep y ∧ ChLive t₀ ch y) ∧ ApplyC y t₀ ∧ c0.getLsbD 0 = decide (ch = 0)"
            " ∧ y.start ≠ 0 ∧ ch < 2 ∧ s.regs.get64 .rax = BitVec.ofNat 64 (y.d ch).nenv"
            " ∧ s.regs.get64 .rbx = dA t₀ ch ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrX x t₀ ch c0 y))")
    # Env tail (owner apply, 12:10): L90f9_1 -> L99c6 -> L99cf -> L9146 is acyclic inside one channel
    # iteration, but L99cf -> L9146 jumps backward in text, so the laminar loop merge folds it into the
    # channel loop (119, 375) and the generated phase digit (0) was below L9146's (1). Rank the two tail
    # blocks above L9146 = [0, MCH, 1, 0, 0, ..] and below L90f9_1 = [0, MCH, 1, 2 * (48 - rbx) + 1, ..].
    MCH = "(2 - (slot64 s 0x1a0).toNat)"
    g.digits("L99c6", ["0", MCH, "1", "0", "2"])
    g.digits("L99cf", ["0", MCH, "1", "0", "1"])
