# entries / frames of shard EntrySyn (Entry, Setup, Syn phases)
BL1 = "BitVec.setWidth 8 (s.regs.get64 .rbx) = 1#8"
BL0 = "BitVec.setWidth 8 (s.regs.get64 .rbx) = 0#8"
SF0 = ("cells", "Int.toBytes 1 (dsN x : Int) =@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)")
FRD = {"R": "arg4 t₀", "L": "arg3 t₀", "che": "arg1 t₀", "ac": "arg0 t₀",
       "idaac": "(BitVec.setWidth 32 (arg2 t₀)).toInt", "sf0": SF0}


def define(g):
    g.frame("FrA", {"R": "arg4 t₀", "L": "arg3 t₀"})
    # after start_1: `setl -0xf0(%rbp)`, the `ds` byte (the low byte of slot sf0)
    g.frame("FrA1", {"R": "arg4 t₀", "L": "arg3 t₀", "sf0": SF0})
    # after start_2: che/ac/idaac slots stored too (shared by the dequant slices DqCpl/DqSce)
    g.frame("FrD", FRD)
    # shared exit of DqCpl / DqSce: `movl $0, 0x28928(%r9)` (sbr->ready_for_dequant = 0)
    g.entry("L74de", "(ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀"
            " ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))")
    g.entry("start_1", "ApplyC x t₀ ∧ Base t₀ s ∧ ArgRegs t₀ s ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrA x t₀))")
    g.entry("start_2", "ApplyC x t₀ ∧ BaseZ t₀ s ∧ ArgRegs t₀ s"
            " ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrA1 x t₀))")
    g.entry("L6797", "ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .rdi = arg0 t₀ ∧ s.regs.get64 .rdx = arg2 t₀"
            " ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))")
    # after start_2's `je L6817` (start = 0) or the inlined sbr_turnoff (L6797_1)
    g.entry("L6817", f"ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ {BL1}"
            " ∧ ∃ x' : Args, (x' = x ∨ x' = x.turnoff.spSet) ∧ IdLive t₀ x' ∧ (s.dmem =⋆ Mm k e x' ra t₀ (FrD x t₀))")
    # start_3: `jne L6825` on the flags of `cmpl $0, pushed` (start ≠ 0, ready ≠ 0: the dequant path, bl = 0)
    g.entry("start_3", f"(ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ {BL0}"
            " ∧ x.start ≠ 0 ∧ s.status.zf = decide (x.pushed = 0) ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))")
    # L676e / L6825: the kx_and_m_pushed step; bl = 1 (no dequant: start = 0) or bl = 0 (dequant, no turnoff)
    PRE = (f"ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ ∃ x' : Args, (x' = x ∨ x' = x.turnoff.spSet)"
           f" ∧ ({BL1} ∨ ({BL0} ∧ x' = x ∧ x.start ≠ 0))")
    g.entry("L676e", PRE + " ∧ x'.pushed = 0 ∧ IdLive t₀ x' ∧ (s.dmem =⋆ Mm k e x' ra t₀ (FrD x t₀))")
    g.entry("L6825", PRE + " ∧ x'.pushed ≠ 0 ∧ IdLive t₀ x' ∧ (s.dmem =⋆ Mm k e x' ra t₀ (FrD x t₀))")
    # dequant prologue (start ≠ 0, no turnoff: the state is x.push)
    DQ = "(ApplyC x t₀ ∧ IdLive t₀ x) ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ x.start ≠ 0"
    g.entry("L6838", DQ + " ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))")
    g.frame("FrE", dict(FRD, sc8="BitVec.ofNat 64 1"))
    g.entry("L6838_1", DQ + " ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrE x t₀))")
    g.entry("L6838_2", DQ + " ∧ s.regs.get64 .rbx = 1#64 ∧ s.regs.get64 .r12 = arg1 t₀ + 0x53670#64"
            " ∧ s.regs.get64 .r13 = arg1 t₀ + 0x538b0#64 ∧ (s.dmem =⋆ Mm k e x.push ra t₀ (FrD x t₀))")
    # `No quantized data read for sbr_dequant` (start ≠ 0, ready = 0): av_log, sbr_turnoff
    g.entry("L6f32", f"ApplyC x t₀ ∧ BaseZ t₀ s ∧ {BL1} ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))")
    g.entry("L6f32_1", f"ApplyC x t₀ ∧ BaseZ t₀ s ∧ {BL1} ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))")
    g.entry("L6f32_2", f"ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ {BL1}"
            " ∧ (s.dmem =⋆ Mm k e x.turnoff.spSet ra t₀ (FrD x t₀))")
    # Setup (L74de: after the dequant, ready_for_dequant = 0)
    g.entry("L74e9", "ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀"
            " ∧ ∃ y : Args, (x.Keep y ∧ IdLive t₀ y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrD x t₀))")
    # Setup L74e9_1..L74e9_4: the channel-level slots (FR_CH) are stored in four groups
    SB = "sbrA t₀ + {}#64"
    ch = g.FR_CH
    F1 = dict(FRD, sbr="sbrA t₀")
    # after L74e9_1 has copied the ds byte to slot ds, sf0 is dead until L74e9_4 overwrites it
    SF0B = ("cells", "1 ?@ (r - 0xf8#64) ⋆ 7 ?@ (r - 0xf7#64)")
    F2 = dict(F1, sf0=SF0B, **{n: ch[n] for n in ["ds", "dsp", "d0", "Xl", "a0", "a1"]})
    F3 = dict(F2, **{n: ch[n] for n in ["Xh", "fth", "ftl", "eom", "qmap", "smap"]})
    F4 = dict(F3, **{n: ch[n] for n in ["spp", "ecur", "qm", "sm", "gain", "X", "fth4", "ah1"]})
    g.frame("FrS1", F1)
    g.frame("FrS2", F2)
    g.frame("FrS3", F3)
    g.frame("FrS4", F4)
    GOT = 's.regs.get64 .rax = lab "_GLOBAL_OFFSET_TABLE_"'
    R1213 = (" ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r13 = sbrA t₀ + 0x5fdc0#64")
    R15 = ' ∧ s.regs.get64 .r15 = lab "sbr_qmf_window_ds"'
    KY = " ∧ ∃ y : Args, (x.Keep y ∧ IdLive t₀ y) ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ ({} x t₀))"
    g.entry("L74e9_1", "ApplyC x t₀ ∧ BaseZ t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ " + GOT + KY.format("FrS1"))
    g.entry("L74e9_2", "ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀ ∧ " + GOT + R1213
            + KY.format("FrS2"))
    g.entry("L74e9_3", "ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀" + R1213 + R15
            + " ∧ s.regs.get64 .rax = sbrA t₀ + 0x1c#64" + KY.format("FrS3"))
    g.entry("L74e9_4", "ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀" + R1213 + R15 + KY.format("FrS4"))
    g.entry("L6797_1", "ApplyC x t₀ ∧ BaseZ t₀ s ∧ (s.dmem =⋆ Mm k e x ra t₀ (FrD x t₀))")
    # ---------------- Syn (apply): ps_apply / memcpy, the two sbr_qmf_synthesis calls ----------------
    # IN from GainAsm (text agreed with dqsce)
    g.entry("L9a02", "∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀"
            " ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64"
            " ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))")
    SR = (" ∧ s.regs.get64 .rbx = arg0 t₀ ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64"
          " ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x)")
    MY = " ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))"
    g.entry("L9a02_1", "∃ ch c0, ApplyC x t₀ ∧ Base t₀ s" + SR + MY)
    g.entry("L9a69", "∃ ch c0, ApplyC x t₀ ∧ Base t₀ s" + SR
            + " ∧ s.regs.get64 .rax = arg1 t₀ + 0x81060#64" + MY)
    g.entry("L9a7d", "∃ ch c0, ApplyC x t₀ ∧ Base t₀ s" + SR + MY)
    g.entry("L9a85", "∃ ch c0, ApplyC x t₀ ∧ Base t₀ s ∧ s.regs.get64 .r9 = arg1 t₀" + SR + MY)
    # at the calls: rsp below the four pushed stack arguments (SynArgs, carved off the callees' area)
    RS = ("s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1e8#64 ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64"
          " ∧ s.regs.get64 .rbx = arg1 t₀ ∧ s.regs.get64 .r15 = arg0 t₀ ∧ s.regs.get64 .r13 = sbrA t₀ + 0x601e0#64"
          " ∧ s.regs.get64 .r12 = sbrA t₀ + 0x5fcc0#64 ∧ s.regs.get64 .r14 = BitVec.ofNat 64 (dsN x)")
    CA = (" ∧ s.regs.get64 .rdi = y.synCtx ∧ s.regs.get64 .rsi = e.fs.qfs.tx.toBitVec"
          " ∧ s.regs.get64 .rcx = y.fdsp ∧ s.regs.get64 .rdx = sbrA t₀ + 0x601e0#64")
    g.entry("L9a85_1", "∃ ch c0, ApplyC x t₀ ∧ " + RS + " ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀" + CA
            + " ∧ s.regs.get64 .r8 = arg3 t₀ ∧ s.regs.get64 .r9 = sbrA t₀ + 0x53b40#64"
            " ∧ (s.dmem =⋆ MmS k e y ra t₀ (SynArgs x t₀ 0) (FrCs x t₀ ch c0))")
    # after channel 0's synthesis: its v_off has a new value v within DWF's bounds (QmfFPost's VOffW);
    # ApplyC y still holds for the other fields (and channel 1)
    g.entry("L9a85_2", "∃ ch c0, ApplyC x t₀ ∧ " + RS + " ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀"
            " ∧ ∃ v : BitVec 32, v.toInt ≤ 1664 ∧ v.toNat % 8 = 0"
            " ∧ (s.dmem =⋆ Mm k e (y.setV0 v) ra t₀ (FrCs x t₀ ch c0))")
    RS3 = RS.replace("s.regs.get64 .rbx = arg1 t₀", "s.regs.get64 .rbx = arg1 t₀ + 0x41d60#64")
    g.entry("L9a85_3", "∃ ch c0, ApplyC x t₀ ∧ " + RS3 + " ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀" + CA
            + " ∧ s.regs.get64 .r8 = arg4 t₀ ∧ s.regs.get64 .r9 = sbrA t₀ + 0x58740#64"
            " ∧ ∃ v : BitVec 32, v.toInt ≤ 1664 ∧ v.toNat % 8 = 0"
            " ∧ (s.dmem =⋆ MmS k e (y.setV0 v) ra t₀ (SynArgs x t₀ 1) (FrCs x t₀ ch c0))")
    # after both syntheses: ApplyC of the new values (applyc_setV0/1), for ApplyFPost's SbrWF
    MK = " ∧ ∃ y : Args, x.Keep y ∧ ApplyC y t₀ ∧ (s.dmem =⋆ Mm k e y ra t₀ (FrCs x t₀ ch c0))"
    g.entry("L9a85_4", "∃ ch c0, ApplyC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x1e8#64"
            " ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64" + MK)
    g.entry("L9b24", "∃ ch c0, ApplyC x t₀ ∧ Base t₀ s" + MK)
    g.entry("L9b2b", "ApplyC x t₀ ∧ s.regs.get64 .rsp = t₀.regs.get64 .rsp - 0x30#64"
            " ∧ s.regs.get64 .rbp = t₀.regs.get64 .rsp - 8#64"
            " ∧ (s.dmem =⋆ Reserve (0x298 + k) (t₀.regs.get64 .rsp - 0x1c8#64) ⋆ (ApplyFPost e x t₀"
            " ⋆ FrRaw t₀ (RetCell ra (t₀.regs.get64 .rsp) ⋆ x.R)))")
    g.entry("done", "s.regs.get64 .rsp = t₀.regs.get64 .rsp ∧ s.regs.get64 .rbp = t₀.regs.get64 .rbp"
            " ∧ SavedRegs t₀ s ∧ (s.dmem =⋆ RetCell ra (t₀.regs.get64 .rsp)"
            " ⋆ (Reserve (applyNeed k) (t₀.regs.get64 .rsp) ⋆ (ApplyFPost e x t₀ ⋆ x.R)))")


_define_entries = define


def define(g):
    _define_entries(g)
    # variant: the prologue has no loop, but the layout's back edges make two Entry-region
    # "loops" (4,60) (L6f32_2/L6817 -> L676e) and (8,60) (L6f32_2 -> L6825); constant measures
    # order the blocks along the real (acyclic) control flow
    for i in ["L6f32", "L6f32_1", "L6f32_2"]:
        g.measure(i, ["1", "0"])
    for i in ["L6797", "L6797_1", "L6817"]:
        g.measure(i, ["1"])
    g.measure("L676e", ["0"])
