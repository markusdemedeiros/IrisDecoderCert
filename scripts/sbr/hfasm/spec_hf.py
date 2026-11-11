"""Label specification for sbr_hf_assemble."""
Y, X, S, C, EA = "arg0 t₀", "arg1 t₀", "arg2 t₀", "arg3 t₀", "arg4 t₀"
G, Q = f"{C} + 0x11130#64", f"{C} + 0x130b0#64"
KX, KM = "BitVec.ofNat 64 x.kx", "BitVec.ofNat 64 x.m"
SM = "x.smooth.setWidth 64"
XMM4 = "s.zmms.get (.xmm .mm4) = x.idx.setWidth 128"
R10 = "(s.regs.get64 .r10).toNat % 256 = if x.smooth = 0 then 1 else 0"
FC = {"ea": EA, "xkx": X, "y": Y, "kx": KX, "m": KM}
FP = dict(FC, gh=G, qb=Q, sbr=S, ch=C)

VALS = ["hC.2.2.2.2.2.2.1", "hC.2.2.2.2.2.2.2.1", "hC.2.2.2.2.2.2.2.2.1"]
PRE_VALS = """    have hkx := sext_ofInt32_nat x.kx (by have := hC.2.2.2.2.2.2.2.2.1; omega)
    have hmm := sext_ofInt32_nat x.m (by have := hC.2.2.2.2.2.2.2.1; omega)
"""


HEADS = ["La970", "Laa10", "Laab0", "Lab50", "Labf0", "Lac90", "Lad30", "Ladcc"]
CHECKS = ["La8f6", "La9c2", "Laa62", "Lab02", "Laba2", "Lac42", "Lace2", "Lad82", "Lae0d"]
H = "BitVec.ofNat 64 (hSL x)"


def te_reg(k):
    return f"s.regs.get64 .{'rax' if k % 2 else 'rcx'} = BitVec.ofNat 64 (x.te {k})"


def eregion(g):
    FE = dict(FP, sm4="x.smooth.toInt", xv="(x.idx.setWidth 128).toInt", s38=("d", "(x.nenv : Int)"),
              s48=H, s50=H)
    g.defframe("FE", FE)
    g.EXIT_FRAMES.append("FE")
    M4 = "BitVec.ofNat 64 (4 * x.m)"
    def CK(k):
        return ["HfC x t₀", "Base t₀ s", f"s.regs.get64 .r8 = {C}", f"s.regs.get64 .r13 = {M4}",
                f"s.regs.get64 .rsi = {H}", f"s.regs.get64 .r9 = {H}", "(s.regs.get64 .rdx).toNat % 2 ^ 32 = x.nenv",
                XMM4, f"{k} ≤ x.nenv", te_reg(k)]
    def VAR(k, extra="64"):
        return f"2000000 + {(8 - k) * 100} + {extra}"
    for k in range(1, 8):
        g.entry(CHECKS[k], CK(k), "FE", var=VAR(k))
    for k in range(8):
        sk = CK(k) + ([te_reg(k + 1)] if k < 7 else []) + [f"x.te {k} < x.te {k + 1}", f"{k + 1} ≤ x.nenv"]
        g.entry(f"s{k}", sk, "FE", var=VAR(k))
        if k < 7:
            rb, r13 = f"s.regs.get64 .rbx = {S} + {0x5f6c0 + 192 * k:#x}#64", f"s.regs.get64 .r13 = {M4}"
        else:
            rb, r13 = f"s.regs.get64 .rbx = {M4}", f"s.regs.get64 .r13 = {S} + {0x5f6c0 + 192 * k:#x}#64"
        hd = ["HfC x t₀", "Base t₀ s", rb, f"s.regs.get64 .r15 = {S} + {0x5eac0 + 192 * k:#x}#64", r13,
              f"x.te {k} * 2 ≤ (s.regs.get64 .r14).toNat", f"(s.regs.get64 .r14).toNat < x.te {k + 1} * 2",
              f"s.regs.get64 .r12 = {C} + 0x130b0#64 + BitVec.ofNat 64 (192 * (hSL x + (s.regs.get64 .r14).toNat))",
              f"{k + 1} ≤ x.nenv"]
        iv = VAR(k, "(64 - (s.regs.get64 .r14).toNat)")
        g.entry(HEADS[k], hd, "FE", var=iv)
        g.entry(f"c{k}", hd, "FE", var=iv)
        g.entry(f"d{k}", hd, "FE", var=iv)
        if k < 7:
            g.entry(f"x{k}", ["HfC x t₀", "Base t₀ s", f"s.regs.get64 .r8 = {C}", f"s.regs.get64 .r13 = {M4}",
                              te_reg(k + 1), f"{k + 1} ≤ x.nenv"], "FE", var=VAR(k, "0"))
    g.entry("Lae0d", ["HfC x t₀", "Base t₀ s", f"s.regs.get64 .r8 = {C}", "8 ≤ x.nenv"], "FE", var="2000000")
    g.entry("Lae20", ["HfC x t₀", "Base t₀ s", f"s.regs.get64 .r8 = {C}", XMM4, f"s.regs.get64 .r9 = {H}",
                       "1 ≤ x.nenv"], "FE", var="1999999")
    # blocks
    g.plain_block("La8f6", {"sm4", "xv", "s38", "s48", "s50", "m", "Te"}, [("s0", "fall"), ("La9c2", "jump")],
                  hb=3000000)
    for k in range(8):
        g.plain_block(f"s{k}", {"sbr"}, [(HEADS[k], "fall")], hb=2000000, extra_simp=", te_row")
        hh = (f"    have hte : x.te {k + 1} ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 {k + 1} (by omega)\n"
              "    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega\n")
        nf = len(g.ENTRY[HEADS[k]][0])
        hs = [f"h{j}" for j in range(2, nf)]
        pat = "⟨⟨h0, ⟨hrsp, hrbp⟩, " + ", ".join(hs) + ", hm⟩, hn⟩"
        fl = g.ENTRY[HEADS[k]][0]
        g.BLOCKS.append((HEADS[k], CALL_BLK(HEADS[k], pat, "FE", hs, pre=hh, facts=fl)))
        g.BLOCKS.append((f"c{k}", CALL_BLK(f"c{k}", pat, "FE", hs, pre=hh, facts=fl)))
        nxt = f"x{k}" if k < 7 else "Lae0d"
        g.plain_block(f"d{k}", {"ch", "Te"}, [(HEADS[k], "jump"), (nxt, "fall")], hb=2000000)
        if k < 7:
            g.plain_block(f"x{k}", {"xv", "s38", "s48", "s50"}, [(CHECKS[k + 1], "fall")], hb=2000000)
    for k in range(1, 8):
        g.plain_block(CHECKS[k], {"Te"}, [("Lae20", "jump"), (CHECKS[k + 1], "jump"), (f"s{k}", "fall")],
                      hb=2000000)
    g.plain_block("Lae0d", {"s38", "xv", "s48"}, [("Lae20", "fall")], hb=2000000)
    import mregion
    mregion.mregion(g, FE)


def define(g):
    g.defframe("FA", {}, saved_val=False)
    g.defframe("FB", {})
    g.defframe("FC", FC)
    g.defframe("FP", FP)
    g.entry("", [], "FA", var="3000000")
    g.entry("p1", ["HfC x t₀", "Base t₀ s", "ArgRegs t₀ s"], "FB", var="3000000")
    g.entry("p2", ["HfC x t₀", "Base t₀ s", f"s.regs.get64 .rdx = {S}", f"s.regs.get64 .rcx = {C}",
                   f"s.regs.get64 .r8 = {C}", f"s.regs.get64 .rdi = {Y}", f"s.regs.get64 .r14 = {SM}",
                   "s.regs.get64 .r9 = 0#64", R10], "FC", var="3000000")
    PF = ["HfC x t₀", "Base t₀ s", f"s.regs.get64 .r8 = {C}", f"s.regs.get64 .r14 = {SM}",
          "s.regs.get64 .r9 = 0#64", R10, XMM4]
    g.entry("r0", PF + ["x.smooth = 0"], "FP", var="3000000")
    g.entry("La8e1", PF, "FP", var="3000000")
    g.entry("La8ea", PF, "FP", var="3000000")
    g.entry("Lb426", PF, "FP", var="3000000")
    g.entry("La8f6", PF + ["(s.regs.get64 .rdx).toNat % 2 ^ 32 = x.nenv", "x.nenv ≠ 0"], "FP", var="2999999")
    # Lb426 copy (t_env_num_env_old rows -> t_env[0] rows), cut into y1..y14
    YF = PF + [f"s.regs.get64 .rsi = {G}",
          "s.regs.get64 .rax = BitVec.ofNat 64 (384 * x.te 0)", "s.regs.get64 .rcx = BitVec.ofNat 64 (384 * x.te 9)"]
    for j in range(1, 15):
        g.entry(f"y{j}", YF + ([f"s.regs.get64 .rdi = {Q}"] if j >= 3 else []), "FP", var="3000000")
    g.EXIT_FRAMES.append("FP")
    g.defframe("FR", dict(FP, sm4="x.smooth.toInt", xv="(x.idx.setWidth 128).toInt", s38=("b", "1")))
    RF = ["HfC x t₀", "Base t₀ s", "x.smooth = 0", f"s.regs.get64 .rbx = {G}",
          f"s.regs.get64 .r13 = {S} + 0x5eac0#64", f"s.regs.get64 .r14 = {S} + 0x5f6c0#64",
          "s.regs.get64 .r12 = BitVec.ofNat 64 (4 * x.m)"]
    RF2 = RF + [f"s.regs.get64 .r15 = {Q}"]
    g.entry("r1", RF, "FR", var="3000000")
    for i in range(2, 9):
        g.entry(f"r{i}", RF2, "FR", var="3000000")
    for i in range(8):
        base = G if i % 2 == 0 else Q
        o = "384 * x.te 0" + (f" + {192 * (i // 2)}" if i >= 2 else "")
        src = f"{S} + 0x5f6c0#64" if i % 2 == 0 else f"{S} + 0x5eac0#64"
        g.entry(f"r{i}c", (RF if i == 0 else RF2) + [f"s.regs.get64 .rdi = {base} + BitVec.ofNat 64 ({o})",
                f"s.regs.get64 .rsi = {src}", "s.regs.get64 .rdx = BitVec.ofNat 64 (4 * x.m)"], "FR", var="3000000")
    g.EXIT_FRAMES.append("FR")
    # G1: xmm4 (the new f_indexnoise/f_indexsine pair) is in range at the store; `done` returns the
    # cell as `HfIdxOut` (Spec.lean)
    XB = "(s.zmms.get (.xmm .mm4)).toNat % 2 ^ 32 ≤ 515 ∧ (s.zmms.get (.xmm .mm4)).toNat / 2 ^ 32 % 2 ^ 32 < 4"
    g.entry("Lb820", ["HfC x t₀", "Base t₀ s", f"s.regs.get64 .r8 = {C}", XB], "FZ", IC="8 ?@ (arg3 t₀ + 0x15aac#64)", var="0")
    g.entry("done", ["HfC x t₀", "s.regs.get64 .rsp = t₀.regs.get64 .rsp", "s.regs.get64 .rbp = t₀.regs.get64 .rbp",
                     "SavedRegs t₀ s"], "FZ", IC="HfIdxOut t₀", var="0")
    g.plain_block("", {"rbx", "r12", "r13", "r14", "r15", "rbp"}, [("p1", "fall")])
    g.plain_block("p1", {"ea", "xkx", "y", "kx", "m", "Sc"}, [("p2", "fall")], hb=3000000,
                  pre_tac="    have hC := h0\n" + PRE_VALS)
    g.plain_block("p2", {"gh", "qb", "sbr", "ch", "Sc", "IC"},
                  [("La8e1", "jump"), ("La8ea", "jump"), ("r0", "fall")], hb=3000000)
    g.plain_block("r0", {"sm4", "xv", "s38", "sbr", "m", "gh", "Te"}, [("r0c", "fall")], hb=3000000,
                  extra_simp=", te_row", pre_tac="    rw [s38_split0] at hm\n")
    g.plain_block("r1", {"ch", "qb", "Te"}, [("r1c", "fall")], hb=3000000, extra_simp=", te_row")
    for i in range(2, 8):
        g.plain_block(f"r{i}", {"ch", "Te"}, [(f"r{i}c", "fall")], hb=3000000, extra_simp=", te_row")
    g.plain_block("r8", {"s38", "xv", "sm4", "ch", "Te"}, [("La8f6", "jump", "FR"), ("Lb820", "jump", "FR")],
                  hb=3000000)
    g.plain_block("La8e1", set(), [("Lb426", "jump"), ("La8ea", "fall")])
    g.plain_block("La8ea", {"Te"}, [("Lb820", "jump", "FP"), ("La8f6", "fall")], hb=2000000)
    eregion(g)
    for i in range(8):
        nf = len(g.ENTRY[f"r{i}c"][0])
        hs = [f"h{j}" for j in range(2, nf)]
        pat = "⟨⟨h0, ⟨hrsp, hrbp⟩, " + ", ".join(hs) + ", hm⟩, hn⟩"
        g.BLOCKS.append((f"r{i}c", CALL_BLK(f"r{i}c", pat, "FR", hs)))
    g.BLOCKS.append(("Lb820", EXIT_BLK("Lb820", "⟨⟨h0, ⟨hrsp, hrbp⟩, h8, hm⟩, hn⟩")))
    g.BLOCKS.append(("done", EXIT_BLK("done", "⟨⟨h0, hrsp, hrbp, hsv, hm⟩, hn⟩")))


def CALL_BLK(l, pat, fr, hs, hb=2000000, pre="", facts=None):
    # only equation facts go into `simp at *` (inequalities would be simped to True)
    if facts is not None:
        hs = [h for h in hs if (lambda f: " = " in f and not any(c in f for c in "≤<≠"))(facts[int(h[1:])])]
    hsl = "".join(", " + h for h in hs)
    return f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats {hb} in
theorem blk_{l} (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.{l}" := by
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "{l}"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain {pat} := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
{pre}    simp only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ {fr} x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd{g_RBPO()}, qrow_g, hrbp{hsl}] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'
"""


def g_RBPO():
    import gen
    return gen.RBPO


def EXIT_BLK(l, pat):
    return f"""set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
theorem blk_{l} (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.{l}" := by
  clear hc
  cfg_block
  measure_hb "{l}"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain {pat} := hs₀
    simp only [T, FZ, Saved, Rest] at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp only [Rest, T, FZ, Saved, AddrIndex.offset64, BitVec.add_zero] at *
    all_goals try call_simp
    all_goals first | omega | with_reducible assumption | grind_cells'
"""
