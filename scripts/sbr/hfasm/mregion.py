"""Main region (Lae20 .. Lb400) of sbr_hf_assemble: frames, table entries, variant.

Design (hfasm, 19:50):
  frames  FMa (m1): FE + s50 = Y+8kx, xkx = X+320kx, s38 one blank qword, s48 blank
          FMb (m2): FMa + sm = S+0x5f0c0, gh = G+192h           (kx1, vec stay blank)
          FM  (m3): FMb + m4, m16, qh = Q+192h, ykx8 = Y+8kx+8, mz = m, mm1 = m-1
          FL0 (Laf40, Lb400): FM with xv, y blank (written in the loop)
          FL e (iteration labels): FL0 + sme = S+0x5f0c0+192e, s48 = e+1
  e = r10 (r15 between the hf_g_filt call and a1), i = r15 (rbx-derived after the call).
  xmm4 bound XB: low 32 bits ≤ 515 (f_indexnoise; after the first update the mask
  LCPI17_11 = (0x1ff, 3, 0, 0) gives ≤ 511 and idxsine ≤ 3).
  variant: C(e) = 1900000 - 100000 e, minus 2000 i, plus a per-label offset in layout
  order (Lafd9 1900, Lb248 group 1890..1150 with inner-loop terms, Lb000 1100,
  Lb01d 1000, g1 900, Lb08f 800, n1 700, n2 600, Lb140 400 + (100 - rdi), Lb16c 300,
  Lb1a0 200, a1 150, Lafa0 100); Laf40 C(e)+1999; Lb400 C(e)-90000.
"""
from spec_hf import Y, X, S, C, G, Q, KX, KM, H, XMM4

# slot values in the form the instructions compute them (lea (rdi,rdx,8); lea+shl+add)
Y8 = f"{Y} + {KX} * 8#64"
X320 = f"({KX} + {KX} * 4#64) <<< 6 + {X}"
XB = "(s.zmms.get (.xmm .mm4)).toNat % 2 ^ 32 ≤ 515 ∧ (s.zmms.get (.xmm .mm4)).toNat / 2 ^ 32 % 2 ^ 32 < 4"
E = "(s.regs.get64 .r10).toNat"
I = "(s.regs.get64 .r15).toNat"


def CE(e):
    return f"(1900000 - 100000 * {e})"


def mregion(g, FE):
    FMa = dict(FE, s50=Y8, xkx=X320, s38=("q", None))
    FMa.pop("s48", None)
    g.defframe("FE1", dict(FE, s50=Y8, xkx=X320))
    g.defframe("FMa", FMa)
    FMb = dict(FMa, sm=f"{S} + 0x5f0c0#64", gh=f"{G} + BitVec.ofNat 64 (192 * hSL x)")
    g.defframe("FMb", FMb)
    FM = dict(FMb, m4="BitVec.ofNat 64 (x.m / 4 * 4)", m16="BitVec.ofNat 64 (16 * (x.m / 4))",
              qh=f"{Q} + BitVec.ofNat 64 (192 * hSL x)", ykx8=f"{Y} + BitVec.ofNat 64 (8 * x.kx + 8)",
              )   # rsp-0xc0 (m) and rsp-0xf8 (m - 1) are stored by m3 itself: blank in FM
    g.defframe("FM", FM)
    FMx = dict(FM, mz=KM, mm1="BitVec.ofNat 64 (x.m - 1)")   # after m3's store
    g.defframe("FMx", FMx)
    FL0 = dict(FMx)
    FL0.pop("xv", None)
    FL0.pop("y", None)
    g.defframe("FL0", FL0)
    g.defframe("FL", dict(FL0, sme=f"{S} + 0x5f0c0#64 + BitVec.ofNat 64 (192 * e)", s48="BitVec.ofNat 64 (e + 1)"),
               params=" (e : Nat)")
    B = ["HfC x t₀", "Base t₀ s"]
    R8 = f"s.regs.get64 .r8 = {C}"
    g.entry("m1", B + [R8, XMM4, f"s.regs.get64 .r9 = {H}", f"s.regs.get64 .rsi = {KM}",
                       f"s.regs.get64 .rdx = {KX}", f"s.regs.get64 .rdi = {Y}",
                       f"s.regs.get64 .rcx = {KM}", "1 ≤ x.nenv"], "FMa", var="1999998")
    g.entry("m2", B + [R8, XMM4, f"s.regs.get64 .rcx = {KM}", "s.regs.get64 .r9 = BitVec.ofNat 64 (x.m - 1)", f"s.regs.get64 .rdx = {KX}",
                       f"s.regs.get64 .rdi = {Y}", f"s.regs.get64 .r10 = {S}",
                       "s.regs.get64 .rax = BitVec.ofNat 64 (192 * hSL x)", "1 ≤ x.nenv"], "FMb", var="1999997")
    g.entry("m3", B + [R8, XMM4, f"s.regs.get64 .rcx = {KM}", "s.regs.get64 .r9 = BitVec.ofNat 64 (x.m - 1)",
                       f"s.regs.get64 .r14 = {S} + 0x5f0c4#64", "s.regs.get64 .r10 = 0#64", "1 ≤ x.nenv"], "FM", var="1999996")
    LH = B + [R8, XB, f"s.regs.get64 .rcx = {KM}", f"{E} < x.nenv",
              f"s.regs.get64 .r14 = {S} + 0x5f0c4#64 + BitVec.ofNat 64 (192 * {E})"]
    g.entry("Laf40", LH, "FL0", var=f"{CE(E)} + 1999")
    # Lb400: rdi = e + 1 (from lea / s48), r14 still row e
    g.entry("Lb400", B + [R8, XB, f"s.regs.get64 .rcx = {KM}", "1 ≤ (s.regs.get64 .rdi).toNat", "(s.regs.get64 .rdi).toNat ≤ x.nenv",
                          f"s.regs.get64 .r14 = {S} + 0x5f0c4#64 + BitVec.ofNat 64 (192 * ((s.regs.get64 .rdi).toNat - 1))"],
            "FL0", var=f"{CE('((s.regs.get64 .rdi).toNat - 1)')} - 90000")
    # iteration labels (e = r10, i = r15), frame FL e
    def IT(e, i):
        return B + [R8, XB, f"s.regs.get64 .rcx = {KM}", f"{e} < x.nenv", f"x.te {e} * 2 ≤ {i}", f"{i} < x.te ({e} + 1) * 2",
                    f"s.regs.get64 .r12 = {Q} + BitVec.ofNat 64 (192 * (hSL x + {i}))",
                    f"s.regs.get64 .r11 = {Y} + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * {i})",
                    f"s.regs.get64 .r14 = {S} + 0x5f0c4#64 + BitVec.ofNat 64 (192 * {e})"]
    def V(off, e=E, i=I):
        return f"{CE(e)} - 2000 * {i} + {off}"
    # Lafa0: i = old i; xmm4 is recomputed (masked) inside, so no XB
    g.entry("Lafa0", [f for f in IT(E, I) if f != XB], "FL", args=[E], var=V(100))
    g.entry("Lafd9", IT(E, I), "FL", args=[E], var=V(1900))
    g.entry("Lb000", IT(E, I), "FL", args=[E], var=V(1100))
    g.entry("Lb01d", IT(E, I) + [
        f"(s.regs.get64 .rdx = {G} + BitVec.ofNat 64 (192 * (hSL x + {I})) ∧ s.regs.get64 .r13 = {Q} + BitVec.ofNat 64 (192 * {I}))"
        f" ∨ (s.regs.get64 .rdx = t₀.regs.get64 .rsp - 0x288#64 ∧ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x1c8#64)"],
        "FL", args=[E], var=V(1000))
    # ---- after Lb01d: frame FL2 e i v (y = row pointer, s38 = i, xv = v); i and v read back
    # from their frame cells (the registers holding them are clobbered by the calls)
    FL2 = dict(FL0, sme=f"{S} + 0x5f0c0#64 + BitVec.ofNat 64 (192 * e)", s48="BitVec.ofNat 64 (e + 1)",
               y=f"{Y} + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * i)", s38=("q", "BitVec.ofNat 64 i"),
               xv="v.toInt")
    P2 = " (e : Nat) (i : Nat) (v : BitVec 128)"
    g.defframe("FL2", FL2, params=P2)
    # FL2 without g_filt_tab: the caller's part of the frame across the hf_g_filt call
    g.defframe("FL2g", dict(FL2, gtab="OMIT"), params=P2)
    # FL2 with q_filt_tab out (the hf_apply_noise call reads it)
    g.defframe("FL2q", dict(FL2, qtab="OMIT"), params=P2)
    LB01D_T = {"slot", "kx", "s50", "xkx", "sbr", "y", "s38", "xv", "Fn"}
    g.LEMMAS.append(g.view_lemma("Lb01d_pre", "FL", "IdxC x t₀", LB01D_T))
    g.LEMMAS.append(g.view_lemma("Lb01d_post_g1", "FL2", "IdxC x t₀", LB01D_T))
    g.LEMMAS.append(g.view_lemma("FL2_s38", "FL2", "IdxC x t₀", {"s38"}))
    g.LEMMAS.append(g.view_lemma("FL2_xv", "FL2", "IdxC x t₀", {"xv"}))
    g.LEMMAS.append(g.view_lemma("FL_kx", "FL", "IdxC x t₀", {"kx"}))
    g.LEMMAS.append(g.view_lemma("Lb1a0_pre", "FL2", "IdxC x t₀", {"slot", "sme", "kx", "m", "sbr", "Fn"}))
    import os as _os
    DEV = bool(_os.environ.get("HFASM_DEV"))   # call-block lemmas under development (hfasm only)
    # call-block lemmas (tested; always on since 23:15)
    if True:
        g.LEMMAS.append(open(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "lb01d_dev.lean")).read())
    if _os.path.exists(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "dev2.lean")):  # Lb1a0 noise-index lemmas
        g.LEMMAS.append(open(_os.path.join(_os.path.dirname(_os.path.abspath(__file__)), "dev2.lean")).read())
    IM = "(BitVec.ofInt 64 ((s.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat"
    XV = "BitVec.ofInt 128 ((s.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0)"
    E15 = "(s.regs.get64 .r15).toNat"
    def G1F(e):
        return B + [f"{e} < x.nenv", f"({XV}).toNat % 2 ^ 32 ≤ 515", f"({XV}).toNat / 2 ^ 32 % 2 ^ 32 < 4",
                    f"x.te {e} * 2 ≤ {IM}", f"{IM} < x.te ({e} + 1) * 2",
                    f"s.regs.get64 .rbx = {Y8} + BitVec.ofNat 64 (512 * {IM})",
                    f"s.regs.get64 .r12 = {Q} + BitVec.ofNat 64 (192 * (hSL x + {IM}))",
                    f"s.regs.get64 .r13 = {Q} + BitVec.ofNat 64 (192 * {IM}) ∨ s.regs.get64 .r13 = t₀.regs.get64 .rsp - 0x1c8#64",
                    f"s.regs.get64 .r14 = {S} + 0x5f0c4#64 + BitVec.ofNat 64 (192 * {e})"]
    # the variant has no t₀: read i through rsp (rsp = rsp0 - 0x288 inside the body)
    IMs = "(BitVec.ofInt 64 ((s.dmem.loadInt (s.regs.get64 .rsp + 0x248#64) 8).getD 0)).toNat"
    def V2(off, e):
        return f"{CE(e)} - 2000 * {IMs} + {off}"
    g.entry("g1", G1F(E15), "FL2", args=[E15, IM, XV], var=V2(900, E15))
    # entering g1 / a1 (after a call): i, v, e explicit; the frame cells give IM = i, XV = v
    def rb_tbl(l):
        fl = g.ENTRY[l][0]
        sub = lambda f: f.replace(IM, "i").replace(XV, "v").replace(E15, "e")
        hyps = [sub(f) for f in fl] + ["s.regs.get64 .r15 = BitVec.ofNat 64 e",
                                       "s.dmem =⋆ T k fs x ra t₀ (IdxC x t₀) (FL2 x t₀ e i v)"]
        n = len(fl)
        hs = ", ".join(f"h{j}" for j in range(n))
        shown = " ∧ ".join([f"({f})" for f in fl] + [g.mem_of(l)])
        g.LEMMAS.append(f"""theorem {l}_tbl_rb (k : Nat) (fs : HfFns) (x : HfArgs) (ra : Int64) (t₀ s : MachineData)
    (e i : Nat) (v : BitVec 128) :
    ({" ∧ ".join("(" + h + ")" for h in hyps)}) →
    table k fs x ra t₀ "{g.lab(l)}" s := by
  rintro ⟨{hs}, h15, hm⟩
  have hte := h0.2.2.2.2.2.2.2.2.2.2.1 (e + 1) (by omega)
  have hI := FL2_read_i hm (by omega)
  have hV := FL2_read_v hm
  have hE : (s.regs.get64 .r15).toNat = e := by rw [h15, BitVec.toNat_ofNat]; omega
  show {shown}
  rw [hI, hV, hE]
  exact ⟨{hs}, hm⟩
""")

    g.entry("Lb08f", G1F(E) + [f"s.regs.get64 .r10 = s.regs.get64 .r15"], "FL2", args=[E, IM, XV], var=V2(800, E))
    N2 = G1F(E) + [R8, "s.regs.get64 .r9 = BitVec.ofNat 64 (x.m - 1)", f"s.regs.get64 .rcx = {KM}",
                   f"s.regs.get64 .r11 = {Y} + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * {IM})",
                   f"s.regs.get64 .r15 = BitVec.ofNat 64 {IM}", "(s.regs.get64 .rdx).toNat < 2"]
    g.entry("n2", N2 + ["2 ≤ x.m"], "FL2", args=[E, IM, XV], var=V2(600, E))
    RDI = "(s.regs.get64 .rdi).toNat"
    g.entry("Lb140", N2 + [f"s.regs.get64 .rsi = {Y} + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * {IM} + 4 * (s.regs.get64 .rdx).toNat)",
                           f"{RDI} % 2 = 0", f"{RDI} + 1 < x.m"], "FL2", args=[E, IM, XV],
            var=V2(f"400 + (100 - {RDI})", E))
    g.entry("Lb16c", N2 + [f"{RDI} % 2 = 0", f"{RDI} ≤ x.m"], "FL2", args=[E, IM, XV], var=V2(300, E))
    g.entry("Lb1a0", G1F(E) + [f"(s.regs.get64 .rcx).toNat % 2 ^ 32 = ({XV}).toNat / 2 ^ 32 % 2 ^ 32",
                               "s.regs.get64 .r15 = s.regs.get64 .r10", f"s.zmms.get (.xmm .mm3) = {XV}"],
            "FL2", args=[E, IM, XV], var=V2(200, E))
    g.entry("a1", G1F(E15), "FL2", args=[E15, IM, XV], var=V2(150, E15))
    if True:
        rb_tbl("g1")
        rb_tbl("a1")
    # ---- filter path (sm4 = 0, e ∉ e_a, so smoothing is on and h = 4); frame FL e, gtab/qtab blank
    FI = IT(E, I) + ["x.smooth = 0"]
    RAX = "(s.regs.get64 .rax).toNat"
    g.entry("Lb248", FI, "FL", args=[E], var=V(1890))
    g.entry("Lb26b", FI + ["4 ≤ x.m"], "FL", args=[E], var=V(1880))
    VF = FI + ["s.regs.get64 .rdx = BitVec.ofNat 64 (16 * (x.m / 4))", f"{RAX} % 16 = 0", f"{RAX} < 16 * (x.m / 4)"]
    g.entry("Lb280", VF, "FL", args=[E], var=V(f"1600 + (200 - {RAX})"))
    g.entry("v1", VF, "FL", args=[E], var=V(f"1600 + (200 - {RAX})"))
    g.entry("v2", FI, "FL", args=[E], var=V(1500))
    WF = FI + [f"{RAX} < x.m"]
    g.entry("Lb340", WF, "FL", args=[E], var=V(f"1200 + (100 - {RAX})"))
    g.entry("w1", WF, "FL", args=[E], var=V(f"1200 + (100 - {RAX})"))
    g.entry("w2", FI, "FL", args=[E], var=V(1150))
    # blocks
    g.plain_block("Lae20", {"s50", "xkx", "y", "kx", "m"}, [("m1", "fall", "FE1")], hb=2000000)
    # h = hSL x is 0 or 4: split so the `shl $6` / `lea (r9,r9,2)` arithmetic is on literals
    g.plain_block("m1", {"sbr", "sm", "kx1", "gh", "vec"}, [("m2", "fall")], hb=3000000,
                  pre_tac="    by_cases hsm : x.smooth = 0 <;> simp only [hSL, hsm, if_true, if_false, ite_true, ite_false] at *\n",
                  extra_simp=", hSL, hsm, BitVec.reduceShiftLeft, BitVec.reduceSetWidth, BitVec.reduceMul, BitVec.reduceOfNat")
    g.plain_block("m2", {"m4", "m16", "qh", "ykx8"}, [("m3", "fall")], hb=2000000)
    # generated attempts for the iteration labels (helpers override)
    V2A = [E, IM, XV]
    g.plain_block("Laf40", {"Te", "sm", "sme", "s48"}, [("Lb400", "jump"), ("Lafd9", "jump")], hb=3000000)
    g.plain_block("Lafa0", {"vec", "s48", "Te", "Data"}, [("Lb400", "jump", "FL", [E]), ("Lafd9", "fall")], hb=3000000)
    g.plain_block("Lafd9", {"sm4", "ea", "Ea"}, [("Lb000", "jump"), ("Lb248", "jump")], hb=3000000)
    g.plain_block("Lb000", {"gh", "qb"}, [("Lb01d", "fall")], hb=2000000)
    g.plain_block("g1", {"ea", "Ea", "xv"}, [("Lb08f", "jump"), ("Lb1a0", "jump"), ("Lb08f", "fall")], hb=3000000)
    g.plain_block("a1", {"xv", "ch", "mz", "Data", "y", "s38"}, [("Lafa0", "jump", "FL2", V2A)], hb=3000000)
    g.plain_block("Lb08f", {"kx", "kx1", "mz", "ch", "mm1", "Data", "y", "s38"}, [("n2", "fall"), ("Lb16c", "jump")], hb=3000000)
    g.plain_block("n2", set(), [("Lb140", "fall")], hb=2000000)
    g.plain_block("Lb140", {"Data"}, [("Lb140", "jump"), ("Lb16c", "fall")], hb=3000000)
    g.plain_block("Lb16c", {"sme", "Data"}, [("Lafa0", "jump", "FL2", V2A)], hb=3000000)
    g.plain_block("Lb248", {"m"}, [("Lb01d", "jump"), ("Lb26b", "jump"), ("Lb340", "jump")], hb=2000000)
    g.plain_block("Lb26b", {"m16"}, [("Lb280", "fall")], hb=2000000)
    g.plain_block("Lb280", {"Data"}, [("v1", "fall")], hb=3000000)
    g.plain_block("v1", {"Data", "gtab", "qtab"}, [("Lb280", "jump"), ("v2", "fall")], hb=3000000)
    g.plain_block("v2", {"m4"}, [("Lb01d", "jump"), ("Lb340", "fall")], hb=2000000)
    g.plain_block("Lb340", {"Data"}, [("w1", "fall")], hb=3000000)
    g.plain_block("w1", {"Data", "gtab", "qtab"}, [("Lb340", "jump"), ("w2", "fall")], hb=3000000)
    g.plain_block("w2", set(), [("Lb01d", "jump")], hb=2000000)
    g.EXIT_FRAMES.append("FL0")
    g.plain_block("Lb400", {"Te"}, [("Lb820", "jump", "FL0"), ("Laf40", "jump")], hb=2000000)
    g.plain_block("m3", {"mz", "mm1", "Data"}, [("Laf40", "fall", "FMx")], hb=2000000)
