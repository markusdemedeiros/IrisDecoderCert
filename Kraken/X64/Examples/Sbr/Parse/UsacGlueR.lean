import Kraken.X64.Examples.Sbr.Parse.UsacSpec
import Kraken.X64.Examples.Sbr.Parse.DecExtGlueH

/-!
# `ff_aac_sbr_decode_usac_data`: the `sbr_make_f_tablelim` and `sbr_reset` adapters

The callees' own statements (`Reset.TlimSpec`, `Reset.ResetSpec`) give the local contracts of
`UsacSpec` (`TablelimSpec`, `ResetSpec`).

* `u_widen`: a contract of the form of `UsacSpec`'s callee contracts with `need` bytes of stack
  holds with any `k ≥ need`; the excess joins the caller's memory.
* `adr`: address sums are rewritten to `adr` before `ac_rfl` regroups a footprint (`ac_rfl`
  would also normalise the sums, and recurses too deep on the large footprints).
* The caller's `UF` is the callee's footprint and a frame, passed as the callee's caller memory;
  `Oth` is taken through an equation (`Oth = BwR ⋆ O`, `Oth = CstR ⋆ (BwR ⋆ O)`), so that the
  adapters compose with any session layout.
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

/-! ## Tools -/

/-- An address sum that `ac_rfl` does not look into. -/
def adr (a b : BitVec 64) : BitVec 64 := a + b

theorem add_adr (a b : BitVec 64) : a + b = adr a b := rfl

/-- The six bytes of `spectrum_params` as one cell. -/
theorem sp_join (sp : List UInt8) (s : BitVec 64) (hl : sp.length = 6) :
    (sp.take 4 =@ (s + 0x1c#64) ⋆ sp.drop 4 =@ (s + 0x20#64)) = sp =@ (s + 0x1c#64) := by
  have hlen : (sp.take 4).length + (sp.drop 4).length ≤ 2 ^ 64 := by
    simp only [List.length_take, List.length_drop, hl]; omega
  have h := At_append_sep (sp.take 4) (sp.drop 4) (s + 0x1c#64) hlen
  rw [List.take_append_drop] at h
  have ea : s + 0x1c#64 + BitVec.ofNat 64 (sp.take 4).length = s + 0x20#64 := by
    rw [List.length_take, hl, BitVec.add_assoc]; rfl
  rw [ea] at h
  simp only [Val.eq]
  exact h.symm

variable [CodeEnv]

/-- `CPre` with `need` bytes of stack. -/
abbrev CPreN (need : Nat) (Ext Oth : Mem 64 → Prop) (A : UA) (ra : Int64) (t : MachineData) :
    Prop :=
  CallPre need (UF A.1 A.2 ⋆ A.1.R) ra t ∧ QE Ext Oth A.1

/-- `CPost` with `need` bytes of stack. -/
abbrev CPostN (need : Nat) (Rel : USt → USt → Prop) (A : UA) (ra : Int64) (t s : MachineData) :
    Prop :=
  ∃ st', Rel A.2 st' ∧ CallPost need (UF A.1 st' ⋆ A.1.R) ra t s

/-- A callee contract on `UF` with `need` bytes of stack holds with `k ≥ need` bytes. -/
theorem u_widen {f : Int64} {need k : Nat} {Ext Oth : Mem 64 → Prop}
    {C : UA → Int64 → MachineData → Prop} {Rel : UA → USt → USt → Prop}
    (h : ProcSpecA f (fun A ra t => CPreN need Ext Oth A ra t ∧ C A ra t)
      (fun A => CPostN need (Rel A) A))
    (hC : ∀ (A : UA) (R : Mem 64 → Prop) ra t, C A ra t → C ({ A.1 with R := R }, A.2) ra t)
    (hR : ∀ (A : UA) (R : Mem 64 → Prop) st', Rel ({ A.1 with R := R }, A.2) A.2 st' →
      Rel A A.2 st')
    (hk : need ≤ cneed k) (_hk' : cneed k ≤ 2 ^ 64) :
    ProcSpecA f (fun A ra t => CPre k Ext Oth A ra t ∧ C A ra t)
      (fun A => CPost k (Rel A) A) := by
  intro A ra t ⟨⟨hcall, hq⟩, hc⟩
  have e := Reserve.excess need (cneed k) (t.regs.get64 .rsp) hk (CallPre.le hcall)
  refine eventually_weaken _ _ _ _ ?_
    (h ({ A.1 with R := A.1.R ⋆ (cneed k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 (cneed k)) },
      A.2) ra t ⟨⟨?_, hq⟩, hC A _ ra t hc⟩)
  · rintro st (⟨hra, st', hp, h1, h2, h3, hm⟩ | hab)
    · refine Or.inl ⟨hra, st', hR A _ st' hp, h1, h2, h3, ?_⟩
      have hm' : st.1.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
          ⋆ (UF A.1 st' ⋆ (A.1.R
            ⋆ (cneed k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 (cneed k))))) := hm
      rw [e]
      exact Mem.ac hm'
    · exact Or.inr hab
  · show t.dmem =⋆ RetCell ra (t.regs.get64 .rsp) ⋆ (Reserve need (t.regs.get64 .rsp)
        ⋆ (UF A.1 A.2 ⋆ (A.1.R ⋆ (cneed k - need) ?@ (t.regs.get64 .rsp - .ofNat 64 (cneed k)))))
    unfold CallPre at hcall
    rw [e] at hcall
    exact Mem.ac hcall

/-! ## `sbr_make_f_tablelim` -/

/-- `SHW` without `bs_limiter_bands` and `kx[1]`. -/
abbrev ShT (c : BitVec 64) (st : USt) : Mem 64 → Prop :=
  let s := sA c
  cell4 s st.x.sampleRate ⋆ (cell4 (s + 0x4#64) st.x.start ⋆ (cell4 (s + 0x8#64) st.x.ready
    ⋆ (cell4 (s + 0xc#64) st.x.idAac ⋆ (cell4 (s + 0x10#64) st.u ⋆ (4 ?@ (s + 0x14#64)
    ⋆ (cell4 (s + 0x18#64) st.x.reset ⋆ (st.sp.take 4 =@ (s + 0x1c#64)
    ⋆ (st.sp.drop 4 =@ (s + 0x20#64) ⋆ (2 ?@ (s + 0x22#64)
    ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (4 ?@ (s + 0x28#64) ⋆ (c4 (s + 0x30#64) st.x.limGains
    ⋆ (cell4 (s + 0x34#64) st.x.interpol ⋆ (cell4 (s + 0x38#64) st.x.smooth
    ⋆ (cell4 (s + 0x3c#64) st.x.coupling ⋆ (c4 (s + 0x40#64) st.x.k0 ⋆ (16 ?@ (s + 0x44#64)
    ⋆ (c4 (s + 0x54#64) st.x.kx0 ⋆ (c4 (s + 0x5c#64) st.x.m0
    ⋆ (c4 (s + 0x60#64) st.x.m1 ⋆ (cell4 (s + 0x64#64) st.x.pushed
    ⋆ 24 ?@ (s + 0x68#64))))))))))))))))))))))

/-- `TWc` without the cells of `sbr_make_f_tablelim`. -/
abbrev TwT (c : BitVec 64) (x : Args) : Mem 64 → Prop :=
  let s := sA c
  c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq ⋆ (98 ?@ (s + 0x4c1f0#64)
    ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64) ⋆ (2 ?@ (s + 0x4c32e#64)
    ⋆ x.pstart =@ (s + 0x4c33a#64))))))

/-- The caller's part at the `sbr_make_f_tablelim` call. -/
abbrev FrT (q : UQ) (st : USt) (O : Mem 64 → Prop) : Mem 64 → Prop :=
  ShT q.c st ⋆ (TwT q.c st.x ⋆ (DSc q.c 0 st.x.d0 ⋆ (DRaw q.c 0 ⋆ (DSc q.c 1 st.x.d1
    ⋆ (DRaw q.c 1 ⋆ (AcU q.a st.x ⋆ (GbU q st.i ⋆ (Blocks [(q.buf, q.L), (lab "ceil_log2", 6)]
    ⋆ (Grid.JtW ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ (q.Ext ⋆ (O ⋆ q.R))))))))))))

theorem uf_tl (q : UQ) (st : USt) (O : Mem 64 → Prop) (hO : q.Oth = Reset.BwR ⋆ O)
    (t : MachineData) (h0 : arg0 t = sA q.c) :
    UF q st ⋆ q.R = Reset.TlimF (BitVec.ofNat 32 st.h.lb) st.x t ⋆ FrT q st O := by
  simp only [UF, SHW, TWc, RdU, hO, Reset.TlimF, h0, FrT, ShT, TwT, Reset.BwR, add_adr]
  ac_rfl

/-- **`sbr_make_f_tablelim`'s adapter.** -/
theorem usac_tlim_glue (k kt : Nat) (Ext Oth O : Mem 64 → Prop) (hO : Oth = Reset.BwR ⋆ O)
    (hk : Reset.tlimNeed kt ≤ Usac.cneed k) (hk' : Usac.cneed k ≤ 2 ^ 64)
    (hT : Reset.TlimSpec kt) : Usac.TablelimSpec k Ext Oth := by
  refine u_widen (need := Reset.tlimNeed kt) (ProcSpec.toA ?main) ?hc ?hr hk hk'
  case hc => exact fun _ _ _ _ h => h
  case hr => exact fun _ _ _ h => h
  apply DecExt.ProcSpec.adapt hT
  intro A ra t ⟨⟨hcall, hqe, hqo⟩, h0, hsc, htw, hn0, hnp, hlb, hlens, hnw⟩
  have hO' : A.1.Oth = Reset.BwR ⋆ O := hqo.trans hO
  refine ⟨(FrT A.1 A.2 O, BitVec.ofNat 32 A.2.h.lb, A.2.x), ⟨?_, ?_⟩, ?_⟩
  · show t.dmem =⋆ _ ⋆ (_ ⋆ (Reset.TlimF (BitVec.ofNat 32 A.2.h.lb) A.2.x t ⋆ FrT A.1 A.2 O))
    rw [← uf_tl A.1 A.2 O hO' t h0]
    exact hcall
  · show Reset.TlimC (BitVec.ofNat 32 A.2.h.lb) A.2.x t
    obtain ⟨w1, -, -, w4, w5, -, -, -, w9, -, -, -, w13, -, -, -, -, -, -, -, w21⟩ := htw
    obtain ⟨-, -, -, s4, -, -, -, s8, -, -, s11, s12⟩ := hsc
    have hl : (BitVec.ofNat 32 A.2.h.lb).toNat = A.2.h.lb := by
      rw [BitVec.toNat_ofNat]; omega
    refine ⟨by omega, s8, s12, fun _ => by omega, w1, w4, w5, ⟨w9, w13⟩, w21, s4, by omega, ?_⟩
    rw [h0]; omega
  · intro s ⟨y, hy, hsr, hbp, hsv, hm⟩
    have hl : (BitVec.ofNat 32 A.2.h.lb).toNat = A.2.h.lb := by
      rw [BitVec.toNat_ofNat]; omega
    rw [hl] at hy
    obtain ⟨fl, nl, rfl⟩ := DecExt.tablelim_keep hy
    obtain ⟨l1, l2, l3, -, l5, l6, l7⟩ := hlens
    refine ⟨{ A.2 with x := DecExt.limSet A.2.x fl nl }, ⟨_, hy, rfl,
      l1, l2, l3, DecExt.tablelim_len hy, l5, l6, l7⟩, hsr, hbp, hsv, ?_⟩
    rw [uf_tl A.1 _ O hO' t h0]
    exact hm

/-! ## `sbr_reset` -/

/-- The scalar cells of `*sbr` that `sbr_reset` does not hold. -/
abbrev ShR (c : BitVec 64) (st : USt) : Mem 64 → Prop :=
  let s := sA c
  cell4 (s + 0xc#64) st.x.idAac ⋆ (4 ?@ (s + 0x14#64) ⋆ (cell4 (s + 0x18#64) st.x.reset
    ⋆ (2 ?@ (s + 0x22#64) ⋆ (cell4 (s + 0x24#64) st.amp ⋆ (4 ?@ (s + 0x28#64)
    ⋆ (c4 (s + 0x30#64) st.x.limGains ⋆ (cell4 (s + 0x34#64) st.x.interpol
    ⋆ (cell4 (s + 0x38#64) st.x.smooth ⋆ (cell4 (s + 0x3c#64) st.x.coupling
    ⋆ (8 ?@ (s + 0x4c#64) ⋆ (c4 (s + 0x54#64) st.x.kx0 ⋆ (c4 (s + 0x5c#64) st.x.m0
    ⋆ (cell4 (s + 0x64#64) st.x.pushed ⋆ 20 ?@ (s + 0x6c#64))))))))))))))

/-- `DSc` without `e_a[1]` and `f_indexnoise`/`f_indexsine`. -/
abbrev DScR (c : BitVec 64) (ch : Nat) (v : DV) : Mem 64 → Prop :=
  let d := dAc c ch
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
    ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64)
    ⋆ (4 ?@ (d + 0x64#64) ⋆ (cell4 (d + 0x3900#64) v.vOff ⋆ (4 ?@ (d + 0x3904#64)
    ⋆ (c4 (d + 0x7920#64) v.ypos ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ v.tq =@ (d + 0x15aa6#64))))))))))))

/-- The caller's part at the `sbr_reset` call. -/
abbrev FrR (q : UQ) (st : USt) (O : Mem 64 → Prop) : Mem 64 → Prop :=
  ShR q.c st ⋆ (2 ?@ (sA q.c + 0x4c32e#64) ⋆ (DScR q.c 0 st.x.d0 ⋆ (DRaw q.c 0
    ⋆ (DScR q.c 1 st.x.d1 ⋆ (DRaw q.c 1 ⋆ (cell4 (q.a + 0x57f4#64) st.x.extRate
    ⋆ (GbU q st.i ⋆ (Blocks [(q.buf, q.L), (lab "ceil_log2", 6)] ⋆ (Grid.JtW
    ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ (O ⋆ q.R)))))))))))

/-- `sbr_reset`'s logical variable at `st`, with caller's memory `F`. -/
abbrev raOf (st : USt) (F : Mem 64 → Prop) : Reset.RArgs :=
  ⟨{ st.x with R := F }, st.sp, BitVec.ofNat 32 st.h.lb, st.u⟩

omit [CodeEnv] in
theorem blk_split (n k : Nat) (a b : BitVec 64) (hk : k ≤ n) (hn : n ≤ 2 ^ 64)
    (hb : a + BitVec.ofNat 64 k = b) : (n ?@ a) = k ?@ a ⋆ (n - k) ?@ b := by
  rw [Block.split_at a n k hk hn, hb]

theorem uf_r (e : Reset.REnv) (q : UQ) (st : USt) (O F : Mem 64 → Prop)
    (hO : q.Oth = Reset.CstR ⋆ (Reset.BwR ⋆ O)) (hE : q.Ext = e.Ext) (t : MachineData)
    (h0 : arg0 t = q.a) (h1 : arg1 t = sA q.c) (hl : st.sp.length = 6) :
    UF q st ⋆ q.R = Reset.RF e (raOf st F) t ⋆ FrR q st O := by
  have e1 : ∀ s : BitVec 64, (16 ?@ (s + 0x44#64)) = 8 ?@ (s + 0x44#64) ⋆ 8 ?@ (s + 0x4c#64) :=
    fun s => blk_split 16 8 _ _ (by omega) (by omega) (by rw [BitVec.add_assoc]; rfl)
  have e2 : ∀ s : BitVec 64, (24 ?@ (s + 0x68#64)) = 4 ?@ (s + 0x68#64) ⋆ 20 ?@ (s + 0x6c#64) :=
    fun s => blk_split 24 4 _ _ (by omega) (by omega) (by rw [BitVec.add_assoc]; rfl)
  simp only [UF, SHW, TWc, DSc, AcU, RdU, hO, hE, Reset.RF, Reset.ScR, Reset.TabR, Reset.DR,
    Apply.c8, h0, h1, FrR, ShR, DScR, e1, e2, ← sp_join st.sp (sA q.c) hl]
  simp only [dAc, BitVec.add_assoc, BitVec.reduceAdd, Nat.reduceMul, Nat.reduceAdd]
  simp only [add_adr]
  ac_rfl

omit [CodeEnv] in
theorem scal_eq {x y : Args} (h : Scal x) (e1 : y.kx0 = x.kx0) (e2 : y.m0 = x.m0)
    (e3 : y.limGains = x.limGains) (e4 : y.kx1 = x.kx1) (e5 : y.m1 = x.m1) (e6 : y.k0 = x.k0)
    (e7 : y.n0 = x.n0) (e8 : y.n1 = x.n1) (e9 : y.nq = x.nq) (e10 : y.nlim = x.nlim)
    (e11 : y.npatch = x.npatch) : Scal y := by
  unfold Scal at *
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  exact h

/-- **`sbr_reset`'s adapter.** -/
theorem usac_reset_glue (k kr : Nat) (e : Reset.REnv) (Oth O : Mem 64 → Prop)
    (hO : Oth = Reset.CstR ⋆ (Reset.BwR ⋆ O)) (hk : Reset.resetNeed kr ≤ Usac.cneed k)
    (hk' : Usac.cneed k ≤ 2 ^ 64) (hR : Reset.ResetSpec kr e) (hB : Reset.BandsOK e.lg e.pw)
    (hal : isAligned 16 (lab "LCPI5_6") = true) : Usac.ResetSpec k e.Ext Oth := by
  refine u_widen (need := Reset.resetNeed kr) (ProcSpec.toA ?main) ?hc ?hr hk hk'
  case hc => exact fun _ _ _ _ h => h
  case hr => exact fun _ _ _ h => h
  apply DecExt.ProcSpec.adapt hR
  intro A ra t ⟨⟨hcall, hqe, hqo⟩, h0, h1, _, hst, hsc, hsp, hs3, hs4, hnw, hal16⟩
  have hO' : A.1.Oth = Reset.CstR ⋆ (Reset.BwR ⋆ O) := hqo.trans hO
  obtain ⟨sl, s0, s2, slb, hlens⟩ := hsp
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hlens
  let F := FrR A.1 A.2 O
  refine ⟨raOf A.2 F, ⟨?_, ?_, hB⟩, ?_⟩
  · show t.dmem =⋆ _ ⋆ (_ ⋆ (Reset.RF e (raOf A.2 F) t ⋆ F))
    rw [← uf_r e A.1 A.2 O F hO' hqe t h0 h1 sl]
    exact hcall
  · refine ⟨sl, ?_, hs3, hs4, hsc, ?_, l1, l2, l3, l4, l5, l6, ?_, hal16, hal⟩
    · show u8 A.2.sp 0 < 16
      rw [s0]; exact hst
    · show (BitVec.ofNat 32 A.2.h.lb).toNat ≤ 3
      rw [BitVec.toNat_ofNat]; omega
    · rw [h1]; omega
  · intro s ⟨x', sp', us', hout, hsr, hbp, hsv, hm⟩
    obtain ⟨sc', hrl, y, ht, -, -, hyav, hz⟩ := hout
    obtain ⟨t1, t2, t3, t4, -, -, -, -, -, -, t11, t12⟩ := ht
    let x0 := A.2.x
    let y' : Args := { y with
      R := x0.R, idAac := x0.idAac, reset := x0.reset, limGains := x0.limGains,
      interpol := x0.interpol, smooth := x0.smooth, coupling := x0.coupling, kx0 := x0.kx0,
      m0 := x0.m0, pushed := x0.pushed, psc := x0.psc, psh := x0.psh, anaCtx := x0.anaCtx,
      synCtx := x0.synCtx, fdsp := x0.fdsp, ps := x0.ps, extRate := x0.extRate,
      d0 := { x0.d0 with idx := y.d0.idx }, d1 := { x0.d1 with idx := y.d1.idx } }
    have hd0 : y'.d0 = x0.d0 ∨ y'.d0 = clrNoise x0.d0 := by
      have t : y.d0 = x0.d0 ∨ y.d0 = clrNoise x0.d0 := t11
      rcases t with h | h
      · left; show { x0.d0 with idx := y.d0.idx } = x0.d0
        rw [h]
      · right; show { x0.d0 with idx := y.d0.idx } = clrNoise x0.d0
        rw [h]; rfl
    have hd1 : y'.d1 = x0.d1 ∨ y'.d1 = clrNoise x0.d1 := by
      have t : y.d1 = x0.d1 ∨ y.d1 = clrNoise x0.d1 := t12
      rcases t with h | h
      · left; show { x0.d1 with idx := y.d1.idx } = x0.d1
        rw [h]
      · right; show { x0.d1 with idx := y.d1.idx } = clrNoise x0.d1
        rw [h]; rfl
    have hTF : TFrame x0 y' := ⟨rfl, rfl, rfl, t4, rfl, rfl, rfl, rfl, rfl, rfl, hd0, hd1⟩
    have hUK : UKeep x0 y' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, hyav, rfl⟩
    rcases hz with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, tz, n1, n2⟩
    · let st' : USt :=
        { A.2 with x := (Args.turnoff y'), h := (A.2.h.turnoff), sp := (List.replicate 6 0xff),
                   u := (0#32) }
      refine ⟨st', ⟨scal_eq sc' t1.symm t2.symm t3.symm rfl rfl rfl rfl rfl rfl rfl rfl,
        y', hTF, hUK, Or.inl ⟨rfl, rfl, rfl⟩, rfl,
        ⟨rfl, rfl, rfl, slb, hrl.1, hrl.2.1, hrl.2.2.1, hrl.2.2.2.1, hrl.2.2.2.2.1,
          hrl.2.2.2.2.2, l7⟩⟩, hsr, hbp, hsv, ?_⟩
      rw [uf_r e A.1 st' O F hO' hqe t h0 h1 rfl]
      exact hm
    · let st' : USt := { A.2 with x := y' }
      refine ⟨st', ⟨scal_eq sc' t1.symm t2.symm t3.symm rfl rfl rfl rfl rfl rfl rfl rfl,
        y', hTF, hUK, Or.inr ⟨rfl, rfl, rfl, tz, n1, n2⟩, rfl,
        ⟨sl, s0, s2, slb, hrl.1, hrl.2.1, hrl.2.2.1, hrl.2.2.2.1, hrl.2.2.2.2.1,
          hrl.2.2.2.2.2, l7⟩⟩, hsr, hbp, hsv, ?_⟩
      rw [uf_r e A.1 st' O F hO' hqe t h0 h1 sl]
      exact hm

end Kraken.Examples.Sbr.Usac
