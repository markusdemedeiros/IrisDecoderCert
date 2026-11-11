import Kraken.X64.Examples.Sbr.Parse.UsacGlueR

/-!
# `ff_aac_sbr_decode_usac_data`: the `read_sbr_header` adapter

`usac_hdr_glue`: `read_sbr_header`'s own statement for every callee footprint (`Hdr.HdrSpec`,
with `sbr->usac` a value at entry: `DecExt.hdrU_of`) and `sbr_make_f_tablelim`'s contract
(`Reset.TlimSpec`, as `read_sbr_header` sees it: `DecExt.tlim_glue`) give the local contract
`HeaderSpec`.

* The caller's `UF` is `read_sbr_header`'s footprint `HFU` (the six bytes of `spectrum_params`
  as one cell, `sp_join`) and the frame `FrHU` (`uf_h`).
* With `is_usac = 1` the header keeps `bs_xover_band` and `bs_amp_res_header`; its values are a
  model `Header true` step (`hdr_header_u`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

namespace Kraken.Examples.Sbr.Usac

/-- `read_sbr_header`'s values (`Hdr.HdrOut`, `is_usac = 1`) as a model `Header true` step from
`(x, h)`; `y` is the result of the optional `sbr_make_f_tablelim`. -/
theorem hdr_header_u {x : Args} {h : Hid} {hx : Hdr.HArgs} {st : Hdr.HSt} {ret : BitVec 32}
    {y : Args}
    (hrr : hx.reset = x.reset) (hs : h.start = u8 hx.sp 0)
    (hlb : hx.lb.toNat = h.lb) (ho : Hdr.HdrOut hx 1#32 st ret)
    (hy : if st.called hx then Tablelim st.lb.toNat (DecExt.hdrVals x st) y
      else y = DecExt.hdrVals x st) :
    Header true (x, h) (y, ⟨u8 st.sp 0, h.xover, st.lb.toNat⟩) := by
  obtain ⟨-, -, -, o0, -, -, -, -, -, -, ores, olb, olg, -, -, -, -, -⟩ := ho
  have hres : st.reset = if decide (st.sp ≠ hx.sp) = true then 1 else x.reset := by
    rw [ores, hrr]; by_cases e : st.sp = hx.sp <;> simp [e]
  have hlim : HdrLim st.lb.toNat h.lb
      (DecExt.hdrSet x (if decide (st.sp ≠ hx.sp) = true then 1 else x.reset) st) y := by
    rw [← hres]
    by_cases hc : st.called hx
    · rw [if_pos hc] at hy
      refine HdrLim.lim ?_ hc.2 hy
      intro e; apply hc.1; rw [← hlb] at e; exact BitVec.eq_of_toNat_eq e
    · rw [if_neg hc] at hy
      subst hy
      refine HdrLim.keep ?_
      by_cases e : st.lb = hx.lb
      · left; rw [e, hlb]
      · right; intro h0; exact hc ⟨e, h0⟩
  refine Header.mk (u8 st.sp 0) h.xover st.lb.toNat st.lg.toNat 0 st.ip st.sm
    (decide (st.sp ≠ hx.sp)) o0 (fun e => Bool.noConfusion e) (fun _ => rfl) olb olg
    (Or.inl rfl) ?_ hlim
  intro hne
  simp only [decide_eq_true_eq]
  intro e; apply hne; rw [hs, e]

variable [CodeEnv]

/-- The header fields of `st`. -/
def stU (st : USt) : Hdr.HSt :=
  ⟨st.i, st.x.start, st.x.ready, st.x.reset, st.sp, st.amp, BitVec.ofNat 32 st.h.lb,
    BitVec.ofNat 32 st.x.limGains, st.x.interpol, st.x.smooth⟩

/-- `read_sbr_header`'s logical variable at `st`, with caller's memory `F`. -/
def hxU (q : UQ) (st : USt) (F : Mem 64 → Prop) : Hdr.HArgs :=
  ⟨F, st.x.start, st.x.ready, st.x.reset, st.sp, st.amp, BitVec.ofNat 32 st.h.lb,
    BitVec.ofNat 32 st.x.limGains, st.x.interpol, st.x.smooth, q.buf, st.i, q.p8, q.L⟩

omit [CodeEnv] in
theorem hxU_st (q : UQ) (st : USt) (F : Mem 64 → Prop) : (hxU q st F).st = stU st := rfl

/-- The caller's part at the `read_sbr_header` call. -/
abbrev FrHU (q : UQ) (st : USt) (O : Mem 64 → Prop) : Mem 64 → Prop :=
  let s := sA q.c
  cell4 s st.x.sampleRate ⋆ (cell4 (s + 0xc#64) st.x.idAac ⋆ (4 ?@ (s + 0x14#64)
    ⋆ (2 ?@ (s + 0x22#64) ⋆ (4 ?@ (s + 0x28#64) ⋆ (cell4 (s + 0x3c#64) st.x.coupling
    ⋆ (c4 (s + 0x40#64) st.x.k0 ⋆ (16 ?@ (s + 0x44#64) ⋆ (c4 (s + 0x54#64) st.x.kx0
    ⋆ (c4 (s + 0x5c#64) st.x.m0 ⋆ (c4 (s + 0x60#64) st.x.m1 ⋆ (cell4 (s + 0x64#64) st.x.pushed
    ⋆ (24 ?@ (s + 0x68#64) ⋆ (TwT q.c st.x ⋆ (DSc q.c 0 st.x.d0 ⋆ (DRaw q.c 0
    ⋆ (DSc q.c 1 st.x.d1 ⋆ (DRaw q.c 1 ⋆ (AcU q.a st.x ⋆ (6 ?@ lab "ceil_log2"
    ⋆ (Grid.JtW ⋆ (q.uev =@ (q.ue + 0xc#64) ⋆ (q.Ext ⋆ (O ⋆ q.R)))))))))))))))))))))))

theorem uf_h (q : UQ) (st : USt) (O F : Mem 64 → Prop) (hO : q.Oth = Reset.BwR ⋆ O)
    (t : MachineData) (h0 : arg0 t = sA q.c) (h1 : arg1 t = q.g) (hl : st.sp.length = 6)
    (hlg : st.x.limGains ≤ 3) :
    UF q st ⋆ q.R = DecExt.HFU (hxU q st F) st.u t (stU st) (DecExt.TlC0 st.x (arg0 t))
      ⋆ FrHU q st O := by
  simp only [UF, SHW, TWc, RdU, hO, DecExt.HFU, DecExt.SbU, Hdr.GbW, GbU, DecExt.TlC0, FrHU,
    TwT, stU, hxU, h0, h1, Blocks, Reset.BwR, ← sp_join st.sp (sA q.c) hl,
    DecExt.lb_cell _ _ hlg]
  simp only [add_adr]
  ac_rfl

omit [CodeEnv] in
theorem stU_eq (x : Args) (st : Hdr.HSt) (s0 xo : Nat) (h1 : st.start = 1#32)
    (h2 : st.ready = 0#32) :
    stU ⟨DecExt.hdrVals x st, ⟨s0, xo, st.lb.toNat⟩, st.i, 1#32, st.amp, st.sp⟩ = st := by
  obtain ⟨i, a, b, r, sp, am, lb, lg, ip, sm⟩ := st
  simp only at h1 h2
  subst h1 h2
  simp only [stU, DecExt.ofNat_toNat32]
  rfl

/-- **`read_sbr_header`'s adapter.** -/
theorem usac_hdr_glue (k kh kt : Nat) (Ext Oth O : Mem 64 → Prop) (hO : Oth = Reset.BwR ⋆ O)
    (hk : Hdr.hdrNeed kh ≤ Usac.cneed k) (hk' : Usac.cneed k ≤ 2 ^ 64)
    (hH : ∀ TlT TlT' TlC, Hdr.TlimSpec TlT TlT' TlC (Reset.tlimNeed kt) →
      Hdr.HdrSpec kh TlT TlT' TlC)
    (hT : Reset.TlimSpec kt) : Usac.HeaderSpec k Ext Oth := by
  refine u_widen (need := Hdr.hdrNeed kh) (ProcSpec.toA ?main) ?hc ?hr hk hk'
  case hc => exact fun _ _ _ _ h => h
  case hr => exact fun _ _ _ h => h
  refine DecExt.ProcSpec.adaptD
    (Pre := fun A : UA => DecExt.HdrPreU kh (DecExt.TlC0 A.2.x) (DecExt.TlCs A.2.x))
    (Post := fun A : UA => DecExt.HdrPostU kh (DecExt.TlC0 A.2.x) (DecExt.TlP A.2.x))
    (fun A => DecExt.hdrU_of (hH _ _ _ (DecExt.tlim_glue kt A.2.x hT))) ?_
  intro A ra t ⟨⟨hcall, _, hqo⟩, h0, h1, h2, hmi, hr0, hsp, hi, hgb, hnw⟩
  have hO' : A.1.Oth = Reset.BwR ⋆ O := hqo.trans hO
  obtain ⟨sl, s0, s2, slb, hlens⟩ := hsp
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hlens
  have hA : AI A.2.x := hmi.1
  have hI : I1 A.2.x A.2.h := hmi.2
  have hsc : Scal A.2.x := hA.1
  have hlg : A.2.x.limGains ≤ 3 := hsc.2.2.2.2.2.2.1
  let F := FrHU A.1 A.2 O
  refine ⟨(hxU A.1 A.2 F, A.2.u), ⟨?_, ?_⟩, ?_⟩
  · show t.dmem =⋆ _ ⋆ (_ ⋆ (DecExt.HFU (hxU A.1 A.2 F) A.2.u t (stU A.2)
      (DecExt.TlC0 A.2.x (arg0 t)) ⋆ FrHU A.1 A.2 O))
    rw [← uf_h A.1 A.2 O F hO' t h0 h1 sl hlg]
    exact hcall
  · refine ⟨sl, hi, hgb.1, hgb.2.1, hgb.2.2, fun _ hs lb hl _ => ?_⟩
    have hst : A.2.x.start ≠ 0 := by
      intro h; have := hI h
      change u8 A.2.sp 0 < 16 at hs
      omega
    obtain ⟨w1, -, -, w4, w5, -, -, -, w9, -, -, -, w13, -, -, -, -, -, -, -, w21⟩ :=
      (hA.2.1 hst).1
    have n1 := (hA.2.1 hst).2.1
    obtain ⟨-, -, -, s4, -, -, -, s8, -, -, s11, s12⟩ := hsc
    refine ⟨by omega, s8, s12, fun _ => by omega, w1, w4, w5, ⟨w9, w13⟩, w21, s4, by omega, ?_⟩
    rw [h0]; omega
  · intro s ⟨hs, hout, hsr, hbp, hsv, hm⟩
    rw [h2] at hout hm
    suffices H : ∃ fl nl, (if hs.called (hxU A.1 A.2 F)
          then Tablelim hs.lb.toNat (DecExt.hdrVals A.2.x hs)
            (DecExt.hdrVals (DecExt.limSet A.2.x fl nl) hs)
          else DecExt.hdrVals (DecExt.limSet A.2.x fl nl) hs = DecExt.hdrVals A.2.x hs)
        ∧ fl.length = 60
        ∧ s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve (Hdr.hdrNeed kh) (t.regs.get64 .rsp)
          ⋆ (DecExt.HFU (hxU A.1 A.2 F) 1#32 t hs
            (DecExt.TlC0 (DecExt.limSet A.2.x fl nl) (arg0 t)) ⋆ F)) by
      obtain ⟨fl, nl, hy, hfl, hmem⟩ := H
      have hlbN : (hxU A.1 A.2 F).lb.toNat = A.2.h.lb := by
        show (BitVec.ofNat 32 A.2.h.lb).toNat = A.2.h.lb
        rw [BitVec.toNat_ofNat]; omega
      have hh := hdr_header_u rfl s0.symm hlbN hout hy
      obtain ⟨o1, o2, o3, -, -, -, o7, o8, o9, -, -, olb, olg, -, -, -, o17, -⟩ := hout
      let st' : USt := ⟨DecExt.hdrVals (DecExt.limSet A.2.x fl nl) hs,
        ⟨u8 hs.sp 0, A.2.h.xover, hs.lb.toNat⟩, hs.i, 1#32, hs.amp, hs.sp⟩
      have hx2 : u8 hs.sp 2 = A.2.h.xover := by
        have e := (o7 (by decide)).1
        show (hs.sp.getD 2 0).toNat = _
        rw [e, ← s2]; rfl
      refine ⟨st', ⟨hh, rfl, ⟨o3, rfl, hx2, by show hs.lb.toNat ≤ 3; omega,
        l1, l2, l3, hfl, l5, l6, l7⟩, o17, o8, o9⟩, hsr, hbp, hsv, ?_⟩
      rw [uf_h A.1 st' O F hO' t h0 h1 o3 (by show hs.lg.toNat ≤ 3; omega)]
      rw [stU_eq _ _ _ _ o1 o2]
      exact hmem
    by_cases hc : hs.called (hxU A.1 A.2 F)
    · have hm' : s.dmem =⋆ 8 ?@ (t.regs.get64 .rsp) ⋆ (Reserve (Hdr.hdrNeed kh)
          (t.regs.get64 .rsp) ⋆ (DecExt.HFU (hxU A.1 A.2 F) 1#32 t hs
            (DecExt.TlP A.2.x hs.lb (arg0 t)) ⋆ F)) := by
        have := hm; simp only [Hdr.TlOut, if_pos hc] at this; exact this
      obtain ⟨fl, nl, ht, hz⟩ := DecExt.ex_tl hm'
      exact ⟨fl, nl, by rw [if_pos hc]; exact DecExt.tablelim_hv hs ht,
        DecExt.tablelim_len ht, hz⟩
    · refine ⟨A.2.x.ftLim, A.2.x.nlim, by rw [if_neg hc], l4, ?_⟩
      have := hm; simp only [Hdr.TlOut, if_neg hc] at this; exact this

end Kraken.Examples.Sbr.Usac
