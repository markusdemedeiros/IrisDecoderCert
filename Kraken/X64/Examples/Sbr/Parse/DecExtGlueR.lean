import Kraken.X64.Examples.Sbr.Parse.DecExtGlue
import Kraken.X64.Examples.Sbr.Parse.DecExtMem

/-!
# `ff_aac_sbr_decode_extension`: the `sbr_reset` adapter

`reset_glue`: `sbr_reset`'s own statement (`Reset.ResetSpec`), `BandsOK` and the alignment of
`LCPI5_6` give the local contract `ResetSpec`.

The footprints: the caller's `CF` at `sbr` is `sbr_reset`'s `RF` and a frame `FRm` (the cells
of `*sbr` it does not own, the reader, the bitstream, the jump table); `RF`'s logical variable
has `x.R := FRm …`. At the return the frame `FRm` is that of the values left, by `TFrame`;
`DS.si` (`bs_limiter_bands`) is kept (`si_reset`).
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.Session
open Kraken.Examples.Sbr.ParseModel

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

/-- The scalar cells of `*sbr` that `sbr_reset` owns, but `usac` (`ScR` without its raw `usac`). -/
abbrev ScX (a : Args) (sp : List UInt8) (lb : Nat) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 s a.sampleRate ⋆ (cell4 (s + 0x4#64) a.start ⋆ (cell4 (s + 0x8#64) a.ready
    ⋆ (sp =@ (s + 0x1c#64) ⋆ (c4 (s + 0x2c#64) lb
    ⋆ (c4 (s + 0x40#64) a.k0 ⋆ (8 ?@ (s + 0x44#64) ⋆ (c4 (s + 0x58#64) a.kx1
    ⋆ (c4 (s + 0x60#64) a.m1 ⋆ 4 ?@ (s + 0x68#64)))))))))

/-- The other scalar cells of `*sbr`. -/
abbrev ScY (d : DS) (s : BitVec 64) : Mem 64 → Prop :=
  cell4 (s + 0xc#64) d.a.idAac ⋆ (cell4 (s + 0x14#64) d.it ⋆ (cell4 (s + 0x18#64) d.a.reset
    ⋆ (2 ?@ (s + 0x22#64) ⋆ (cell4 (s + 0x24#64) d.amp ⋆ (4 ?@ (s + 0x28#64)
    ⋆ (c4 (s + 0x30#64) d.a.limGains ⋆ (cell4 (s + 0x34#64) d.a.interpol
    ⋆ (cell4 (s + 0x38#64) d.a.smooth ⋆ (cell4 (s + 0x3c#64) d.a.coupling
    ⋆ (8 ?@ (s + 0x4c#64) ⋆ (c4 (s + 0x54#64) d.a.kx0 ⋆ (c4 (s + 0x5c#64) d.a.m0
    ⋆ (cell4 (s + 0x64#64) d.a.pushed ⋆ 0x14 ?@ (s + 0x6c#64))))))))))))))

theorem sbrS_eq (d : DS) (s : BitVec 64) :
    SbrS d s = cell4 (s + 0x10#64) d.usac ⋆ (ScX d.a d.sp d.h.lb s ⋆ ScY d s) := by
  have e1 : (16 ?@ (s + 0x44#64)) = 8 ?@ (s + 0x44#64) ⋆ 8 ?@ (s + 0x4c#64) := by
    rw [Block.split_at (s + 0x44#64) 16 8 (by omega) (by omega)]
    simp only [BitVec.add_assoc, BitVec.reduceOfNat, BitVec.reduceAdd, Nat.reduceSub]
  have e2 : (0x18 ?@ (s + 0x68#64)) = 4 ?@ (s + 0x68#64) ⋆ 0x14 ?@ (s + 0x6c#64) := by
    rw [Block.split_at (s + 0x68#64) 0x18 4 (by omega) (by omega)]
    simp only [BitVec.add_assoc, BitVec.reduceOfNat, BitVec.reduceAdd, Nat.reduceSub]
  simp only [SbrS, ScX, ScY, e1, e2]
  ac_rfl

/-- One `SBRData` but `e_a[1]` (+0x3908) and `f_indexnoise/sine` (+0x15aac). -/
abbrev DataR (v : DV) (d : BitVec 64) : Mem 64 → Prop :=
  4 ?@ d ⋆ (4 ?@ (d + 0x4#64) ⋆ (c4 (d + 0x8#64) v.nenv ⋆ (v.freqRes =@ (d + 0xc#64)
  ⋆ (3 ?@ (d + 0x15#64) ⋆ (c4 (d + 0x18#64) v.nnoise ⋆ (11 ?@ (d + 0x1c#64)
  ⋆ (v.invf =@ (d + 0x27#64) ⋆ (48 ?@ (d + 0x31#64) ⋆ (3 ?@ (d + 0x61#64)
  ⋆ (4 ?@ (d + 0x64#64) ⋆ (0x3898 ?@ (d + 0x68#64) ⋆ (cell4 (d + 0x3900#64) v.vOff
  ⋆ (4 ?@ (d + 0x3904#64) ⋆ (0x4014 ?@ (d + 0x390c#64)
  ⋆ (c4 (d + 0x7920#64) v.ypos
  ⋆ (0xe178 ?@ (d + 0x7924#64) ⋆ (v.te =@ (d + 0x15a9c#64) ⋆ (v.tq =@ (d + 0x15aa6#64)
  ⋆ (3 ?@ (d + 0x15aa9#64) ⋆ 12 ?@ (d + 0x15ab4#64))))))))))))))))))))

theorem dataF_eq (v : DV) (d : BitVec 64) :
    DataF v d = 4 ?@ (d + 0x3908#64) ⋆ (Apply.c8 (d + 0x15aac#64) v.idx ⋆ DataR v d) := by
  simp only [DataF, DataR]; ac_rfl

/-- `sbr_reset`'s tables (`TabR`) at `s`. -/
abbrev TabRs (x : Args) (s : BitVec 64) : Mem 64 → Prop :=
  c4 (s + 0x4c1e0#64) x.n0 ⋆ (c4 (s + 0x4c1e4#64) x.n1 ⋆ (c4 (s + 0x4c1e8#64) x.nq
    ⋆ (c4 (s + 0x4c1ec#64) x.nlim ⋆ (98 ?@ (s + 0x4c1f0#64) ⋆ (x.ftLow =@ (s + 0x4c252#64)
    ⋆ (x.ftHigh =@ (s + 0x4c284#64) ⋆ (x.ftNoise =@ (s + 0x4c2e6#64)
    ⋆ (x.ftLim =@ (s + 0x4c2f2#64) ⋆ (c4 (s + 0x4c330#64) x.npatch
    ⋆ (x.pnum =@ (s + 0x4c334#64) ⋆ x.pstart =@ (s + 0x4c33a#64)))))))))))

theorem tabF_eq (x : Args) (s : BitVec 64) :
    TabF x s = TabRs x s ⋆ 2 ?@ (s + 0x4c32e#64) := by
  simp only [TabF, TabRs]; ac_rfl

theorem tabR_eq (x : Args) (t : MachineData) (s : BitVec 64) (h : arg1 t = s) :
    Reset.TabR x t = TabRs x s := by
  simp only [Reset.TabR, h]

/-- `sbr_reset`'s cells of `data[0..1]` at `s`. -/
abbrev DRs (x : Args) (s : BitVec 64) : Mem 64 → Prop :=
  4 ?@ (s + 0x80#64 + 0x3908#64) ⋆ (Apply.c8 (s + 0x80#64 + 0x15aac#64) x.d0.idx
    ⋆ (4 ?@ (s + 0x15b40#64 + 0x3908#64) ⋆ Apply.c8 (s + 0x15b40#64 + 0x15aac#64) x.d1.idx))

theorem dR_eq (x : Args) (t : MachineData) (s : BitVec 64) (h : arg1 t = s) :
    Reset.DR x t = DRs x s := by
  simp only [Reset.DR, DRs, h, BitVec.add_assoc, BitVec.reduceAdd]

omit [CodeEnv] in
theorem lb_cell (a : BitVec 64) (n : Nat) (hn : n ≤ 3) :
    cell4 a (BitVec.ofNat 32 n) = c4 a n := by
  match n, hn with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl

theorem scR_eq (x : Args) (sp : List UInt8) (n : Nat) (us : BitVec 32) (t : MachineData)
    (s : BitVec 64) (h : arg1 t = s) (hn : n ≤ 3) :
    Reset.ScR x sp (BitVec.ofNat 32 n) us t = cell4 (s + 0x10#64) us ⋆ ScX x sp n s := by
  simp only [Reset.ScR, h, lb_cell _ n hn, ScX]; ac_rfl

/-- `Ext` with `sbr_reset`'s read-only data in it. -/
abbrev ExtR (e : Reset.REnv) : Mem 64 → Prop := Reset.CstR ⋆ (Reset.BwR ⋆ e.Ext)

/-- The caller's part at the `sbr_reset` call: the cells of `*sbr` it does not own, and `G`. -/
abbrev FRm (d : DS) (s : BitVec 64) (G : Mem 64 → Prop) : Mem 64 → Prop :=
  ScY d s ⋆ (DataR d.a.d0 (s + 0x80#64) ⋆ (DataR d.a.d1 (s + 0x15b40#64)
    ⋆ (d.a.psc =@ (s + 0x2b600#64) ⋆ (2 ?@ (s + 0x4c32e#64) ⋆ G))))

/-- Both sides without the `usac` cell. -/
abbrev Wr (e : Reset.REnv) (d : DS) (s ac : BitVec 64) (G : Mem 64 → Prop) : Mem 64 → Prop :=
  ScX d.a d.sp d.h.lb s ⋆ (TabRs d.a s ⋆ (DRs d.a s ⋆ (Apply.c8 (ac + 8#64) d.a.avctx
    ⋆ (Reset.CstR ⋆ (Reset.BwR ⋆ (e.Ext ⋆ FRm d s G))))))

theorem cf_eq (e : Reset.REnv) (c : CA) (d : DS) (i : BitVec 32) :
    CF (ExtR e) c d i ⋆ c.R = cell4 (c.s + 0x10#64) d.usac
      ⋆ Wr e d c.s c.ac (GbR c.g c.r i ⋆ (BufW c.r ⋆ (Grid.JtW ⋆ c.R))) := by
  simp only [CF, SbrF, sbrS_eq, dataF_eq, tabF_eq, Wr, FRm, ExtR, AvW, DRs, BitVec.add_assoc,
    BitVec.reduceAdd]
  ac_rfl

omit [CodeEnv] in
theorem sepM {X Y K K' : Mem 64 → Prop} (e₁ : Mem.Entails X Y)
    (e₂ : Mem.Entails K K') : Mem.Entails (X ⋆ K) (Y ⋆ K') := by
  intro m ⟨m₁, m₂, hd, hm, h₁, h₂⟩
  exact ⟨m₁, m₂, hd, hm, e₁ m₁ h₁, e₂ m₂ h₂⟩

/-- `Wr` on any values. -/
abbrev Wr' (e : Reset.REnv) (x : Args) (sp : List UInt8) (n : Nat) (s ac : BitVec 64)
    (F : Mem 64 → Prop) : Mem 64 → Prop :=
  ScX x sp n s ⋆ (TabRs x s ⋆ (DRs x s ⋆ (Apply.c8 (ac + 8#64) x.avctx
    ⋆ (Reset.CstR ⋆ (Reset.BwR ⋆ (e.Ext ⋆ F))))))

theorem rf_gen (e : Reset.REnv) (x : Args) (sp : List UInt8) (n : Nat) (t : MachineData)
    (us : BitVec 32) (s ac : BitVec 64) (F : Mem 64 → Prop) (h1 : arg1 t = s) (h0 : arg0 t = ac)
    (hn : n ≤ 3) :
    Reset.RF e ⟨x, sp, BitVec.ofNat 32 n, us⟩ t ⋆ F
      = cell4 (s + 0x10#64) us ⋆ Wr' e x sp n s ac F := by
  simp only [Reset.RF, scR_eq _ _ _ us t s h1 hn, tabR_eq _ t s h1, dR_eq _ t s h1, h0, Wr', DRs,
    BitVec.add_assoc, BitVec.reduceAdd]
  ac_rfl

omit [CodeEnv] in
theorem dataR_clr (v : DV) (a : BitVec 64) : DataR (clrNoise v) a = DataR v a := by
  unfold clrNoise; rfl

omit [CodeEnv] in
theorem frm_eq (d d' : DS) (s : BitVec 64) (G : Mem 64 → Prop)
    (h1 : d'.a.idAac = d.a.idAac) (h2 : d'.it = d.it) (h3 : d'.a.reset = d.a.reset)
    (h4 : d'.amp = d.amp) (h5 : d'.a.limGains = d.a.limGains) (h6 : d'.a.interpol = d.a.interpol)
    (h7 : d'.a.smooth = d.a.smooth) (h8 : d'.a.coupling = d.a.coupling) (h9 : d'.a.kx0 = d.a.kx0)
    (h10 : d'.a.m0 = d.a.m0) (h11 : d'.a.pushed = d.a.pushed) (h12 : d'.a.psc = d.a.psc)
    (h13 : d'.a.d0 = d.a.d0 ∨ d'.a.d0 = clrNoise d.a.d0)
    (h14 : d'.a.d1 = d.a.d1 ∨ d'.a.d1 = clrNoise d.a.d1) :
    FRm d' s G = FRm d s G := by
  have e0 : DataR d'.a.d0 (s + 0x80#64) = DataR d.a.d0 (s + 0x80#64) := by
    rcases h13 with h | h <;> rw [h]; exact dataR_clr _ _
  have e1 : DataR d'.a.d1 (s + 0x15b40#64) = DataR d.a.d1 (s + 0x15b40#64) := by
    rcases h14 with h | h <;> rw [h]; exact dataR_clr _ _
  simp only [FRm, ScY, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, e0, e1]

omit [CodeEnv] in
/-- `DS.si` after `sbr_reset`: `bs_limiter_bands` kept. -/
theorem si_reset {d d' : DS} (h : d.si) (hlb : d'.h.lb = d.h.lb) : d'.si := by
  unfold DS.si; rw [hlb]; exact h

/-- **`sbr_reset`'s adapter.** -/
theorem reset_glue (k : Nat) (e : Reset.REnv) (hR : Reset.ResetSpec k e)
    (hB : Reset.BandsOK e.lg e.pw) (hal : isAligned 16 (lab "LCPI5_6") = true) :
    ResetSpec (Reset.resetNeed k) (ExtR e) := by
  apply ProcSpec.adapt hR
  intro c ra t ⟨⟨hcall, hrok, hdok⟩, h0, h1, hhi, hres, hs3, hs4, hlb, hnw, hal16⟩
  let G := GbR c.g c.r c.i ⋆ (BufW c.r ⋆ (Grid.JtW ⋆ c.R))
  obtain ⟨l1, l2, l3, l4, l5, l6, l7⟩ := hdok.2.2.2
  refine ⟨⟨{ c.d.a with R := FRm c.d c.s G }, c.d.sp, BitVec.ofNat 32 c.d.h.lb, c.d.usac⟩,
    ⟨?_, ?_, hB⟩, ?_⟩
  · have hm : t.dmem =⋆ _ ⋆ (_ ⋆ (CF (ExtR e) c c.d c.i ⋆ c.R)) := hcall
    rw [cf_eq] at hm
    show t.dmem =⋆ _ ⋆ (_ ⋆ (Reset.RF e ⟨_, c.d.sp, BitVec.ofNat 32 c.d.h.lb, c.d.usac⟩ t
      ⋆ FRm c.d c.s G))
    rw [rf_gen _ _ _ _ t _ c.s c.ac _ h1 h0 hlb]
    exact hm
  · refine ⟨hdok.1, ?_, hs3, hs4, hhi.1, ?_, l1, l2, l3, l4, l5, l6, ?_, hal16, hal⟩
    · show u8 c.d.sp 0 < 16
      rw [← hdok.2.1]; exact hhi.2.2.1 hres
    · show (BitVec.ofNat 32 c.d.h.lb).toNat ≤ 3
      rw [BitVec.toNat_ofNat]; omega
    · show (arg1 t).toNat + _ < _
      rw [h1]; exact hnw
  · intro s ⟨x', sp', us', hout, hsr, hbp, hsv, hm⟩
    have hm' : s.dmem =⋆ _ ⋆ (_ ⋆ (Reset.RF e ⟨x', sp', BitVec.ofNat 32 c.d.h.lb, us'⟩ t
      ⋆ FRm c.d c.s G)) := hm
    rw [rf_gen _ _ _ _ t _ c.s c.ac _ h1 h0 hlb] at hm'
    obtain ⟨hmi, hid, hpsc⟩ :=
      reset_mi (x := { c.d.a with R := FRm c.d c.s G }) hhi hdok.2.1 hout
    obtain ⟨-, hlens, y, ht, -, -, hyav, hz⟩ := hout
    have hsp : sp'.length = 6 := by
      rcases hz with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩
      · rfl
      · exact hdok.1
    obtain ⟨t1, t2, t3, -, -, -, t7, t8, t9, t10, t11, t12⟩ := ht
    have hx : x'.kx0 = y.kx0 ∧ x'.m0 = y.m0 ∧ x'.limGains = y.limGains ∧ x'.psh = y.psh
        ∧ x'.anaCtx = y.anaCtx ∧ x'.synCtx = y.synCtx ∧ x'.fdsp = y.fdsp ∧ x'.d0 = y.d0
        ∧ x'.d1 = y.d1 ∧ x'.avctx = y.avctx := by
      rcases hz with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨x1, x2, x3, x7, x8, x9, x10, x11, x12, x13⟩ := hx
    let a₁ : Args := { x' with
      R := c.d.a.R
      reset := c.d.a.reset
      interpol := c.d.a.interpol
      smooth := c.d.a.smooth
      coupling := c.d.a.coupling
      pushed := c.d.a.pushed
      ps := c.d.a.ps }
    let d₁ : DS := ⟨a₁, hidOf sp' c.d.h.lb, us', c.d.amp, sp', c.d.it⟩
    have hf : FRm d₁ c.s G = FRm c.d c.s G :=
      frm_eq _ _ _ _ hid rfl rfl rfl (x3.trans t3) rfl rfl rfl (x1.trans t1) (x2.trans t2) rfl
        hpsc (x11 ▸ t11) (x12 ▸ t12)
    refine ⟨d₁, c.i, ⟨hmi, hid, hpsc, fun hs => si_reset (d' := d₁) hs rfl⟩,
      ⟨hsp, rfl, rfl, hlens.1, hlens.2.1, hlens.2.2.1, hlens.2.2.2.1, hlens.2.2.2.2.1,
        hlens.2.2.2.2.2, (hpsc.trans (rfl : _ = c.d.a.psc)).symm ▸ l7⟩,
      ⟨rfl, x10.trans t10, x8.trans t8, x9.trans t9, x7.trans t7, x13.trans hyav, rfl⟩,
      hrok.1, hsr, hbp, hsv, ?_⟩
    show s.dmem =⋆ _ ⋆ (_ ⋆ (CF (ExtR e) c d₁ c.i ⋆ c.R))
    rw [cf_eq]
    have hw : Wr e d₁ c.s c.ac G = Wr' e x' sp' c.d.h.lb c.s c.ac (FRm c.d c.s G) := by
      show Wr' e d₁.a d₁.sp d₁.h.lb c.s c.ac (FRm d₁ c.s G) = _
      rw [hf]
    rw [hw]; exact hm'

end Kraken.Examples.Sbr.DecExt
