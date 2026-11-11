import Kraken.X64.Examples.Sbr.Parse.DecExtPro2

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the calls of `read_sbr_header` and `sbr_reset`

At both calls the callee gets `CF` (the decoder state, the frame's `gbc`, the bitstream,
`ac->avctx`, the jump table, `Ext`); the caller keeps `GR` (the other locals, `*gb_host`, the
fields of `*ac`, the saved registers). The callee's values `d'` come back with
`ext_sample_rate` (a cell of `AcF`, kept in `GR`) set back to the caller's value (`DS.er`):
no conjunct of `HI`/`MI` reads it.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- The caller's part of the memory at a decoder-state call (`gbc` at `rbp - 0x40`): the other
locals, `*gb_host`, the `ac` fields, the saved registers and the caller's rest. -/
def GR (X : XA) (ra : Int64) (t₀ : MachineData) (d : DS) (ih : BitVec 32) : Mem 64 → Prop :=
  let r := t₀.regs.get64 .rsp
  (8 ?@ (r - 0x68#64) ⋆ (8 ?@ (r - 0x60#64) ⋆ (Apply.c8 (r - 0x58#64) (arg4 t₀)
    ⋆ (8 ?@ (r - 0x50#64) ⋆ 4 ?@ (r - 0x34#64)))))
  ⋆ (GhW (arg2 t₀) X ih ⋆ (AcF (arg0 t₀) d.a X.sr ⋆ Saved t₀ (Rest X.R ra t₀)))

/-- The callee's logical variable at a call before `read_sbr_data`. -/
abbrev cH (X : XA) (ra : Int64) (t₀ : MachineData) (d : DS) (gi ih : BitVec 32) : CA :=
  ⟨GR X ra t₀ d ih, d, sbrA t₀, arg0 t₀, t₀.regs.get64 .rsp - 0x48#64, X.r, gi⟩

omit [CodeEnv] in
theorem perm14 (a1 a2 a3 a4 g a5 S Gh Av Ac Bf Jt E Sv : Mem 64 → Prop) :
    (a1 ⋆ (a2 ⋆ (a3 ⋆ (a4 ⋆ (g ⋆ a5))))) ⋆ ((S ⋆ (Gh ⋆ (Av ⋆ (Ac ⋆ (Bf ⋆ (Jt ⋆ E)))))) ⋆ Sv)
      = (S ⋆ (g ⋆ (Bf ⋆ (Av ⋆ (Jt ⋆ E))))) ⋆ ((a1 ⋆ (a2 ⋆ (a3 ⋆ (a4 ⋆ a5)))) ⋆ (Gh ⋆ (Ac ⋆ Sv))) := by
  ac_rfl

theorem T_hdr (kc : Nat) (Ext : Mem 64 → Prop) (X : XA) (ra : Int64) (t₀ : MachineData)
    (d : DS) (gi ih : BitVec 32) :
    T kc Ext X ra t₀ (Saved t₀) (LocW0 X t₀ gi) d ih =
      8 ?@ (t₀.regs.get64 .rsp - 0x70#64) ⋆ (Reserve kc (t₀.regs.get64 .rsp - 0x70#64)
        ⋆ (CF Ext (cH X ra t₀ d gi ih) d gi ⋆ GR X ra t₀ d ih)) := by
  let r := t₀.regs.get64 .rsp
  exact congrArg (fun H => 8 ?@ (r - 0x70#64) ⋆ (Reserve kc (r - 0x70#64) ⋆ H))
    (perm14 (8 ?@ (r - 0x68#64)) (8 ?@ (r - 0x60#64)) (Apply.c8 (r - 0x58#64) (arg4 t₀))
      (8 ?@ (r - 0x50#64)) (GbR (r - 0x48#64) X.r gi) (4 ?@ (r - 0x34#64))
      (SbrF d (sbrA t₀)) (GhW (arg2 t₀) X ih) (AvW (arg0 t₀) d.a) (AcF (arg0 t₀) d.a X.sr)
      (BufW X.r) Grid.JtW Ext (Saved t₀ (Rest X.R ra t₀)))

omit [CodeEnv] in
theorem al_ret (r : BitVec 64) (h : isAligned 16 (r + 8#64) = true) :
    isAligned 16 (r - 112#64 + 8#64) = true := by
  have e : r - 112#64 + 8#64 = r - BitVec.ofNat 64 0x68 := by bv_omega
  rw [e]; exact al_sub r 0x68 h (by decide)

omit [CodeEnv] in
theorem sub112 (r : BitVec 64) : r - 112#64 + 8 = r - 104#64 := by bv_omega

/-- `ext_sample_rate` reset to its old value. -/
abbrev DS.er (d' : DS) (e : BitVec 32) : DS := { d' with a := { d'.a with extRate := e } }

omit [CodeEnv] in
theorem hi_er {d' : DS} (e : BitVec 32) (h : HI (d'.a, d'.h)) : HI ((d'.er e).a, (d'.er e).h) := h

theorem GR_er (X : XA) (ra : Int64) (t₀ : MachineData) (d d' : DS) (ih : BitVec 32)
    (h1 : d'.a.ps = d.a.ps) (h2 : d'.a.avctx = d.a.avctx) :
    GR X ra t₀ (d'.er d.a.extRate) ih = GR X ra t₀ d ih := by
  simp only [GR, AcF, DS.er, h1, h2]

theorem CF_er (Ext : Mem 64 → Prop) (c : CA) (d' : DS) (e i : BitVec 32) :
    CF Ext c (d'.er e) i = CF Ext c d' i := rfl

omit [CodeEnv] in
theorem xkeep_trans {x y z : Args} (h1 : XKeep x y) (h2 : XKeep y z) : XKeep x z := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7⟩ := h2
  exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6, b7.trans a7⟩

theorem blk_Lff (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hH : HdrSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.Lff" := by
  cfg_block
  measure_hb "Lff"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, gi, ih, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    have hI2 := inv2_pro hC
    simp only [Mm0] at hm
    rw [T_hdr] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at (cH X ra t₀ (X.d.pro X.sr) gi ih) "read_sbr_header" hH]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hC.2.1⟩, ?_, ?_, ?_, hI2.1, pro_reset _ _,
      hC.2.2.2.2.2.2.2.2.2.2.1, hC.2.2.2.2.2.2.1⟩,
      fun s' hpost => ?_⟩, hld⟩
    · rw [e70]; exact hpush _
    · exact hdi
    · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
    · simp
    · obtain ⟨d', i', ⟨hHI, -, -, -, hpsc, -, hu, h3, h4, hlb⟩, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩,
        hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, i', d'.er (X.d.pro X.sr).a.extRate, ih,
        ⟨hi_er _ hHI, hok, ?_, xkeep_trans hI2.2.2.2.1 hxk, Nat.le_of_lt_succ hlb,
          fun _ => ⟨Nat.le_of_lt_succ h3, Nat.le_of_lt_succ h4, Nat.le_of_lt_succ hlb⟩⟩, ⟨hi', hrb.2⟩, ?_⟩, ?_⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [hbx']; exact hdi
      · rw [h12']; exact h12
      · rw [h13']; exact h13
      · show PI d'.a.psc
        rw [hpsc]; exact hC.2.2.1
      · show (T kc Ext X ra t₀ (Saved t₀) (LocW0 X t₀ i') (d'.er (X.d.pro X.sr).a.extRate) ih) s'.dmem
        rw [T_hdr, GR_er _ _ _ _ _ _ hxk.2.2.2.2.2.2 hxk.2.2.2.2.2.1]
        rw [e70] at hm'
        exact hm'
      · first | exact Nat.le_of_eq (var_L10d _) | (rw [var_L10d]; omega)

omit [CodeEnv] in
theorem mi_er {d' : DS} (e : BitVec 32) (h : MI (d'.a, d'.h)) : MI ((d'.er e).a, (d'.er e).h) := h

theorem blk_L11d (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hR : ResetSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L11d" := by
  cfg_block
  measure_hb "L11d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, hbx, h12, h13, gi, d, ih, ⟨hI, hr⟩, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0] at hm
    rw [T_hdr] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at (cH X ra t₀ d gi ih) "sbr_reset" hR]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hI.2.1⟩, ?_, ?_, hI.1, hr,
      (hI.2.2.2.2.2 hr).1, (hI.2.2.2.2.2 hr).2.1, (hI.2.2.2.2.2 hr).2.2,
      hC.2.2.2.2.2.2.2.2.2.2.1, ?_⟩,
      fun s' hpost => ?_⟩, hld⟩
    · rw [e70]; exact hpush _
    · exact h12
    · exact hbx
    · rw [e70]; exact al_ret _ hC.2.2.2.2.2.1
    · obtain ⟨d', i', ⟨hMI, -, hpsc, hsi⟩, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩,
        hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, i', d'.er d.a.extRate, ih,
        ⟨mi_er _ hMI, hok, ?_, xkeep_trans hI.2.2.2.1 hxk, hsi hI.2.2.2.2.1⟩, ⟨hi', hrb.2⟩, ?_⟩, ?_⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [hbx']; exact hbx
      · rw [h12']; exact h12
      · rw [h13']; exact h13
      · show PI d'.a.psc
        rw [hpsc]; exact hI.2.2.1
      · show (T kc Ext X ra t₀ (Saved t₀) (LocW0 X t₀ i') (d'.er d.a.extRate) ih) s'.dmem
        rw [T_hdr, GR_er _ _ _ _ _ _ hxk.2.2.2.2.2.2 hxk.2.2.2.2.2.1]
        rw [e70] at hm'
        exact hm'
      · first | exact Nat.le_of_eq (var_L128 _) | (rw [var_L128]; omega)

end Kraken.Examples.Sbr.DecExt
