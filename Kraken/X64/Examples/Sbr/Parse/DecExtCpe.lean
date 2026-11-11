import Kraken.X64.Examples.Sbr.Parse.DecExtPs

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the channel pair element (dispatch)

`L164` sends `id_aac = 1` to `L16e` (`read_sbr_channel_pair_element`), any other id to `L466`
(the log of an invalid id, then `L481` to `L48b`). `L779`: a negative result of the last
`read_sbr_noise` jumps to `L48b`.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option hygiene false in
/-- A goal `table … l s` with `l` a label of `tableC`: the main table's last case, `tableE`'s
last case, then the `tableC` case `e`. -/
macro "to_tableC " e:ident : tactic => `(tactic| (
  try rw [table.match_1.eq_46]
  all_goals try (intro h; simp only [String.reduceEq] at h)
  unfold tableE
  rw [tableE.match_1.eq_19]
  all_goals try (intro h; simp only [String.reduceEq] at h)
  unfold tableC
  rw [$e:ident]
  all_goals try (intro h; simp only [String.reduceEq] at h)))

/-- The ranking `var` at the literal labels of the channel pair element. -/
macro "var_c " h:ident : tactic => `(tactic| (
  simp only [var_L466, var_L481, var_L16e, var_L1a7, var_L1d4, var_L1ea, var_L483, var_L591,
    var_L215, var_L239, var_L251, var_L26a, var_L27c, var_L29e, var_L2c2, var_L2e3, var_L76e,
    var_L779, var_L781, var_L7b5, var_L8e2, var_L8ec, var_L913, var_L939, var_L960, var_L998,
    var_L9a7, var_L9d4, var_La04, var_La29, var_La33, var_La59, var_La80, var_Laa6, var_Ladf,
    var_Laed, var_L5a2, var_L5cc, var_L5e1, var_L5fd, var_L614, var_L62b, var_L647, var_L663,
    var_L686, var_L69a, var_L6b3, var_L6d0, var_L6ed, var_L708, var_L729, var_L751] at $h:ident
  subst $h:ident))

omit [CodeEnv] in
theorem sinv_tinv {PI : List UInt8 → Prop} {X : XA} {t₀ : MachineData} {d : DS}
    (h : SInv PI X t₀ d) : TInv PI X d :=
  ⟨h.1.1.1, h.1.2⟩

theorem blk_L164 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L164" := by
  cfg_block
  measure_hb "L164"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hS, hr8⟩, hrb, hm⟩, hsi, h12, h13, hz⟩, hn⟩ :=
      hs₀
    var_n hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    case vc1 =>
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_1
      refine ⟨by decide, ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, sinv_tinv hS, hrb, p_h0.down⟩, h12,
        h13⟩, ?_⟩
      edge_ok var_L466
    case vc2 =>
      rename_i hc
      to_tableC tableC.match_1.eq_3
      refine ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hS, hr8⟩, hrb, p_h0.down⟩, hsi, h12, ?_⟩,
        Nat.le_of_eq (var_L16e _)⟩
      dsimp only at hc
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result_sub, h13, sw32_64,
        Bool.not_eq_false', beq_iff_eq] at hc
      exact hc

theorem blk_L481 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L481" := by
  cfg_block
  measure_hb "L481"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hT, hrb, hm⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    left; apply Table.ofLabels_at
    rw [table.match_1.eq_26]
    refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hT, hrb, p_h0.down⟩, ?_⟩
    edge_ok var_L48b

theorem blk_L779 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L779" := by
  cfg_block
  measure_hb "L779"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    case vc1 =>
      rename_i hs _ _; subst hs
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_26]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, einv_tinv hE, hrb, p_h0.down⟩, ?_⟩
      edge_ok var_L48b
    case vc2 =>
      rename_i hs _ _; subst hs
      to_tableC tableC.match_1.eq_19
      exact ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, p_h0.down⟩, Nat.le_of_eq (var_L781 _)⟩

omit [CodeEnv] in
theorem r14_sbr (t₀ : MachineData) :
    t₀.regs.get64 .rsi + Int64.toBitVec 166176 = sbrA t₀ := rfl

theorem blk_L2c2 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hN : NoiseSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L2c2" := by
  cfg_block
  measure_hb "L2c2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, hbx, h13⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have hq := hE.1.1.1.2.2.2.2.2.2.2.2.2.1
    have hz0 := hE.1.1.2.2.1.2.2.2.2.2.2.1
    have hz1 := hE.1.1.2.2.2.1.2.2.2.2.2.2.1
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_noise" hN]
    all_goals try call_simp
    case vc1 =>
      rename_i hs _ _; subst hs
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_26]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, einv_tinv hE, hrb, p_h0.down⟩, ?_⟩
      edge_ok var_L48b
    case vc2 =>
      rename_i hs _ _ _; subst hs
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, h12, ?_, ?_, Or.inl hbx, hq, hz0,
        hz1⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · rw [h14]; rfl
      · rw [hbp]; exact sub8_m64 _
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_16
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_, ?_⟩,
          Nat.le_of_eq (var_L2e3 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12
        · rw [hbx']; exact hbx
        · rw [h13']; exact h13

theorem blk_L2e3 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L2e3" := by
  cfg_block
  measure_hb "L2e3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, hbx, h13⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals subst s₀
    case vc1 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_26]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, einv_tinv hE, hrb, p_h0.down⟩, ?_⟩
      edge_ok var_L48b
    case vc2 =>
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_17
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, p_h0.down⟩, ?_, ?_, ?_, ?_⟩,
        ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, hsp, hbp, h14,
        h12, h13]
      all_goals first
        | edge_ok var_L76e
        | (rw [show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega)
        | exact r14_sbr _

theorem blk_L76e (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hN : NoiseSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L76e" := by
  cfg_block
  measure_hb "L76e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hdx, hdi, hsi, hcx⟩, hn⟩ := hs₀
    var_c hn
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have hq := hE.1.1.1.2.2.2.2.2.2.2.2.2.1
    have hz0 := hE.1.1.2.2.1.2.2.2.2.2.2.1
    have hz1 := hE.1.1.2.2.2.1.2.2.2.2.2.2.1
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_noise" hN]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, hdi, hsi, hdx, Or.inr hcx, hq, hz0,
      hz1⟩, fun s' hpost => ?_⟩, hld⟩
    · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
    · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      to_tableC tableC.match_1.eq_18
      refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, Nat.le_of_eq (var_L779 _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [T, DecF, GRW] at hm' ⊢
        sep_close hm'

omit [CodeEnv] in
theorem r14_d0 (t₀ : MachineData) :
    t₀.regs.get64 .rsi + Int64.toBitVec 166304 = sbrA t₀ + 0x80#64 := by
  rw [show Int64.toBitVec 166304 = 166304#64 from rfl]; simp only [sbrA, arg1]; bv_omega

omit [CodeEnv] in
theorem r14_d1 (t₀ : MachineData) :
    t₀.regs.get64 .rsi + Int64.toBitVec 255072 = sbrA t₀ + 0x15b40#64 := by
  rw [show Int64.toBitVec 255072 = 255072#64 from rfl]; simp only [sbrA, arg1]; bv_omega

theorem blk_L27c (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hV : EnvSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L27c" := by
  cfg_block
  measure_hb "L27c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
    var_c hn
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have hal : (sbrA t₀).toNat % 32 = 0 := by
      have h := hC.2.2.2.2.2.2.2.2.1
      simp only [isAligned, beq_iff_eq] at h
      exact h
    have D0 := hE.1.1.2.2.1
    have D1 := hE.1.1.2.2.2.1
    have hn0 := hE.1.1.1.2.2.2.2.2.2.2.1
    have hn1 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    vcgen [call_procS_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_envelope" hV]
    all_goals try call_simp
    rename_i hs _; subst hs
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, ?_, ?_, ?_, Or.inl ?_, D0, D1,
      hn0, hn1, hal⟩, fun s' hpost => ?_⟩, fun a ha s' => Or.inr (Or.inr (Or.inr ha)), hld⟩
    · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
    · exact h12
    · exact hbx
    · exact h13
    · rw [h14]; exact r14_d0 _
    · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      to_tableC tableC.match_1.eq_14
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_, ?_⟩,
        Nat.le_of_eq (var_L29e _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [T, DecF, GRW] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact h12
      · rw [hbx', h14]; exact r14_d0 _
      · rw [h13', h14]; exact r14_d1 _

theorem blk_L29e (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hV : EnvSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L29e" := by
  cfg_block
  measure_hb "L29e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, hbx, h13⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have hal : (sbrA t₀).toNat % 32 = 0 := by
      have h := hC.2.2.2.2.2.2.2.2.1
      simp only [isAligned, beq_iff_eq] at h
      exact h
    have D0 := hE.1.1.2.2.1
    have D1 := hE.1.1.2.2.2.1
    have hn0 := hE.1.1.1.2.2.2.2.2.2.2.1
    have hn1 := hE.1.1.1.2.2.2.2.2.2.2.2.1
    vcgen [call_procS_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_envelope" hV]
    all_goals try call_simp
    case vc1 =>
      rename_i hs _ _; subst hs
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_26]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, einv_tinv hE, hrb, p_h0.down⟩, ?_⟩
      edge_ok var_L48b
    case vc2 =>
      rename_i hs _ _ _; subst hs
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, h12, ?_, ?_, Or.inr h13, D0, D1,
        hn0, hn1, hal⟩, fun s' hpost => ?_⟩, fun a ha s' => Or.inr (Or.inr (Or.inr ha)), hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · rw [h14]; rfl
      · rw [hbp]; exact sub8_m64 _
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_15
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_, ?_⟩,
          Nat.le_of_eq (var_L2c2 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12
        · rw [hbx']; exact hbx
        · rw [h13']; exact h13

omit [CodeEnv] in
theorem invf1_eq (d : DS) (vals : Nat → Nat) :
    d.invf 1 vals = { d with a := { d.a with d1 := invfRead d.a.nq d.a.d1 vals } } := rfl

omit [CodeEnv] in
/-- `read_sbr_invf` on `data[1]` keeps `EInv`. -/
theorem einv_invf1 {PI : List UInt8 → Prop} {X : XA} {d : DS} {vals : Nat → Nat}
    (hE : EInv PI X d) (hok : (d.invf 1 vals).ok) (hxk : XKeep d.a (d.invf 1 vals).a) :
    EInv PI X (d.invf 1 vals) := by
  rw [invf1_eq] at hok hxk ⊢
  obtain ⟨⟨⟨a1, a2, a3, a4, a5, a6⟩, i1⟩, ⟨l0, l1⟩, -, hP, hK, hsi⟩ := hE
  exact ⟨⟨⟨a1, a2, a3, dwf_invfRead a4, a5, a6⟩, i1⟩, ⟨l0, fun h => live_invfRead (l1 h)⟩, hok,
    hP, xkeep_trans hK hxk, hsi⟩

theorem blk_L251 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hI : InvfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L251" := by
  cfg_block
  measure_hb "L251"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_c hn
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have hq := hE.1.1.1.2.2.2.2.2.2.2.2.2.1
    have hl0 := hE.1.1.2.2.1.2.1
    have hl1 := hE.1.1.2.2.2.1.2.1
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_invf" hI]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, ?_, h13, Or.inl ?_, hq, hl0, hl1⟩,
      fun s' hpost => ?_⟩, hld⟩
    · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
    · rw [h14]; rfl
    · rw [h14]; exact r14_d0 _
    · obtain ⟨d', i', ⟨vals, hd'⟩, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ :=
        hpost
      rw [h14, r14_d0] at hd'
      simp only [↓reduceIte] at hd'
      subst hd'
      refine MachineWP.nil_spec.le_wp s' ?_
      to_tableC tableC.match_1.eq_12
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, einv_invf0 hE hok hxk, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_,
        ?_⟩, Nat.le_of_eq (var_L26a _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [T, DecF, GRW, invf0_eq, AcF] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact h12
      · rw [h13']; exact h13
      · rw [hbx', h14]; rfl

theorem blk_L26a (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hI : InvfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L26a" := by
  cfg_block
  measure_hb "L26a"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
    var_c hn
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have hq := hE.1.1.1.2.2.2.2.2.2.2.2.2.1
    have hl0 := hE.1.1.2.2.1.2.1
    have hl1 := hE.1.1.2.2.2.1.2.1
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_invf" hI]
    all_goals try call_simp
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, ?_, ?_, Or.inr ?_, hq, hl0, hl1⟩,
      fun s' hpost => ?_⟩, hld⟩
    · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
    · exact hbx
    · exact h13
    · rw [h14]; exact r14_d1 _
    · obtain ⟨d', i', ⟨vals, hd'⟩, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ :=
        hpost
      rw [h14, r14_d1] at hd'
      have hne : ¬ (sbrA t₀ + 0x15b40#64 = sbrA t₀ + 0x80#64) := by
        intro h; have := congrArg (· - sbrA t₀) h; simp at this
      simp only [hne, ↓reduceIte] at hd'
      subst hd'
      refine MachineWP.nil_spec.le_wp s' ?_
      to_tableC tableC.match_1.eq_13
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, einv_invf1 hE hok hxk, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_,
        ?_⟩, Nat.le_of_eq (var_L27c _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [T, DecF, GRW, invf1_eq, AcF] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact h12
      · rw [h13']; exact h13
      · rw [hbx']; exact hbx


theorem blk_L215 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hD : DtdfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L215" := by
  cfg_block
  measure_hb "L215"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hT, hE⟩, hrb, hm⟩, h12⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_dtdf" hD]
    all_goals try call_simp
    all_goals try subst_vars
    case vc3 =>
      rename_i v hx _
      have hv : v = Int.ofBytes (Int.toBytes 4 d.usac.toInt) := by
        have hmu := p_h0.down
        simp only [DecF, SbrF, SbrS, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hmu
        simp only [h14, Int64.toBitVec_ofNat_norm] at hx
        sep_vals hmu
        rfl
      subst hv
      rename_i _ hz _
      have hE' := hE (by
        simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.and_self,
          Bool.not_eq_false', beq_iff_eq] at hz
        exact hz)
      have D0 := hT.1.2.2.1
      have D1 := hT.1.2.2.2.1
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hT.2.1⟩, ?_, ?_, Or.inl ?_, ?_,
        D0.2.2.2.2.1, D0.2.2.2.2.2.2.1, D1.2.2.2.2.1, D1.2.2.2.2.2.2.1⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, BitVec.setWidth_32_64_32]
      · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
      · rw [h14]; exact r14_d0 _
      · simp only [BitVec.xor_self, BitVec.setWidth_zero]
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_10
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE', ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_⟩,
          Nat.le_of_eq (var_L239 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12
        · rw [h13', hbp]; exact sub8_m64 _
    case vc1 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_26]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hT, hrb, p_h0.down⟩, ?_⟩
      edge_ok var_L48b
    case vc2 =>
      have hmu := p_h0.down
      simp only [DecF, SbrF, SbrS, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
      simp only [h14, Int64.toBitVec_ofNat_norm]
      sep_mem hmu

theorem blk_L239 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hD : DtdfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L239" := by
  cfg_block
  measure_hb "L239"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    have D0 := hE.1.1.2.2.1
    have D1 := hE.1.1.2.2.2.1
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_dtdf" hD]
    all_goals try call_simp
    all_goals try subst_vars
    case vc2 =>
      rename_i v hx _
      have hv : v = Int.ofBytes (Int.toBytes 4 d.usac.toInt) := by
        have hmu := p_h0.down
        simp only [DecF, SbrF, SbrS, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hmu
        simp only [h14, Int64.toBitVec_ofNat_norm] at hx
        sep_vals hmu
        rfl
      subst hv
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, ?_, h13, Or.inr ?_, ?_,
        D0.2.2.2.2.1, D0.2.2.2.2.2.2.1, D1.2.2.2.2.1, D1.2.2.2.2.2.2.1⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, BitVec.setWidth_32_64_32]
      · rw [h14]; exact r14_d1 _
      · simp only [BitVec.xor_self, BitVec.setWidth_zero]
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_11
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_⟩,
          Nat.le_of_eq (var_L251 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12
        · rw [h13']; exact h13
    case vc1 =>
      have hmu := p_h0.down
      simp only [DecF, SbrF, SbrS, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hmu
      simp only [h14, Int64.toBitVec_ofNat_norm]
      sep_mem hmu

theorem blk_L483 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L483" := by
  cfg_block
  measure_hb "L483"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hT, hC0⟩, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    case vc1 =>
      rename_i hs _ hz; subst hs
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_8
      simp only [CondCode.interp_z, StatusFlags.zf_from_result, BitVec.and_self,
        beq_iff_eq] at hz
      refine ⟨by decide, ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hC0 hz, hrb, p_h0.down⟩, h12, h13⟩,
        ?_⟩
      edge_ok var_L591
    case vc2 =>
      rename_i hs _ _; subst hs
      rw [table.match_1.eq_26]
      exact ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hT, hrb, p_h0.down⟩, by
        simp only [var_L48b]; omega⟩

omit [CodeEnv] in
theorem setCh_true (d : DS) (v : DV) : d.setCh true v = { d with a := { d.a with d1 := v } } :=
  rfl

omit [CodeEnv] in
/-- After `read_sbr_grid` on `data[0]` of a channel pair element (`id_aac = 1`): `TInv`, and
`CInv0` on success. -/
theorem grid_inv_c {PI : List UInt8 → Prop} {X : XA} {t₀ : MachineData} {d : DS}
    {n nn : Nat} {fr te tq : List UInt8} {ret : BitVec 32} (hS : SInv PI X t₀ d)
    (hid : idA t₀ = 1#32)
    (hok : (d.setCh false (dvGrid d.a.d0 n fr nn te tq)).ok)
    (hxk : XKeep d.a (d.setCh false (dvGrid d.a.d0 n fr nn te tq)).a)
    (hG : GridV (dvGrid d.a.d0 n fr nn te tq) ret) :
    TInv PI X (d.setCh false (dvGrid d.a.d0 n fr nn te tq))
      ∧ (ret = 0#32 → CInv0 PI X (d.setCh false (dvGrid d.a.d0 n fr nn te tq))) := by
  rw [setCh_false] at hok hxk ⊢
  obtain ⟨⟨⟨⟨a1, a2, -, a4, a5, a6⟩, i1⟩, -, hP, hK, hsi⟩, hst, hidA⟩ := hS
  have hA : AI { d.a with d0 := dvGrid d.a.d0 n fr nn te tq } :=
    ⟨a1, a2, hG.1, a4, a5, ⟨hG.2.1, a6.2⟩⟩
  exact ⟨⟨hA, hok, hP, xkeep_trans hK hxk, hsi⟩, fun h0 => ⟨⟨hA, i1⟩, hG.2.2.2 h0, hok, hP,
    xkeep_trans hK hxk, hsi, hst, hidA.trans hid⟩⟩

omit [CodeEnv] in
/-- After `read_sbr_grid` on `data[1]` from `CInv0`: `TInv`, and `EInv` on success. -/
theorem grid_einv1 {PI : List UInt8 → Prop} {X : XA} {d : DS}
    {n nn : Nat} {fr te tq : List UInt8} {ret : BitVec 32} (hC : CInv0 PI X d)
    (hok : (d.setCh true (dvGrid d.a.d1 n fr nn te tq)).ok)
    (hxk : XKeep d.a (d.setCh true (dvGrid d.a.d1 n fr nn te tq)).a)
    (hG : GridV (dvGrid d.a.d1 n fr nn te tq) ret) :
    TInv PI X (d.setCh true (dvGrid d.a.d1 n fr nn te tq))
      ∧ (ret = 0#32 → EInv PI X (d.setCh true (dvGrid d.a.d1 n fr nn te tq))) := by
  rw [setCh_true] at hok hxk ⊢
  obtain ⟨⟨⟨a1, a2, a3, -, a5, a6⟩, i1⟩, hL0, -, hP, hK, hsi, -, -⟩ := hC
  have hA : AI { d.a with d1 := dvGrid d.a.d1 n fr nn te tq } :=
    ⟨a1, a2, a3, hG.1, a5, ⟨a6.1, hG.2.1⟩⟩
  exact ⟨⟨hA, hok, hP, xkeep_trans hK hxk, hsi⟩, fun h0 => ⟨⟨hA, i1⟩,
    ⟨fun _ => hL0, fun _ => hG.2.2.2 h0⟩, hok, hP, xkeep_trans hK hxk, hsi⟩⟩

theorem blk_L1d4 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hG : GridSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L1d4" := by
  cfg_block
  measure_hb "L1d4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hS, hrb, hm⟩, hsi, h12, hid⟩, hn⟩ := hs₀
    var_c hn
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [call_procS_spec_at ((cD X ra t₀ d i0 gi ih), false) "read_sbr_grid" hG.toS]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hS.1.2.1⟩, ?_, ?_, ?_, ?_, hS.1.1.1.2.2.1,
      hS.1.1.1.2.2.2.2.2.1⟩, fun s' hpost => ?_⟩, fun a ha s' => Or.inr (Or.inr (Or.inl ha)), hld⟩
    · rw [e70]; exact hpush _
    · exact h12
    · exact hsi
    · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
    · rw [h14]; exact r14_d0 _
    · obtain ⟨d', i', ⟨n', fr, nn, te, tq, rfl, hGV⟩, hok, hxk, hi', hsp', hbp',
        ⟨-, h12', h13', h14', -⟩, hm'⟩ := hpost
      refine MachineWP.nil_spec.le_wp s' ?_
      to_tableC tableC.match_1.eq_6
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih,
        grid_inv_c (n := n') (fr := fr) (nn := nn) (te := te) (tq := tq) hS hid hok hxk hGV,
        ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_⟩, Nat.le_of_eq (var_L1ea _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [T, DecF, GRW, setCh_false, AcF] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact h12
      · rw [h13', h14]; exact r14_d0 _

theorem blk_L1ea (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hG : GridSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L1ea" := by
  cfg_block
  measure_hb "L1ea"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hT, hC0⟩, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    rw [T_dat] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    clear hm
    vcgen [call_procS_spec_at ((cD X ra t₀ d i0 gi ih), true) "read_sbr_grid" hG.toS]
    all_goals try call_simp
    case vc1 =>
      rename_i hs _ _; subst hs
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_7
      refine ⟨by decide, ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hT, hC0⟩, hrb, p_h0.down⟩, h12,
        h13⟩, ?_⟩
      edge_ok var_L483
    case vc2 =>
      rename_i hs _ _ _ _; subst hs
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_26]
      refine ⟨by decide, ⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hT, hrb, p_h0.down⟩, ?_⟩
      edge_ok var_L48b
    case vc3 =>
      rename_i hs _ _ _ hz; subst hs
      simp only [CondCode.interp_nz, StatusFlags.zf_from_result, BitVec.and_self,
        Bool.not_eq_false', beq_iff_eq] at hz
      have hC1 := hC0 hz
      all_goals try dsimp only at *
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hT.2.1⟩, ?_, ?_, ?_, ?_, hT.1.2.2.2.1,
        hT.1.2.2.2.2.2.2⟩, fun s' hpost => ?_⟩, fun a ha s' => Or.inr (Or.inr (Or.inl ha)), hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · exact h12
      · rw [h14]; exact r14_sbr _
      · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
      · rw [h14]; exact r14_d1 _
      · obtain ⟨d', i', ⟨n', fr, nn, te, tq, rfl, hGV⟩, hok, hxk, hi', hsp', hbp',
          ⟨-, h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_9
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih,
          grid_einv1 (n := n') (fr := fr) (nn := nn) (te := te) (tq := tq) hC1 hok hxk hGV,
          ⟨hi', hrb.2⟩, ?_⟩, ?_⟩, Nat.le_of_eq (var_L215 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW, setCh_true, AcF] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12

theorem blk_L466 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hAv : AvLogSpec Ext kc) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L466" := by
  cfg_block
  measure_hb "L466"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hT, hrb, hm⟩, h12, h13⟩, hn⟩ := hs₀
    var_c hn
    have hl1 : (s₀.dmem.loadInt (t₀.regs.get64 .rdi + 8#64) 8).isSome = true := by
      have hm' := hm
      simp only [T, DecF, AvW, arg0] at hm'
      sep_mem hm'
    obtain ⟨F, hF⟩ := T_ext kc Ext X ra t₀ (Saved t₀) (LocW X t₀ i0 gi) d ih
    rw [hF] at hm
    have hld : (s₀.dmem.loadInt (s₀.regs.get64 .rsp - 8#64) 8).isSome = true := by
      rw [hsp, BitVec.sub_sub_ofNat]
      exact Block.loadInt_isSome hm (by simp)
    have hpush := fun v => Block.storeInt_val hm (Split.here _ _) v
    have e70 : s₀.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
      rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
    vcgen [MachineWP.call_proc_spec_at F "av_log" hAv]
    all_goals try call_simp
    all_goals try dsimp only at *
    all_goals try subst_vars
    case vc1 =>
      simp only [h12, AddrIndex.offset64_none, add_ofNat0]
      rw [show (8 : Int64).toBitVec = 8#64 from rfl]
      exact hl1
    case vc2 =>
      refine ⟨fun ra' => ⟨⟨?_, trivial⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [e70]; exact hpush _
      · rw [e70] at hpost
        obtain ⟨hsp', hbp', ⟨-, -, -, h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_2
        refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hT, hrb, ?_⟩, ?_⟩
        · rw [hsp']; bv_omega
        all_goals try (first | rw [hbp']; exact hbp | rw [h14']; exact h14)
        · exact (congrFun hF s'.dmem).mpr hm'
        · simp only [var_L481]; omega

theorem blk_L16e (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L16e" := by
  cfg_block
  measure_hb "L16e"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨hS, hr8⟩, hrb, hm⟩, hsi, h12, hid⟩, hn⟩ := hs₀
    var_c hn
    simp only [T, DecF, LocW, GbR, GbW] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have hgi : (BitVec.setWidth 32 (s₀.regs.get64 .r8)).toNat ≤ X.r.p8.toNat := by
      rw [hr8]; exact hrb.1
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, hsi, DecF]
    dx_br hm
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Width.bytes,
      BitVec.mul_one] at *
    case vc3 =>
      sep_mem hm
      rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega]
      exact rd_off1 _ _ _ hgi hC.2.2.2.1.2.2.1
    case vc4 =>
      to_tableC tableC.match_1.eq_4
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, _, d, ih, hS, hrb, ?_⟩, ?_, ?_, hid, ?_, ?_, ?_⟩, ?_⟩
      all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
      · exact hsp
      · exact hbp
      · exact h14
      · simp only [T, DecF, LocW, GbR, GbW]
        try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
        sep_close hm
      · exact hsi
      · exact h12
      · split
        · rw [BitVec.add_comm]; exact setl_inc _ _ _ _ _ hgi hC.2.2.2.1.2.1
        · exact clamp_le _ _ _ _
      all_goals first
        | exact Nat.le_of_eq (var_L1a7 _)
        | (simp only [var_L1a7]; omega)

omit [CodeEnv] in
theorem acf_coup (ac : BitVec 64) (x : Args) (c sr : BitVec 32) :
    AcF ac { x with coupling := c } sr = AcF ac x sr := rfl

omit [CodeEnv] in
theorem tabf_coup (x : Args) (c : BitVec 32) (s : BitVec 64) :
    TabF { x with coupling := c } s = TabF x s := rfl

omit [CodeEnv] in
/-- `bs_coupling` is outside `SInv`. -/
theorem sinv_coup {PI : List UInt8 → Prop} {X : XA} {t₀ : MachineData} {d : DS} (c : BitVec 32)
    (h : SInv PI X t₀ d) : SInv PI X t₀ { d with a := { d.a with coupling := c } } := h

theorem blk_L1a7 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L1a7" := by
  cfg_block
  measure_hb "L1a7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hS, hrb, hm⟩, hsi, h12, hid, hcx, hdx, hax⟩,
      hn⟩ := hs₀
    var_c hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, SbrS, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, h12, hsi, hax, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try simp only [Width.bytes, BitVec.mul_one] at *
    all_goals try (rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega, sw32_64]
                   exact rd_off1 _ _ _ hcx hC.2.2.2.1.2.2.1)
    rename_i hld
    generalize hv : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 _ + BitVec.setWidth 32 _))
      : BitVec 32) = v at hm
    generalize hc : (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.setWidth 64 _)
      &&& BitVec.setWidth 32 1#64)) : BitVec 32) = c at hm
    to_tableC tableC.match_1.eq_5
    refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, v, { d with a := { d.a with coupling := c } }, ih,
      sinv_coup c hS, ⟨?_, hrb.2⟩, ?_⟩, ?_, ?_, hid⟩, ?_⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_false, sw32_64]
    · exact hsp
    · exact hbp
    · exact h14
    · rw [← hv, sw32_64, hdx]
      exact setl_inc _ _ _ _ _ (hdx ▸ hcx) hC.2.2.2.1.2.1
    · simp only [T, DecF, LocW, GbR, GbW, SbrF, SbrS, sbrA, arg1, acf_coup, tabf_coup,
        BitVec.add_assoc, BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm
    · exact hsi
    · exact h12
    all_goals first
      | exact Nat.le_of_eq (var_L1d4 _)
      | (simp only [var_L1d4]; omega)

theorem blk_L781 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L781" := by
  cfg_block
  measure_hb "L781"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_c hn
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen [shl_cl32_havoc]
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    dx_br hm
    all_goals try simp only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Width.bytes,
      BitVec.mul_one] at *
    case vc4 =>
      sep_mem hm
      rw [show ∀ a b : BitVec 64, a + b - a = b from fun a b => by bv_omega]
      exact rd_off1 _ _ _ hrb.1 hC.2.2.2.1.2.2.1
    case vc6 =>
      left; apply Table.ofLabels_at
      to_tableC tableC.match_1.eq_28
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      all_goals first
        | exact trivial
        | edge_ok var_L9d4
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
           all_goals first
             | exact setl_inc _ _ _ _ _ hrb.1 hC.2.2.2.1.2.1
             | (rw [BitVec.add_comm]; exact setl_inc _ _ _ _ _ hrb.1 hC.2.2.2.1.2.1)
             | rfl
             | assumption)
        | (simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
             BitVec.reduceAdd]
           try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
           sep_close hm)
    case vc7 =>
      to_tableC tableC.match_1.eq_20
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_⟩, Nat.le_of_eq (var_L7b5 _)⟩
      all_goals first
        | exact trivial
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
           all_goals first
             | exact setl_inc _ _ _ _ _ hrb.1 hC.2.2.2.1.2.1
             | (rw [BitVec.add_comm]; exact setl_inc _ _ _ _ _ hrb.1 hC.2.2.2.1.2.1)
             | rfl
             | assumption)
        | (simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
             BitVec.reduceAdd]
           try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
           sep_close hm)

end Kraken.Examples.Sbr.DecExt
