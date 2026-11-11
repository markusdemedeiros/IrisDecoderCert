import Kraken.X64.Examples.Sbr.Parse.DecExtCpeH

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the coupled channel pair (the calls)

After the copy (`EInv`): `L686` `read_sbr_dtdf` of `data[1]`, `L69a` `read_sbr_invf` of
`data[0]`, `L6ed` `read_sbr_envelope` of `data[0]`, `L708` `read_sbr_noise` of `data[0]`, `L729`
`read_sbr_envelope` of `data[1]`; `L751` sets up the `read_sbr_noise` of `data[1]` at `L76e`.
As the blocks `L239`, `L251`, `L27c`, `L2c2`, `L29e` of the independent pair.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L686 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hD : DtdfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L686" := by
  cfg_block
  measure_hb "L686"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
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
      · first | exact hbx | (rw [h14]; exact r14_d1 _)
      · simp only [BitVec.xor_self, BitVec.setWidth_zero]
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_46
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_⟩,
          Nat.le_of_eq (var_L69a _)⟩
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


theorem blk_L69a (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hI : InvfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L69a" := by
  cfg_block
  measure_hb "L69a"
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
      to_tableC tableC.match_1.eq_47
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, einv_invf0 hE hok hxk, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_,
        ?_⟩, Nat.le_of_eq (var_L6b3 _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [T, DecF, GRW, invf0_eq, AcF] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact h12
      · rw [h13']; exact h13
      · rw [hbx', h14]; rfl


theorem blk_L6ed (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hV : EnvSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L6ed" := by
  cfg_block
  measure_hb "L6ed"
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
      to_tableC tableC.match_1.eq_50
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_⟩,
        Nat.le_of_eq (var_L708 _)⟩
      · rw [hsp', e70]; exact sub112 _
      · rw [hbp']; exact hbp
      · rw [h14']; exact h14
      · rw [e70] at hm'
        simp only [T, DecF, GRW] at hm' ⊢
        sep_close hm'
      · rw [h12']; exact h12
      · rw [hbx', h14]; exact r14_d0 _


theorem blk_L708 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hN : NoiseSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L708" := by
  cfg_block
  measure_hb "L708"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, hbx⟩, hn⟩ := hs₀
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
        to_tableC tableC.match_1.eq_51
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_⟩,
          Nat.le_of_eq (var_L729 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12


theorem blk_L729 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hV : EnvSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L729" := by
  cfg_block
  measure_hb "L729"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12⟩, hn⟩ := hs₀
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
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, h12, ?_, ?_, Or.inr ?_, D0, D1,
        hn0, hn1, hal⟩, fun s' hpost => ?_⟩, fun a ha s' => Or.inr (Or.inr (Or.inr ha)), hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · rw [h14]; rfl
      · rw [hbp]; exact sub8_m64 _
      · rw [h14]; exact r14_d1 _
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_52
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_⟩,
          Nat.le_of_eq (var_L751 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12


theorem blk_L751 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L751" := by
  cfg_block
  measure_hb "L751"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12⟩, hn⟩ := hs₀
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
      to_tableC tableC.match_1.eq_17
      refine ⟨⟨⟨hC, ⟨by fr_ok, by fr_ok, by fr_ok⟩, i0, gi, d, ih, hE, hrb, p_h0.down⟩, ?_, ?_, ?_,
        ?_⟩, by simp only [var_L76e]; omega⟩
      all_goals simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
        Int64.toBitVec_ofNat_norm]
      · rw [hbp]; exact sub8_m64 _
      · exact h12
      · rw [h14]
      · rw [h14]; exact r14_d1 _

end Kraken.Examples.Sbr.DecExt
