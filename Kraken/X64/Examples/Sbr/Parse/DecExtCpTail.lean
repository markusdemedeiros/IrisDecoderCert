import Kraken.X64.Examples.Sbr.Parse.DecExtCpB

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the coupled channel pair (the copy)

`L5cc`–`L647`: the byte copies of the inlined `copy_sbr_grid(&data[1], &data[0])` (`CpI`);
`L663`: the raw `e_a[1]` copy and `read_sbr_dtdf` of `data[0]`; `L6b3`, `L6d0`: the two `memcpy`
of `bs_invf_mode`.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L663 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hD : DtdfSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L663" := by
  cfg_block
  measure_hb "L663"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, hdx, hbx⟩, hn⟩ := hs₀
    var_c hn
    have p_h0 : PLift _ := ⟨hm⟩
    clear hm
    have D0 := hE.1.1.2.2.1
    have D1 := hE.1.1.2.2.2.1
    vcgen [MachineWP.call_proc_spec_at (cD X ra t₀ d i0 gi ih) "read_sbr_dtdf" hD]
    all_goals try call_simp
    all_goals try subst_vars
    case vc4 =>
      rename_i s v _ w _ hx
      have hm2 : (storeInt s.dmem (s.regs.get64 .r14 + Int64.toBitVec 269672) 4
          (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 v))).toInt)
          =⋆ T kc Ext X ra t₀ (Saved t₀) (LocW X t₀ i0 gi) d ih := by
        have hmu := p_h0.down
        simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
          BitVec.reduceAdd] at hmu ⊢
        simp only [h14, Int64.toBitVec_ofNat_norm]
        try sep_mem hmu
        sep_close hmu
      generalize (storeInt s.dmem (s.regs.get64 .r14 + Int64.toBitVec 269672) 4
          (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 v))).toInt) = M at hm2 hx ⊢
      have hv : w = Int.ofBytes (Int.toBytes 4 d.usac.toInt) := by
        have hmu := hm2
        simp only [T, DecF, SbrF, SbrS, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hmu
        simp only [h14, Int64.toBitVec_ofNat_norm] at hx ⊢
        sep_vals hmu
        rfl
      subst hv
      rw [T_dat] at hm2
      have hld : (M.loadInt (s.regs.get64 .rsp - 8#64) 8).isSome = true := by
        rw [hsp, BitVec.sub_sub_ofNat]
        exact Block.loadInt_isSome hm2 (by simp)
      have hpush := fun v => Block.storeInt_val hm2 (Split.here _ _) v
      have e70 : s.regs.get64 .rsp - Width.W64.bytesv = t₀.regs.get64 .rsp - 112#64 := by
        rw [hsp]; show _ - 104#64 - 8#64 = _; bv_omega
      clear hm2
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, ?_, ?_, Or.inl hdx, ?_,
        D0.2.2.2.2.1, D0.2.2.2.2.2.2.1, D1.2.2.2.2.1, D1.2.2.2.2.2.2.1⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt_toInt, BitVec.setWidth_32_64_32]
      · rw [hbp, show (-64 : Int64).toBitVec = -64#64 from rfl]; bv_omega
      · simp only [BitVec.xor_self, BitVec.setWidth_zero]
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        to_tableC tableC.match_1.eq_45
        refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, ?_, ?_, ?_⟩,
          Nat.le_of_eq (var_L686 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [T, DecF, GRW] at hm' ⊢
          sep_close hm'
        · rw [h12']; exact h12
        · rw [h13', hbp]; exact sub8_m64 _
        · rw [hbx']; exact hbx
    all_goals
      have hmu := p_h0.down
      simp only [DecF, SbrF, DataF, SbrS, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd] at hmu
      simp only [h14, Int64.toBitVec_ofNat_norm]
      sep_mem hmu

end Kraken.Examples.Sbr.DecExt
