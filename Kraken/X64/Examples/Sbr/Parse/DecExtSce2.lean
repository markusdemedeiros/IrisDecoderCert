import Kraken.X64.Examples.Sbr.Parse.DecExtSce

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the single channel element, after `read_sbr_envelope`

`L3e4` (a negative result of `read_sbr_envelope` jumps to `L48b`, else the `read_sbr_noise`
call) and `L401` (a negative result of `read_sbr_noise` jumps to `L48b`). `EInv` gives the
`TInv` of `L48b`. `L409`: the inlined `get_bits1` of `bs_add_harmonic_flag[0]`, stored at
`sbr + 0x84`; the next index stays in `eax` (`RegB`) for `Lb1a` or `L43d`.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem einv_tinv {PI : List UInt8 → Prop} {X : XA} {d : DS} (h : EInv PI X d) : TInv PI X d :=
  ⟨h.1.1, h.2.2⟩

theorem blk_L3e4 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop)
    (hN : NoiseSpec kc Ext) (X : XA) (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L3e4" := by
  cfg_block
  measure_hb "L3e4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
    var_n hn
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
      refine ⟨fun ra' => ⟨⟨⟨?_, ⟨hrb.1, hC.2.2.2.1.2⟩, hE.2.2.1⟩, hbx, h12, ?_, Or.inl h13, hq, hz0,
        hz1⟩, fun s' hpost => ?_⟩, hld⟩
      · rw [show _ - Width.W64.bytesv = _ from e70]; exact hpush _
      · rw [hbp]; exact sub8_m64 _
      · obtain ⟨d', i', rfl, hok, hxk, hi', hsp', hbp', ⟨hbx', h12', h13', h14', -⟩, hm'⟩ := hpost
        refine MachineWP.nil_spec.le_wp s' ?_
        refine ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, i', _, ih, hE, ⟨hi', hrb.2⟩, ?_⟩, Nat.le_of_eq (var_L401 _)⟩
        · rw [hsp', e70]; exact sub112 _
        · rw [hbp']; exact hbp
        · rw [h14']; exact h14
        · rw [e70] at hm'
          simp only [DecF, GRW] at hm' ⊢
          sep_close hm'

theorem blk_L401 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L401" := by
  cfg_block
  measure_hb "L401"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
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
      rw [table.match_1.eq_23]
      exact ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, p_h0.down⟩, Nat.le_of_eq (var_L409 _)⟩

omit [CodeEnv] in
theorem sw32_64 (y : BitVec 32) : BitVec.setWidth 32 (BitVec.setWidth 64 y) = y := by
  rw [BitVec.setWidth_setWidth_of_le _ (by omega), BitVec.setWidth_eq]

theorem blk_L409 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L409" := by
  cfg_block
  measure_hb "L409"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    have p_h0 : PLift _ := ⟨hm⟩
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
      rw [table.match_1.eq_25]
      refine ⟨by decide, ⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_⟩, ?_⟩
      all_goals first
        | exact trivial
        | edge_ok var_Lb1a
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
           all_goals first
             | exact setl_inc _ _ _ _ _ hrb.1 hC.2.2.2.1.2.1
             | rfl
             | assumption)
        | (simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
           sep_close hm)
    case vc7 =>
      refine ⟨⟨⟨hC, ⟨?_, ?_, ?_⟩, i0, gi, d, ih, hE, hrb, ?_⟩, ?_, ?_, ?_⟩, Nat.le_of_eq (var_L43d _)⟩
      all_goals first
        | exact trivial
        | (simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sw32_64]
           all_goals first
             | exact setl_inc _ _ _ _ _ hrb.1 hC.2.2.2.1.2.1
             | rfl
             | assumption)
        | (simp only [DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
           sep_close hm)

end Kraken.Examples.Sbr.DecExt
