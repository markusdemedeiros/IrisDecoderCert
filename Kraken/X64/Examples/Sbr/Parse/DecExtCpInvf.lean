import Kraken.X64.Examples.Sbr.Parse.DecExtCpG

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the two `memcpy` of `bs_invf_mode` (coupled path)

`L6b3`: `bs_invf_mode[1]` of channel 1 from its `bs_invf_mode[0]`; `L6d0`: channel 1's
`bs_invf_mode[0]` from channel 0's. The 10-byte arrays are split at the copied bytes (`inv10`):
a 4-byte cell, a byte, a 4-byte cell, a byte.
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

omit [CodeEnv] in
theorem inv10 (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt8) (a : BitVec 64) :
    [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] =@ a
      = Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes [x0, x1, x2, x3])).toInt =@ a
        ⋆ (Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes [x4])).toInt =@ (a + 4#64)
          ⋆ (Int.toBytes 4 (BitVec.ofInt 32 (Int.ofBytes [x5, x6, x7, x8])).toInt =@ (a + 5#64)
            ⋆ Int.toBytes 1 (BitVec.ofInt 8 (Int.ofBytes [x9])).toInt =@ (a + 9#64))) := by
  have e : [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]
      = [x0, x1, x2, x3] ++ ([x4] ++ ([x5, x6, x7, x8] ++ [x9])) := rfl
  rw [e, Val.append_eq _ _ a (a + 4#64) rfl (by simp),
    Val.append_eq _ _ (a + 4#64) (a + 5#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
    Val.append_eq _ _ (a + 5#64) (a + 9#64) (by rw [BitVec.add_assoc]; rfl) (by simp),
    tb_ofInt 4 [x0, x1, x2, x3] rfl, tb_ofInt 1 [x4] rfl, tb_ofInt 4 [x5, x6, x7, x8] rfl,
    tb_ofInt 1 [x9] rfl]

omit [CodeEnv] in
theorem lit10 (l : List UInt8) (h : l.length = 10) :
    ∃ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9, l = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] := by
  match l, h with
  | [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9], _ => exact ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, rfl⟩

omit [CodeEnv] in
theorem shift_lit (v : DV) {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : UInt8}
    (hx : v.invf = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]) :
    (invfShift v).invf = [x0, x1, x2, x3, x4, x0, x1, x2, x3, x4] := by
  simp only [invfShift]; rw [hx]; rfl

omit [CodeEnv] in
theorem couple_lit (u v : DV) {x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 : UInt8}
    (hy : u.invf = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9])
    (hx : v.invf = [x0, x1, x2, x3, x4, x5, x6, x7, x8, x9]) :
    (invfCouple u (invfShift v)).invf = [y0, y1, y2, y3, y4, x0, x1, x2, x3, x4] := by
  simp only [invfCouple, invfShift]; rw [hy, hx]; rfl

theorem blk_L6b3 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L6b3" := by
  cfg_block
  measure_hb "L6b3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hE, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1] at h12 h13 hbx
    have hD1 : DWF False d.a.d1 := hE.1.1.2.2.2.1
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, hx⟩ := lit10 _ hD1.2.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    rw [hx, inv10] at hm
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt_toInt, sw8, BitVec.setWidth_32_64_32, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_48
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi, d.setCh true (invfShift d.a.d1), ih,
        ⟨d, hE, rfl⟩, hrb, ?_⟩, by fr_a, by fr_a, by fr_a⟩, Nat.le_of_eq (var_L6d0 _)⟩
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [shift_lit _ hx, inv10]
      simp only [invfShift, BitVec.add_assoc, BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm

theorem blk_L6d0 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L6d0" := by
  cfg_block
  measure_hb "L6d0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨d, hE, rfl⟩, hrb, hm⟩, h12, h13, hbx⟩, hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1] at h12 h13 hbx
    have hD0 : DWF False d.a.d0 := hE.1.1.2.2.1
    have hD1 : DWF False d.a.d1 := hE.1.1.2.2.2.1
    obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, hx⟩ := lit10 _ hD1.2.1
    obtain ⟨y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, hy⟩ := lit10 _ hD0.2.1
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
      c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    rw [shift_lit _ hx, inv10, hy, inv10] at hm
    simp only [invfShift, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt_toInt, sw8, BitVec.setWidth_32_64_32, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_49
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi,
        (d.setCh true (invfShift d.a.d1)).setCh true (invfCouple d.a.d0 (invfShift d.a.d1)), ih,
        einv_couple (einv_shift hE), hrb, ?_⟩, by fr_a, by fr_a, by fr_a⟩,
        Nat.le_of_eq (var_L6ed _)⟩
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      rw [couple_lit _ _ hy hx, inv10, hy, inv10]
      simp only [invfCouple, invfShift, BitVec.add_assoc, BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm

end Kraken.Examples.Sbr.DecExt
