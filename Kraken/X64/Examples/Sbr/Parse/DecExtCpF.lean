import Kraken.X64.Examples.Sbr.Parse.DecExtCpB

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

/-- A frame goal, the hypotheses first (`rfl` on these goals can exhaust the recursion depth). -/
macro "fr_a" : tactic => `(tactic| (
  (try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false, sbrA, arg0, arg1,
    BitVec.add_assoc, BitVec.reduceAdd]) <;> first | assumption | rfl))

omit [CodeEnv] in
/-- A 4-byte value loaded with `mov` and stored back. -/
theorem tb4w (bs : List UInt8) (h : bs.length = 4) :
    Int.toBytes 4 (BitVec.setWidth 32 (BitVec.setWidth 64 (BitVec.ofInt 32 (Int.ofBytes bs)))).toInt
      = bs := by
  rw [show ∀ x : BitVec 32, BitVec.setWidth 32 (BitVec.setWidth 64 x) = x from fun x => by bv_omega]
  exact tb_ofInt 4 bs h

theorem blk_L5cc (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L5cc" := by
  cfg_block
  measure_hb "L5cc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, hCp, hrb, hm⟩, h12, hdx, hbx⟩, hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at h12 hdx hbx
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_39
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi, d, ih, hCp, hrb, ?_⟩, by fr_a, by fr_a,
        by fr_a⟩, Nat.le_of_eq (var_L5e1 _)⟩
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrA, arg1, BitVec.add_assoc,
        BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      sep_close hm

theorem blk_L62b (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L62b" := by
  cfg_block
  measure_hb "L62b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨e, hCe, rfl⟩, hrb, hm⟩, h12, hdx, hbx⟩, hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at h12 hdx hbx
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
      c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_43
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi, e.setCh true (cpD e.a.d0 e.a.d1), ih,
        ⟨e, hCe, rfl⟩, hrb, ?_⟩, by fr_a, by fr_a, by fr_a⟩, Nat.le_of_eq (var_L647 _)⟩
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, cpD, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      rw [tb4w _ (Int.toBytes_length _ _)] at hm
      sep_close hm

theorem blk_L647 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L647" := by
  cfg_block
  measure_hb "L647"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, h14⟩, i0, gi, d, ih, ⟨e, hCe, rfl⟩, hrb, hm⟩, h12, hdx, hbx⟩, hn⟩ := hs₀
    var_c hn
    simp only [sbrA, arg0, arg1, BitVec.add_assoc, BitVec.reduceAdd] at h12 hdx hbx
    simp only [T, DecF, LocW, GbR, GbW, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
      c1_psc, c1_avctx, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd] at hm
    try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, BitVec.add_assoc, BitVec.reduceAdd]
    all_goals try omega
    all_goals
      to_tableC tableC.match_1.eq_44
      refine ⟨⟨⟨hC, ⟨by fr_a, by fr_a, by fr_a⟩, i0, gi, e.setCh true (cpE e.a.d0 e.a.d1), ih,
        cp_einv hCe, hrb, ?_⟩, by fr_a, by fr_a, by fr_a⟩, Nat.le_of_eq (var_L663 _)⟩
      simp only [T, LocW, GbR, GbW, DecF, SbrF, DataF, sbrS_c1, tabF_c1, acF_c1, AvW, c1_d0, c1_d1,
        c1_psc, c1_avctx, cpE, sbrA, arg1, BitVec.add_assoc, BitVec.reduceAdd]
      try simp (disch := decide) only [BitVec.sub_add_ofNat_cancel, Nat.reduceSub]
      rw [tb4w _ (Int.toBytes_length _ _)] at hm
      sep_close hm

end Kraken.Examples.Sbr.DecExt
