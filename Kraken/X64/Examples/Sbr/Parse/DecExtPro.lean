import Kraken.X64.Examples.Sbr.Parse.DecExtMem

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply Kraken.Examples.Sbr.ParseModel
open Kraken.Examples.Sbr.Parse

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

/-!
# `ff_aac_sbr_decode_extension`: the prologue blocks (`reset`, rates, CRC skip)
-/

namespace Kraken.Examples.Sbr.DecExt

variable [CodeEnv]

theorem blk_L63 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L63" := by
  cfg_block
  measure_hb "L63"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, hcx, ih, hrb, hm⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, BitVec.add_assoc, BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, h12, DecF, SbrF, SbrS, AcF, BitVec.add_assoc, BitVec.reduceAdd]
    dx_br hm
    case vc3 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_5]
      refine ⟨by decide, ?_, ?_⟩
      · simp only [DS.st1, TabF_st1, BitVec.toInt_zero, BitVec.ofNat_eq_ofNat]
        simp only [‹X.d.a.sampleRate = 0›] at hm
        refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, X.i, ih, hrb, ?_⟩, ?_, ?_⟩
        all_goals first | assumption | trivial | sep_close hm
      · edge_ok var_L301
    case vc5 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_6]
      refine ⟨by decide, ?_, ?_⟩
      · simp only [DS.st1, TabF_st1, newRate, ‹X.d.a.sampleRate ≠ 0›, ‹X.d.a.extRate = 0›, ite_false,
          BitVec.toInt_zero, BitVec.ofNat_eq_ofNat]
        simp only [‹X.d.a.extRate = 0›] at hm
        refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, X.i, ih, hrb, ?_⟩, ?_, ?_⟩
        all_goals first | assumption | trivial | sep_close hm
      · edge_ok var_L31c
    case vc6 =>
      simp only [DS.st1, TabF_st1, ‹X.d.a.sampleRate ≠ 0›, ‹X.d.a.extRate ≠ 0›, ite_false,
        BitVec.toInt_zero, BitVec.ofNat_eq_ofNat]
      refine ⟨⟨⟨hC, ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, h13⟩, X.i, ih, hrb, ?_⟩, ?_⟩, (by rw [var_L8b]; decide)⟩
      · sep_close hm
      · first | trivial | exact hcx


theorem blk_L301 (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L301" := by
  cfg_block
  measure_hb "L301"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, gi, ih, hrb, hm⟩, hcx, hsr⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, DS.st1, TabF_st1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, h12, DecF, SbrF, SbrS, AcF, DS.st1, TabF_st1, BitVec.add_assoc,
      BitVec.reduceAdd]
    dx_br hm
    case vc4 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_7]
      refine ⟨by decide, ?_, ?_⟩
      · simp only [DS.st1, TabF_st1, hsr, newRate, ‹X.d.a.extRate ≠ 0›, BitVec.ofNat_eq_ofNat,
          ↓reduceIte, ite_true, ite_false]
        refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, gi, ih, hrb, ?_⟩, ?_⟩
        all_goals first | assumption | trivial | sep_close hm
      · edge_ok var_L8b
    case vc5 =>
      simp only [DS.st1, TabF_st1, hsr, newRate, ‹X.d.a.extRate = 0›, ↓reduceIte, ite_true]
      simp only [‹X.d.a.extRate = 0›] at hm
      refine ⟨⟨⟨hC, ⟨⟨trivial, trivial, trivial⟩, trivial, trivial, h13⟩, gi, ih, hrb, ?_⟩, ?_⟩, Nat.le_of_eq (var_L31c _)⟩
      · sep_close hm
      · first | trivial | exact ⟨hcx, rfl⟩ | exact ⟨trivial, rfl⟩

theorem blk_L31c (PI : List UInt8 → Prop) (kc : Nat) (Ext : Mem 64 → Prop) (X : XA)
    (ra : Int64) (t₀ : MachineData) :
    BlockOb PI kc Ext X ra t₀ "ff_aac_sbr_decode_extension.L31c" := by
  cfg_block
  measure_hb "L31c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨⟨hsp, hbp, h14⟩, hdi, h12, h13⟩, gi, ih, hrb, hm⟩, hcx, hsr⟩, hn⟩ := hs₀
    var_n hn
    simp only [Mm0, T, DecF, SbrF, SbrS, AcF, sbrA, DS.st1, TabF_st1, BitVec.add_assoc,
      BitVec.reduceAdd] at hm
    have p_hm : PLift _ := ⟨hm⟩
    clear hm
    vcgen
    all_goals have hm := p_hm.down; clear p_hm
    dx_run hm [hbp, hsp, h14, hdi, h12, DecF, SbrF, SbrS, AcF, DS.st1, TabF_st1, BitVec.add_assoc,
      BitVec.reduceAdd]
    dx_br hm
    case vc3 =>
      left; apply Table.ofLabels_at
      rw [table.match_1.eq_7]
      refine ⟨by decide, ?_, ?_⟩
      · simp only [DS.st1, TabF_st1, hsr, newRate_zero, newRate, ite_true, ↓reduceIte]
        refine ⟨⟨hC, ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, gi, ih, hrb, ?_⟩, ?_⟩
        all_goals first | assumption | trivial | sep_close hm
      · edge_ok var_L8b

end Kraken.Examples.Sbr.DecExt
