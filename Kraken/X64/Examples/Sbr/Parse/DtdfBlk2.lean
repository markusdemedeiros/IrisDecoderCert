import Kraken.X64.Examples.Sbr.Parse.DtdfBlk1

/-!
# `read_sbr_dtdf`: the dispatch blocks after the loops, the exit, the unreachable blocks
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Dtdf

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

theorem blk_L5272 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5272" := by
  cfg_block
  measure_hb "L5272"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hn⟩ := hs₀
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    have hb9 : ((s₀.regs.get64 .rdx + 37#64) - (arg2 t₀ + 0x1c#64)).toNat + 1 ≤ 11 := by
      rw [hrdx]; simp only [arg2]; bv_omega
    have hst := T_st_df hm _ hb9 (BitVec.setWidth 8 0#64).toInt
    have h1 : Ld4 (storeInt s₀.dmem (s₀.regs.get64 .rdx + 37#64) 1 (BitVec.setWidth 8 0#64).toInt)
        (s₀.regs.get64 .rdx + 24#64) x.v.nnoise := by
      have h := hst
      rw [hrdx] at h ⊢
      exact T_ld_nn h
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try (simp only [h1.get, Option.isSome_some]; done)
    all_goals try simp only [h1.get, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *
    case vc1 => exact T_ld_df hm _ hb9
    case vc3 =>
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5622") ⟨rfl,
        ⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hst⟩, Or.inl (show 1 < 20 by decide)⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals assumption
    case vc4 =>
      rename_i hle hnz
      rw [le_dec _ (by omega)] at hle
      rw [nz_dec _ (by omega)] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hle hnz
      exfalso; omega
    case vc5 =>
      rename_i hle hnz
      rw [le_dec _ (by omega)] at hle
      rw [nz_dec _ (by omega)] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, ne_eq, Decidable.not_not] at hle hnz
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5317") ⟨rfl,
        ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hst⟩, 0, ?_, by omega⟩, Or.inl (show 0 < 20 by decide)⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try assumption
      simp

theorem blk_L5552 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5552" := by
  cfg_block
  measure_hb "L5552"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    dtdf_vc
    case vc2 =>
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5622") ⟨rfl,
        ⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, Or.inl (show 1 < 20 by decide)⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals assumption
    case vc3 =>
      rename_i hle hnz
      rw [le_sx _ (by omega)] at hle
      rw [nz_sx _ (by omega)] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hle hnz
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L556b") ⟨rfl,
        ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, by omega, ?_⟩, Or.inr ⟨rfl, by decide⟩⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try assumption
      exact sx_eq _ (by omega)
    case vc4 =>
      rename_i hle hnz
      rw [le_sx _ (by omega)] at hle
      rw [nz_sx _ (by omega)] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, ne_eq, Decidable.not_not] at hle hnz
      exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hnz⟩, Nat.le_refl _⟩

theorem blk_L5564 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5564" := by
  cfg_block
  measure_hb "L5564"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, h1⟩, hn⟩ := hs₀
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64] at *
    refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L55f3") ⟨rfl,
      ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, 0, ?_, by omega⟩, Or.inl (show 1 < 20 by decide)⟩)
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
    all_goals try assumption
    exact xor0 _

theorem blk_L556b (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L556b" := by
  cfg_block
  measure_hb "L556b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, h2, hdi⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      BitVec.setWidth_32_64_32] at *
    exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, 0, xor0 _, rfl, by omega, hdi, by rw [hdi]; exact and_nat _ (by omega)⟩,
      by omega⟩

theorem blk_L5347 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5347" := by
  cfg_block
  measure_hb "L5347"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, h2, hdi⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      BitVec.setWidth_32_64_32] at *
    exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, 0, xor0 _, rfl, by omega, hdi, by rw [hdi]; exact and_nat _ (by omega)⟩,
      by omega⟩

theorem blk_L54a2 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L54a2" := by
  cfg_block
  measure_hb "L54a2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, h2, hdi⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      BitVec.setWidth_32_64_32] at *
    exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, 0, xor0 _, rfl, by omega, hdi, by rw [hdi]; exact and_nat _ (by omega)⟩,
      by omega⟩

theorem blk_L51bf (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L51bf" := by
  cfg_block
  measure_hb "L51bf"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, h3, hax⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      BitVec.setWidth_32_64_32] at *
    exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, 0, xor0 _, rfl, by omega, by rw [hax]; exact zx_nat _ (by omega),
      by rw [hax]; exact and_nat _ (by omega)⟩, by omega⟩

theorem blk_L55ed (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L55ed" := by
  cfg_block
  measure_hb "L55ed"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hdi, hax⟩, hn⟩ := hs₀
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64] at *
    case vc1 =>
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5622") ⟨rfl,
        ⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, Or.inr ⟨rfl, by decide⟩⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals assumption
    case vc2 =>
      rename_i hz
      have o := test1_odd hdi hz
      exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, _, hax, by omega⟩, Nat.le_refl _⟩

theorem blk_L5622 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5622" := by
  cfg_block
  measure_hb "L5622"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hn⟩ := hs₀
    vcgen
    all_goals try subst_vars
    refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.done") ⟨rfl,
      ⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, Or.inl (show 0 < 1 by decide)⟩)

theorem blk_done (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.done" := by
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hn⟩ := hs₀
    have hpost : s₀.dmem =⋆ 8 ?@ t₀.regs.get64 .rsp
        ⋆ (Reserve k (t₀.regs.get64 .rsp) ⋆ (DtdfF x t₀ i ⋆ x.R)) :=
      Block.sep_intro (Int.toBytes_length _ _) (by decide) hm
    have l0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp) 8
        = some (Int.ofBytes (Int.toBytes 8 ra.toBitVec.toInt)) :=
      loadInt_sep _ _ 8 _ _ hm (Int.toBytes_length 8 _) (by omega)
    have hra : s₀.retAddr = some ra := by
      simp only [MachineData.retAddr, hsp, l0, Option.map_some,
        BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Int64.ofBitVec_toBitVec]
    clear hm l0
    vcgen
    all_goals try subst_vars
    all_goals simp only [hra, Option.isSome_some, Option.some.injEq] at *
    subst_vars
    right
    refine ⟨rfl, i, hi, ?_, ?_, ?_, hpost⟩
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ↓reduceIte, hsp, hbp]
    · rfl
    · exact hsv

theorem blk_L528f (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L528f" := by
  cfg_block
  intro n
  exact Triple.pin fun _ hs₀ => hs₀.1.elim

theorem blk_L52a0 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L52a0" := by
  cfg_block
  intro n
  exact Triple.pin fun _ hs₀ => hs₀.1.elim

theorem blk_L52d2 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L52d2" := by
  cfg_block
  intro n
  exact Triple.pin fun _ hs₀ => hs₀.1.elim

end Kraken.Examples.Sbr.Dtdf
