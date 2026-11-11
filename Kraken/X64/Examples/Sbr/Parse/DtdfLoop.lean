import Kraken.X64.Examples.Sbr.Parse.DtdfBase

/-!
# `read_sbr_dtdf`: the loop blocks
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply
open Kraken.Examples.Sbr.Parse (bswap32_havoc shl_cl32_havoc shr_cl32_havoc)

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Dtdf

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option hygiene false in
/-- The common part of a `get_bits1` block: the facts about `*gb`, the bitstream byte and the
index store, then `vcgen` and the substitution of the three loads of `*gb`. Expects `s₀`, `hm`,
`hrsi`, `i`, `hi`, `hC` in the context. -/
macro "gb1_vc" : tactic => `(tactic| (
    have hL := GbL.of hm hrsi
    have hbs := T_ld_bs hm
    have hsi : ∀ v : BitVec 32, s₀.dmem.storeInt (s₀.regs.get64 .rsi + 8#64) 4 v.toInt
        =⋆ T k x ra t₀ v := by rw [hrsi]; exact T_st_i hm
    have hoff := rd_off1 i x.p8 x.L hi hC.2.2.2.2.1
    have hnx := gb1_next i x.p8
    have hp := hC.2.2.2.1
    vcgen [shl_cl32_havoc]
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try (simp only [hL.ld_i, hL.ld_buf, hL.ld_p8, Option.isSome_some]; done)
    all_goals try simp only [hL.ld_i, hL.ld_buf, hL.ld_p8, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4, BitVec.ofInt64_ofBytes_toBytes8,
      BitVec.ofInt_toInt] at *))

set_option hygiene false in
/-- The first half of a two-element loop body (`Lp cnt` to `Lp cnt`, the same `rax`). -/
macro "dtdf_head" : tactic => `(tactic| (
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, j, hax, hj2, hj, hdi, hr8⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    gb1_vc
    case vc4 => exact hbs _ 1 hoff
    case vc6 => exact T_ld_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega)
    case vc7 =>
      exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, _, hnx _ _ _ hi hp,
        T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩,
        ⟨j, hax, hj2, hj, hdi, hr8⟩⟩, Nat.le_refl _⟩))

set_option hygiene false in
/-- The second half of a two-element loop body of the `bs_df_env` loops: back to the head
`back` (`jne`), out to `exit` for an even count (`je`), or on to the last element. -/
macro "dtdf_tail" back:str exit:str : tactic => `(tactic| (
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, j, hax, hj2, hj, hdi, hr8⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    gb1_vc
    case vc4 => exact hbs _ 1 hoff
    case vc6 => exact T_ld_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega)
    case vc7 =>
      rename_i hnz _
      have e := cmp2_ne hr8 hax (by omega) (by omega) hnz
      refine Or.inl (Table.ofLabels_at (l := $back) ⟨rfl, ⟨⟨hC,
        ⟨?_, ?_, ?_, ?_, ?_⟩, _, hnx _ _ _ hi hp,
        T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩,
        j + 2, ?_, by omega, by omega, ?_, ?_⟩, Or.inl ?_⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try assumption
      · rw [hax, add2 j (by omega)]
      · show 40 - _ < 40 - _
        rw [hax, add2 j (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
    case vc8 =>
      refine Or.inl (Table.ofLabels_at (l := $exit) ⟨rfl, ⟨hC,
        ⟨?_, ?_, ?_, ?_, ?_⟩, _, hnx _ _ _ hi hp,
        T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩, Or.inl ?_⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try assumption
      show 20 < 40 - _
      rw [hax, BitVec.toNat_ofNat]
      omega
    case vc9 =>
      rename_i hnz hz _
      have e := cmp2_eq hr8 hax (by omega) (by omega) hnz
      have o := test1_odd hdi hz
      refine ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, _, hnx _ _ _ hi hp,
        T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩,
        j + 2, by rw [hax, add2 j (by omega)], by omega⟩, ?_⟩
      rw [hax, BitVec.toNat_ofNat]
      omega))

set_option hygiene false in
/-- The last element (`Tl cnt`), on to the next block. -/
macro "dtdf_last" : tactic => `(tactic| (
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, j, hax, hj⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    gb1_vc
    case vc4 => exact hbs _ 1 hoff
    case vc6 => exact T_ld_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega)
    case vc7 =>
      exact ⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, _, hnx _ _ _ hi hp,
        T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩,
        by first | exact Nat.le_refl _ | exact Nat.zero_le _⟩))

set_option hygiene false in
/-- The second half of a two-element loop body of the `bs_df_noise` loops: back to the head
`back` (`jne`), else on to `L55ed` with `rax = cnt / 2 * 2`. -/
macro "dtdf_ntail" back:str : tactic => `(tactic| (
    obtain ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, j, hax, hj2, hj, hdi, hr8⟩, hn⟩ := hs₀
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    gb1_vc
    case vc4 => exact hbs _ 1 hoff
    case vc6 => exact T_ld_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega)
    case vc7 =>
      rename_i hnz _
      have e := cmp2_ne hr8 hax (by omega) (by omega) hnz
      refine Or.inl (Table.ofLabels_at (l := $back) ⟨rfl, ⟨⟨hC,
        ⟨?_, ?_, ?_, ?_, ?_⟩, _, hnx _ _ _ hi hp,
        T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩,
        j + 2, ?_, by omega, by omega, ?_, ?_⟩, Or.inl ?_⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try assumption
      · rw [hax, add2 j (by omega)]
      · show 20 - _ < 20 - _
        rw [hax, add2 j (by omega), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
    case vc8 =>
      rename_i hnz _
      have e := cmp2_eq hr8 hax (by omega) (by omega) hnz
      first
      | refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L55ed") ⟨rfl, ⟨⟨hC,
          ⟨?_, ?_, ?_, ?_, ?_⟩, _, hnx _ _ _ hi hp,
          T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩, ?_, ?_⟩,
          Or.inl ?_⟩)
        all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
        all_goals try assumption
        · rw [hax, add2 j (by omega), e]
        · show 1 < 20 - _
          rw [hax, BitVec.toNat_ofNat]
          omega
      | refine ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, _, hnx _ _ _ hi hp,
          T_st_df (hsi _) _ (by rw [hrdx, hax]; simp only [arg2]; bv_omega) _⟩,
          hdi, by rw [hax, add2 j (by omega), e]⟩, ?_⟩
        show 1 ≤ 20 - _
        simp only [hax, BitVec.toNat_ofNat]
        omega))

theorem blk_L51d0 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L51d0" := by
  cfg_block
  measure_hb "L51d0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_head

theorem blk_L5360 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5360" := by
  cfg_block
  measure_hb "L5360"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_head

theorem blk_L54b0 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L54b0" := by
  cfg_block
  measure_hb "L54b0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_head

theorem blk_L5430 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5430" := by
  cfg_block
  measure_hb "L5430"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_head

theorem blk_L5580 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5580" := by
  cfg_block
  measure_hb "L5580"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_head

theorem blk_L5202 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5202" := by
  cfg_block
  measure_hb "L5202"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_tail "read_sbr_dtdf.L51d0" "read_sbr_dtdf.L5272"

theorem blk_L5392 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5392" := by
  cfg_block
  measure_hb "L5392"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_tail "read_sbr_dtdf.L5360" "read_sbr_dtdf.L5402"

theorem blk_L54e2 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L54e2" := by
  cfg_block
  measure_hb "L54e2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_tail "read_sbr_dtdf.L54b0" "read_sbr_dtdf.L5552"

theorem blk_L5243 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5243" := by
  cfg_block
  measure_hb "L5243"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_last

theorem blk_L5317 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5317" := by
  cfg_block
  measure_hb "L5317"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_last

theorem blk_L53d3 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L53d3" := by
  cfg_block
  measure_hb "L53d3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_last

theorem blk_L5523 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5523" := by
  cfg_block
  measure_hb "L5523"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_last

theorem blk_L55f3 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L55f3" := by
  cfg_block
  measure_hb "L55f3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_last

theorem blk_L5462 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5462" := by
  cfg_block
  measure_hb "L5462"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_ntail "read_sbr_dtdf.L5430"

theorem blk_L55b2 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L55b2" := by
  cfg_block
  measure_hb "L55b2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_ntail "read_sbr_dtdf.L5580"

end Kraken.Examples.Sbr.Dtdf
