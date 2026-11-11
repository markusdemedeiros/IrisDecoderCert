import Kraken.X64.Examples.Sbr.Parse.DtdfBase

/-!
# `read_sbr_dtdf`: the dispatch blocks
-/

open Kraken Kraken.SysV Mem Kraken.X64.Parser Std.WP MachineWP
open Kraken.Examples.Sbr Kraken.Examples.Sbr.Apply

set_option mvcgen.warning false
set_option grind.warning false
set_option experimental.vcgen true

namespace Kraken.Examples.Sbr.Dtdf

variable [CodeEnv]

open scoped Kraken.Rules.GenericMem.Norm

set_option hygiene false in
/-- `vcgen` and the substitution of the loads of `bs_num_env`, `bs_num_noise`. Expects `hm`,
`hrdx`. -/
macro "dtdf_vc" : tactic => `(tactic| (
    have hN := NL.of hm hrdx
    vcgen
    all_goals try subst_vars
    all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64,
      AddrIndex.offset64_scale1, AddrIndex.offset64_none, Int64.toBitVec_ofNat_norm,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      BitVec.setWidth_32_64_32] at *
    all_goals try (simp only [hN.nenv, hN.nn, Option.isSome_some]; done)
    all_goals try simp only [hN.nenv, hN.nn, Option.some.injEq] at *
    all_goals try subst_vars
    all_goals try simp only [BitVec.ofInt32_ofBytes_toBytes4] at *))

theorem blk_entry (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf" := by
  cfg_block
  measure_hb "entry"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨rfl, hC, hm⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    have hb0 : ((s₀.regs.get64 .rdx + 28#64) - (arg2 s₀ + 0x1c#64)).toNat + 1 ≤ 11 := by
      simp only [arg2, BitVec.sub_self, BitVec.toNat_zero]; omega
    have hst := T_st_df hm _ hb0 (BitVec.setWidth 8 0#64).toInt
    have h1 : Ld4 (storeInt s₀.dmem (s₀.regs.get64 .rdx + 28#64) 1 (BitVec.setWidth 8 0#64).toInt)
        (s₀.regs.get64 .rdx + 8#64) x.v.nenv := T_ld_nenv hst
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
    case vc1 =>
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5185") ⟨rfl,
        ⟨hC, ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, x.idx, hC.2.2.1, hm⟩,
        Or.inr ⟨rfl, by decide⟩⟩)
    case vc2 =>
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L51a2") ⟨rfl,
        ⟨hC, ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, x.idx, hC.2.2.1, hm⟩,
        Or.inr ⟨rfl, by decide⟩⟩)
    case vc3 => exact T_ld_df hm _ hb0
    case vc5 =>
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5272") ⟨rfl,
        ⟨hC, ⟨rfl, rfl, ⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, x.idx, hC.2.2.1, hst⟩,
        Or.inl (show 20 < 40 by decide)⟩)
    case vc6 =>
      rename_i hle hnz
      rw [le_dec _ hn8] at hle
      rw [nz_dec _ hn8] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hle hnz
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L51bf") ⟨rfl,
        ⟨⟨hC, ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, x.idx, hC.2.2.1, hst⟩, by omega, ?_⟩,
        Or.inr ⟨rfl, by decide⟩⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      exact rax_dec _ (by omega) hn8
    case vc7 =>
      rename_i hle hnz
      rw [le_dec _ hn8] at hle
      rw [nz_dec _ hn8] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, ne_eq, Decidable.not_not] at hle hnz
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5243") ⟨rfl,
        ⟨⟨hC, ⟨?_, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩, x.idx, hC.2.2.1, hst⟩, 0, ?_, by omega⟩,
        Or.inl (show 20 < 40 by decide)⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      simp

set_option hygiene false in
/-- `movslq bs_num_env; test; jle le; cmp $1; jne ne; xor %eax; jmp tl`. -/
macro "dtdf_disp_env" le:str ne:str tl:str : tactic => `(tactic| (
    obtain ⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hn⟩ := hs₀
    have hn8 : x.v.nenv ≤ 8 := hC.1
    dtdf_vc
    case vc2 =>
      refine Or.inl (Table.ofLabels_at (l := $le) ⟨rfl,
        ⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, Or.inl (show 20 < 40 by decide)⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals assumption
    case vc3 =>
      rename_i hle hnz
      rw [le_sx _ hn8] at hle
      rw [nz_sx _ hn8] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hle hnz
      refine Or.inl (Table.ofLabels_at (l := $ne) ⟨rfl,
        ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, by omega, ?_⟩,
        Or.inr ⟨rfl, by decide⟩⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try assumption
      exact sx_eq _ hn8
    case vc4 =>
      rename_i hle hnz
      rw [le_sx _ hn8] at hle
      rw [nz_sx _ hn8] at hnz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq, ne_eq, Decidable.not_not] at hle hnz
      refine Or.inl (Table.ofLabels_at (l := $tl) ⟨rfl,
        ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, 0, ?_, by omega⟩,
        Or.inl (show 20 < 40 by decide)⟩)
      all_goals simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals try assumption
      simp))

theorem blk_L5185 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5185" := by
  cfg_block
  measure_hb "L5185"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_disp_env "read_sbr_dtdf.L5402" "read_sbr_dtdf.L5347" "read_sbr_dtdf.L53d3"

theorem blk_L51a2 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L51a2" := by
  cfg_block
  measure_hb "L51a2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    dtdf_disp_env "read_sbr_dtdf.L5552" "read_sbr_dtdf.L54a2" "read_sbr_dtdf.L5523"

theorem blk_L5402 (k : Nat) (x : DArgs) (ra : Int64) (t₀ : MachineData) :
    BlockOb k x ra t₀ "read_sbr_dtdf.L5402" := by
  cfg_block
  measure_hb "L5402"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, hn⟩ := hs₀
    have hnn : x.v.nnoise ≤ 2 := hC.2.1
    dtdf_vc
    case vc2 =>
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5622") ⟨rfl,
        ⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, Or.inl (show 1 < 20 by decide)⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals assumption
    case vc3 =>
      rename_i hle hz
      rw [le_sx _ (by omega)] at hle
      rw [z_sx _ (by omega)] at hz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hle hz
      refine Or.inl (Table.ofLabels_at (l := "read_sbr_dtdf.L5564") ⟨rfl,
        ⟨⟨hC, ⟨?_, ?_, ?_, ?_, ?_⟩, i, hi, hm⟩, hz⟩, Or.inr ⟨rfl, by decide⟩⟩)
      all_goals try simp only [reduceCtorEq, ↓reduceIte, Reg64s.get64_set64]
      all_goals assumption
    case vc4 =>
      rename_i hle hz
      rw [le_sx _ (by omega)] at hle
      rw [z_sx _ (by omega)] at hz
      simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hle hz
      exact ⟨⟨⟨hC, ⟨hsp, hbp, hsv, hrsi, hrdx⟩, i, hi, hm⟩, 0, xor0 _, rfl, by omega,
        sx_eq _ (by omega), and_sx _ (by omega)⟩, by omega⟩

end Kraken.Examples.Sbr.Dtdf
