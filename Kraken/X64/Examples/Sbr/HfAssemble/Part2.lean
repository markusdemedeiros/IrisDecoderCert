import Kraken.X64.Examples.Sbr.HfAssemble.Base

/-! `sbr_hf_assemble`: block theorems, part 2 of 2 (generated; the split balances
the measured heartbeats). -/

open Kraken
open Kraken.SysV
open Mem

open Kraken.X64.Parser
open Std.WP
open MachineWP
open scoped Kraken.FrameLemmas.Int32Nat
open scoped Kraken.HelperLemmas.Bytes16

set_option mvcgen.warning false
set_option grind.warning false

namespace Kraken.Examples.Sbr.HfAssemble

variable [CodeEnv]

set_option maxRecDepth 100000 in
theorem blk_start (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble" := by
  info_off
  clear hc
  cfg_block
  measure_hb "start"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨hs, hC, hm⟩, hn⟩ := hs₀
    subst hs
    rw [start_pre] at hm
    vcgen
    all_goals try refine ⟨p1_tbl_start _ _ _ _ _ _ ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_p2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.p2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "p2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [p2_pre] at hm
    have hB0 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)⟩
    have hB1 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB2 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB3 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB5 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
    have hB6 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    have hB7 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
    have hB8 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _)
    have hS1 := fun (v1 : Int) => store_keep hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (v := v2)
    have hL2_0 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hL2_1 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL2_2 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL2_3 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL2_5 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL2_6 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (v := v3)
    have hL3_0 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hL3_1 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_2 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_5 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_6 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_7 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (v := v4)
    clear hS1 hS2 hS3
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.La8e1") ⟨by decide, La8e1_tbl_p2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.La8ea") ⟨by decide, La8ea_tbl_p2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨r0_tbl_p2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hL2_0, hL2_1, hL2_2, hL2_3, hL2_5, hL2_6, hL3_0, hL3_1, hL3_2, hL3_3, hL3_5, hL3_6, hL3_7, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hL2_0, hL2_1, hL2_2, hL2_3, hL2_5, hL2_6, hL3_0, hL3_1, hL3_2, hL3_3, hL3_5, hL3_6, hL3_7, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals first | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1400000 in
theorem blk_r0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r0" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r0_pre] at hm
    rw [s38_split0] at hm
    vcgen
    all_goals try refine ⟨r0c_tbl_r0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    -- the frame goal first through its rewrite (a failing `grind` on it costs 0.4M)
    all_goals first
      | omega | with_reducible assumption | cell_some | cell_lcpi | cell_val
      | (simp -implicitDefEqProofs only [h3, h6, hf2_r10b _ _ h5 h7, BitVec.setWidth_32_64_32]; close_cell)
      | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_r0c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r0c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r0c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FR x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h5, h6, h7, h8, h9] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_r1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, hm⟩, hn⟩ := hs₀
    rw [r1_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR5 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR6 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR7 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR8 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR9 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR10 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR11 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR12 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨r1c_tbl_r1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_r1c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r1c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r1c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FR x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h5, h6, h7, h8, h9, h10] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_r2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r2_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR5 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR6 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR7 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR8 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR9 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR10 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR11 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨r2c_tbl_r2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_r3 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r3" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r3_pre] at hm
    vcgen
    all_goals try refine ⟨r3c_tbl_r3 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first
      | omega
      | with_reducible assumption
      | (simp -implicitDefEqProofs only [BitVec.setWidth_eq, BitVec.mul_one, hf_lit_add_row']; refine hf_add_congr ?_ ?_ <;> close_part)
      | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_r3c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r3c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r3c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FR x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h5, h6, h7, h8, h9, h10] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_r5 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r5" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r5_pre] at hm
    vcgen
    all_goals try refine ⟨r5c_tbl_r5 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first
      | omega
      | with_reducible assumption
      | (simp -implicitDefEqProofs only [BitVec.setWidth_eq, BitVec.mul_one, hf_lit_add_row']; refine hf_add_congr ?_ ?_ <;> close_part)
      | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_r5c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r5c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r5c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FR x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h5, h6, h7, h8, h9, h10] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_r7 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r7" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r7_pre] at hm
    vcgen
    all_goals try refine ⟨r7c_tbl_r7 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first
      | omega
      | with_reducible assumption
      | (simp -implicitDefEqProofs only [BitVec.setWidth_eq, BitVec.mul_one, hf_lit_add_row']; refine hf_add_congr ?_ ?_ <;> close_part)
      | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_r7c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r7c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r7c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FR x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h5, h6, h7, h8, h9, h10] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_r8 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r8" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r8"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r8_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR5 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR6 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR7 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR8 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR9 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR10 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR11 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR12 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR13 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR16 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.La8f6") ⟨by decide, La8f6_tbl_r8 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb820") ⟨by decide, Lb820_tbl_r8 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR16, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, hR12, hR13, hR16, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_La8f6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.La8f6" := by
  info_off
  clear hc
  cfg_block
  measure_hb "La8f6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hr9 := hf1_r9_hSL x _ _ h4 h5
    have hrdx := hf1_toInt32 _ _ h7 (by have := h0.2.2.2.2.2.2.2.2.2.1; omega)
    rw [La8f6_pre] at hm
    have hB0 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)⟩
    have hB1 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB2 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB3 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB4 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB5 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB6 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB7 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB8 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB9 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB10 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB11 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB12 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hB13 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hB14 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hB15 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hB16 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hB17 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hS1 := fun (v1 : Int) => store_keep hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (v := v1)
    have hL1_0 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hL1_1 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_2 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_3 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_4 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_5 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_6 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_7 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_8 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_9 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_10 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_11 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_13 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (v := v3)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (v := v4)
    have hS5 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) => store_keep (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (v := v5)
    clear hS1 hS2 hS3 hS4
    vcgen
    all_goals try refine ⟨s0_tbl_La8f6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.La9c2") ⟨by decide, La9c2_tbl_La8f6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hL1_0, hL1_1, hL1_2, hL1_3, hL1_4, hL1_5, hL1_6, hL1_7, hL1_8, hL1_9, hL1_10, hL1_11, hL1_13, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hL1_0, hL1_1, hL1_2, hL1_3, hL1_4, hL1_5, hL1_6, hL1_7, hL1_8, hL1_9, hL1_10, hL1_11, hL1_13, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption)
    all_goals try simp -implicitDefEqProofs only [hr9] at *
    all_goals try simp -implicitDefEqProofs only [h3, h6, hrdx, hSL, BitVec.setWidth_32_64_32] at ⊢
    -- loaded values by their cells (`cell_reads`): the `t_env` bytes are then closed by `hf_te_sw`
    all_goals try cell_reads
    all_goals first
      | omega | with_reducible assumption | cell_some | cell_lcpi | cell_val
      | (simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1]
         rw [hf_te_sw _ (by have := h0.2.2.2.2.2.2.2.2.2.2.1 0 (by omega); have := h0.2.2.2.2.2.2.2.2.2.2.1 1 (by omega); omega)])
      | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_c0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c0" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 1 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 1 (by omega)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h7] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_x0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.x0" := by
  info_off
  clear hc
  cfg_block
  measure_hb "x0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [x0_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨La9c2_tbl_x0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_La9c2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.La9c2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "La9c2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [La9c2_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae20") ⟨by decide, Lae20_tbl_La9c2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Laa62") ⟨by decide, Laa62_tbl_La9c2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨s1_tbl_La9c2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_s1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    have hteK : x.te 1 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 1 (by omega)
    rw [s1_pre] at hm
    vcgen
    all_goals try refine ⟨Laa10_tbl_s1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | close_cell | (simp -implicitDefEqProofs only [h2, h4, h9, h10, hSL]; exact hf_s_row _ _ _ (by omega) (by split <;> omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_Laa10 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Laa10" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "Laa10"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 2 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 2 (by omega)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h7] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_d1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d1_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR5 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR6 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR7 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR8 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR9 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR10 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR11 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Laa10") ⟨by decide, Laa10_tbl_d1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨x1_tbl_d1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_d2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d2_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR5 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR6 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR7 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR8 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR9 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR10 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR11 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Laab0") ⟨by decide, Laab0_tbl_d2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨x2_tbl_d2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_Lab50 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lab50" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "Lab50"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 4 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 4 (by omega)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h7] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_c3 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c3" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 4 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 4 (by omega)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h7] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_x3 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.x3" := by
  info_off
  clear hc
  cfg_block
  measure_hb "x3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [x3_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Laba2_tbl_x3 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 700000 in
theorem blk_Laba2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Laba2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Laba2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [Laba2_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae20") ⟨by decide, Lae20_tbl_Laba2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lac42") ⟨by decide, Lac42_tbl_Laba2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨s4_tbl_Laba2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_s4 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s4" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    have hteK : x.te 4 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 4 (by omega)
    rw [s4_pre] at hm
    vcgen
    all_goals try refine ⟨Labf0_tbl_s4 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | close_cell | (simp -implicitDefEqProofs only [h2, h4, h9, h10, hSL]; exact hf_s_row _ _ _ (by omega) (by split <;> omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_c4 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c4" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 5 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 5 (by omega)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h7, h8] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_d4 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d4" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d4_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR5 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR6 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR7 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR8 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR9 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR10 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR11 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Labf0") ⟨by decide, Labf0_tbl_d4 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨x4_tbl_d4 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_s5 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s5" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    have hteK : x.te 5 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 5 (by omega)
    rw [s5_pre] at hm
    vcgen
    all_goals try refine ⟨Lac90_tbl_s5 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | close_cell | (simp -implicitDefEqProofs only [h2, h4, h9, h10, hSL]; exact hf_s_row _ _ _ (by omega) (by split <;> omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_Lac90 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lac90" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "Lac90"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 6 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 6 (by omega)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h7, h8] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_d5 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d5" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d5_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR5 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR6 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR7 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR8 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR9 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR10 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR11 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lac90") ⟨by decide, Lac90_tbl_d5 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨x5_tbl_d5 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hR5, hR6, hR7, hR8, hR9, hR10, hR11, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
theorem blk_x5 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.x5" := by
  info_off
  clear hc
  cfg_block
  measure_hb "x5"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [x5_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Lace2_tbl_x5 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_s7 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s7" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    have hteK : x.te 7 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 7 (by omega)
    rw [s7_pre] at hm
    vcgen
    all_goals try refine ⟨Ladcc_tbl_s7 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | close_cell | (simp -implicitDefEqProofs only [h2, h4, h9, h10, hSL]; exact hf_s_row _ _ _ (by omega) (by split <;> omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_Ladcc (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Ladcc" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "Ladcc"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 8 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 8 (by omega)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    simp -implicitDefEqProofs only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, qrow_g, hrbp, h2, h3, h4, h7, h8] at *
    all_goals try dsimp only at *
    all_goals first
      | (refine ⟨fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · apply DataW_carve_mc <;> omega
         · vcgen
           all_goals grind_cells'
         · grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_Lae20 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lae20" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lae20"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [Lae20_pre] at hm
    have hB0 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)⟩
    have hB1 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB2 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB3 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB4 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS1 := fun (v1 : Int) => store_keep_val hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (v := v1)
    have hL1_0 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hL1_1 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_2 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_3 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL1_4 := fun (v1 : Int) => Mem.Val.loadInt (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep_val (hS1 v1) (Mem.Split.here _ _) (Int.toBytes_length _ _) (Mem.Split.here _ _) (v := v2)
    clear hS1
    vcgen
    all_goals try refine ⟨m1_tbl_Lae20 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hL1_0, hL1_1, hL1_2, hL1_3, hL1_4, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, hR2, hR3, hR4, hL1_0, hL1_1, hL1_2, hL1_3, hL1_4, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals first | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_m2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.m2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "m2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    rw [m2_pre] at hm
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    vcgen
    all_goals try refine ⟨m3_tbl_m2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first
      | close_cell
      | (simp -implicitDefEqProofs only [h2, h4, h6, h7, h9, hf2_m4_and _ hm48, hf2_m4_shl _ hm48, hf2_m2_e0, hf2_m2_d8]; with_reducible refine hf2_m2_frame ?_; first | with_reducible exact hm | close_cell)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_m3 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.m3" := by
  info_off
  clear hc
  cfg_block
  measure_hb "m3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [m3_pre] at hm
    have hB1 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.here _ _) _)
    have hB2 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
    have hS1 := fun (v1 : Int) => store_keep hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep (hS1 v1) (Mem.Split.right (Mem.Split.here _ _) _) (Mem.Split.right (Mem.Split.here _ _) _) (v := v2)
    clear hS1
    vcgen
    all_goals try refine ⟨Laf40_tbl_m3 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption)
    all_goals first
      | close_cell
      | (simp -implicitDefEqProofs only [h4, h5]; close_cell)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_Lb000 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb000" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb000"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    rw [Lb000_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Lb01d_tbl_Lb000 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, hR1, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1400000 in
theorem blk_Lb01d (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb01d" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  clear hN0 hN1 hN2 hN3 hMc
  cfg_block
  measure_hb "Lb01d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hi32 : (s₀.regs.get64 .r15).toNat < 38 := by omega
    have hi37 : (s₀.regs.get64 .r15).toNat ≤ 37 := by omega
    have hsh := hf_shl9 (s₀.regs.get64 .r15) (by omega)
    have hkx4 := hfc_load_lo4 (by rw [FL_kx] at hm; exact hm) (Mem.Split.here _ _)
    have hkx32 := hf_kx32 x.kx (by omega)
    rw [Lb01d_pre] at hm
    vcgen [MachineWP.call_mem_proc_spec_at
      (DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x288#64),
        ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀ ⋆ (IdxC x t₀
          ⋆ FL2g x t₀ (s₀.regs.get64 .r10).toNat (s₀.regs.get64 .r15).toNat (s₀.zmms.get (.xmm .mm4))
            (Rest x.R ra t₀)))))) fs.gfilt
      (Kraken.Executable.ProcSpec.widen (k := k) hG (Nat.zero_le k) (by omega))]
    all_goals try clear hG
    case' vc2 => exfalso
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280,
      hrsp, hrbp, BitVec.xor_self, BitVec.setWidth_32_64_32,
      BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    case vc1 => simp only [hkx4, Option.isSome_some]
    case vc2 =>
      exfalso
      rename_i xv hcond hld
      rw [hkx4, Option.some.injEq] at hld
      subst hld
      rw [hkx32] at hcond
      simp only [CondCode.interp_nc, StatusFlags.cf_from_result, BitVec.unsigned_eq,
        hf_sub_cf32, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq,
        decide_eq_false_iff_not] at hcond
      simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hcond
      omega
    case vc8 => exact hf_align_xv _ h0.1
    case vc10 =>
      refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
      · simp only [Option.map_eq_some_iff]
        exact ⟨Int.ofBytes (Int.toBytes 8 fs.gfilt.toBitVec.toInt), by grind_cells', hf_fn_load _⟩
      · refine Mem.push_slot_res (b := t₀.regs.get64 .rsp - 0x290#64) ?_ ?_ _
        · rw [← T_FL2_call, Lb01d_post_g1]
          simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
          grind_cells'
        · first | rfl | exact hf_rsp_648_8 _ | exact hf_rsp_656_648 _
      · refine ⟨hf_add2_lt _ hi32, ?_, ?_⟩ <;> simp only [h4, BitVec.toNat_ofNat] <;> omega
      · refine Lb01d_carve' x t₀ x.kx x.m _ _ _ _ _ hkm hi37 ?hD ?e0 ?e1 ?eM
        case e0 => refine hf_add_congr ?_ rfl; grind_cells'
        case hD =>
          rcases h11 with ⟨h11, -⟩ | ⟨h11, -⟩
          · left; refine ⟨hSL x + _, ?_, h11⟩; simp only [hSL]; split <;> omega
          · right; exact ⟨h11, hm48⟩
        case e1 => grind_cells'
        case eM => simp only [h4, BitVec.toNat_ofNat]; omega
      · obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
        rw [← T_FL2_call] at hm'
        have hI := FL2_read_i hm' (by omega)
        have hra : s'.regs.get64 .rsp + 0x248#64 = t₀.regs.get64 .rsp - 0x40#64 := by
          rw [hrsp']; first | exact hf_rsp_656_8_584 _ | exact hf_rsp_648_584 _
        vcgen
        refine ⟨g1_tbl_rb _ _ _ _ _ s' _ _ _ ⟨h0, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hm'⟩, ?_⟩
        · rw [hrsp']; first | exact hf_rsp_656_8 _ | rfl
        · exact hrbp'
        · exact h5
        · exact h3.1
        · exact h3.2
        · exact h6
        · exact h7
        · rw [hbx', hsh]
          refine hf_add_congr ?_ rfl
          grind_cells'
        · rw [h12']; exact h8
        · rw [h13']
          rcases h11 with h | h
          · exact Or.inl h.2
          · exact Or.inr h.2
        · rw [h14']; exact h10
        · rw [h15', BitVec.ofNat_toNat, BitVec.setWidth_eq]
        · simp only [hra, hI, h15'] at *; omega
      · grind_cells'
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_g1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.g1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "g1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    rw [g1_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb08f") ⟨by decide, Lb08f_tbl_g1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb1a0") ⟨by decide, Lb1a0_tbl_g1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨Lb08f_tbl_g1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals close_cell

set_option maxRecDepth 100000 in
theorem blk_n2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.n2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "n2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, hm⟩, hn⟩ := hs₀
    try dsimp only at *
    generalize hI : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    rw [n2_pre] at hm
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    vcgen
    all_goals try refine ⟨Lb140_tbl_n2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hI, hV]
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | (simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] <;> omega)
      | exact hf_and1_lt2 _
      | (rw [h14]; exact hf_lea4 _ _ _)
      | (simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.isSome_some]; done)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 700000 in
theorem blk_Lb140 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb140" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb140"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, hm⟩, hn⟩ := hs₀
    generalize hI0 : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV0 : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    have hI := And.intro hI0 True.intro
    have hV := And.intro hV0 True.intro
    clear hI0 hV0
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hne : x.nenv ≤ 8 := h0.2.2.2.2.2.2.2.2.2.1
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    have hsw1 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rdi)) = s₀.regs.get64 .rdi := by
      apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth]; omega
    have hsw2 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rdi) + BitVec.setWidth 32 (s₀.regs.get64 .rdi))
        = s₀.regs.get64 .rdi + s₀.regs.get64 .rdi := by
      apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_add]; omega
    have hrw : t₀.regs.get64 .rsp - 648#64 + 584#64 = t₀.regs.get64 .rsp - 0x40#64 := by bv_omega
    rw [Lb140_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb140") ⟨by decide, Lb140_rb (i := i) (v := v) rfl h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩)
    all_goals try refine ⟨Lb16c_rb (i := i) (v := v) rfl h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hI.1, hV.1, hrw]
    all_goals (run_tac Lean.Elab.Tactic.withMainContext do
      let lctx ← Lean.getLCtx
      let mut k := 0
      for d in lctx do
        if d.isImplementationDetail then continue
        if !d.userName.hasMacroScopes then continue
        let ty ← Lean.instantiateMVars d.type
        if ty.isAppOfArity ``Eq 3 && ((ty.getArg! 1).getAppFn.constName?.map (·.toString) |>.getD "").endsWith "loadInt" then
          let g ← Lean.Elab.Tactic.getMainGoal
          let g' ← g.rename d.fvarId (Lean.Name.mkSimple s!"hld{k}")
          Lean.Elab.Tactic.replaceMainGoal [g']
          k := k + 1)
    all_goals try simp -implicitDefEqProofs only [Option.some.injEq] at hld0
    all_goals try simp -implicitDefEqProofs only [Option.some.injEq] at hld1
    all_goals try simp -implicitDefEqProofs only [Option.some.injEq] at hld2
    all_goals try simp -implicitDefEqProofs only [Option.some.injEq] at hld3
    all_goals try simp -implicitDefEqProofs only [Option.some.injEq] at hld4
    all_goals try simp -implicitDefEqProofs only [Option.some.injEq] at hld5
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hsw1, hsw2]
    try (case vc1 => exact hf_dw_ld2 hm (hf_inR14m _ _ _ _ h10 (by omega) (by omega)))
    try (case vc2 => exact hf_dw_ld0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    try (case vc3 => exact hf_dw_ld0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    try (case vc4 => exact hf_dw_ld2 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inR14 _ _ _ _ h10 (by omega) (by omega)))
    try (case vc5 => exact hf_dw_ld0 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    try (case vc6 => exact hf_dw_ld0 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)))
    all_goals first
      | (have hl := ‹CondCode.l.interp _ = true›
         have hlt := hf_l_true_lt64 _ _ (by simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega) (by rw [h12, BitVec.toNat_ofNat]; omega) _ hl rfl
         rw [h12] at hlt
         simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hlt ⊢
         omega)
      | (rw [hf3_read_i (hf_T_st2 (Lb140_pre _ _ _ _ _ _ _ _) hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega))) (by omega)]
         try simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
         omega)
      | (rw [Lb140_pre]; exact hf_dw_st0 (hf_dw_st0 hm (hf_inYm _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _) (hf_inY2 _ _ _ _ _ _ h17 (by omega) (by omega) h16 (by omega)) _)
      | (simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat] <;> omega)
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | (rw [h15, BitVec.toNat_ofNat]; omega)
      | (rw [Lb140_pre]; exact hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_Lb16c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb16c" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb16c"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hm⟩, hn⟩ := hs₀
    generalize hI0 : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV0 : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    have hI := And.intro hI0 True.intro
    have hV := And.intro hV0 True.intro
    clear hI0 hV0
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hne : x.nenv ≤ 8 := h0.2.2.2.2.2.2.2.2.2.1
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    have hsw1 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rdi)) = s₀.regs.get64 .rdi := by
      apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth]; omega
    have hsw2 : BitVec.setWidth 64 (BitVec.setWidth 32 (s₀.regs.get64 .rdi) + BitVec.setWidth 32 (s₀.regs.get64 .rdi))
        = s₀.regs.get64 .rdi + s₀.regs.get64 .rdi := by
      apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_add]; omega
    have hrw : t₀.regs.get64 .rsp - 648#64 + 584#64 = t₀.regs.get64 .rsp - 0x40#64 := by bv_omega
    rw [Lb16c_pre] at hm
    have hsme := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lafa0") ⟨by decide, Lafa0_rb (i := i) (v := v) rfl h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hI.1, hV.1, hrw]
    all_goals (run_tac Lean.Elab.Tactic.withMainContext do
      let lctx ← Lean.getLCtx
      let mut k := 0
      for d in lctx do
        if d.isImplementationDetail then continue
        if !d.userName.hasMacroScopes then continue
        let ty ← Lean.instantiateMVars d.type
        if ty.isAppOfArity ``Eq 3 && ((ty.getArg! 1).getAppFn.constName?.map (·.toString) |>.getD "").endsWith "loadInt" then
          let g ← Lean.Elab.Tactic.getMainGoal
          let g' ← g.rename d.fvarId (Lean.Name.mkSimple s!"hld{k}")
          Lean.Elab.Tactic.replaceMainGoal [g']
          k := k + 1)
    all_goals try simp -implicitDefEqProofs only [hsme, Option.some.injEq] at hld0
    all_goals try simp -implicitDefEqProofs only [hsme, Option.some.injEq] at hld1
    all_goals try simp -implicitDefEqProofs only [hsme, Option.some.injEq] at hld2
    all_goals try simp -implicitDefEqProofs only [hsme, Option.some.injEq] at hld3
    all_goals try simp -implicitDefEqProofs only [hsme, Option.some.injEq] at hld4
    all_goals try simp -implicitDefEqProofs only [hsme, Option.some.injEq] at hld5
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, hsw1, hsw2]
    case vc3 => exact hf_dw_ld2 hm (hf_inS _ _ _ (by omega) (by omega))
    case vc4 => exact hf_dw_ld0 hm (hf_inY _ _ _ _ _ _ h7 (by have := hf_test1_odd x.m _ _ (by omega) h13 (by assumption); omega) (by omega) h16 (by omega))
    case vc5 => exact hf_dw_ld0 hm (hf_inY _ _ _ _ _ _ h7 (by have := hf_test1_odd x.m _ _ (by omega) h13 (by assumption); omega) (by omega) h16 (by omega))
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | (rw [hsme]; rfl)
      | (rw [h15, BitVec.toNat_ofNat]; omega)
      | (rw [Lb16c_pre]; exact hm)
      | exact hf_dw_st0 hm (hf_inY _ _ _ _ _ _ h7 (by have := hf_test1_odd x.m _ _ (by omega) h13 (by assumption); omega) (by omega) h16 (by omega)) _
      | (rw [Lb16c_pre]; exact hf_dw_st0 hm (hf_inY _ _ _ _ _ _ h7 (by have := hf_test1_odd x.m _ _ (by omega) h13 (by assumption); omega) (by omega) h16 (by omega)) _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_a1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.a1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "a1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    rw [a1_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lafa0") ⟨by decide, Lafa0_tbl_a1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals close_cell

set_option maxRecDepth 100000 in
theorem blk_Lb26b (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb26b" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb26b"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    rw [Lb26b_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Lb280_tbl_Lb26b _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR0, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR0, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 700000 in
theorem blk_v1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.v1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "v1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hm⟩, hn⟩ := hs₀
    rw [v1_pre] at hm
    have hh4 : hSL x = 4 := by simp -implicitDefEqProofs only [hSL, h11, ite_true]
    have hteB : x.te ((s₀.regs.get64 .r10).toNat + 1) ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 _ (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hG := hm
    rw [hf2_DataW_G, Std.ExtHashMap.sep_assoc] at hG
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb280") ⟨by decide, Lb280_tbl_v1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨v2_tbl_v1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | hf2_ldG | hf2_st | close_cell

set_option maxRecDepth 100000 in
theorem blk_Lb340 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb340" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb340"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    rw [Lb340_pre] at hm
    have hh4 : hSL x = 4 := by simp -implicitDefEqProofs only [hSL, h11, ite_true]
    have hteB : x.te ((s₀.regs.get64 .r10).toNat + 1) ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 _ (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hG := hm
    rw [hf2_DataW_G, Std.ExtHashMap.sep_assoc] at hG
    vcgen
    all_goals try refine ⟨w1_tbl_Lb340 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | hf2_ldG | hf2_st | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_w1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.w1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "w1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    rw [w1_pre] at hm
    have hh4 : hSL x = 4 := by simp -implicitDefEqProofs only [hSL, h11, ite_true]
    have hteB : x.te ((s₀.regs.get64 .r10).toNat + 1) ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 _ (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hG := hm
    rw [hf2_DataW_G, Std.ExtHashMap.sep_assoc] at hG
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb340") ⟨by decide, Lb340_tbl_w1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨w2_tbl_w1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | hf2_ldG | hf2_st | close_cell

set_option maxRecDepth 100000 in
theorem blk_w2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.w2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "w2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    rw [w2_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb01d") ⟨by decide, Lb01d_tbl_w2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_Lb400 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb400" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb400"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [Lb400_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb820") ⟨by decide, Lb820_tbl_Lb400 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Laf40") ⟨by decide, Laf40_tbl_Lb400 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first
      | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_y4 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y4" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hm0 := hm
    rw [La8ea_pre] at hm
    vcgen
    all_goals try refine ⟨(show (HfC x t₀) ∧ (Base t₀ _) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [h2, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | y_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_y7 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y7" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hte9 : x.te 9 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.2.1
    rw [T_eq_TR] at hm
    refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs
      ∧ s.zmms.get (.xmm .mm4) = s₀.zmms.get (.xmm .mm4)
      ∧ (s.dmem =⋆ DataW x t₀ ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀))) ?_ ?_
    · by_cases heq : x.te 0 = x.te 9
      · rw [heq] at h8
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x180#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y7-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x180#64)
          (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) + 0x180#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide), off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y7-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y8" s ∧ var "sbr_hf_assemble.y8" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_y10 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y10" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y10"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hm0 := hm
    rw [La8ea_pre] at hm
    vcgen
    all_goals try refine ⟨(show (HfC x t₀) ∧ (Base t₀ _) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [h2, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | y_close

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_y11 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y11" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y11"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hte9 : x.te 9 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.2.1
    rw [T_eq_TR] at hm
    refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs
      ∧ s.zmms.get (.xmm .mm4) = s₀.zmms.get (.xmm .mm4)
      ∧ (s.dmem =⋆ DataW x t₀ ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀))) ?_ ?_
    · by_cases heq : x.te 0 = x.te 9
      · rw [heq] at h8
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x240#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y11-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x240#64)
          (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) + 0x240#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide), off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y11-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y12" s ∧ var "sbr_hf_assemble.y12" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_y14 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y14" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y14"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    rw [La8ea_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.La8f6") ⟨by decide, La8f6_tbl_La8ea _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨Lb820_tbl_La8ea _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | y_close

theorem blk_Lb843 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb843" := by
  info_off
  intro blk _ n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact hs₀.1.elim

theorem blk_Lb84d (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb84d" := by
  info_off
  intro blk _ n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact hs₀.1.elim

end Kraken.Examples.Sbr.HfAssemble
