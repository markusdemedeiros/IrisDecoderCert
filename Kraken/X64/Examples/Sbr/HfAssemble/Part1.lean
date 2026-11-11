import Kraken.X64.Examples.Sbr.HfAssemble.Base

/-! `sbr_hf_assemble`: block theorems, part 1 of 2 (generated; the split balances
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
theorem blk_p1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.p1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "p1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, ⟨ha0, ha1, ha2, ha3, ha4⟩, hm⟩, hn⟩ := hs₀
    rw [p1_pre] at hm
    have hB0 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)⟩
    have hB1 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB2 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB3 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB4 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
    have hB5 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
    have hB6 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _)
    have hB7 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _)
    have hB8 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _)
    have hS1 := fun (v1 : Int) => store_keep hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (v := v2)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (v := v3)
    have hL3_0 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hL3_1 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_2 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_4 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_5 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_7 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (v := v4)
    have hL4_0 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hL4_1 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL4_2 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL4_3 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL4_4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL4_5 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL4_6 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL4_7 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => Mem.Val.loadInt (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS5 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) (v5 : Int) => store_keep (hS4 v1 v2 v3 v4) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) (v := v5)
    clear hS1 hS2 hS3 hS4
    have hC := h0
    have hkx := sext_ofInt32_nat x.kx (by have := hC.2.2.2.2.2.2.2.2.1; omega)
    have hmm := sext_ofInt32_nat x.m (by have := hC.2.2.2.2.2.2.2.1; omega)
    vcgen
    all_goals try refine ⟨p2_tbl_p1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, ha0, ha1, ha2, ha3, ha4,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hL3_0, hL3_1, hL3_2, hL3_3, hL3_4, hL3_5, hL3_7, hL4_0, hL4_1, hL4_2, hL4_3, hL4_4, hL4_5, hL4_6, hL4_7, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hL3_0, hL3_1, hL3_2, hL3_3, hL3_4, hL3_5, hL3_7, hL4_0, hL4_1, hL4_2, hL4_3, hL4_4, hL4_5, hL4_6, hL4_7, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals first | ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption) | close_cell

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_r2c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r2c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r2c"
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
theorem blk_r4 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r4" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r4_pre] at hm
    vcgen
    all_goals try refine ⟨r4c_tbl_r4 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_r4c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r4c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r4c"
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
theorem blk_r6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r6" := by
  info_off
  clear hc
  cfg_block
  measure_hb "r6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, hm⟩, hn⟩ := hs₀
    rw [r6_pre] at hm
    vcgen
    all_goals try refine ⟨r6c_tbl_r6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_r6c (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.r6c" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "r6c"
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
theorem blk_La8e1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.La8e1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "La8e1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, hm⟩, hn⟩ := hs₀
    rw [La8e1_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb426") ⟨by decide, Lb426_tbl_La8e1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨La8ea_tbl_La8e1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals close_cell

set_option maxRecDepth 100000 in
theorem blk_La8ea (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.La8ea" := by
  info_off
  clear hc
  cfg_block
  measure_hb "La8ea"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, hm⟩, hn⟩ := hs₀
    rw [La8ea_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb820") ⟨by decide, Lb820_tbl_La8ea _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨La8f6_tbl_La8ea _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_s0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s0" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    have hteK : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (by omega)
    rw [s0_pre] at hm
    vcgen
    all_goals try refine ⟨La970_tbl_s0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | close_cell | (simp -implicitDefEqProofs only [h2, h4, h9, h10, hSL]; exact hf1_s0_row _ _ _ _ (by omega) (by split <;> omega) (by simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_mul]; omega))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_La970 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.La970" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "La970"
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
set_option maxHeartbeats 500000 in
theorem blk_d0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d0" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d0_pre] at hm
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
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.La970") ⟨by decide, La970_tbl_d0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨x0_tbl_d0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_c1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c1" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c1"
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
theorem blk_x1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.x1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "x1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [x1_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Laa62_tbl_x1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_Laa62 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Laa62" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Laa62"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [Laa62_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae20") ⟨by decide, Lae20_tbl_Laa62 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lab02") ⟨by decide, Lab02_tbl_Laa62 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨s2_tbl_Laa62 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_s2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    have hteK : x.te 2 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 2 (by omega)
    rw [s2_pre] at hm
    vcgen
    all_goals try refine ⟨Laab0_tbl_s2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_Laab0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Laab0" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "Laab0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 3 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 3 (by omega)
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
theorem blk_c2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c2" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 3 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 3 (by omega)
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
theorem blk_x2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.x2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "x2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [x2_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Lab02_tbl_x2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_Lab02 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lab02" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lab02"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [Lab02_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae20") ⟨by decide, Lae20_tbl_Lab02 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Laba2") ⟨by decide, Laba2_tbl_Lab02 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨s3_tbl_Lab02 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_s3 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s3" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    have hteK : x.te 3 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 3 (by omega)
    rw [s3_pre] at hm
    vcgen
    all_goals try refine ⟨Lab50_tbl_s3 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_d3 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d3" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d3"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d3_pre] at hm
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
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lab50") ⟨by decide, Lab50_tbl_d3 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨x3_tbl_d3 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_Labf0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Labf0" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "Labf0"
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
         · first | exact Mem.push_slot_res hm (by first | rfl | bv_omega | (rw [hrsp]; show _ - 8#64 = _; bv_omega)) _
         · exact True.intro
         · first | (apply DataW_carve_mc <;> omega)
         · vcgen
           all_goals first | grind_cells'
         · first | grind_cells')
      | grind_cells'

set_option maxRecDepth 100000 in
theorem blk_x4 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.x4" := by
  info_off
  clear hc
  cfg_block
  measure_hb "x4"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [x4_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Lac42_tbl_x4 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_Lac42 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lac42" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lac42"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [Lac42_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae20") ⟨by decide, Lae20_tbl_Lac42 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lace2") ⟨by decide, Lace2_tbl_Lac42 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨s5_tbl_Lac42 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_c5 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c5" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c5"
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
set_option maxHeartbeats 700000 in
theorem blk_Lace2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lace2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lace2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [Lace2_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae20") ⟨by decide, Lae20_tbl_Lace2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lad82") ⟨by decide, Lad82_tbl_Lace2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨s6_tbl_Lace2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_s6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.s6" := by
  info_off
  clear hc
  cfg_block
  measure_hb "s6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, hm⟩, hn⟩ := hs₀
    have hteK : x.te 6 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 6 (by omega)
    rw [s6_pre] at hm
    vcgen
    all_goals try refine ⟨Lad30_tbl_s6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_Lad30 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lad30" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "Lad30"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 7 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 7 (by omega)
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
theorem blk_c6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c6" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hte : x.te 7 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 7 (by omega)
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
theorem blk_d6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d6" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d6_pre] at hm
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
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lad30") ⟨by decide, Lad30_tbl_d6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨x6_tbl_d6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_x6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.x6" := by
  info_off
  clear hc
  cfg_block
  measure_hb "x6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, hm⟩, hn⟩ := hs₀
    rw [x6_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    have hR1 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hR2 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨Lad82_tbl_x6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
set_option maxHeartbeats 400000 in
theorem blk_Lad82 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lad82" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lad82"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [Lad82_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae20") ⟨by decide, Lae20_tbl_Lad82 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lae0d") ⟨by decide, Lae0d_tbl_Lad82 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨s7_tbl_Lad82 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_c7 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.c7" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  cfg_block
  measure_hb "c7"
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
set_option maxHeartbeats 500000 in
theorem blk_d7 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.d7" := by
  info_off
  clear hc
  cfg_block
  measure_hb "d7"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    rw [d7_pre] at hm
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
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Ladcc") ⟨by decide, Ladcc_tbl_d7 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨Lae0d_tbl_d7 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩
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
set_option maxHeartbeats 800000 in
theorem blk_Lae0d (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lae0d" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lae0d"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, hm⟩, hn⟩ := hs₀
    rw [Lae0d_pre] at hm
    vcgen
    all_goals try refine ⟨Lae20_tbl_Lae0d _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
theorem blk_m1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.m1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "m1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [m1_pre] at hm
    have hB0 := Mem.Block.loadInt_isSome_at hm (Mem.Split.here _ _)
    have hB1 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.here _ _) _)
    have hB2 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _)
    have hB3 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hB4 := Option.isSome_iff_exists.mpr ⟨_, Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)⟩
    have hR3 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hR4 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS1 := fun (v1 : Int) => store_keep hm (Mem.Split.right (Mem.Split.here _ _) _) (Mem.Split.right (Mem.Split.here _ _) _) (v := v1)
    have hS2 := fun (v1 : Int) (v2 : Int) => store_keep (hS1 v1) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (v := v2)
    have hL2_1 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL2_2 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL2_3 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL2_4 := fun (v1 : Int) (v2 : Int) => Mem.Val.loadInt (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => store_keep_val (hS2 v1 v2) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (v := v3)
    have hL3_1 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_2 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_3 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hL3_4 := fun (v1 : Int) (v2 : Int) (v3 : Int) => Mem.Val.loadInt (hS3 v1 v2 v3) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hS4 := fun (v1 : Int) (v2 : Int) (v3 : Int) (v4 : Int) => store_keep (hS3 v1 v2 v3) (Mem.Split.here _ _) (Mem.Split.here _ _) (v := v4)
    clear hS1 hS2 hS3
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    vcgen
    all_goals try refine ⟨m2_tbl_m1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hR3, hR4, hL2_1, hL2_2, hL2_3, hL2_4, hL3_1, hL3_2, hL3_3, hL3_4, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try simp -implicitDefEqProofs only [hR3, hR4, hL2_1, hL2_2, hL2_3, hL2_4, hL3_1, hL3_2, hL3_3, hL3_4, Option.some.injEq, Option.isSome_some] at *
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt8_ofBytes_toBytes1, BitVec.ofInt32_ofBytes_toBytes4,
      BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt128_ofBytes_toBytes16, BitVec.ofInt_toInt] at *
    all_goals try ((repeat (with_reducible apply Mem.loadInt_isSome_storeInt)); with_reducible assumption)
    -- the cell closers, then the frame goal through `hf2_r9mul` before any `grind` (a failing
    -- `grind` on it costs 0.17M)
    all_goals first
      | omega | with_reducible assumption | cell_some | cell_lcpi | cell_val
      | (simp -implicitDefEqProofs only [h4, hf2_r9mul]; close_cell)
      | close_cell
      | (rw [h4]; exact hf2_r9mul x)
      | (rw [h8]; first | exact hf2_sub1 _ hm1 hm48 | exact hf2_addm1 _ hm1 hm48 | exact hf2_m1addm1 _ hm1 hm48)
      | ((repeat apply Mem.loadInt_isSome_storeInt); simp -implicitDefEqProofs only [Hid, DataW, Blocks, Std.ExtHashMap.sep_assoc] at hm; grind_cells')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_Laf40 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Laf40" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Laf40"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, hm⟩, hn⟩ := hs₀
    have hne : x.nenv ≤ 8 := h0.2.2.2.2.2.2.2.2.2.1
    have hte0 := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat) (by omega)
    have hte1 := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    rw [Laf40_pre] at hm
    have hT := hm
    rw [hf4_te_arr (arg3 t₀) x.te] at hT
    obtain ⟨htl0, htl1⟩ := hf4_te_ld2 (r := s₀.regs.get64 .r10) hT h2 (by omega)
    clear hT
    have hmH := hm
    unfold Mem.Hid at hmH
    have hlf0 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hlf1 := Mem.Val.loadInt hmH (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hlf2 := Mem.Val.loadInt hmH (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    clear hmH
    have hsb0 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hsb1 := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb400") ⟨by decide, Lb400_tbl_Laf40 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lafd9") ⟨by decide, Lafd9_tbl_Laf40 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
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
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld0); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld0); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld1); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld1); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld2); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld2); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld3); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld3); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld4); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld4); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld5); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld5); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5)
    all_goals try subst_vars
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld0); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld0); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld1); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld1); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld2); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld2); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld3); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld3); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld4); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld4); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4)
    all_goals try ((try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide)] at hld5); (try rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide)] at hld5); simp -implicitDefEqProofs only [htl0, htl1, hlf0, hlf1, hlf2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, BitVec.toNat_ofNat]
    all_goals try simp -implicitDefEqProofs only [hf4_b8] at *
    all_goals try (refine Mem.Block.storeInt_val2 hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) ?_ ?_)
    case vc11.refine_8 =>
      rw [hf4_r12 _ _ _ hte0]
      try rfl
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | (rw [htl0]; rfl)
      | (rw [htl1]; rfl)
      | (rw [Laf40_pre]; with_reducible exact hm)
      | (congr 1; rw [hf4_r192]; all_goals first | rfl | omega)
      | (congr 1; rw [hf4_inc]; all_goals omega)
      | (rw [hf4_inc]; all_goals omega)
      | exact fun h => h
      | (rw [hlf0]; rfl)
      | with_reducible exact hsb0
      | (rw [Mem.loadInt_storeInt_sub_lo _ _ 176 232 _ (by decide) (by decide), hlf1]; rfl)
      | (rw [Mem.loadInt_storeInt_sub_lo _ _ 176 224 _ (by decide) (by decide), hlf2]; rfl)
      | (rw [Mem.loadInt_storeInt_sub_hi _ _ 176 80 _ (by decide) (by decide)]; with_reducible exact hsb1)
      | (rw [hf4_tn_inc]; all_goals first | omega | (left; omega))
      | (rw [hf4_tn_inc, Nat.add_sub_cancel, h6]; all_goals first | rfl | omega)
      | (rw [hf4_r12 _ _ _ hte0]; rfl)
      | (simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega)
      | (have hc := ‹CondCode.nc.interp _ = false›
         rw [CondCode.interp_nc_sub8 _ _ _ rfl] at hc
         simp -implicitDefEqProofs only [decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hc
         simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]
         omega)
      | (try simp -implicitDefEqProofs only [arg0, arg3, hSL]
         apply BitVec.eq_of_toNat_eq
         simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_shiftLeft, BitVec.toNat_mul, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Nat.reducePow]
         try generalize (if x.smooth = 0 then 4 else 0) = H at hh ⊢
         omega)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_Lafa0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lafa0" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lafa0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    have hne : x.nenv ≤ 8 := h0.2.2.2.2.2.2.2.2.2.1
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    rw [Lafa0_pre] at hm
    have hl50 := Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hvec := Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) _) _) _) _) _)
    have hl11 := hf4_l11 hm
    have htl := hf4_te_ld ((s₀.regs.get64 .r10).toNat + 1) (by omega) hm
    have hh : hSL x ≤ 4 := by unfold hSL; split <;> omega
    have htv := hf4_te2 (x.te ((s₀.regs.get64 .r10).toNat + 1)) (by omega)
    have htl2 : s₀.dmem.loadInt (s₀.regs.get64 .r8 + BitVec.ofNat 64 ((s₀.regs.get64 .r10).toNat + 1) * 1#64 + 88732#64) 1
        = some (Int.ofBytes (Int.toBytes 1 ((x.te ((s₀.regs.get64 .r10).toNat + 1) : Nat) : Int))) := by
      rw [BitVec.mul_one, h2, BitVec.add_assoc, BitVec.add_comm (BitVec.ofNat 64 _) 88732#64, ← BitVec.add_assoc]
      exact htl
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb400") ⟨by decide, Lb400_tbl_Lafa0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨Lafd9_tbl_Lafa0 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
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
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld0
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld1
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld2
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld3
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld4
    all_goals try simp -implicitDefEqProofs only [hl50, hl11, htl2, BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.some.injEq] at hld5
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, BitVec.toNat_ofNat]
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | with_reducible exact hf4_xb _
      | (rw [hl11]; rfl)
      | (rw [hl50]; rfl)
      | (rw [htl2]; rfl)
      | with_reducible exact hvec
      | (rw [hf4_tn_succ _ (by omega)]; omega)
      | (have hc := ‹CondCode.nc.interp _ = false›
         rw [CondCode.interp_nc_sub64 _ _ _ rfl, htv] at hc
         simp -implicitDefEqProofs only [decide_eq_false_iff_not, Nat.not_le] at hc
         rw [hf4_tn_succ _ (by omega)] at hc ⊢
         omega)
      | (simp -implicitDefEqProofs only [ArgRegs]; with_reducible exact hf4_step _ _ _ _ _ h7 (by omega) (by rw [hf4_tn_succ _ (by omega)]; omega))
      | (try simp -implicitDefEqProofs only [arg0, arg3, hSL]
         rw [h7, hf4_tn_succ _ (by omega)]
         apply BitVec.eq_of_toNat_eq
         simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
         try generalize (if x.smooth = 0 then 4 else 0) = H at hh ⊢
         omega)
      | (simp -implicitDefEqProofs only [ArgRegs]; with_reducible exact hf4_step _ _ _ _ _ h8 (by omega) (by rw [hf4_tn_succ _ (by omega)]; omega))
      | (try simp -implicitDefEqProofs only [arg0, arg3, hSL]
         rw [h8, hf4_tn_succ _ (by omega)]
         apply BitVec.eq_of_toNat_eq
         simp -implicitDefEqProofs only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
         try generalize (if x.smooth = 0 then 4 else 0) = H at hh ⊢
         omega)
      | (rw [h9]; congr 3; omega)
      | (refine ⟨?_, ?_⟩
         · first | (rw [h9]; congr 3; omega) | (rw [h9]; congr 2; congr 1; omega) | (simp -implicitDefEqProofs only [ArgRegs]; rw [h9]; congr 3; omega)
         · first | with_reducible assumption | exact hm)
      | (rw [Lafa0_pre]; exact hm)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_Lafd9 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lafd9" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lafd9"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, hm⟩, hn⟩ := hs₀
    rw [Lafd9_pre] at hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb000") ⟨by decide, Lb000_tbl_Lafd9 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb248") ⟨by decide, Lb248_tbl_Lafd9 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨Lb000_tbl_Lafd9 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
set_option maxHeartbeats 1000000 in
theorem blk_Lb08f (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb08f" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb08f"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    try dsimp only at *
    generalize hI0 : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV0 : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    have hI := And.intro hI0 True.intro
    have hV := And.intro hV0 True.intro
    clear hI0 hV0
    rw [Lb08f_pre] at hm
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hkx := Mem.Val.loadInt_lo4 (v := (BitVec.ofNat 64 x.kx).toInt) hm (Mem.Split.right (Mem.Split.right
      (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
    rw [BitVec.toInt_ofNat64_of_lt _ (by omega)] at hkx
    have hlf8 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0xf8#64) 8 = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 (x.m - 1)).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.here _ _) _) (Int.toBytes_length _ _) (by decide)
    have hlc0 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0xc0#64) 8 = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 x.m).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) (Int.toBytes_length _ _) (by decide)
    have hl88 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x88#64) 8 = some (Int.ofBytes (Int.toBytes 8 (arg0 t₀ + BitVec.ofNat 64 (8 * x.kx + 8 + 512 * i)).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hl40 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8 = some (Int.ofBytes (Int.toBytes 8 (BitVec.ofNat 64 i).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    have hl38 : s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x38#64) 8 = some (Int.ofBytes (Int.toBytes 8 (arg3 t₀).toInt)) :=
      Mem.Val.loadInt hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _) _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try refine ⟨n2_tbl_Lb08f _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb16c") ⟨by decide, Lb16c_tbl_Lb08f _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp -implicitDefEqProofs only [hI.1, hV.1]
    case vc2 =>
      exfalso
      have hl := ‹Mem.loadInt _ (t₀.regs.get64 .rsp - 0x90#64) 4 = some _›
      rw [hkx] at hl
      obtain rfl := Option.some.inj hl
      have hf := ‹CondCode.z.interp _ = true›
      rw [BitVec.ofInt32_ofBytes_toBytes4, hf_z32_ne _ _ (by omega) (by decide)] at hf
      exact absurd hf (by decide)
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
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld0
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld1
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld2
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld3
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld4
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld5
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld6
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld7
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld8
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld9
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld10
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld11
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld12
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld13
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld14
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld15
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld16
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld17
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld18
    all_goals try simp -implicitDefEqProofs only [hkx, hlf8, hlc0, hl88, hl40, hl38, Option.some.injEq] at hld19
    all_goals try subst_vars
    all_goals first
      | exact ⟨trivial, trivial⟩
      | omega
      | with_reducible assumption
      | cell_some
      | cell_lcpi
      | (simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.zero_mod] <;> omega)
      | exact hf_and1_lt2 _
      | (have hf := ‹CondCode.l.interp _ = false›
         exact hf_l_false_ge _ _ (by omega) (by omega) _ hf rfl)
      | (have hf := ‹CondCode.l.interp _ = false›
         rw [CondCode.interp_l_sub32 _ _ _ rfl] at hf
         simp -implicitDefEqProofs (disch := omega) only [decide_eq_false_iff_not, not_lt, BitVec.ofInt64_ofBytes_toBytes8,
           BitVec.ofInt_toInt, hf_toInt_sw32] at hf
         omega)
      | (rw [h14]; exact hf_lea4 _ _ _)
      | (simp -implicitDefEqProofs only [BitVec.ofInt64_ofBytes_toBytes8, BitVec.ofInt_toInt, Option.isSome_some]; done)
      | with_reducible exact Mem.Block.loadInt_isSome_at hm (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
      | (have hD := hm; simp -implicitDefEqProofs only [DataW] at hD
         first
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.here _ _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _)
           | with_reducible exact Mem.Block.loadInt_isSome_at hD (Mem.Split.left (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.right (Mem.Split.here _ _) _) _) _) _) _) _))
      | (rw [hkx]; rfl)
      | (rw [hlf8]; rfl)
      | (rw [hlc0]; rfl)
      | (rw [hl88]; rfl)
      | (rw [hl40]; rfl)
      | (rw [hl38]; rfl)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1700000 in
theorem blk_Lb1a0 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb1a0" := by
  info_off
  obtain ⟨hG, hN0, hN1, hN2, hN3, hMc⟩ := hc
  clear hG hMc
  cfg_block
  measure_hb "Lb1a0"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hm⟩, hn⟩ := hs₀
    have hte := h0.2.2.2.2.2.2.2.2.2.2.1 ((s₀.regs.get64 .r10).toNat + 1) (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hkm : x.kx + x.m ≤ 64 := h0.2.2.2.2.2.2.2.2.1
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    rw [show var "sbr_hf_assemble.Lb1a0" s₀ = 1900000 - 100000 * (s₀.regs.get64 .r10).toNat - 2000 * (BitVec.ofInt 64 ((s₀.dmem.loadInt (s₀.regs.get64 .rsp + 0x248#64) 8).getD 0)).toNat + 200 from rfl] at hn
    rw [show s₀.regs.get64 .rsp + 0x248#64 = t₀.regs.get64 .rsp - 0x40#64 by rw [hrsp]; exact hf_rsp_648_584 _] at hn
    generalize hI : (BitVec.ofInt 64 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x40#64) 8).getD 0)).toNat = i at *
    generalize hV : BitVec.ofInt 128 ((s₀.dmem.loadInt (t₀.regs.get64 .rsp - 0x78#64) 16).getD 0) = v at *
    generalize hE : (s₀.regs.get64 .r10).toNat = e at *
    have hE2 := And.intro hE trivial
    have h13v := And.intro h13 trivial
    clear hI hV hE h13
    have hi37 : i ≤ 37 := by omega
    have he8 : e < 8 := by omega
    rw [Lb1a0_pre] at hm
    obtain ⟨q, hq, hq4⟩ : ∃ q, (s₀.regs.get64 .rcx).toNat % 2 ^ 32 = q ∧ q < 4 := ⟨_, rfl, by omega⟩
    have hq32 : (s₀.regs.get64 .rcx).setWidth 32 = BitVec.ofNat 32 q := by apply BitVec.eq_of_toNat_eq; simp -implicitDefEqProofs only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]; omega
    clear hq
    have hNq := hf_noise_spec q hq4 hN0 hN1 hN2 hN3
    clear hN0 hN1 hN2 hN3
    vcgen [MachineWP.call_mem_proc_spec_at
      (DataW x t₀ ⋆ 192 ?@ (t₀.regs.get64 .rsp - 0x1c8#64),
        ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀ ⋆ (IdxC x t₀
          ⋆ FL2q x t₀ e i v (Rest x.R ra t₀)))))) (hfNoiseFn fs q)
      (Kraken.Executable.ProcSpec.widen (k := k) hNq (Nat.zero_le k) (by omega))]
    all_goals try clear hNq
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280,
      hrsp, hrbp, hq32, BitVec.xor_self, BitVec.setWidth_32_64_32,
      BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne, ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    case vc6 =>
         refine ⟨?_, fun ra => ⟨⟨?_, ?_, ?_⟩, fun s' hpost => ?_⟩, ?_⟩
         · simp -implicitDefEqProofs only [Option.map_eq_some_iff]
           refine ⟨Int.ofBytes (Int.toBytes 8 (hfNoiseFn fs q).toBitVec.toInt), ?_, hf_fn_load _⟩
           rename_i v8 v7 v6 v5 hcnd l8 l7 l6 l5
           have e5 : BitVec.ofInt 64 v5 = arg2 t₀ := by
             grind_cells'
           rw [e5]
           rcases hf_noise_cases q hq4 with rfl | rfl | rfl | rfl <;> simp -implicitDefEqProofs only [hfNoiseFn_0, hfNoiseFn_1, hfNoiseFn_2, hfNoiseFn_3] <;> grind_cells'
         · refine Mem.push_slot_res (b := t₀.regs.get64 .rsp - 0x290#64) ?_ ?_ _
           · rw [← T_FL2_callq, Lb1a0_pre]
             first | exact hm | grind_cells'
           · first | rfl | exact hf_rsp_648_8 _ | exact hf_rsp_656_648 _
         · rename_i v8 v7 v6 v5 hcnd l8 l7 l6 l5
           have e8 : BitVec.ofInt 64 v8 = arg2 t₀ + 0x5f0c0#64 + BitVec.ofNat 64 (192 * e) := by
             grind_cells'
           have e6 : BitVec.ofInt 64 v6 = BitVec.ofNat 64 x.m := by
             grind_cells'
           refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hf_noiseK_align h0 q hq4⟩
           · rw [e8]; exact hf_align_row _ _ _ h0.2.1 (by omega) (by omega) (by omega)
           · rcases h9 with h | h <;> rw [h]; exact hf_align_row _ _ _ h0.2.2.1 (by omega) (by omega) (by omega); exact hf_align_qtab _ h0.1
           · rw [e6, BitVec.toNat_ofNat]; omega
           · rw [e6, BitVec.toNat_ofNat]; omega
           · rw [h13v.1]; simp -implicitDefEqProofs only [BitVec.toNat_setWidth]; omega
         · rename_i v8 v7 v6 v5 hcnd l8 l7 l6 l5
           refine Lb1a0_carve x t₀ x.kx x.m i e _ _ _ _ (BitVec.ofInt 64 v6) _ (hfc_ypos h0) (hfc_y1 h0) hkm hm48 hi37 he8 ?hr9 ?hIt ?e0 ?e1 ?hQ (hf_noiseK_cases q hq4)
           case hIt => rfl
           case e0 => exact h7
           case hQ => exact h9
           case hr9 => grind_cells'
           case e1 => grind_cells'
         · obtain ⟨hrsp', hrbp', ⟨hbx', h12', h13', h14', h15'⟩, hm'⟩ := hpost
           rw [← T_FL2_callq] at hm'
           have hI' := FL2_read_i hm' (by omega)
           have hra : s'.regs.get64 .rsp + 0x248#64 = t₀.regs.get64 .rsp - 0x40#64 := by
             rw [hrsp']; first | exact hf_rsp_656_8_584 _ | exact hf_rsp_648_584 _
           vcgen
           refine ⟨a1_tbl_rb _ _ _ _ _ s' e i v ⟨h0, ⟨?_, hrbp'⟩, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, ?_, hm'⟩, ?_⟩
           all_goals first
             | (rw [hrsp']; first | exact hf_rsp_656_8 _ | rfl)
             | (rw [hbx']; exact h7)
             | (rw [h12']; exact h8)
             | (rw [h13']; exact h9)
             | (rw [h14']; exact h10)
             | (rw [h15', h12, ← hE2.1, BitVec.ofNat_toNat, BitVec.setWidth_eq])
             | (rw [hra, hI', h15', h12, hE2.1]; omega)
             | fail
         · grind_cells'
    all_goals first
      | close_cell
      | (exfalso; rename_i hcnd; simp -implicitDefEqProofs only [CondCode.interp_nc, StatusFlags.cf_from_result, BitVec.unsigned_eq, hf_sub_cf32, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, BitVec.toNat_setWidth, BitVec.toNat_ofNat] at hcnd; omega)
      | fail

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_Lb248 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb248" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb248"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    rw [Lb248_pre] at hm
    have hld := hf2_ld_lo _ _ _ (by have := h0.2.2.2.2.2.2.2.1; omega) _ hm
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb01d") ⟨by decide, Lb01d_tbl_Lb248 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb26b") ⟨by decide, Lb26b_tbl_Lb248 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb340") ⟨by decide, Lb340_tbl_Lb248 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | (rw [hld]; rfl) | close_cell

set_option maxRecDepth 100000 in
theorem blk_Lb280 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb280" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb280"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hm⟩, hn⟩ := hs₀
    rw [Lb280_pre] at hm
    have hh4 : hSL x = 4 := by simp -implicitDefEqProofs only [hSL, h11, ite_true]
    have hteB : x.te ((s₀.regs.get64 .r10).toNat + 1) ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 _ (by omega)
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    have hG := hm
    rw [hf2_DataW_G, Std.ExtHashMap.sep_assoc] at hG
    vcgen
    all_goals try refine ⟨v1_tbl_Lb280 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
set_option maxHeartbeats 400000 in
theorem blk_v2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.v2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "v2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hm⟩, hn⟩ := hs₀
    rw [v2_pre] at hm
    have hR0 := Mem.Val.loadInt hm (Mem.Split.here _ _) (Int.toBytes_length _ _) (by decide)
    vcgen
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.Lb01d") ⟨by decide, Lb01d_tbl_v2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try refine ⟨Lb340_tbl_v2 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
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
set_option maxHeartbeats 300000 in
theorem blk_Lb426 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb426" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb426"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, hm⟩, hn⟩ := hs₀
    have hm0 := hm
    rw [La8ea_pre] at hm
    vcgen
    all_goals try refine ⟨(show (HfC x t₀) ∧ (Base t₀ _) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [h2, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | y_close

set_option maxRecDepth 100000 in
theorem blk_y1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y1" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hte9 : x.te 9 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.2.1
    rw [T_eq_TR] at hm
    refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs
      ∧ s.zmms.get (.xmm .mm4) = s₀.zmms.get (.xmm .mm4)
      ∧ (s.dmem =⋆ DataW x t₀ ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀))) ?_ ?_
    · by_cases heq : x.te 0 = x.te 9
      · rw [heq] at h8
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9))
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y1-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9))
          (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0))
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega), off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y1-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y2" s ∧ var "sbr_hf_assemble.y2" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
theorem blk_y2 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y2" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y2"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    have hte0 : x.te 0 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.1 0 (Nat.zero_le _)
    have hte9 : x.te 9 ≤ 19 := h0.2.2.2.2.2.2.2.2.2.2.2.1
    rw [T_eq_TR] at hm
    refine Triple.post_imp (Q' := fun _ s => s.regs = s₀.regs.set64 .rdi (arg3 t₀ + 0x130b0#64)
      ∧ s.zmms.get (.xmm .mm4) = s₀.zmms.get (.xmm .mm4)
      ∧ (s.dmem =⋆ DataW x t₀ ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀))) ?_ ?_
    · by_cases heq : x.te 0 = x.te 9
      · rw [heq] at h8
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9))
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y2-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h2, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9))
          (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0))
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
          (by rw [off_toNat _ _ _ _ (by decide) (by decide) (by omega), off_toNat _ _ _ _ (by decide) (by decide) (by omega)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y2-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h2, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y3" s ∧ var "sbr_hf_assemble.y3" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_y3 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y3" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y3"
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
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0xc0#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y3-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 9) + 0xc0#64)
          (arg3 t₀ + 0x11130#64 + BitVec.ofNat 64 (384 * x.te 0) + 0xc0#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide), off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y3-ne"
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
      show table k fs x ra t₀ "sbr_hf_assemble.y4" s ∧ var "sbr_hf_assemble.y4" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 300000 in
theorem blk_y5 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y5" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y5"
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
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) + 0xc0#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y5-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) + 0xc0#64)
          (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0) + 0xc0#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide), off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y5-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y6" s ∧ var "sbr_hf_assemble.y6" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_y6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y6" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y6"
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
set_option maxHeartbeats 400000 in
theorem blk_y8 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y8" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y8"
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
theorem blk_y9 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y9" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y9"
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
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x180#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y9-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x180#64)
          (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0) + 0x180#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide), off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y9-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y10" s ∧ var "sbr_hf_assemble.y10" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
theorem blk_y12 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y12" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y12"
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
theorem blk_y13 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y13" := by
  info_off
  clear hc
  cfg_block
  measure_hb "y13"
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
        obtain ⟨H, eH⟩ := DataW_carve_y1 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x240#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y13-eq"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals first | rfl | grind_cells'
      · obtain ⟨H, eH⟩ := DataW_carve_y2 x t₀ (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) + 0x240#64)
          (arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0) + 0x240#64)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
          (by rw [off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide), off_toNat3 _ _ _ _ _ (by decide) (by decide) (by omega) (by decide)]; omega)
        rw [eH] at hm ⊢
        simp -implicitDefEqProofs only [Std.ExtHashMap.sep_assoc] at hm ⊢
        generalize H ⋆ TR k fs x ra t₀ (IdxC x t₀) (FP x t₀) = G at hm ⊢
        measure_hb "y13-ne"
          vcgen
          all_goals try subst_vars
          all_goals try dsimp only at *
          all_goals opaque_stores
          all_goals try simp -implicitDefEqProofs only [h7, h8, h9, h10, AddrIndex.offset64, Int64.toBitVec_ofNat_norm,
            BitVec.ofNat_eq_ofNat, BitVec.add_zero, add_zero64, RegZmms.get_set_ymm_xmm_ne, ne_eq,
            reduceCtorEq, not_false_eq_true, Reg64s.get64_set64, ite_true, ite_false, Width.bytes, BitVec.mul_one] at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 9) = S at *
          all_goals try generalize arg3 t₀ + 0x130b0#64 + BitVec.ofNat 64 (384 * x.te 0) = D at *
          all_goals first | rfl | grind_cells'
    · rintro s ⟨hr, hx, hmem⟩
      show table k fs x ra t₀ "sbr_hf_assemble.y14" s ∧ var "sbr_hf_assemble.y14" s ≤ n
      refine ⟨(show (HfC x t₀) ∧ (Base t₀ s) ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ from ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩), ?_⟩
      all_goals try simp -implicitDefEqProofs only [Base, hr, hx, Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false]
      all_goals first | exact ⟨hrsp, hrbp⟩ | assumption | rfl | (rw [T_eq_TR]; exact hmem) | (subst hn; exact Nat.le_refl _)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 500000 in
theorem blk_Lb820 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb820" := by
  info_off
  clear hc
  cfg_block
  measure_hb "Lb820"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h8, hxb, hm⟩, hn⟩ := hs₀
    -- G1: the stored low half of xmm4 is in range; `done` takes the cell as `HfIdxOut`
    have hv := hf_xb64 hxb
    simp -implicitDefEqProofs only [T, FZ, Saved, Rest] at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Rest, T, FZ, Saved, AddrIndex.offset64, BitVec.add_zero] at *
    all_goals try call_simp
    all_goals try (first | omega | with_reducible assumption | grind_cells')
    all_goals try refine ⟨⟨h0, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try refine hf_idx_intro _ hv.1 hv.2 ?_
    all_goals try (first | omega | with_reducible assumption | grind_cells')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 600000 in
theorem blk_done (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.done" := by
  info_off
  clear hc
  cfg_block
  measure_hb "done"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, hrsp, hrbp, hsv, hm⟩, hn⟩ := hs₀
    simp -implicitDefEqProofs only [T, FZ, Saved, Rest] at hm
    vcgen
    all_goals try subst_vars
    all_goals try simp -implicitDefEqProofs only [Rest, T, FZ, Saved, AddrIndex.offset64, BitVec.add_zero] at *
    all_goals try call_simp
    all_goals first | omega | with_reducible assumption | grind_cells'

theorem blk_Lb83e (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb83e" := by
  info_off
  intro blk _ n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact hs₀.1.elim

theorem blk_Lb848 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb848" := by
  info_off
  intro blk _ n
  refine Triple.pin fun s₀ hs₀ => ?_
  exact hs₀.1.elim

end Kraken.Examples.Sbr.HfAssemble
