set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem blk_Lad30 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lad30" := by
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
    simp only [T] at hm
    vcgen [MachineWP.call_proc_spec_at (DataW x t₀, ScW x t₀ ⋆ (FnW fs t₀ ⋆ (TeW x t₀ ⋆ (EaW x t₀
      ⋆ (IdxC x t₀ ⋆ FE x t₀ (Rest x.R ra t₀)))))) "memcpy"
      (Kraken.Executable.ProcSpec.widen (k := k) hMc (Nat.le_refl k) (by omega))]
    clear hG hN0 hN1 hN2 hN3 hMc
    all_goals call_simp
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
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
