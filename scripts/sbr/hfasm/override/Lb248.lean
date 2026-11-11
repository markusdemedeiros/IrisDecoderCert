set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem blk_Lb248 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.Lb248" := by
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
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | (rw [hld]; rfl) | close_cell
