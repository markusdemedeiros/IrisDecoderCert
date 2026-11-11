set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_La8f6 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.La8f6" := by
  clear hc
  cfg_block
  measure_hb "La8f6"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, hm⟩, hn⟩ := hs₀
    have hr9 := hf1_r9_hSL x _ _ h4 h5
    have hrdx := hf1_toInt32 _ _ h7 (by have := h0.2.2.2.2.2.2.2.2.2.1; omega)
    rw [La8f6_pre] at hm
    vcgen
    all_goals try refine ⟨s0_tbl_La8f6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try (left; refine Table.ofLabels_at (l := "sbr_hf_assemble.La9c2") ⟨by decide, La9c2_tbl_La8f6 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩)
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals try simp only [hr9] at *
    all_goals try simp only [h3, h6, hrdx, hSL, BitVec.setWidth_32_64_32] at ⊢
    -- loaded values by their cells (`cell_reads`): the `t_env` bytes are then closed by `hf_te_sw`
    all_goals try cell_reads
    all_goals first
      | omega | with_reducible assumption | cell_some | cell_lcpi | cell_val
      | (simp only [BitVec.ofInt8_ofBytes_toBytes1]
         rw [hf_te_sw _ (by have := h0.2.2.2.2.2.2.2.2.2.2.1 0 (by omega); have := h0.2.2.2.2.2.2.2.2.2.2.1 1 (by omega); omega)])
      | close_cell
