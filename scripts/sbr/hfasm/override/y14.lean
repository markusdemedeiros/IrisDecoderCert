set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_y14 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.y14" := by
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
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, hrsp, hrbp, te_row,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    all_goals first | y_close
