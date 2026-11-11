set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem blk_m1 (k : Nat) (hk : k ≤ 2 ^ 32) (fs : HfFns) (hc : HfCallees k fs)
    (x : HfArgs) (ra : Int64) (t₀ : MachineData) : BlockOb k fs x ra t₀ "sbr_hf_assemble.m1" := by
  clear hc
  cfg_block
  measure_hb "m1"
    intro n
    refine Triple.pin fun s₀ hs₀ => ?_
    obtain ⟨⟨h0, ⟨hrsp, hrbp⟩, h2, h3, h4, h5, h6, h7, h8, h9, hm⟩, hn⟩ := hs₀
    rw [m1_pre] at hm
    have hm1 : 1 ≤ x.m := h0.2.2.2.2.2.2.1
    have hm48 : x.m ≤ 48 := h0.2.2.2.2.2.2.2.1
    vcgen
    all_goals try refine ⟨m2_tbl_m1 _ _ _ _ _ _ ⟨h0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    all_goals try subst_vars
    all_goals try simp only [Reg64s.get64_set64, reduceCtorEq, ite_true, ite_false,
      Nat.reducePow, Nat.reduceDiv, Nat.reduceMul, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd,
      BitVec.toNat_ofNat, AddrIndex.offset64, BitVec.sub_sub_eight, BitVec.reduceAdd, add_zero64, Int64.toBitVec_ofNat_norm, rbpo_30, rbpo_38, rbpo_40, rbpo_48, rbpo_50, rbpo_54, rbpo_70, rbpo_78, rbpo_80, rbpo_88, rbpo_90, rbpo_98, rbpo_9c, rbpo_a8, rbpo_b0, rbpo_b8, rbpo_c0, rbpo_c8, rbpo_d0, rbpo_d8, rbpo_e0, rbpo_e8, rbpo_f0, rbpo_100, rbpo_1c0, rbpo_280, hrsp, hrbp,
      Base, ArgRegs, BitVec.xor_self, BitVec.setWidth_32_64_32, sete_z_low, BitVec.ofInt_toInt, RegZmms.get_set_xmm_same, RegZmms.get_set_xmm_ne,
      ne_eq, not_false_eq_true,
      Reg64s.get_low32, Width.bytes, BitVec.add_zero] at *
    all_goals try dsimp only at hn hm ⊢
    -- the cell closers, then the frame goal through `hf2_r9mul` before any `grind` (a failing
    -- `grind` on it costs 0.17M)
    all_goals first
      | omega | with_reducible assumption | cell_some | cell_lcpi | cell_val
      | (simp only [h4, hf2_r9mul]; close_cell)
      | close_cell
      | (rw [h4]; exact hf2_r9mul x)
      | (rw [h8]; first | exact hf2_sub1 _ hm1 hm48 | exact hf2_addm1 _ hm1 hm48 | exact hf2_m1addm1 _ hm1 hm48)
      | ((repeat apply Mem.loadInt_isSome_storeInt); simp only [Hid, DataW, Blocks, Std.ExtHashMap.sep_assoc] at hm; grind_cells')
